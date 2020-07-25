//
// Created by dragos on 31.05.2019.
//

#include "PSAConverter.h"
#include <common/parseInput.h>
#include <fstream>
#include <p4/toP4/toP4.h>
#include <test/gtest/helpers.h>

namespace BMV2 {
const IR::Node *cleanNode(const IR::Node *node) {
  auto copy = node->clone();
  copy->srcInfo = Util::SourceInfo();
  return copy;
}

std::map<cstring, unsigned> PACKET_PATH_NUMBERS = {
    {"NORMAL", 0},     {"NORMAL_UNICAST", 0}, {"NORMAL_MULTICAST", 0},
    {"CLONE_I2E", 3},  {"CLONE_E2E", 4},      {"RESUBMIT", 5},
    {"RECIRCULATE", 6}};
class MkIngressParser : public Inspector {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  V1ProgramStructure *structure;
};

class DeclareStructsAndHeaders : public Inspector {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  bool externs;

public:
  const IR::P4Program *newprogram;
  DeclareStructsAndHeaders(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                           const IR::P4Program *newprogram)
      : refMap(refMap), typeMap(typeMap), externs(false),
        newprogram(newprogram) {}
  DeclareStructsAndHeaders(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                           bool externs, const IR::P4Program *newprogram)
      : refMap(refMap), typeMap(typeMap), externs(externs),
        newprogram(newprogram) {}

  bool preorder(const IR::Type_Header *node) override {
    if (externs)
      return false;
    if (!newprogram->getDeclsByName(node->name)->count()) {
      // most likely it's already there
      auto cl = newprogram->clone();
      cl->objects.push_back(cleanNode(node));
      newprogram = cl;
    }
    return false;
  }

  bool preorder(const IR::Type_Extern *node) override {
    if (!externs)
      return false;
    if (!newprogram->getDeclsByName(node->name)->count()) {
      // most likely it's not already there
      auto cl = newprogram->clone();
      LOG4("declaring extern " << node);
      cl->objects.push_back(cleanNode(node));
      newprogram = cl;
    }
    return false;
  }

  bool preorder(const IR::Type_Struct *node) override {
    if (externs)
      return false;
    if (!newprogram->getDeclsByName(node->name)->count()) {
      // most likely it's already there
      auto cl = newprogram->clone();
      cl->objects.push_back(cleanNode(node));
      newprogram = cl;
    }
    return false;
  }

  bool preorder(const IR::Type_Enum *node) override {
    if (externs)
      return false;
    if (!newprogram->getDeclsByName(node->name)->count()) {
      // most likely it's already there
      auto cl = newprogram->clone();
      cl->objects.push_back(cleanNode(node));
      newprogram = cl;
    }
    return false;
  }
  bool preorder(const IR::Type_Error *errtype) override {
    if (externs)
      return false;
    auto tt = typeMap->getTypeType(errtype, true)->to<IR::Type_Error>();
    IR::IndexedVector<IR::Declaration_ID> tobedeclared;
    for (auto mem : errtype->members) {
      if (!tt->getDeclByName(mem->name)) {
        tobedeclared.push_back(mem);
      }
    }
    if (!tobedeclared.empty()) {
      auto newerrtype = new IR::Type_Error(errtype->name, tobedeclared);
      auto cl = newprogram->clone();
      cl->objects.push_back(newerrtype);
      newprogram = cl;
    }
    return false;
  }
};

class FindStandardMetadataReferences : public Inspector {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  std::set<const IR::PathExpression *> &to_be_replaced;
  BMV2::V1ProgramStructure *structure;

public:
  FindStandardMetadataReferences(
      P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
      std::set<const IR::PathExpression *> &to_be_replaced,
      V1ProgramStructure *structure)
      : refMap(refMap), typeMap(typeMap), to_be_replaced(to_be_replaced),
        structure(structure) {}

  void postorder(const IR::PathExpression *pe) override {
    auto control = findContext<IR::P4Control>();
    if (control) {
      if (control == structure->ingress || control == structure->egress) {
        auto ref = refMap->getDeclaration(pe->path);
        if (ref->is<IR::Parameter>()) {
          if (control->getApplyParameters()->getParameter(2) == ref) {
            to_be_replaced.emplace(pe);
          }
        }
      }
    } else {
      auto parser = findContext<IR::P4Parser>();
      if (parser == structure->parser) {
        auto ref = refMap->getDeclaration(pe->path);
        if (ref->is<IR::Parameter>()) {
          if (parser->getApplyParameters()->getParameter(3) == ref) {
            to_be_replaced.emplace(pe);
          }
        }
      }
    }
  }
};

class ControlHandler : public virtual Visitor {
protected:
  const IR::P4Control *currentControl() {
    auto ct = getChildContext();
    if (auto crt = ct->original->to<IR::P4Control>())
      return crt;
    return findContext<IR::P4Control>();
  }
  IR::Expression *standardMetadata() {
    auto ctrl = currentControl();
    if (ctrl->name == "ingress" || ctrl->name == "egress") {
      auto metaParm = currentControl()->getApplyParameters()->getParameter(1);
      return new IR::Member(new IR::PathExpression(metaParm->name),
                            "standard_metadata");
    } else if (ctrl->name == "ingressDeparser") {
      auto metaParm = currentControl()->getApplyParameters()->getParameter(5);
      return new IR::Member(new IR::PathExpression(metaParm->name),
                            "standard_metadata");
    } else if (ctrl->name == "egressDeparser") {
      auto metaParm = currentControl()->getApplyParameters()->getParameter(4);
      return new IR::Member(new IR::PathExpression(metaParm->name),
                            "standard_metadata");
    }
    BUG("can't reason about %1%", ctrl);
  }
  IR::Expression *istd() {
    auto istd = currentControl()->getApplyParameters()->getParameter(2);
    auto expr = new IR::PathExpression(istd->name);
    return expr;
  }
  IR::Expression *ostd() {
    auto istd = currentControl()->getApplyParameters()->getParameter(3);
    auto expr = new IR::PathExpression(istd->name);
    return expr;
  }
};

#define ASSIGN(left, right)                                                    \
  new IR::AssignmentStatement(                                                 \
      left, new IR::MethodCallExpression(                                      \
                new IR::PathExpression("do_cast"),                             \
                new IR::Vector<IR::Argument>(                                  \
                    {new IR::Argument(right), new IR::Argument(left)})))

#define PUSH(bla) body->push_back(bla)
class HandleControlInput : public ControlHandler, Transform {
  cstring name;

public:
  HandleControlInput(const cstring &name) : name(name) {}

  const IR::Node *preorder(IR::P4Control *control) override {
    if (control->name != name)
      prune();
    return control;
  }
  IR::Statement *map_packet_path() {
    auto pp = new IR::Member(istd(), "packet_path");
    auto PSA_PACKET_PATH = new IR::PathExpression("PSA_PacketPath_t");
    IR::Statement *crt = new IR::EmptyStatement();
    for (const auto &p : PACKET_PATH_NUMBERS) {
      auto cond = new IR::Equ(pp, new IR::Member(PSA_PACKET_PATH, p.first));
      auto asg =
          ASSIGN(new IR::Member(standardMetadata(), "instance_type"),
                 new IR::Constant(new IR::Type_Bits(32, false), p.second));
      crt = new IR::IfStatement(cond, asg, crt);
    }
    return crt;
  }
  IR::Statement *map_fields(cstring src, cstring dst) {
    auto left = new IR::Member(standardMetadata(), dst);
    auto right = new IR::Member(istd(), src);
    return ASSIGN(left, right);
  }

  const IR::Node *postorder(IR::P4Control *control) override {
    // INGRESS rules:
    // packet_path -> instance_type
    auto body = new IR::BlockStatement();
    PUSH(map_packet_path());
    // ingress_port -> ingress_port
    if (name == "ingress") {
      PUSH(map_fields("ingress_port", "ingress_port"));
      PUSH(map_fields("ingress_timestamp", "ingress_global_timestamp"));
    }
    PUSH(map_fields("parser_error", "parser_error"));
    // timestamp -> ingress_global_timestamp
    // parser_error -> parser_error
    // EGRESS rules:
    // class_of_service -> priority (?)
    // packet_path -> instance_type
    // egress_port -> egress_port
    // timestamp -> egress_global_timestamp
    // parser_error -> parser_error
    if (name == "egress") {
      PUSH(map_fields("class_of_service", "priority"));
      PUSH(map_fields("egress_port", "egress_port"));
      PUSH(map_fields("egress_timestamp", "egress_global_timestamp"));
    }
    body->components.insert(body->components.end(),
                            control->body->components.begin(),
                            control->body->components.end());
    control->body = body;
    return control;
  }
};

class HandleControlOutput : public ControlHandler, Transform {
  cstring name;

public:
  HandleControlOutput(const cstring &name) : name(name) {}

  const IR::Node *preorder(IR::P4Control *control) override {
    if (control->name != name)
      prune();
    return control;
  }
  IR::Statement *map_fields(cstring src, cstring dst) {
    return ASSIGN(new IR::Member(ostd(), dst),
                  new IR::Member(standardMetadata(), src));
  }
  const IR::Node *postorder(IR::P4Control *control) override {
    // INGRESS rules:
    // priority -> class_of_service
    // clone_spec <> 0 -> clone
    // clone_spec & 0xFFFF -> clone_session_id
    // egress_spec == 511 -> drop
    // mcast_grp -> multicast_group
    // egress_spec -> egress_port
    auto body = control->body->clone();
    if (name == "ingress") {
      PUSH(map_fields("priority", "class_of_service"));
      PUSH(map_fields("egress_spec", "egress_port"));
      PUSH(map_fields("mcast_grp", "multicast_group"));
    }

    PUSH(ASSIGN(
        new IR::Member(ostd(), "clone_session_id"),
        new IR::Cast(
            new IR::Type_Bits(16, false),
            new IR::BAnd(
                new IR::Member(standardMetadata(), "clone_spec"),
                new IR::Constant(new IR::Type_Bits(32, false), 0xFFFF)))));
    PUSH(new IR::AssignmentStatement(
        new IR::Member(ostd(), "clone"),
        new IR::Mux(
            new IR::Equ(new IR::Member(standardMetadata(), "clone_spec"),
                        new IR::Constant(new IR::Type_Bits(32, false), 0)),
            new IR::BoolLiteral(false), new IR::BoolLiteral(true))));
    PUSH(new IR::AssignmentStatement(
        new IR::Member(ostd(), "drop"),
        new IR::Mux(
            new IR::Equ(new IR::Member(standardMetadata(), "egress_spec"),
                        new IR::Constant(new IR::Type_Bits(9, false), 511)),
            new IR::BoolLiteral(true), new IR::BoolLiteral(false))));
    control->body = body;
    return control;
  }
};

class ReplaceStandardMetadataReferences : public Transform {
  std::set<const IR::PathExpression *> &to_be_replaced;

public:
  ReplaceStandardMetadataReferences(
      std::set<const IR::PathExpression *> &to_be_replaced)
      : to_be_replaced(to_be_replaced) {}

  const IR::Node *postorder(IR::PathExpression *exp) override {
    auto orig = getOriginal<IR::PathExpression>();
    if (to_be_replaced.count(orig)) {
      auto control = findContext<IR::P4Control>();
      if (control) {
        auto parm = control->getApplyParameters()->getParameter(1);
        return new IR::Member(new IR::PathExpression(parm->name),
                              "standard_metadata");
      } else {
        auto parser = findContext<IR::P4Parser>();
        auto parm = parser->getApplyParameters()->getParameter(2);
        return new IR::Member(new IR::PathExpression(parm->name),
                              "standard_metadata");
      }
    }
    return exp;
  }
};

class GatherAllMetadataAndHeaders : public Inspector {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  BMV2::V1ProgramStructure *structure;
  std::set<IR::Expression *> &headers;
  std::set<IR::Expression *> &metas;
  std::map<IR::Expression *, const IR::Type *> &metaTypes;

public:
  GatherAllMetadataAndHeaders(
      P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
      V1ProgramStructure *structure, std::set<IR::Expression *> &headers,
      std::set<IR::Expression *> &metas,
      std::map<IR::Expression *, const IR::Type *> &metaTypes)
      : refMap(refMap), typeMap(typeMap), structure(structure),
        headers(headers), metas(metas), metaTypes(metaTypes) {}

  void postorder(const IR::Declaration *parm) override {
    auto parser = findContext<IR::P4Parser>();
    if (parser != structure->parser) {
      return;
    }
    auto parmType = typeMap->getType(parm);
    if (auto strt = parmType->to<IR::Type_Struct>()) {
      bool all_scalars = true;
      for (auto sf : strt->fields) {
        auto sft = typeMap->getType(sf);
        if (sft->is<IR::Type_StructLike>()) {
          all_scalars = false;
          break;
        }
      }
      auto ctx = getChildContext();
      auto child = ctx;
      std::vector<cstring> components;
      while (ctx->node->is<IR::Declaration>()) {
        auto dec = ctx->node->to<IR::Declaration>();
        components.push_back(dec->name);
        child = ctx;
        ctx = ctx->parent;
      }
      if (child->node->is<IR::Parameter>() &&
          parser->getApplyParameters()->getParameter(3) == child->node) {
        // standard meta goes here
        auto metaName = parser->getApplyParameters()->getParameter(2)->name;
        components.clear();
        components.push_back("standard_metadata");
        components.push_back(metaName);
      }
      if (all_scalars) {
        IR::Expression *crt = nullptr;
        for (auto I = components.rbegin(); I != components.rend(); ++I) {
          if (!crt) {
            crt = new IR::PathExpression(*I);
          } else {
            crt = new IR::Member(crt, *I);
          }
        }
        for (auto sf : strt->fields) {
          auto sft = typeMap->getType(sf);
          auto I = metas.emplace(new IR::Member(crt, sf->name));
          metaTypes.emplace(*I.first, sft);
        }
      }
    } else if (parmType->is<IR::Type_Header>()) {
      auto ctx = getChildContext();
      std::vector<cstring> components;
      while (ctx->node->is<IR::Declaration>()) {
        auto dec = ctx->node->to<IR::Declaration>();
        components.push_back(dec->name);
        ctx = ctx->parent;
      }
      IR::Expression *crt = nullptr;
      for (auto I = components.rbegin(); I != components.rend(); ++I) {
        if (!crt) {
          crt = new IR::PathExpression(*I);
        } else {
          crt = new IR::Member(crt, *I);
        }
      }
      headers.emplace(crt);
    } else if (auto hdrStack = parmType->to<IR::Type_Stack>()) {
      auto ctx = getChildContext();
      std::vector<cstring> components;
      while (ctx->node->is<IR::Declaration>()) {
        auto dec = ctx->node->to<IR::Declaration>();
        components.push_back(dec->name);
        ctx = ctx->parent;
      }
      IR::Expression *crt = nullptr;
      for (auto I = components.rbegin(); I != components.rend(); ++I) {
        if (!crt) {
          crt = new IR::PathExpression(*I);
        } else {
          crt = new IR::Member(crt, *I);
        }
      }
      for (unsigned i = 0; i != hdrStack->getSize(); ++i)
        headers.emplace(new IR::ArrayIndex(crt, new IR::Constant(i)));
    }
  }
};

class RenameParserStart : public Transform {
  const IR::P4Parser *oldParser;
  bool transformed = false;

public:
  RenameParserStart(const IR::P4Parser *oldParser) : oldParser(oldParser) {
    visitDagOnce = false;
  }

  const IR::Node *preorder(IR::P4Parser *parser) override {
    if (getOriginal<IR::P4Parser>()->name != oldParser->name) {
      prune();
    }
    return parser;
  }
  const IR::Node *postorder(IR::ParserState *state) override {
    if (!transformed && state->name == IR::ParserState::start) {
      transformed = true;
      auto newstate = new IR::ParserState("start_", state->components,
                                          state->selectExpression);
      state->selectExpression = new IR::PathExpression("start_");
      state->components.clear();
      return new IR::IndexedVector<IR::ParserState>({newstate, state});
    }
    return state;
  }
};

class IngressParserPopulateStandardMeta : public Transform {
  const IR::Expression *standard_meta() {
    auto parser = findContext<IR::P4Parser>();
    auto parm = parser->getApplyParameters()->getParameter(2);
    return new IR::Member(new IR::PathExpression(parm->name),
                          "standard_metadata");
  }

public:
  const IR::Node *preorder(IR::P4Parser *parser) override {
    if (parser->name != "ingressParser") {
      prune();
    }
    return parser;
  }
  const IR::Node *postorder(IR::ParserState *state) override {
    if (state->name == IR::ParserState::start) {
      auto istd = new IR::PathExpression("istd");
      auto ingressPort = new IR::Member(istd, "ingress_port");
      auto stm = standard_meta();
      auto stmiport = new IR::Member(stm, "ingress_port");
      state->components.push_back(ASSIGN(stmiport, ingressPort));
    }
    return state;
  }
};

class EgressParserPopulateStandardMeta : public Transform {
  const IR::Expression *standard_meta() {
    auto parser = findContext<IR::P4Parser>();
    auto parm = parser->getApplyParameters()->getParameter(2);
    return new IR::Member(new IR::PathExpression(parm->name),
                          "standard_metadata");
  }

public:
  const IR::Node *preorder(IR::P4Parser *parser) override {
    if (parser->name != "egressParser") {
      prune();
    }
    return parser;
  }
  const IR::Node *postorder(IR::ParserState *state) override {
    if (state->name == IR::ParserState::start) {
      auto istd = new IR::PathExpression("istd");
      auto ingressPort = new IR::Member(istd, "egress_port");
      auto stm = standard_meta();
      auto stmiport = new IR::Member(stm, "egress_port");
      state->components.push_back(ASSIGN(stmiport, ingressPort));
    }
    return state;
  }
};

class IngressParserAddInitializer : public Transform {
  std::set<cstring> &allowed_paths;
  cstring name;
  static unsigned get_instance_type(cstring name) {
    /*
     * NORMAL,
    NORMAL_UNICAST,   /// Normal packet received by egress which is unicast
    NORMAL_MULTICAST, /// Normal packet received by egress which is multicast
    CLONE_I2E,  /// Packet created via a clone operation in ingress,
                /// destined for egress
    CLONE_E2E,  /// Packet created via a clone operation in egress,
                /// destined for egress
    RESUBMIT,   /// Packet arrival is the result of a resubmit operation
    RECIRCULATE
     */
    if (name == "NORMAL")
      return 0;
    else if (name == "NORMAL_UNICAST")
      return 0;
    else if (name == "NORMAL_MULTICAST")
      return 0;
    else if (name == "CLONE_I2E")
      return 3;
    else if (name == "CLONE_E2E")
      return 4;
    else if (name == "RESUBMIT")
      return 5;
    else if (name == "RECIRCULATE")
      return 6;
    else
      BUG("unknown %1%", name);
  }

public:
  IngressParserAddInitializer(std::set<cstring> &allowed_paths,
                              const cstring &name)
      : allowed_paths(allowed_paths), name(name) {}

  const IR::Node *preorder(IR::P4Parser *parser) override {
    if (parser->name != name) {
      prune();
    }
    return parser;
  }
  const IR::Expression *standard_meta() {
    auto parser = findContext<IR::P4Parser>();
    auto parm = parser->getApplyParameters()->getParameter(2);
    return new IR::Member(new IR::PathExpression(parm->name),
                          "standard_metadata");
  }
  const IR::Node *postorder(IR::ParserState *state) override {
    if (state->name == IR::ParserState::start) {
      auto orig = getOriginal<IR::ParserState>();
      auto parser = findContext<IR::P4Parser>();
      auto parm = parser->getApplyParameters()->getParameter(3);
      auto expr =
          new IR::Member(new IR::PathExpression(parm->name), "packet_path");
      auto lexp = new IR::ListExpression(IR::Vector<IR::Expression>({expr}));
      IR::Vector<IR::SelectCase> selectCases;
      for (auto allowed : allowed_paths) {
        IR::SelectCase *selc = getCase(allowed);
        selectCases.push_back(selc);
      }
      state->selectExpression = new IR::SelectExpression(lexp, selectCases);
      auto states = new IR::IndexedVector<IR::ParserState>();
      auto stm = standard_meta();
      auto instance_type = new IR::Member(stm, "instance_type");
      for (auto allowed : allowed_paths) {
        auto ps = new IR::ParserState(cstring("start_" + allowed),
                                      orig->selectExpression);
        ps->components.push_back(new IR::AssignmentStatement(
            instance_type, new IR::Constant(new IR::Type_Bits(32, false),
                                            get_instance_type(allowed))));
        states->push_back(ps);
      }
      states->push_back(state);
      return states;
    }
    return state;
  }

  IR::SelectCase *getCase(const cstring &now) const {
    auto name_now = cstring("start_" + now);
    auto constantExpr =
        new IR::Member(new IR::PathExpression("PSA_PacketPath_t"), now);
    auto selc =
        new IR::SelectCase(constantExpr, new IR::PathExpression(name_now));
    return selc;
  }
};
struct location {
  int idx;
  cstring mem;
  location(int idx) : idx(idx) {}
  location(cstring mem) : idx(-1), mem(mem) {}
  bool is_idx() const { return idx >= 0; }
  bool operator<(const location &other) const {
    if (is_idx() != other.is_idx()) {
      return is_idx();
    }
    if (is_idx()) {
      return idx < other.idx;
    } else
      return mem < other.mem;
  }
};

cstring stringify(const std::vector<location> &locs) {
  std::stringstream ss;
  ss << "field";
  for (auto &l : locs) {
    ss << '_';
    if (l.is_idx())
      ss << l.idx;
    else
      ss << l.mem;
  }
  return cstring(ss.str());
}

class DisentangleExpression : public Inspector {
  std::vector<location> &locs;

public:
  static std::vector<location> disentangle(const IR::Expression *e) {
    std::vector<location> locs;
    DisentangleExpression disentangleExpression(locs);
    e->apply(disentangleExpression);
    return std::move(disentangleExpression.locs);
  }
  DisentangleExpression(std::vector<location> &locs) : locs(locs) {}

  void end_apply() override { std::reverse(locs.begin(), locs.end()); }

  bool preorder(const IR::Member *mem) override {
    locs.emplace_back(mem->member);
    return true;
  }
  bool preorder(const IR::ArrayIndex *idx) override {
    BUG_CHECK(idx->right->is<IR::Constant>(), "array index must be a constant");
    locs.emplace_back(idx->right->to<IR::Constant>()->asInt());
    return true;
  }
  bool preorder(const IR::PathExpression *pex) override {
    locs.emplace_back(pex->path->name);
    return true;
  }
};

class DisentangleNestedExpression : public Inspector {
  std::map<std::vector<location>, const IR::Expression *> &expressions;

public:
  DisentangleNestedExpression(
      std::map<std::vector<location>, const IR::Expression *> &expressions)
      : expressions(expressions) {}

public:
  static std::map<std::vector<location>, const IR::Expression *>
  disentangle(const IR::ListExpression *expression) {
    std::map<std::vector<location>, const IR::Expression *> all_locations;
    DisentangleNestedExpression disentangleExpression(all_locations);
    expression->apply(disentangleExpression);
    return all_locations;
  }
  bool preorder(const IR::ListExpression *lexp) override {
    for (auto e : lexp->components) {
      if (e->is<IR::ListExpression>()) {
        visit(e);
      } else {
        auto locs = DisentangleExpression::disentangle(e);
        expressions.emplace(std::move(locs), e);
      }
    }
    return false;
  }
};

class FindFieldLists : public ControlHandler, Inspector {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  V1ProgramStructure *structure;
  std::map<std::set<std::vector<location>>, unsigned> &field_lists;
  std::map<std::vector<location>, const IR::Type *> &mem_type;
  std::map<const IR::Node *, unsigned> &primitive_mapping;

public:
  FindFieldLists(
      P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
      V1ProgramStructure *structure,
      std::map<std::set<std::vector<location>>, unsigned int> &field_lists,
      std::map<std::vector<location>, const IR::Type *> &mem_type,
      std::map<const IR::Node *, unsigned> &primitive_mapping)
      : refMap(refMap), typeMap(typeMap), structure(structure),
        field_lists(field_lists), mem_type(mem_type),
        primitive_mapping(primitive_mapping) {}

  void postorder(const IR::MethodCallExpression *mce) override {
    auto mi = P4::MethodInstance::resolve(mce, refMap, typeMap);
    auto top_stat = findContext<IR::Statement>();
    if (auto ef = mi->to<P4::ExternFunction>()) {
      if (P4V1::V1Model::instance.clone.clone3.name == ef->method->name) {
        auto fl = mce->arguments->at(2);
        auto lexp = fl->expression->to<IR::ListExpression>();
        auto flid = extractFieldList(lexp);
        primitive_mapping[top_stat] = flid;
      } else if (P4V1::V1Model::instance.resubmit.name == ef->method->name) {
        auto fl = mce->arguments->at(0);
        auto lexp = fl->expression->to<IR::ListExpression>();
        auto flid = extractFieldList(lexp);
        primitive_mapping[top_stat] = flid;
      } else if (P4V1::V1Model::instance.recirculate.name == ef->method->name) {
        auto fl = mce->arguments->at(0);
        auto lexp = fl->expression->to<IR::ListExpression>();
        auto flid = extractFieldList(lexp);
        primitive_mapping[top_stat] = flid;
      } else if (P4V1::V1Model::instance.clone.name == ef->method->name) {
        primitive_mapping[top_stat] = 0;
      }
    }
  }

  unsigned extractFieldList(const IR::ListExpression *lexp) {
    auto final = DisentangleNestedExpression::disentangle(lexp);
    std::set<std::vector<location>> final_locations;
    for (auto &locs_exprs : final) {
      auto locations = locs_exprs.first;
      auto e = locs_exprs.second;
      auto control = currentControl();
      if (control != structure->ingress && control != structure->egress) {
        BUG("calling clone from control %1%, must be ingress or egress "
            "(please inline)",
            control);
      }
      for (unsigned idx = 0; idx != control->getApplyParameters()->size();
           ++idx) {
        auto p = control->getApplyParameters()->getParameter(idx);
        if (p->name == locations[0].mem) {
          if (idx == 1) {
            locations[0] = 1;
            mem_type[locations] = typeMap->getType(e);
          } else if (idx == 0) {
            locations[0] = 0;
            mem_type[locations] = typeMap->getType(e);
          } else if (idx == 2) {
            // standard meta
            locations[0] = cstring("standard_metadata");
            locations.insert(locations.begin(), 1);
            mem_type[locations] = typeMap->getType(e);
          } else
            BUG("can't handle this argument %1% at position %2%", p, idx);
          break;
        }
      }
      final_locations.emplace(locations);
    }
    return field_lists.emplace(move(final_locations), field_lists.size() + 1)
        .first->second;
  }
};

class MakeNormalMetaType : public Transform {
  cstring headerType;
  cstring metaType;

public:
  MakeNormalMetaType(const cstring &headerType, const cstring &metaType)
      : headerType(headerType), metaType(metaType) {}

  const IR::Node *preorder(IR::Type_Struct *strs) override {
    if (strs->name == "normal_meta_t") {
      strs->fields.push_back(
          new IR::StructField("headers", new IR::Type_Name(headerType)));
      strs->fields.push_back(
          new IR::StructField("meta", new IR::Type_Name(metaType)));
    }
    prune();
    return strs;
  }
};

class PopulateForwardingMetas : public ControlHandler, Transform {
  bool ingressDeparser;
  std::map<std::set<std::vector<location>>, unsigned> &field_lists;

public:
  PopulateForwardingMetas(
      std::map<std::set<std::vector<location>>, unsigned int> &field_lists)
      : field_lists(field_lists) {}

  const IR::Node *preorder(IR::P4Control *control) override {
    if (control->name == "egressDeparser" ||
        control->name == "ingressDeparser") {
      ingressDeparser = control->name == "ingressDeparser";
    } else {
      prune();
    }
    return control;
  }

  const IR::Expression *headers() {
    if (ingressDeparser)
      return new IR::PathExpression(
          currentControl()->getApplyParameters()->getParameter(4)->name);
    else
      return new IR::PathExpression(
          currentControl()->getApplyParameters()->getParameter(3)->name);
  }
  const IR::Expression *metas() {
    if (ingressDeparser)
      return new IR::PathExpression(
          currentControl()->getApplyParameters()->getParameter(5)->name);
    else
      return new IR::PathExpression(
          currentControl()->getApplyParameters()->getParameter(4)->name);
  }

  const IR::Statement *populate_field_list(const IR::Expression *headers,
                                           const IR::Expression *metas,
                                           const IR::Expression *field_list_id,
                                           const IR::Type *field_list_id_kind,
                                           const IR::Expression *target) {
    const IR::Statement *stat = new IR::EmptyStatement;
    for (auto &l : field_lists) {
      // if field_list == l.second
      auto cond = new IR::Equ(field_list_id,
                              new IR::Constant(field_list_id_kind, l.second));
      auto bs = new IR::BlockStatement();
      auto assign_flid = ASSIGN(new IR::Member(target, "flid"), field_list_id);
      bs->push_back(assign_flid);
      for (auto &to_be_copied : l.first) {
        auto I = to_be_copied.begin();
        const IR::Expression *crt = nullptr;
        if (I->idx == 0) {
          crt = headers;
        } else {
          crt = metas;
        }
        ++I;
        for (; I != to_be_copied.end(); ++I) {
          if (I->is_idx()) {
            crt = new IR::ArrayIndex(crt, new IR::Constant(I->idx));
          } else {
            crt = new IR::Member(crt, I->mem);
          }
        }
        auto mem = stringify(to_be_copied);
        auto asg =
            new IR::AssignmentStatement(new IR::Member(target, mem), crt);
        bs->push_back(asg);
      }
      stat = new IR::IfStatement(cond, bs, stat);
    }
    return stat;
  }

  const IR::Node *postorder(IR::P4Control *control) override {
    auto newbody = control->body->clone();
    if (ingressDeparser) {
      IR::IfStatement *resubInstr = nullptr;
      auto stm = standardMetadata();
      {
        auto resubmit_flag = new IR::Member(stm, "resubmit_flag");
        auto resubmitCondition = new IR::Neq(
            resubmit_flag, new IR::Constant(new IR::Type_Bits(32, false), 0));
        auto asg = populate_field_list(headers(), metas(), resubmit_flag,
                                       new IR::Type_Bits(32, false),
                                       new IR::PathExpression("resub"));
        resubInstr = new IR::IfStatement(resubmitCondition, asg, nullptr);
      }
      IR::IfStatement *ci2einstr = nullptr;
      {
        auto ci2eflag = new IR::Shr(new IR::Member(stm, "clone_spec"),
                                    new IR::Constant(16));
        auto ci2econdition = new IR::Neq(
            ci2eflag, new IR::Constant(new IR::Type_Bits(32, false), 0));
        auto asg = populate_field_list(headers(), metas(), ci2eflag,
                                       new IR::Type_Bits(32, false),
                                       new IR::PathExpression("ci2e"));
        ci2einstr = new IR::IfStatement(ci2econdition, asg, nullptr);
      }
      IR::BlockStatement *normalInstr = nullptr;
      {
        auto normal_meta = new IR::PathExpression("nm");
        normalInstr = new IR::BlockStatement();
        normalInstr->push_back(new IR::AssignmentStatement(
            new IR::Member(normal_meta, "headers"), headers()));
        normalInstr->push_back(new IR::AssignmentStatement(
            new IR::Member(normal_meta, "meta"), metas()));
      }
      resubInstr->ifFalse = ci2einstr;
      ci2einstr->ifFalse = normalInstr;
      newbody->push_back(resubInstr);
    } else {
      IR::IfStatement *resubInstr = nullptr;
      auto stm = standardMetadata();
      {
        auto resubmit_flag = new IR::Member(stm, "recirculate_flag");
        auto resubmitCondition = new IR::Neq(
            resubmit_flag, new IR::Constant(new IR::Type_Bits(32, false), 0));
        auto asg = populate_field_list(
            headers(), metas(), resubmit_flag, new IR::Type_Bits(32, false),
            new IR::PathExpression("recirculate_meta"));
        resubInstr = new IR::IfStatement(resubmitCondition, asg, nullptr);
      }
      IR::IfStatement *ci2einstr = nullptr;
      {
        auto ci2eflag = new IR::Shr(new IR::Member(stm, "clone_spec"),
                                    new IR::Constant(16));
        auto ci2econdition = new IR::Neq(
            ci2eflag, new IR::Constant(new IR::Type_Bits(32, false), 0));
        auto asg = populate_field_list(headers(), metas(), ci2eflag,
                                       new IR::Type_Bits(32, false),
                                       new IR::PathExpression("ce2e"));
        ci2einstr = new IR::IfStatement(ci2econdition, asg, nullptr);
      }
      resubInstr->ifFalse = ci2einstr;
      newbody->push_back(resubInstr);
    }
    control->body = newbody;
    return control;
  }
};

class DefineHelperMetas : public Transform {
  std::map<std::set<std::vector<location>>, unsigned> &field_lists;
  std::map<std::vector<location>, const IR::Type *> &mem_type;

public:
  DefineHelperMetas(
      std::map<std::set<std::vector<location>>, unsigned int> &field_lists,
      std::map<std::vector<location>, const IR::Type *> &mem_type)
      : field_lists(field_lists), mem_type(mem_type) {}

  const IR::Node *postorder(IR::Type_Struct *str) override {
    if (str->name == "ci2e_t" || str->name == "ce2e_t" ||
        str->name == "recirculate_meta_t" || str->name == "resubmit_meta_t") {
      str->fields.push_back(
          new IR::StructField("flid", new IR::Type_Bits(16, false)));
      for (auto &mt : mem_type) {
        std::stringstream ss;
        ss << "field";
        for (auto loc : mt.first) {
          ss << "_";
          if (loc.is_idx())
            ss << loc.idx;
          else
            ss << loc.mem;
        }
        cstring cs(ss.str());
        const IR::Type *actual_type = mt.second;
        if (auto td = actual_type->to<IR::Type_Declaration>())
          actual_type = new IR::Type_Name(td->name);
        auto sf = new IR::StructField(cs, actual_type);
        str->fields.push_back(sf);
      }
    }
    return str;
  }
};

class IngressParserReadMetas : public Transform {
  std::map<std::set<std::vector<location>>, unsigned> &field_lists;
  std::map<std::vector<location>, const IR::Type *> &mem_type;
  cstring name;

public:
  IngressParserReadMetas(
      std::map<std::set<std::vector<location>>, unsigned int> &field_lists,
      std::map<std::vector<location>, const IR::Type *> &mem_type,
      const cstring &name)
      : field_lists(field_lists), mem_type(mem_type), name(name) {}

  const IR::Node *preorder(IR::P4Parser *parser) override {
    if (parser->name != name) {
      prune();
    }
    return parser;
  }
  const IR::Expression *get_corresponding(cstring ppath) {
    if (ppath == "NORMAL" && name == "ingressParser") {
      return nullptr;
    } else if (name == "ingressParser" && ppath == "RESUBMIT") {
      return new IR::PathExpression("resub");
    } else if (name == "ingressParser" && ppath == "RECIRCULATE") {
      return new IR::PathExpression("recirc");
    } else if (name == "egressParser" && ppath == "CLONE_I2E") {
      return new IR::PathExpression("ci2e");
    } else if (name == "egressParser" && ppath == "CLONE_E2E") {
      return new IR::PathExpression("ce2e");
    } else if (name == "egressParser" &&
               (ppath == "NORMAL_UNICAST" || ppath == "NORMAL_MULTICAST")) {
      return new IR::PathExpression("nm");
    } else {
      return nullptr;
    }
  }
  const IR::Expression *headers(const IR::P4Parser *parser) {
    return new IR::PathExpression(
        parser->getApplyParameters()->getParameter(1)->name);
  }
  const IR::Expression *metas(const IR::P4Parser *parser) {
    return new IR::PathExpression(
        parser->getApplyParameters()->getParameter(2)->name);
  }
  const IR::Node *postorder(IR::ParserState *state) override {
    auto parser = findContext<IR::P4Parser>();
    for (auto &p : PACKET_PATH_NUMBERS) {
      if (state->name == "start_" + p.first) {
        auto st = get_corresponding(p.first);
        if (!st)
          continue;
        if (p.first.startsWith("NORMAL")) {
          BUG_CHECK(
              name == "egressParser",
              "normal metadata must be defined only for the egress parser");
          auto hdr = headers(parser);
          auto met = metas(parser);
          auto nm = new IR::PathExpression("nm");
          state->components.push_back(
              new IR::AssignmentStatement(hdr, new IR::Member(nm, "headers")));
          state->components.push_back(
              new IR::AssignmentStatement(met, new IR::Member(nm, "meta")));
          return state;
        }
        auto flid = new IR::Member(st, "flid");
        auto new_states = new IR::IndexedVector<IR::ParserState>();
        IR::Vector<IR::SelectCase> cases;
        for (auto &l : field_lists) {
          auto nr = new IR::Constant(new IR::Type_Bits(16, false), l.second);
          std::stringstream ss;
          ss << state->name << l.second;
          auto state_name =
              new IR::ParserState(cstring(ss.str()), state->selectExpression);
          new_states->push_back(state_name);
          cases.push_back(
              new IR::SelectCase(nr, new IR::PathExpression(state_name->name)));
          for (auto &fl : l.first) {
            auto I = fl.begin();
            const IR::Expression *crt = nullptr;
            if (I->is_idx() && I->idx == 0) {
              crt = headers(parser);
            } else if (I->is_idx() && I->idx == 1) {
              crt = metas(parser);
            }
            ++I;
            for (; I != fl.end(); ++I) {
              if (I->is_idx())
                crt = new IR::ArrayIndex(crt, new IR::Constant(I->idx));
              else
                crt = new IR::Member(crt, I->mem);
            }
            auto mem = stringify(fl);
            state_name->components.push_back(
                new IR::AssignmentStatement(crt, new IR::Member(st, mem)));
          }
        }
        auto nr = new IR::Constant(new IR::Type_Bits(16, false), 0);
        auto zerocase = new IR::SelectCase(
            nr, state->selectExpression->to<IR::PathExpression>());
        cases.push_back(zerocase);
        auto selex = new IR::SelectExpression(
            new IR::ListExpression(IR::Vector<IR::Expression>({flid})), cases);
        state->selectExpression = selex;
        new_states->push_back(state);
        return new_states;
      }
    }
    return state;
  }
};

class ZeroOutMetas : public Transform {
  std::set<IR::Expression *> &headers;
  std::set<IR::Expression *> &metas;
  std::map<IR::Expression *, const IR::Type *> &metaTypes;

public:
  ZeroOutMetas(std::set<IR::Expression *> &headers,
               std::set<IR::Expression *> &metas,
               std::map<IR::Expression *, const IR::Type *> &metaTypes)
      : headers(headers), metas(metas), metaTypes(metaTypes) {}

  const IR::Node *postorder(IR::ParserState *state) override {
    if (state->name == IR::ParserState::start) {
      for (auto h : headers) {
        auto mce = new IR::MethodCallExpression(
            new IR::Member(h, IR::Type_Header::setInvalid));
        state->components.push_back(new IR::MethodCallStatement(mce));
      }
      for (auto meta : metas) {
        auto mtype = metaTypes[meta];
        IR::Expression *rv = nullptr;
        if (auto terror = mtype->to<IR::Type_Error>()) {
          rv = new IR::Member(new IR::PathExpression("error"),
                              terror->members.at(0)->name);
        } else if (auto tenum = mtype->to<IR::Type_Enum>()) {
          auto dec0 = tenum->members.at(0);
          rv = new IR::Member(new IR::PathExpression(tenum->name), dec0->name);
        } else {
          rv = new IR::Constant(metaTypes[meta], 0);
        }
        state->components.push_back(new IR::AssignmentStatement(meta, rv));
      }
    }
    return state;
  }
};

class RewritePrimitives : public ControlHandler, Transform {
  std::map<std::set<std::vector<location>>, unsigned> &field_lists;
  bool relaxed = false;

public:
  RewritePrimitives(
      std::map<std::set<std::vector<location>>, unsigned int> &field_lists,
      bool relaxed = false)
      : field_lists(field_lists), relaxed(relaxed) {}

  const IR::Node *postorder(IR::MethodCallStatement *stat) override {
    auto orig = getOriginal<IR::MethodCallStatement>();
    auto mce = orig->methodCall;
    if (auto pe = mce->method->to<IR::PathExpression>()) {
      unsigned nr = 0;
      const IR::ListExpression *lexp = nullptr;
      if (pe->path->name == P4V1::V1Model::instance.resubmit.name) {
        lexp = mce->arguments->at(0)->expression->to<IR::ListExpression>();
      } else if (pe->path->name == P4V1::V1Model::instance.recirculate.name) {
        lexp = mce->arguments->at(0)->expression->to<IR::ListExpression>();
      } else if (pe->path->name == P4V1::V1Model::instance.clone.clone3.name) {
        lexp = mce->arguments->at(2)->expression->to<IR::ListExpression>();
      } else if (pe->path->name == P4V1::V1Model::instance.clone.name) {
        nr = 0;
      } else if (pe->path->name == P4V1::V1Model::instance.drop.name) {
        const IR::Expression *stm = nullptr;
        if (relaxed) {
          auto control = currentControl();
          CHECK_NULL(control);
          auto metaParm = control->getApplyParameters()->getParameter(2);
          stm = new IR::PathExpression(metaParm->name);
        } else {
          stm = standardMetadata();
        }
        auto egress_spec = new IR::Member(stm, "egress_spec");
        return new IR::AssignmentStatement(
            egress_spec, new IR::Constant(new IR::Type_Bits(9, false), 511));
      } else {
        return stat;
      }
      if (lexp) {
        std::set<std::vector<location>> locations;
        auto expr_locs = DisentangleNestedExpression::disentangle(lexp);
        for (auto &p : expr_locs) {
          auto l = p.first;
          if (!l[0].is_idx()) {
            for (unsigned idx = 0;
                 idx != currentControl()->getApplyParameters()->size(); ++idx) {
              auto parm =
                  currentControl()->getApplyParameters()->getParameter(idx);
              if (parm->name == l[0].mem) {
                if (idx == 0) {
                  l[0] = 0;
                } else if (idx == 1) {
                  l[0] = 1;
                } else if (idx == 2 && relaxed) {
                  l[0] = cstring("standard_metadata");
                  l.insert(l.begin(), 1);
                } else {
                  BUG("unknown argument position");
                }
                break;
              }
            }
          }
          LOG4("for call " << stat << " " << stringify(l));
          locations.emplace(std::move(l));
        }
        auto I = field_lists.find(locations);
        if (I != field_lists.end()) {
          nr = I->second;
        } else {
          return stat;
        }
      }
      if (pe->path->name == P4V1::V1Model::instance.clone.name ||
          pe->path->name == P4V1::V1Model::instance.clone.clone3.name) {
        auto session = mce->arguments->at(1)->expression;
        const IR::Expression *stm = nullptr;
        if (relaxed) {
          auto control = currentControl();
          CHECK_NULL(control);
          auto metaParm = control->getApplyParameters()->getParameter(2);
          stm = new IR::PathExpression(metaParm->name);
        } else {
          stm = standardMetadata();
        }
        auto clone_spec = new IR::Member(stm, "clone_spec");
        const IR::Expression *fl =
            new IR::Constant(new IR::Type_Bits(32, false), nr);
        auto asg = new IR::AssignmentStatement(
            clone_spec,
            new IR::BOr(new IR::Shl(fl, new IR::Constant(16)),
                        new IR::Cast(new IR::Type_Bits(32, false), session)));
        return asg;
      } else if (pe->path->name == P4V1::V1Model::instance.recirculate.name) {
        const IR::Expression *stm = nullptr;
        if (relaxed) {
          auto control = currentControl();
          CHECK_NULL(control);
          auto metaParm = control->getApplyParameters()->getParameter(2);
          stm = new IR::PathExpression(metaParm->name);
        } else {
          stm = standardMetadata();
        }
        auto recirculate_flag = new IR::Member(stm, "recirculate_flag");
        const IR::Expression *fl =
            new IR::Constant(new IR::Type_Bits(32, false), nr);
        auto asg = new IR::AssignmentStatement(recirculate_flag, fl);
        return asg;
      } else if (pe->path->name == P4V1::V1Model::instance.resubmit.name) {
        const IR::Expression *stm = nullptr;
        if (relaxed) {
          auto control = currentControl();
          CHECK_NULL(control);
          auto metaParm = control->getApplyParameters()->getParameter(2);
          stm = new IR::PathExpression(metaParm->name);
        } else {
          stm = standardMetadata();
        }
        auto recirculate_flag = new IR::Member(stm, "resubmit_flag");
        const IR::Expression *fl =
            new IR::Constant(new IR::Type_Bits(32, false), nr);
        auto asg = new IR::AssignmentStatement(recirculate_flag, fl);
        return asg;
      }
    }
    return stat;
  }
};

class FixClones : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

public:
  FixClones(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}

private:
  void split(IR::Vector<IR::Expression> *res, const IR::Expression *e,
             const IR::Type *tp) {
    if (auto ts = tp->to<IR::Type_Struct>()) {
      for (const auto fld : ts->fields) {
        split(res, new IR::Member(e, fld->name), typeMap->getType(fld));
      }
    } else {
      BUG_CHECK(!tp->is<IR::Type_StructLike>() && !tp->is<IR::Type_Stack>(),
                "expecting primary: got %1%", tp);
      res->push_back(e);
    }
  }

  const IR::Node *postorder(IR::MethodCallStatement *stat) {
    auto mi = P4::MethodInstance::resolve(stat->methodCall, refMap, typeMap);
    if (auto ef = mi->to<P4::ExternFunction>()) {
      auto changearg = [&](unsigned argat) {
        auto arg2 = mi->expr->arguments->at(argat)->expression;
        if (auto oldexp = arg2->to<IR::ListExpression>()) {
          // flatten it
          auto a2cl = new IR::Vector<IR::Expression>();
          for (auto exp : oldexp->components) {
            split(a2cl, exp, typeMap->getType(exp));
          }
          auto lex = new IR::ListExpression(std::move(*a2cl));
          auto alist = mi->expr->arguments->clone();
          alist->at(argat) = new IR::Argument(lex);
          auto mcl = mi->expr->clone();
          mcl->typeArguments = new IR::Vector<IR::Type>();
          mcl->arguments = alist;
          stat->methodCall = mcl;
        }
      };
      if (ef->method->name == P4V1::V1Model::instance.clone.clone3.name) {
        changearg(2);
      } else if (ef->method->name == P4V1::V1Model::instance.resubmit.name) {
        changearg(0);
      } else if (ef->method->name == P4V1::V1Model::instance.recirculate.name) {
        changearg(0);
      }
    }
    return stat;
  }
};

RescueClone::RescueClone(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap) {
  passes.push_back(new FixClones(refMap, typeMap));
  addPasses({new P4::ClearTypeMap(typeMap), new P4::ResolveReferences(refMap),
             new P4::TypeInference(refMap, typeMap, false)});
}
}

BMV2::PSAConverter::PSAConverter(BMV2::BMV2Options &options,
                                 P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                                 P4V1::V1Model &v1model,
                                 BMV2::V1ProgramStructure *structure)
    : options(options), refMap(refMap), typeMap(typeMap), v1model(v1model),
      structure(structure) {}

void BMV2::PSAConverter::makeExplicitFieldLists(const IR::P4Program *program) {
  std::map<std::set<std::vector<BMV2::location>>, unsigned int> field_lists;
  std::map<const IR::Node *, unsigned int> primitive_mapping;
  std::map<std::vector<BMV2::location>, const IR::Type *> mem_type;
  BMV2::FindFieldLists ffl(this->refMap, this->typeMap, this->structure,
                           field_lists, mem_type, primitive_mapping);
  oldProgram = program;
  newprogram = oldProgram;
  oldProgram->apply(ffl);
  RewritePrimitives rw(field_lists, true);
  this->newprogram = newprogram->apply(rw);
  auto metafrom = new IR::PathExpression("from");
  auto metato = new IR::PathExpression("to");
  auto smfrom = new IR::PathExpression("smfrom");
  auto smto = new IR::PathExpression("smto");
  auto discriminator = new IR::PathExpression("discriminator");
  const IR::Statement *all = new IR::EmptyStatement();
  for (const auto &flmap : field_lists) {
    auto &vec = flmap.first;
    auto nr = flmap.second;
    auto stat = new IR::BlockStatement();
    for (const auto &path : vec) {
      unsigned idx = 0;
      auto firstcomponent = path[idx++].idx;
      BUG_CHECK(firstcomponent == 1, "expecting meta");
      auto nextcomponent = path[idx].mem;
      if (nextcomponent == "standard_metadata") {
        ++idx;
      }
      bool issm = idx == 2;
      const IR::Expression *crtfrom = metafrom;
      const IR::Expression *crtto = metato;
      if (issm) {
        crtfrom = smfrom;
        crtto = smto;
      }
      // if standard metadata, then do what it takes
      for (unsigned i = idx; i != path.size(); ++i) {
        auto &component = path[idx];
        if (!component.is_idx()) {
          crtfrom = new IR::Member(crtfrom, component.mem);
          crtto = new IR::Member(crtto, component.mem);
        } else {
          crtfrom =
              new IR::ArrayIndex(crtfrom, new IR::Constant(component.idx));
          crtto = new IR::ArrayIndex(crtto, new IR::Constant(component.idx));
        }
      }
      stat->push_back(new IR::AssignmentStatement(crtto, crtfrom));
    }
    all = new IR::IfStatement(new IR::Equ(discriminator, new IR::Constant(nr)),
                              stat, all);
  }
  auto nm =
      typeMap
          ->getType(structure->ingress->getApplyParameters()->parameters.at(1))
          ->to<IR::Type_Struct>()
          ->getName();
  auto metaTypeName = new IR::Type_Name(nm);
  auto plist = new IR::ParameterList();
  plist->push_back(new IR::Parameter("from", IR::Direction::In, metaTypeName));
  plist->push_back(new IR::Parameter("to", IR::Direction::InOut, metaTypeName));
  plist->push_back(
      new IR::Parameter("smfrom", IR::Direction::In,
                        new IR::Type_Name(v1model.standardMetadataType.name)));
  plist->push_back(
      new IR::Parameter("smto", IR::Direction::InOut,
                        new IR::Type_Name(v1model.standardMetadataType.name)));
  plist->push_back(new IR::Parameter("discriminator", IR::Direction::In,
                                     new IR::Type_Bits(16, false)));
  auto mtype = new IR::Type_Method(IR::Type_Void::get(), plist);
  auto fun =
      new IR::Function("copy_field_list", mtype, new IR::BlockStatement({all}));
  auto mut = newprogram->clone();
  mut->objects.push_back(fun);
  newprogram = mut;
  dump_new_program(options.explicitFieldLists);
}

const IR::P4Program *BMV2::PSAConverter::convert(const IR::P4Program *prog) {
  {
    std::ofstream old("oldprog.p4");
    P4::ToP4 olddump(&old, false);
    prog->apply(olddump);
    old.flush();
  }
  std::ofstream ofs(options.psaFile);
  ofs << "#include<core.p4>\n#include <psa.p4>\n";
  ofs.close();
  auto fclone = options.file;
  auto oldversion = options.langVersion;
  options.file = options.psaFile;
  options.langVersion = CompilerOptions::FrontendVersion::P4_16;
  newprogram = P4::parseP4File(options);
  options.file = fclone;
  options.langVersion = oldversion;
  oldProgram = prog;
  {
    auto cl = newprogram->clone();
    IR::IndexedVector<IR::Type_Var> ivec;
    ivec.push_back(new IR::Type_Var("I"));
    ivec.push_back(new IR::Type_Var("O"));
    auto mt = new IR::Type_Method(
        new IR::TypeParameters(ivec), new IR::Type_Name("O"),
        new IR::ParameterList(
            {new IR::Parameter("i", IR::Direction::In, new IR::Type_Name("I")),
             new IR::Parameter("io", IR::Direction::InOut,
                               new IR::Type_Name("O"))}));
    cl->objects.push_back(new IR::Method("do_cast", mt));
    newprogram = cl;
  }

  declareStructsAndExterns();
  declareMetaType();
  declareForwardingMeta();
  declareExternMethods();
  declareExternInstances();
  dump_new_program("post_declare_structures.p4");
  makeIngressParser();
  makeIngressPipeline();
  makeIngressDeparser();
  makeEgressParser();
  makeEgressPipeline();
  makeEgressDeparser();
  replaceStandardMeta();
  initializeParserMetas();
  initializeForwardingMetas();
  declareMain();
  dump_new_program(options.psaFile);
  return newprogram;
}

void BMV2::PSAConverter::declareMain() {
  P4::Evaluator evaluator(this->refMap, this->typeMap);
  this->oldProgram->apply(evaluator);
  auto main = evaluator.getToplevelBlock()->getMain();
  auto parserctv = main->getParameterValue("p")->to<IR::ParserBlock>();
  auto igctv = main->getParameterValue("ig")->to<IR::ControlBlock>();
  auto egctv = main->getParameterValue("eg")->to<IR::ControlBlock>();
  auto depctv = main->getParameterValue("dep")->to<IR::ControlBlock>();
  auto parserCons = parserctv->node->to<IR::ConstructorCallExpression>();
  auto igcons = igctv->node->to<IR::ConstructorCallExpression>();
  auto egcons = egctv->node->to<IR::ConstructorCallExpression>();
  auto depcons = depctv->node->to<IR::ConstructorCallExpression>();

  auto igParserCons = new IR::ConstructorCallExpression(
      new IR::Type_Name("ingressParser"), parserCons->arguments);
  auto egParserCons = new IR::ConstructorCallExpression(
      new IR::Type_Name("egressParser"), parserCons->arguments);
  auto igPipeCons = new IR::ConstructorCallExpression(
      new IR::Type_Name("ingress"), igcons->arguments);
  auto egPipeCons = new IR::ConstructorCallExpression(
      new IR::Type_Name("egress"), egcons->arguments);
  auto igdepCons = new IR::ConstructorCallExpression(
      new IR::Type_Name("ingressDeparser"), depcons->arguments);
  auto egdepCons = new IR::ConstructorCallExpression(
      new IR::Type_Name("egressDeparser"), depcons->arguments);
  auto pre = new IR::ConstructorCallExpression(
      new IR::Type_Name("PacketReplicationEngine"),
      new IR::Vector<IR::Argument>);
  auto bqengine = new IR::ConstructorCallExpression(
      new IR::Type_Name("BufferingQueueingEngine"),
      new IR::Vector<IR::Argument>);
  auto args = new IR::Vector<IR::Argument>;
  args->emplace_back(igParserCons);
  args->emplace_back(igPipeCons);
  args->emplace_back(igdepCons);
  auto igPipe = new IR::ConstructorCallExpression(
      new IR::Type_Name("IngressPipeline"), args);
  args = new IR::Vector<IR::Argument>;
  args->emplace_back(egParserCons);
  args->emplace_back(egPipeCons);
  args->emplace_back(egdepCons);
  auto egPipe = new IR::ConstructorCallExpression(
      new IR::Type_Name("EgressPipeline"), args);
  args = new IR::Vector<IR::Argument>;
  args->emplace_back(igPipe);
  args->emplace_back(pre);
  args->emplace_back(egPipe);
  args->emplace_back(bqengine);
  auto psa_switch = new IR::Declaration_Instance(
      "main", new IR::Type_Name("PSA_Switch"), args);
  auto cl = this->newprogram->clone();
  cl->objects.push_back(psa_switch);
  this->newprogram = cl;
}

void BMV2::PSAConverter::declareExternInstances() {
  auto cl = this->newprogram->clone();
  for (auto o : this->oldProgram->objects) {
    if (auto di = o->to<IR::Declaration_Instance>()) {
      auto actual = P4::Instantiation::resolve(di, this->refMap, this->typeMap);
      if (actual->is<P4::ExternInstantiation>()) {
        cl->objects.push_back(BMV2::cleanNode(di));
      }
    }
  }
  this->newprogram = cl;
}

void BMV2::PSAConverter::declareExternMethods() {
  auto cl = this->newprogram->clone();
  for (auto o : this->oldProgram->objects) {
    if (auto di = o->to<IR::Method>()) {
      cl->objects.push_back(BMV2::cleanNode(di));
    }
  }
  this->newprogram = cl;
}

void BMV2::PSAConverter::declareMetaType() {
  auto parser = this->structure->parser;
  auto Mparm = parser->getApplyParameters()->getParameter(2);
  auto mtype = this->typeMap->getType(Mparm)->to<IR::Type_Struct>();
  auto newmetatype = mtype->clone();
  auto sf = new IR::StructField("standard_metadata",
                                new IR::Type_Name("standard_metadata_t"));
  newmetatype->fields.push_back(sf);
  newmetatype->name = this->refMap->newName(newmetatype->name);
  this->metaTypeName = new IR::Type_Name(newmetatype->name);

  // declare the new meta obtained by adding standard meta to
  // the old struct
  auto cl = this->newprogram->clone();
  cl->objects.push_back(newmetatype);
  this->newprogram = cl;
}

void BMV2::PSAConverter::declareStructsAndExterns() {
  BMV2::DeclareStructsAndHeaders declareStructsAndHeaders(
      this->refMap, this->typeMap, this->newprogram);
  this->oldProgram->apply(declareStructsAndHeaders);
  this->newprogram = declareStructsAndHeaders.newprogram;
  BMV2::DeclareStructsAndHeaders declareStructsAndHeaders2(
      this->refMap, this->typeMap, true, this->newprogram);
  this->oldProgram->apply(declareStructsAndHeaders2);
  this->newprogram = declareStructsAndHeaders2.newprogram;
}

void BMV2::PSAConverter::declareForwardingMeta() {
  auto cl = this->newprogram->clone();
  auto ci2eT = new IR::Type_Struct("ci2e_t");
  cl->objects.push_back(ci2eT);
  auto ce2eT = new IR::Type_Struct("ce2e_t");
  cl->objects.push_back(ce2eT);
  auto nmT = new IR::Type_Struct("normal_meta_t");
  cl->objects.push_back(nmT);
  auto recirc = new IR::Type_Struct("recirculate_meta_t");
  auto resubm = new IR::Type_Struct("resubmit_meta_t");
  cl->objects.push_back(recirc);
  cl->objects.push_back(resubm);
  this->newprogram = cl;
}

void BMV2::PSAConverter::initializeForwardingMetas() {
  BMV2::HandleControlInput handleControlInputIg("ingress");
  BMV2::HandleControlOutput handleControlOutputIg("ingress");
  BMV2::HandleControlInput handleControlInputEg("egress");
  BMV2::HandleControlOutput handleControlOutputEg("egress");
  this->newprogram = this->newprogram->apply(handleControlInputIg)
                         ->apply(handleControlInputEg)
                         ->apply(handleControlOutputIg)
                         ->apply(handleControlOutputEg);
  std::map<std::set<std::vector<BMV2::location>>, unsigned int> field_lists;
  std::map<const IR::Node *, unsigned int> primitive_mapping;
  std::map<std::vector<BMV2::location>, const IR::Type *> mem_type;
  BMV2::FindFieldLists ffl(this->refMap, this->typeMap, this->structure,
                           field_lists, mem_type, primitive_mapping);
  this->oldProgram->apply(ffl);
  BMV2::DefineHelperMetas dhm(field_lists, mem_type);
  BMV2::MakeNormalMetaType makeNormalMetaType(this->headertype->name,
                                              this->metaTypeName->path->name);
  this->newprogram = this->newprogram->apply(dhm)->apply(makeNormalMetaType);
  BMV2::IngressParserReadMetas ingressParserReadMetas(field_lists, mem_type,
                                                      "ingressParser");
  BMV2::IngressParserReadMetas egressParserReadMetas(field_lists, mem_type,
                                                     "egressParser");
  this->newprogram = this->newprogram->apply(ingressParserReadMetas)
                         ->apply(egressParserReadMetas);
  BMV2::PopulateForwardingMetas populateForwardingMetas(field_lists);
  this->newprogram = this->newprogram->apply(populateForwardingMetas);
  RewritePrimitives rw(field_lists);
  this->newprogram = newprogram->apply(rw);
  this->dump_new_program("post_declare_helper_structs.p4");
}

void BMV2::PSAConverter::initializeParserMetas() {
  std::set<IR::Expression *> headers;
  std::set<IR::Expression *> metas;
  std::map<IR::Expression *, const IR::Type *> metaTypes;
  BMV2::GatherAllMetadataAndHeaders gatherAllMetadataAndHeaders(
      this->refMap, this->typeMap, this->structure, headers, metas, metaTypes);
  this->oldProgram->apply(gatherAllMetadataAndHeaders);
  {
    BMV2::RenameParserStart renameParserStart(this->ingressParser);
    this->newprogram = this->newprogram->apply(renameParserStart);
  }
  {
    BMV2::RenameParserStart renameParserStart(this->egressParser);
    this->newprogram = this->newprogram->apply(renameParserStart);
  }
  BMV2::ZeroOutMetas zeroOutMetas(headers, metas, metaTypes);
  this->newprogram = this->newprogram->apply(zeroOutMetas);
  cstring NORMAL = "NORMAL";
  cstring RESUB = "RESUBMIT";
  cstring RECIRC = "RECIRCULATE";

  cstring NORMAL_UNICAST(
      "NORMAL_UNICAST"), /// Normal packet received by egress which is unicast
      NORMAL_MULTICAST("NORMAL_MULTICAST"), /// Normal packet received by egress
                                            /// which is multicast
      CLONE_I2E(
          "CLONE_I2E"), /// Packet created via a clone operation in ingress,
                        /// destined for egress
      CLONE_E2E("CLONE_E2E");
  {
    std::set<cstring> ingress_allowed = {NORMAL, RESUB, RECIRC};
    IngressParserAddInitializer ingressParserAddInitializer(ingress_allowed,
                                                            "ingressParser");
    newprogram = newprogram->apply(ingressParserAddInitializer);
  }
  {
    std::set<cstring> egress_allowed = {NORMAL_UNICAST, NORMAL_MULTICAST,
                                        CLONE_I2E, CLONE_E2E};
    IngressParserAddInitializer ingressParserAddInitializer(egress_allowed,
                                                            "egressParser");
    newprogram = newprogram->apply(ingressParserAddInitializer);
  }
  IngressParserPopulateStandardMeta ingressParserPopulateStandardMeta;
  EgressParserPopulateStandardMeta egressParserPopulateStandardMeta;
  newprogram = newprogram->apply(ingressParserPopulateStandardMeta)
                   ->apply(egressParserPopulateStandardMeta);
  dump_new_program("post_ingress_parser_init.p4");
  // TODO: handle clone/resub/recirc cases:
  // TODO: declare normal_meta_t structure to be a mirror of ingress meta
  // TODO: declare clone_i(e)2e to contain only fields used in tuple arguments
  // of clone3
  // + flid field to be able to discern
  // TODO: declare resubmit_t and recirculate_t to contain only fields used in
  // tuple arguments
  // of resubmit/recirculate and flid to be able to discern
  // TODO: copy metas from corresponding structures into working memory
}

void BMV2::PSAConverter::replaceStandardMeta() {
  std::set<const IR::PathExpression *> to_be_replaced;
  BMV2::FindStandardMetadataReferences findStandardMetadataReferences(
      this->refMap, this->typeMap, to_be_replaced, this->structure);
  this->oldProgram->apply(findStandardMetadataReferences);
  BMV2::ReplaceStandardMetadataReferences replaceStandardMetadataReferences(
      to_be_replaced);
  this->newprogram = this->newprogram->apply(replaceStandardMetadataReferences);
  this->dump_new_program("post_replace_standard_meta.p4");
}

void BMV2::PSAConverter::makeEgressDeparser() { /*
    * control Deparser<H>(packet_out b, in H hdr);
    * control EgressDeparser<H, M, CE2EM, RECIRCM>(
         packet_out buffer,
         out CE2EM clone_e2e_meta,
         out RECIRCM recirculate_meta,
         inout H hdr,
         in M meta,
         in psa_egress_output_metadata_t istd,
         in psa_egress_deparser_input_metadata_t edstd);
    */
  auto cl = this->newprogram->clone();
  auto deparser = this->structure->deparser;
  auto Pout = deparser->getApplyParameters()->getParameter(0);
  auto Hparm = deparser->getApplyParameters()->getParameter(1);

  auto parserClone = deparser->clone();
  auto ptype = deparser->type->clone();
  auto parmList = new IR::ParameterList();

  auto recircTypeName = new IR::Type_Name("recirculate_meta_t");
  auto ce2eTypeName = new IR::Type_Name("ce2e_t");

  parmList->push_back(Pout);
  parmList->push_back(
      new IR::Parameter("ce2e", IR::Direction::Out, ce2eTypeName));
  parmList->push_back(new IR::Parameter("recirculate_meta", IR::Direction::Out,
                                        recircTypeName));
  auto Hparmclone = Hparm->clone();
  Hparmclone->direction = IR::Direction::InOut;
  parmList->push_back(Hparmclone);
  parmList->push_back(
      new IR::Parameter("meta", IR::Direction::In, this->metaTypeName));
  // in psa_ingress_output_metadata_t istd
  parmList->push_back(
      new IR::Parameter("istd", IR::Direction::In,
                        new IR::Type_Name("psa_egress_output_metadata_t")));
  parmList->push_back(new IR::Parameter(
      "edstd", IR::Direction::In,
      new IR::Type_Name("psa_egress_deparser_input_metadata_t")));
  ptype->applyParams = parmList;
  parserClone->type = ptype;
  cl->objects.push_back(parserClone);
  ptype->name = "egressDeparser";
  parserClone->name = "egressDeparser";
  this->newprogram = cl;
  {
    std::ofstream os("post_make_egress_deparser.p4");
    P4::ToP4 toP4(&os, false);
    this->newprogram->apply(toP4);
  }
}

void BMV2::PSAConverter::makeEgressPipeline() { /*
    * control Egress<H, M>(
         inout H hdr, inout M user_meta,
         in    psa_egress_input_metadata_t  istd,
         inout psa_egress_output_metadata_t ostd);
    */
  auto cl = this->newprogram->clone();
  auto egress = this->structure->egress;
  auto Hparm = egress->getApplyParameters()->getParameter(0);
  auto Mparm = egress->getApplyParameters()->getParameter(1);

  auto parserClone = egress->clone();
  auto ptype = egress->type->clone();
  auto parmList = new IR::ParameterList();

  // istd parm: in psa_ingress_parser_input_metadata_t istd,
  auto istdparm =
      new IR::Parameter("istd", IR::Direction::In,
                        new IR::Type_Name("psa_egress_input_metadata_t"));
  auto ostdparm =
      new IR::Parameter("ostd", IR::Direction::InOut,
                        new IR::Type_Name("psa_egress_output_metadata_t"));

  // TODO: compute resubmit and recirculate structures
  parmList->push_back(Hparm);
  auto newMParm = Mparm->clone();
  newMParm->type = this->metaTypeName;
  parmList->push_back(newMParm);
  parmList->push_back(istdparm);
  parmList->push_back(ostdparm);
  ptype->applyParams = parmList;
  parserClone->type = ptype;
  cl->objects.push_back(parserClone);
  ptype->name = "egress";
  parserClone->name = "egress";
  this->newprogram = cl;
  {
    std::ofstream os("post_make_egress_pipe.p4");
    P4::ToP4 toP4(&os, false);
    this->newprogram->apply(toP4);
  }
}

void BMV2::PSAConverter::makeEgressParser() {
  auto cl = this->newprogram->clone();
  auto parser = this->structure->parser;
  auto packetParm = parser->getApplyParameters()->getParameter(0);
  auto Hparm = parser->getApplyParameters()->getParameter(1);
  auto Mparm = parser->getApplyParameters()->getParameter(2);
  auto parserClone = parser->clone();
  auto ptype = parser->type->clone();
  auto parmList = new IR::ParameterList();

  // istd parm: in psa_ingress_parser_input_metadata_t istd,
  auto istdparm = new IR::Parameter(
      "istd", IR::Direction::In,
      new IR::Type_Name("psa_egress_parser_input_metadata_t"));

  // TODO: compute resubmit and recirculate structures
  auto normalMetaTn = new IR::Type_Name("normal_meta_t");
  auto ci2etn = new IR::Type_Name("ci2e_t");
  auto ce2etn = new IR::Type_Name("ce2e_t");
  auto normalMetaParm =
      new IR::Parameter("nm", IR::Direction::In, normalMetaTn);
  auto ci2eparm = new IR::Parameter("ci2e", IR::Direction::In, ci2etn);
  auto ce2eparm = new IR::Parameter("ce2e", IR::Direction::In, ce2etn);

  parmList->push_back(packetParm);
  parmList->push_back(Hparm);
  auto newMParm = Mparm->clone();
  newMParm->type = this->metaTypeName;
  parmList->push_back(newMParm);
  parmList->push_back(istdparm);
  parmList->push_back(normalMetaParm);
  parmList->push_back(ci2eparm);
  parmList->push_back(ce2eparm);
  ptype->applyParams = parmList;
  parserClone->type = ptype;
  cl->objects.push_back(parserClone);
  egressParser = parserClone;
  ptype->name = "egressParser";
  parserClone->name = "egressParser";
  this->newprogram = cl;
  {
    std::ofstream os("post_make_new_egress_parser.p4");
    P4::ToP4 toP4(&os, false);
    this->newprogram->apply(toP4);
  }
}

void BMV2::PSAConverter::makeIngressDeparser() {
  auto cl = this->newprogram->clone();
  auto deparser = this->structure->deparser;
  auto Pout = deparser->getApplyParameters()->getParameter(0);
  auto Hparm = deparser->getApplyParameters()->getParameter(1);

  auto parserClone = deparser->clone();
  auto ptype = deparser->type->clone();
  auto parmList = new IR::ParameterList();

  // TODO: add definitions for CI2EM, CE2EM, RESUBM, NM
  auto normalMetaTypeName = new IR::Type_Name("normal_meta_t");
  auto ci2eTypeName = new IR::Type_Name("ci2e_t");
  auto resubTypeName = new IR::Type_Name("resubmit_meta_t");

  parmList->push_back(Pout);
  parmList->push_back(
      new IR::Parameter("ci2e", IR::Direction::Out, ci2eTypeName));
  parmList->push_back(
      new IR::Parameter("resub", IR::Direction::Out, resubTypeName));
  parmList->push_back(
      new IR::Parameter("nm", IR::Direction::Out, normalMetaTypeName));
  auto Hparmclone = Hparm->clone();
  Hparmclone->direction = IR::Direction::InOut;
  parmList->push_back(Hparmclone);
  parmList->push_back(
      new IR::Parameter("meta", IR::Direction::In, this->metaTypeName));
  // in psa_ingress_output_metadata_t istd
  parmList->push_back(
      new IR::Parameter("istd", IR::Direction::In,
                        new IR::Type_Name("psa_ingress_output_metadata_t")));
  ptype->applyParams = parmList;
  parserClone->type = ptype;
  cl->objects.push_back(parserClone);
  ptype->name = "ingressDeparser";
  parserClone->name = "ingressDeparser";
  this->newprogram = cl;
  {
    std::ofstream os("post_make_ingress_deparser.p4");
    P4::ToP4 toP4(&os, false);
    this->newprogram->apply(toP4);
  }
}

void BMV2::PSAConverter::makeIngressPipeline() { /*
    * control Ingress<H, M>(inout H hdr,
                       inout M meta,
                       inout standard_metadata_t standard_metadata);
    */
  /*
    control Ingress<H, M>(
      inout H hdr, inout M user_meta,
      in    psa_ingress_input_metadata_t  istd,
      inout psa_ingress_output_metadata_t ostd);
   */
  auto cl = this->newprogram->clone();
  auto ingress = this->structure->ingress;
  auto Hparm = ingress->getApplyParameters()->getParameter(0);
  auto Mparm = ingress->getApplyParameters()->getParameter(1);

  auto parserClone = ingress->clone();
  auto ptype = ingress->type->clone();
  auto parmList = new IR::ParameterList();

  // istd parm: in psa_ingress_parser_input_metadata_t istd,
  auto istdparm =
      new IR::Parameter("istd", IR::Direction::In,
                        new IR::Type_Name("psa_ingress_input_metadata_t"));
  auto ostdparm =
      new IR::Parameter("ostd", IR::Direction::InOut,
                        new IR::Type_Name("psa_ingress_output_metadata_t"));

  // TODO: compute resubmit and recirculate structures
  parmList->push_back(Hparm);
  auto newMParm = Mparm->clone();
  newMParm->type = this->metaTypeName;
  parmList->push_back(newMParm);
  parmList->push_back(istdparm);
  parmList->push_back(ostdparm);
  ptype->applyParams = parmList;
  parserClone->type = ptype;
  cl->objects.push_back(parserClone);
  ptype->name = "ingress";
  parserClone->name = "ingress";
  this->newprogram = cl;
  {
    std::ofstream os("post_make_ingress_pipe.p4");
    P4::ToP4 toP4(&os, false);
    this->newprogram->apply(toP4);
  }
}

void BMV2::PSAConverter::makeIngressParser() {
  auto parser = structure->parser;
  auto packetParm = parser->getApplyParameters()->getParameter(0);
  auto Hparm = parser->getApplyParameters()->getParameter(1);
  headertype = typeMap->getType(Hparm)->to<IR::Type_Declaration>();
  auto Mparm = parser->getApplyParameters()->getParameter(2);
  auto parserClone = parser->clone();
  auto ptype = parser->type->clone();
  auto parmList = new IR::ParameterList();
  // declare the new meta obtained by adding standard meta to
  // the old struct
  auto cl = newprogram->clone();
  // istd parm: in psa_ingress_parser_input_metadata_t istd,
  auto istdparm = new IR::Parameter(
      "istd", IR::Direction::In,
      new IR::Type_Name("psa_ingress_parser_input_metadata_t"));

  // TODO: compute resubmit and recirculate structures
  auto recirctn = new IR::Type_Name("recirculate_meta_t");
  auto resubmtn = new IR::Type_Name("resubmit_meta_t");

  auto recircParm = new IR::Parameter("recirc", IR::Direction::In, recirctn);
  auto resubParm = new IR::Parameter("resub", IR::Direction::In, resubmtn);

  parmList->push_back(packetParm);
  parmList->push_back(Hparm);
  auto newMParm = Mparm->clone();
  newMParm->type = metaTypeName;
  parmList->push_back(newMParm);
  parmList->push_back(istdparm);
  parmList->push_back(resubParm);
  parmList->push_back(recircParm);
  ptype->applyParams = parmList;
  parserClone->type = ptype;
  cl->objects.push_back(parserClone);
  ingressParser = parserClone;
  ptype->name = "ingressParser";
  parserClone->name = "ingressParser";
  this->newprogram = cl;
  dump_new_program("post_make_new_parser.p4");
}

std::string BMV2::PSAConverter::readHeader(const char *filename,
                                           bool preprocess) {
  if (preprocess) {
#ifdef __clang__
    std::string cmd("cc -E -x c -Wno-comment");
#else
    std::string cmd("cpp");
#endif
    cmd +=
        cstring(" -C -undef -nostdinc") + " " + "-Ip4include" + " " + filename;
    FILE *in = popen(cmd.c_str(), "r");
    if (in == nullptr)
      throw std::runtime_error(std::string("Couldn't invoke preprocessor"));
    std::stringstream buffer;
    char string[100];
    while (fgets(string, sizeof(string), in))
      buffer << string;
    int exitCode = pclose(in);
    if (WIFEXITED(exitCode) && WEXITSTATUS(exitCode) == 4) {
      throw std::runtime_error(std::string("Couldn't find standard header ") +
                               filename);
    } else if (exitCode != 0) {
      throw std::runtime_error(
          std::string("Couldn't preprocess standard header ") + filename);
    }
    return buffer.str();
  } else {
    std::ifstream input(filename);
    if (!input.good()) {
      throw std::runtime_error(std::string("Couldn't read standard header ") +
                               filename);
    }

    // Initialize a buffer with a #line preprocessor directive. This
    // ensures that any errors we encounter in this header will
    // reference the correct file and line.
    std::stringstream buffer;
    buffer << "#line 1 \"" << filename << "\"" << std::endl;

    // Read the header into the buffer and return it.
    while (input >> buffer.rdbuf())
      continue;
    return buffer.str();
  }
}

void BMV2::PSAConverter::dump_new_program(cstring name) const {
  std::ofstream os(name);
  P4::ToP4 toP4(&os, false);
  newprogram->apply(toP4);
}
