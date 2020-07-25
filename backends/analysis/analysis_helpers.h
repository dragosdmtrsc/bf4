//
// Created by dragos on 17.12.2018.
//

#ifndef P4C_ANALYSIS_HELPERS_H
#define P4C_ANALYSIS_HELPERS_H

#include "VersionedExpression.h"
#include <chrono>
#include <common/model.h>
#include <p4/methodInstance.h>
#include <z3++.h>

namespace analysis {
#define START_ASG(name) name##_start = std::chrono::system_clock::now()

#define END_ASG(name) name##_end = std::chrono::system_clock::now()

#define START(name)                                                            \
  std::chrono::system_clock::time_point name##_start =                         \
      std::chrono::system_clock::now()

#define END(name)                                                              \
  std::chrono::system_clock::time_point name##_end =                           \
      std::chrono::system_clock::now()

#define DURATION(name)                                                         \
  std::chrono::duration_cast<std::chrono::milliseconds>(name##_end -           \
                                                        name##_start)          \
      .count()

class ReplaceOccurence : public Transform {
  const IR::Node *what, *to, *in;
  ReplaceOccurence(const IR::Node *what, const IR::Node *to, const IR::Node *in)
      : what(what), to(to), in(in) {}
  const IR::Node *postorder(IR::Node *x) override {
    if (getOriginal() == what)
      return to;
    return x;
  }

public:
  static const IR::Node *replaceStatic(const IR::Node *what, const IR::Node *to,
                                       const IR::Node *in) {
    ReplaceOccurence roc(what, to, in);
    return in->apply(roc);
  }
};

class MutablePacket : public ::Model::Extern_Model {
public:
  Model::Elem extract;
  Model::Elem lookahead;
  Model::Elem advance;
  Model::Elem length;
  int extractSecondArgSize = 32;

  Model::Elem emit;

public:
  MutablePacket()
      : ::Model::Extern_Model("mutable_packet"), extract("extract"),
        lookahead("lookahead"), advance("advance"), length("length"),
        emit("emit") {}
};

class PacketModel : public ::Model::Extern_Model {
public:
  ::Model::Elem peek;
  ::Model::Elem pop;
  ::Model::Elem advance;
  ::Model::Elem emit;
  ::Model::Elem zero;
  ::Model::Elem prepend;
  ::Model::Elem copy;

public:
  PacketModel()
      : ::Model::Extern_Model("packet_model"), peek("modelPeek"),
        pop("modelPop"), advance("modelAdvance"), emit("modelEmit"),
        zero("modelZero"), prepend("modelPrepend"), copy("modelCopy") {}
};

class AnalysisLibrary : public ::Model::Model {
public:
  static AnalysisLibrary instance;

  MutablePacket mutablePacket;
  PacketModel packetModel;
  ::Model::Elem drop;
  ::Model::Elem send;
  ::Model::Elem assrt, assume, bug, angelicAssert, oob;
  ::Model::Elem havoc;
  ::Model::Elem prependPacket, readPacket, emptyPacket, copyPacket;
  ::Model::Elem readonly;

  ::Model::Elem instrumentKeysAnnotation;
  ::Model::Elem headerAnnotation;
  ::Model::Elem unreach;
  ::Model::Elem dontCare;
  ::Model::Elem keyMatch;

  AnalysisLibrary()
      : ::Model::Model("0.1"), mutablePacket(MutablePacket()), drop("do_drop"),
        send("do_send"), assrt("assert"), assume("assume"), bug("bug"),
        angelicAssert("angelic_assert"), oob("oob"), havoc("havoc"),
        prependPacket("prependPacket"), readPacket("readPacket"),
        emptyPacket("emptyPacket"), copyPacket("copyPacket"),
        readonly("readonly"), instrumentKeysAnnotation("instrument_keys"),
        headerAnnotation("hdr"),
        unreach("UNREACHABLE"), dontCare("dontCare"), keyMatch("key_match") {}
};

template <typename Map, typename K, typename Fun>
auto getOrEmplace(Map &m, const K &key, Fun orElse)
    -> std::pair<decltype(orElse()) &, bool> {
  auto er = m.equal_range(key);
  if (er.first != er.second) {
    return {er.first->second, false};
  } else {
    auto EMI = m.emplace_hint(er.first, key, orElse());
    return {EMI->second, true};
  }
};

template <typename V, typename Map, typename K>
V get(const Map &m, const K &key, V def = V()) {
  auto I = m.find(key);
  if (I != m.end())
    return I->second;
  return def;
};

IR::MethodCallExpression *call_forall(const IR::Type *bound_type,
                                      const IR::PathExpression *bound,
                                      unsigned nr,
                                      const IR::Expression *condition);

inline IR::MethodCallStatement *call_assert(const IR::Expression *e) {
  return new IR::MethodCallStatement(new IR::MethodCallExpression(
      new IR::PathExpression("assert"),
      new IR::Vector<IR::Argument>({new IR::Argument(e)})));
}
inline bool ends_with(std::string const &value, std::string const &ending) {
  if (ending.size() > value.size())
    return false;
  return std::equal(ending.rbegin(), ending.rend(), value.rbegin());
}
inline unsigned long id(const void *nd) {
  return reinterpret_cast<unsigned long>(nd);
}
inline z3::expr substitute(z3::expr &on, z3::expr what, z3::expr withWhat) {
  z3::expr_vector w(on.ctx()), ww(on.ctx());
  w.push_back(what);
  ww.push_back(withWhat);
  return on.substitute(w, ww);
}

inline cstring hit_fun_name(const IR::P4Table *table) {
  return "hits_" + table->externalName().replace(".", "__");
}
inline const P4::MethodInstance *
is_bug(const IR::MethodCallExpression *methodCallExpression,
       P4::ReferenceMap *refMap, P4::TypeMap *typeMap);

const P4::MethodInstance *
is_bug(const IR::MethodCallExpression *methodCallExpression,
       P4::ReferenceMap *refMap, P4::TypeMap *typeMap) {
  auto mi = P4::MethodInstance::resolve(methodCallExpression, refMap, typeMap);
  if (auto ef = mi->to<P4::ExternFunction>()) {
    if (ef->method->name == "bug") {
      return mi;
    }
  }
  return nullptr;
}

IR::MethodCallStatement *call_bug();
IR::MethodCallStatement *call_key_match(const IR::Expression *e);
IR::MethodCallStatement *call_assert_point(const IR::Vector<IR::Expression> &);

const IR::Node *actual_node(const IR::Node *n);
cstring node_repr(const IR::Node *n);

inline P4::MethodInstance *
is_extern_function(const IR::MethodCallExpression *methodCallExpression,
                   P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                   cstring name) {
  auto mi = P4::MethodInstance::resolve(methodCallExpression, refMap, typeMap);
  if (auto ef = mi->to<P4::ExternFunction>()) {
    if (ef->method->name == name) {
      return mi;
    }
  }
  return nullptr;
}

inline P4::MethodInstance *
is_key_match(const IR::MethodCallExpression *methodCallExpression,
             P4::ReferenceMap *refMap, P4::TypeMap *typeMap) {
  return is_extern_function(methodCallExpression, refMap, typeMap,
                            analysis::AnalysisLibrary::instance.keyMatch.name);
}

inline P4::MethodInstance *is_key_match(const IR::MethodCallStatement *mcs,
                                        P4::ReferenceMap *refMap,
                                        P4::TypeMap *typeMap) {
  return is_key_match(mcs->methodCall, refMap, typeMap);
}

inline const P4::MethodInstance *
is_havoc(const IR::MethodCallExpression *methodCallExpression,
         P4::ReferenceMap *refMap, P4::TypeMap *typeMap) {
  return is_extern_function(methodCallExpression, refMap, typeMap, "havoc");
}
inline const P4::MethodInstance *
is_assert(const IR::MethodCallExpression *methodCallExpression,
          P4::ReferenceMap *refMap, P4::TypeMap *typeMap) {
  return is_extern_function(methodCallExpression, refMap, typeMap, "assert");
}
inline const P4::MethodInstance *
is_assert(const IR::MethodCallStatement *methodCallExpression,
          P4::ReferenceMap *refMap, P4::TypeMap *typeMap) {
  return is_extern_function(methodCallExpression->methodCall, refMap, typeMap,
                            "assert");
}
inline const P4::MethodInstance *
is_assume(const IR::MethodCallExpression *methodCallExpression,
          P4::ReferenceMap *refMap, P4::TypeMap *typeMap) {
  return is_extern_function(methodCallExpression, refMap, typeMap, "assume");
}
inline const P4::MethodInstance *
is_assume(const IR::MethodCallStatement *methodCallExpression,
          P4::ReferenceMap *refMap, P4::TypeMap *typeMap) {
  return is_extern_function(methodCallExpression->methodCall, refMap, typeMap,
                            "assume");
}

inline const P4::MethodInstance *
is_bim(const IR::MethodCallExpression *methodCallExpression,
       P4::ReferenceMap *refMap, P4::TypeMap *typeMap, cstring name) {
  auto mi = P4::MethodInstance::resolve(methodCallExpression, refMap, typeMap);
  if (auto ef = mi->to<P4::BuiltInMethod>()) {
    if (ef->name.name == name) {
      return mi;
    }
  }
  return nullptr;
}
cstring endFunctionName(const IR::P4Table *table);
cstring queryFunctionName(const IR::P4Table *table);
cstring table_name_from_query(cstring name);
cstring table_name_from_end(cstring name);
inline const IR::MethodCallStatement *
mcs_call(cstring method,
         std::initializer_list<IR::Expression const *> const &a) {
  return new IR::MethodCallStatement(
      new IR::MethodCallExpression(new IR::PathExpression(method), a));
}

inline bool isExtract(const P4::MethodInstance *mi) {
  if (mi->is<P4::ExternMethod>()) {
    auto em = mi->to<P4::ExternMethod>();
    if (em->actualExternType->name ==
        AnalysisLibrary::instance.mutablePacket.name) {
      if (em->method->name.name ==
          AnalysisLibrary::instance.mutablePacket.extract.name) {
        return true;
      }
    }
  }
  return false;
}

inline const P4::MethodInstance *
is_set_valid(const IR::MethodCallExpression *methodCallExpression,
             P4::ReferenceMap *refMap, P4::TypeMap *typeMap) {
  return is_bim(methodCallExpression, refMap, typeMap, "setValid");
}
inline const P4::MethodInstance *
is_set_invalid(const IR::MethodCallExpression *methodCallExpression,
               P4::ReferenceMap *refMap, P4::TypeMap *typeMap) {
  return is_bim(methodCallExpression, refMap, typeMap, "setInvalid");
}
inline const P4::MethodInstance *
is_is_valid(const IR::MethodCallExpression *methodCallExpression,
            P4::ReferenceMap *refMap, P4::TypeMap *typeMap) {
  return is_bim(methodCallExpression, refMap, typeMap, "isValid");
}
inline const P4::MethodInstance *
is_set_valid(const IR::MethodCallStatement *mcs, P4::ReferenceMap *refMap,
             P4::TypeMap *typeMap) {
  return is_set_valid(mcs->methodCall, refMap, typeMap);
}
inline const P4::MethodInstance *
is_set_invalid(const IR::MethodCallStatement *mcs, P4::ReferenceMap *refMap,
               P4::TypeMap *typeMap) {
  return is_set_invalid(mcs->methodCall, refMap, typeMap);
}
inline const P4::MethodInstance *is_bug(const IR::MethodCallStatement *mcs,
                                        P4::ReferenceMap *refMap,
                                        P4::TypeMap *typeMap) {
  return is_bug(mcs->methodCall, refMap, typeMap);
}

inline bool is_extern(const IR::MethodCallExpression *mce, cstring n) {
  return mce->method->is<IR::PathExpression>() &&
         mce->method->to<IR::PathExpression>()->path->name == n;
}
inline bool is_extern(const IR::MethodCallStatement *mcs, cstring n) {
  return is_extern(mcs->methodCall, n);
}
#define is_bug(m) is_extern(m, analysis::AnalysisLibrary::instance.bug.name)
#define is_drop(m) is_extern(m, analysis::AnalysisLibrary::instance.drop.name)
#define is_send(m) is_extern(m, analysis::AnalysisLibrary::instance.send.name)
#define is_oob(m) is_extern(m, analysis::AnalysisLibrary::instance.oob.name)

#define is_terminal(m) (is_bug(m) || is_drop(m) || is_oob(m) || is_send(m))

inline bool is_controlled(const IR::MethodCallStatement *mcs,
                          P4::ReferenceMap *refMap, P4::TypeMap *typeMap) {
  auto mi = P4::MethodInstance::resolve(mcs, refMap, typeMap);
  if (auto ef = mi->to<P4::ExternFunction>()) {
    if (ef->method->getAnnotation("controlled"))
      return true;
  }
  return false;
}

using namespace z3;
class IRExprToSMT : public Inspector {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  z3::context *context;
  std::map<const IR::Expression *, z3::ast> ast_mappings;
  std::map<cstring, z3::ast> *vars;
  std::map<const IR::Expression *, cstring> partial_string_repr;
  std::map<cstring, z3::sort> enum_sorts;
  std::map<cstring, z3::func_decl_vector> enum_constants;

  void set(const IR::Expression *ex, z3::ast a);
  void create_new(const IR::Expression *what, cstring name);
  void postorder(const IR::LAnd *op) override;
  void postorder(const IR::Leq *op) override;
  void postorder(const IR::Geq *op) override;
  void postorder(const IR::Grt *op) override;
  void postorder(const IR::BoolLiteral *lit) override;
  void postorder(const IR::LOr *op) override;
  void postorder(const IR::Mux *mux) override;
  void postorder(const IR::Equ *op) override;
  void postorder(const IR::LNot *op) override;
  void postorder(const IR::Add *op) override;
  void postorder(const IR::Sub *op) override;
  void postorder(const IR::BAnd *op) override;
  void postorder(const IR::Cmpl *op) override;
  void postorder(const IR::MethodCallExpression *expr) override;
  void postorder(const IR::ArrayIndex *aindex) override;
  void postorder(const IR::BXor *op) override;
  void postorder(const IR::Slice *slice) override;
  void postorder(const IR::Cast *cast) override;
  void postorder(const IR::BOr *op) override;
  void postorder(const IR::Constant *lit) override;
  void postorder(const IR::Neq *op) override;
  void postorder(const IR::PathExpression *pathExpression) override;
  void postorder(const IR::Shl *op) override;
  void postorder(const IR::Shr *op) override;
  void postorder(const IR::Member *mem) override;

public:
  z3::ast *get(const IR::Expression *what);
  z3::expr evaluate(const IR::Expression *what);
  IRExprToSMT(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
              z3::context *context, std::map<cstring, z3::ast> *vars)
      : refMap(refMap), typeMap(typeMap), context(context), vars(vars) {}
};

class ComputeMaxStackSize : public Inspector {
  P4::TypeMap *typeMap;

  unsigned maxStack(const IR::Type *decl);

  unsigned maxStack(const IR::Declaration *decl);
  unsigned maxStack(const IR::ParameterList *parms);
  ComputeMaxStackSize(P4::TypeMap *typeMap) : typeMap(typeMap) {}

public:
  static unsigned maxStackSize(const IR::P4Parser *parser,
                               P4::TypeMap *typeMap);
};

class IsLv : public Inspector {
public:
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

private:
  std::unordered_map<const IR::Expression *, bool> lvs;

  bool preorder(const IR::Expression *e) override {
    lvs[e] = e->is<IR::VersionedExpression>();
    return false;
  }

  bool preorder(const IR::MethodCallExpression *mce) override {
    if (is_is_valid(mce, refMap, typeMap)) {
      auto mem = mce->method->to<IR::Member>();
      visit(mem->expr);
      if (lvs[mem->expr])
        lvs[mce] = true;
      return false;
    }
    lvs[mce] = false;
    return false;
  }
  bool preorder(const IR::Member *mem) override {
    lvs[mem] = !mem->expr->is<IR::TypeNameExpression>();
    return false;
  }
  bool preorder(const IR::PathExpression *pe) override {
    lvs[pe] = true;
    return false;
  }
  bool preorder(const IR::ArrayIndex *ai) override {
    lvs[ai] = true;
    return false;
  }

public:
  IsLv(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}

  const IR::Declaration_ID *isEnumConstant(const IR::Expression *expr) {
    if (expr->is<IR::Member>()) {
      auto mem = expr->to<IR::Member>();
      if (mem->expr->is<IR::TypeNameExpression>()) {
        auto tp = typeMap->getType(expr);
        if (tp->is<IR::Type_Enum>()) {
          return tp->to<IR::Type_Enum>()
              ->getDeclByName(mem->member.name)
              ->to<IR::Declaration_ID>();
        } else if (tp->is<IR::Type_Error>()) {
          return tp->to<IR::Type_Error>()
              ->getDeclByName(mem->member.name)
              ->to<IR::Declaration_ID>();
        }
      } else if (mem->expr->is<IR::PathExpression>()) {
        auto decl =
            refMap->getDeclaration(mem->expr->to<IR::PathExpression>()->path);
        if (decl->is<IR::Type_Enum>()) {
          auto tt = typeMap->getTypeType(decl->to<IR::Type_Enum>(), false)
                        ->to<IR::Type_Enum>();
          return tt->getDeclByName(mem->member.name)->to<IR::Declaration_ID>();
        } else if (decl->is<IR::Type_Error>()) {
          auto tt = typeMap->getTypeType(decl->to<IR::Type_Error>(), false)
                        ->to<IR::Type_Error>();
          return tt->getDeclByName(mem->member.name)->to<IR::Declaration_ID>();
        }
      }
    }
    return nullptr;
  }

  bool operator()(const IR::Node *n) {
    if (n->is<IR::Declaration>()) {
      if (n->is<IR::Declaration_Instance>())
        return false;
      return true;
    } else {
      auto exp = n->to<IR::Expression>();
      CHECK_NULL(exp);
      auto I = lvs.find(exp);
      if (I != lvs.end()) {
        return I->second;
      }
      n->apply(*this);
      return lvs[exp];
    }
  }
};

class LVs : public Inspector {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  IsLv isLv;

public:
  LVs(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);

private:
  std::unordered_set<const IR::Expression *> *current;
  std::unordered_map<const IR::Node *,
                     std::unordered_set<const IR::Expression *>>
      res;
  bool preorder(const IR::Expression *e) override;

public:
  std::unordered_set<const IR::Expression *> *operator()(const IR::Node *n);
};
}
#endif // P4C_ANALYSIS_HELPERS_H
