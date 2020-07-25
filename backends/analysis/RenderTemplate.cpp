//
// Created by dragos on 05.06.2019.
//

#include <inja.hpp>
#include "RenderTemplate.h"
#include "MakeImplementations.h"
#include <analysis/template/GenerateMethods.h>
#include <boost/algorithm/string/split.hpp>
#include <common/parseInput.h>


#include <analysis/tofino/TofinoIntegration.h>
#include <p4/createBuiltins.h>
#include <p4/evaluator/evaluator.h>
#include <p4/methodInstance.h>
#include <p4/moveDeclarations.h>
#include <p4/parseAnnotations.h>
#include <p4/toP4/toP4.h>

using namespace inja;
using json = nlohmann::json;

namespace analysis {

std::map<std::string, std::vector<std::string>>
    RenderTemplate::COMPONENTS({{"ip", {"main", "ingress", "ip"}},
                                {"ig", {"main", "ingress", "ig"}},
                                {"id", {"main", "ingress", "id"}},
                                {"ep", {"main", "egress", "ep"}},
                                {"eg", {"main", "egress", "eg"}},
                                {"ed", {"main", "egress", "ed"}}});

class FindExternTypes : public Inspector {
  std::set<const IR::ExternBlock *> &blocks;
  std::function<bool(const IR::ExternBlock *)> filter;
  FindExternTypes(std::set<const IR::ExternBlock *> &blocks,
                  const std::function<bool(const IR::ExternBlock *)> &filter)
      : blocks(blocks), filter(filter) {}

public:
  static std::set<const IR::ExternBlock *>
  find(const IR::ToplevelBlock *block,
       std::function<bool(const IR::ExternBlock *)> filter) {
    std::set<const IR::ExternBlock *> blocks;
    FindExternTypes fet(blocks, filter);
    block->apply(fet);
    return blocks;
  }

  void recurse(const IR::Block *block) {
    for (auto cv : block->constantValue) {
      if (auto blk = cv.second->to<IR::Block>())
        visit(blk);
    }
  }
  bool preorder(const IR::Block *b) override {
    recurse(b);
    return true;
  }
  bool preorder(const IR::ExternBlock *block) override {
    recurse(block);
    if (filter(block)) {
      blocks.emplace(block);
    }
    return true;
  }
};

class FindPSATypes : public Inspector {
  std::vector<const IR::Node *> path;

public:
  FindPSATypes() { visitDagOnce = false; }
  std::map<const IR::CompileTimeValue *, std::vector<const IR::Node *>>
      revvalues;
  void recurse(const IR::Block *b) {
    for (auto &p : b->constantValue) {
      path.push_back(p.first);
      if (p.second && p.second->is<IR::Block>())
        visit(p.second->to<IR::Block>());
      path.pop_back();
    }
  }
  bool preorder(const IR::PackageBlock *block) override {
    recurse(block);
    return false;
  }
  bool preorder(const IR::ToplevelBlock *tlb) override {
    recurse(tlb);
    return false;
  }
  bool preorder(const IR::ControlBlock *controlBlock) override {
    revvalues[controlBlock] = path;
    recurse(controlBlock);
    return false;
  }
  bool preorder(const IR::ParserBlock *parserBlock) override {
    revvalues[parserBlock] = path;
    recurse(parserBlock);
    return false;
  }
  bool preorder(const IR::ExternBlock *externBlock) override {
    revvalues[externBlock] = path;
    return false;
  }
};

class FindMethods : public Inspector {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  std::function<bool(const P4::MethodInstance *)> met;
  std::set<const P4::MethodInstance *> &instances;

public:
  FindMethods(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
              const std::function<bool(const P4::MethodInstance *)> &met,
              std::set<const P4::MethodInstance *> &instances)
      : refMap(refMap), typeMap(typeMap), met(met), instances(instances) {}

  bool preorder(const IR::MethodCallExpression *mce) override {
    auto res = P4::MethodInstance::resolve(mce, refMap, typeMap);
    if (met(res))
      instances.emplace(res);
    return true;
  }
};
}

analysis::RenderTemplate::RenderTemplate(P4::ReferenceMap *refMap,
                                         P4::TypeMap *typeMap,
                                         const cstring &templateFile,
                                         cstring out)
    : refMap(refMap), typeMap(typeMap), templateFile(templateFile), out(out),
      evaluator(new P4::Evaluator(refMap, typeMap)) {
  passes.push_back(evaluator);
  passes.push_back(new VisitFunctor([this]() {
    CHECK_NULL(evaluator->getToplevelBlock()->getMain());
    auto main = evaluator->getToplevelBlock()->getMain();
    if (main->type->name == "PSA_Switch") {
      this->render();
    } else if (main->type->name == "V1Switch") {
      this->renderv1();
    } else if (main->type->name == "Switch") {
      // go for tofino
      renderTofino();
    } else {
      BUG("unknown architecture %1%", main->type->name);
    }
  }));
}

void analysis::RenderTemplate::renderv1() {
  CHECK_NULL(evaluator->getToplevelBlock()->getMain());
  auto main = evaluator->getToplevelBlock()->getMain();
  BUG_CHECK(main->type->name == "V1Switch", "no v1 switch found, but %1%",
            main->type);
  FindPSATypes psaTypes;
  evaluator->getToplevelBlock()->apply(psaTypes);
  auto parser =
      find_container(psaTypes.revvalues, {"main", "p"})->to<IR::P4Parser>();
  auto H = parser->getApplyParameters()->getParameter(1);
  auto M = parser->getApplyParameters()->getParameter(2);
  std::map<std::string, std::vector<std::string>> COMPONENTS(
      {{"p", {"main", "p"}},
       {"ig", {"main", "ig"}},
       {"eg", {"main", "eg"}},
       {"dep", {"main", "dep"}}});
  json data;
  data["H"] = type_name(H);
  data["M"] = type_name(M);
  Environment env("");
  env.add_callback("declare", 1, [&](Arguments &args) {
    auto declname = args.at(0)->get<std::string>();
    return declare(psaTypes.revvalues, declname, COMPONENTS);
  });
  char ttmp[256] = "temp_";
  mkstemp(ttmp);
  std::ofstream os(ttmp);
  P4::ToP4 toP4(&os, false);
  evaluator->getToplevelBlock()->getProgram()->apply(toP4);
  os << "\n\n// INTEGRATION:\n";
  std::string file = this->templateFile.c_str();
  auto temp = env.parse_template(file);
  env.render_to(os, temp, data);
  os.close();
  AutoCompileContext autoCompileContext(
      new P4CContextWithOptions<CompilerOptions>);
  auto &options = P4CContextWithOptions<CompilerOptions>::get().options();
  options.file = ttmp;
  options.langVersion = CompilerOptions::FrontendVersion::P4_16;
  auto beforeErrcnt = P4CContextWithOptions<CompilerOptions>::get()
                          .errorReporter()
                          .getErrorCount();
  auto parsed = P4::parseP4File(options);
  if (P4CContextWithOptions<CompilerOptions>::get()
          .errorReporter()
          .getErrorCount() != beforeErrcnt) {
    ::error("failed to parse template");
  }
  P4::ReferenceMap newrefMap;
  P4::TypeMap newtypeMap;
  P4::ParseAnnotations::HandlerMap handlers = {PARSE("model", Expression),
                                               PARSE("impl", Expression)};
  auto ostrr = new std::ofstream(out);
  PassManager passManager(
      {new P4::ParseAnnotationBodies(
           new P4::ParseAnnotations("analysis", true, handlers, true),
           &newtypeMap),
       new P4::CreateBuiltins(), new DoCreateMutablePacket(),
       new DoAddErrorField, new P4::UniqueNames(&newrefMap),
       new P4::MoveDeclarations(), new P4::MoveInitializers(),
       new P4::ResolveReferences(&newrefMap),
       new P4::TypeInference(&newrefMap, &newtypeMap, false),
       new GenerateMethods(&newrefMap, &newtypeMap), new P4::ToP4(ostrr, false),
       new VisitFunctor([ostrr]() { ostrr->close(); })});
  beforeErrcnt = ::errorCount();
  parsed->apply(passManager);
  if (::errorCount() != beforeErrcnt) {
    ::error("failed to compile template");
    exit(1);
  }
}

void analysis::RenderTemplate::render() {
  CHECK_NULL(evaluator->getToplevelBlock()->getMain());
  auto main = evaluator->getToplevelBlock()->getMain();
  BUG_CHECK(main->type->name == "PSA_Switch", "no psa found, but %1%",
            main->type);
  FindPSATypes psaTypes;
  evaluator->getToplevelBlock()->apply(psaTypes);
  auto ingress_parser =
      find_container(psaTypes.revvalues, {"main", "ingress", "ip"})
          ->to<IR::P4Parser>();
  auto IH = ingress_parser->getApplyParameters()->getParameter(1);
  auto IM = ingress_parser->getApplyParameters()->getParameter(2);
  auto RESUBM = ingress_parser->getApplyParameters()->getParameter(4);
  auto RECIRC = ingress_parser->getApplyParameters()->getParameter(5);
  auto ingress_deparser =
      find_container(psaTypes.revvalues, {"main", "ingress", "id"})
          ->to<IR::P4Control>();
  auto CI2EM = ingress_deparser->getApplyParameters()->getParameter(1);
  auto NM = ingress_deparser->getApplyParameters()->getParameter(3);
  auto egressParser =
      find_container(psaTypes.revvalues, {"main", "egress", "ep"})
          ->to<IR::P4Parser>();
  auto EH = egressParser->getApplyParameters()->getParameter(1);
  auto EM = egressParser->getApplyParameters()->getParameter(2);
  auto CE2EM = egressParser->getApplyParameters()->getParameter(6);
  std::map<std::string, std::vector<std::string>> COMPONENTS(
      {{"ip", {"main", "ingress", "ip"}},
       {"ig", {"main", "ingress", "ig"}},
       {"id", {"main", "ingress", "id"}},
       {"ep", {"main", "egress", "ep"}},
       {"eg", {"main", "egress", "eg"}},
       {"ed", {"main", "egress", "ed"}}});
  Environment env("");
  json data;
  data["IH"] = type_name(IH);
  data["EH"] = type_name(EH);
  data["IM"] = type_name(IM);
  data["EM"] = type_name(EM);
  data["CI2E"] = type_name(CI2EM);
  data["CE2E"] = type_name(CE2EM);
  data["RESUB"] = type_name(RESUBM);
  data["RECIRC"] = type_name(RECIRC);
  data["NM"] = type_name(NM);
  env.add_callback("declare", 1, [&](Arguments &args) {
    auto declname = args.at(0)->get<std::string>();
    return declare(psaTypes.revvalues, declname, COMPONENTS);
  });

  env.add_callback("implements", 2, [&](Arguments &args) {
    auto what = args.at(0)->get<std::vector<std::string>>();
    auto impl = args.at(1)->get<std::string>();
    return implement(what, impl);
  });
  std::string file = this->templateFile.c_str();
  std::ofstream os(out);
  P4::ToP4 toP4(&os, false);
  evaluator->getToplevelBlock()->getProgram()->apply(toP4);
  os << "\n\n// INTEGRATION:\n";
  auto temp = env.parse_template(file);
  env.render_to(os, temp, data);
  os.close();
}

const IR::IContainer *
analysis::RenderTemplate::find_container(analysis::instance_tree &nodes,
                                         const std::vector<std::string> &path) {
  auto value = find_compile_time_value(nodes, path);
  if (value) {
    if (auto ctb = value->to<IR::ControlBlock>()) {
      return ctb->container;
    } else if (auto psb = value->to<IR::ParserBlock>()) {
      return psb->container;
    }
  }
  return nullptr;
}
const IR::CompileTimeValue *analysis::RenderTemplate::find_compile_time_value(
    analysis::instance_tree &nodes, const std::vector<std::string> &path) {
  const IR::CompileTimeValue *value = nullptr;
  for (auto &ctpath : nodes) {
    if (path.size() == ctpath.second.size()) {
      auto I = path.begin();
      auto I2 = ctpath.second.begin();
      for (; I != path.end(); ++I, ++I2) {
        if (auto dec = (*I2)->to<IR::IDeclaration>()) {
          if (dec->getName().name == *I) {
            continue;
          } else {
            break;
          }
        } else {
          break;
        }
      }
      if (I == path.end()) {
        // not found
        value = ctpath.first;
      }
    }
  }
  return value;
}
std::string analysis::RenderTemplate::declare(
    analysis::instance_tree &nodes, const std::string &name,
    const std::map<std::string, std::vector<std::string>> &COMPONENTS) {
  auto cp = COMPONENTS.find(name);
  if (cp != COMPONENTS.end()) {
    auto ctv = find_compile_time_value(nodes, cp->second);
    if (ctv && ctv->is<IR::Block>()) {
      auto block = ctv->to<IR::Block>();
      auto conscall = block->node->to<IR::ConstructorCallExpression>();
      CHECK_NULL(conscall);
      auto tn = type_name(conscall->type);
      auto di = new IR::Declaration_Instance(
          IR::ID(name), new IR::Type_Name(tn.c_str()), conscall->arguments);
      std::stringstream ss;
      P4::ToP4 top4(&ss, false);
      di->apply(top4);
      return ss.str();
    }
  }
  return "";
}

std::string analysis::RenderTemplate::type_name(const IR::Parameter *parm) {
  auto tp = typeMap->getType(parm);
  return type_name(tp);
}

std::string analysis::RenderTemplate::type_name(const IR::Type *tp) {
  if (auto td = tp->to<IR::Type_Declaration>()) {
    return td->name.name.c_str();
  } else {
    std::stringstream ss;
    ss << tp;
    return ss.str();
  }
}

std::string analysis::RenderTemplate::implement(std::vector<std::string> stuff,
                                                std::string templ) {
  Environment env("");
  std::stringstream buffer;
  auto tmpl = env.parse(templ);
  evaluator->getToplevelBlock();
  for (auto &that : stuff) {
    std::vector<cstring> components;
    const char *cSymbol = that.c_str();
    boost::split(components, cSymbol, [](char c) { return c == '.'; });
    auto decls = evaluator->getToplevelBlock()->getProgram()->getDeclsByName(
        components[0]);
    std::vector<const IR::IDeclaration *> actual_decls;
    for (auto d : *decls) {
      actual_decls.push_back(d);
    }
  }
  return buffer.str();
}

void analysis::RenderTemplate::renderTofino() {
  //TODO: tofino stub
  BUG("tofino backend is not implemented in this version");
}
