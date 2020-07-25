//
// Created by dragos on 07.06.2019.
//

#include "MakeImplementations.h"
#include "analysis_helpers.h"
#include "cfg_algos.h"
#include <build/ir/ir-generated.h>
#include <common/resolveReferences/resolveReferences.h>
#include <frontends/p4/coreLibrary.h>
#include <p4/evaluator/substituteParameters.h>
#include <p4/methodInstance.h>
#include <p4/moveDeclarations.h>
#include <p4/typeChecking/bindVariables.h>
#include <p4/typeChecking/typeChecker.h>
#include <p4/typeMap.h>

namespace analysis {

class DeclarePacket : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  std::map<std::pair<cstring, std::vector<const IR::Type *>>,
           const IR::Declaration *>
      methods;
  std::set<const IR::Declaration *> extra_methods;

public:
  DeclarePacket(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}

  std::set<const IR::Node *> get_dependencies(const IR::Type_MethodBase *tmb) {
    auto prog = getOriginal<IR::P4Program>();
    std::set<const IR::Node *> decls;
    for (auto p : *tmb->parameters) {
      if (p->type->is<IR::Type_Name>()) {
        auto progdecl =
            prog->getDeclsByName(p->type->to<IR::Type_Name>()->path->name);
        for (auto pd : *progdecl) {
          decls.emplace(pd->getNode());
        }
      }
    }
    return decls;
  }

  std::set<const IR::Node *> get_deps(const IR::Node *decl) {
    if (auto m = decl->to<IR::Method>()) {
      return get_dependencies(m->type);
    } else if (auto f = decl->to<IR::Function>()) {
      return get_dependencies(f->type);
    }
    return {};
  }

  void safe_insert(IR::P4Program *prog, const IR::Node *n) {
    auto deps = get_deps(n);
    int i = static_cast<int>(prog->objects.size() - 1);
    for (; i >= 0; --i) {
      auto crt = prog->objects.at(i);
      if (deps.count(crt)) {
        break;
      }
    }
    auto I = prog->objects.begin() + i + 1;
    prog->objects.insert(I, n);
  }

  const IR::Node *postorder(IR::P4Program *prog) override {
    IR::Vector<IR::Node> decls;
    auto text = new IR::Type_Struct("packet_model");
    text->fields.push_back(
        new IR::StructField("contents", new IR::Type_Bits(32, false)));
    text->fields.push_back(
        new IR::StructField("len", new IR::Type_Bits(32, false)));
    if (!prog->getDeclsByName("packet_model")->count()) {
      decls.push_back(text);
    }
    prog->objects.insert(prog->objects.begin(), decls.begin(), decls.end());
    for (auto &n : methods) {
      safe_insert(prog, n.second);
    }
    return prog;
  }

  const IR::Node *postorder(IR::Parameter *parm) override {
    auto ptype = parm->type;
    cstring tname = "";
    if (auto textern = ptype->to<IR::Type_Extern>()) {
      tname = textern->name;
    } else if (auto tyname = ptype->to<IR::Type_Name>()) {
      tname = tyname->path->name;
    }
    if (tname == P4::P4CoreLibrary::instance.packetIn.name ||
        tname == P4::P4CoreLibrary::instance.packetOut.name) {
      parm->type = new IR::Type_Name("packet_model");
      parm->direction = IR::Direction::InOut;
    }
    return parm;
  }

  const IR::Type *convert(const IR::Type *td) {
    if (auto tdd = td->to<IR::Type_Declaration>())
      return new IR::Type_Name(tdd->name);
    return td;
  }

  const IR::Type_Method *make_method_type(
      const IR::Type *extern_type, const IR::Type_Method *actual_method,
      const std::function<const IR::Type *(const IR::Type *)> &fun) {
    auto parmList = new IR::ParameterList();
    parmList->push_back(new IR::Parameter("self", IR::Direction::InOut,
                                          convert(fun(extern_type))));
    for (auto other : *actual_method->parameters) {
      auto op = other->clone();
      op->type = fun(op->type);
      parmList->push_back(op);
    }
    auto tm = actual_method->clone();
    tm->parameters = parmList;
    tm->typeParameters = new IR::TypeParameters;
    tm->returnType = fun(tm->returnType);
    return tm;
  }

  const IR::Type *replace_packet_inout(const IR::Type *tp) {
    cstring tname = "";
    if (auto te = tp->to<IR::Type_Extern>()) {
      tname = te->name;

    } else if (auto tyname = tp->to<IR::Type_Name>()) {
      tname = tyname->path->name;
    }
    if (tname == P4::P4CoreLibrary::instance.packetIn.name ||
        tname == P4::P4CoreLibrary::instance.packetOut.name) {
      return convert(new IR::Type_Name("packet_model"));
    }
    return convert(tp);
  }

  const IR::Node *postorder(IR::MethodCallExpression *e) override {
    auto orig = getOriginal<IR::MethodCallExpression>();
    auto mi = P4::MethodInstance::resolve(orig, refMap, typeMap);
    if (auto me = mi->to<P4::ExternMethod>()) {
      if (me->actualExternType->name ==
              P4::P4CoreLibrary::instance.packetIn.name ||
          me->actualExternType->name ==
              P4::P4CoreLibrary::instance.packetOut.name) {
        auto actual = me->actualMethodType;
        auto newmethod = make_method_type(
            me->actualExternType, me->actualMethodType->to<IR::Type_Method>(),
            [this](const IR::Type *t) { return replace_packet_inout(t); });
        auto typeVector =
            actual->parameters->parameters.getEnumerator()
                ->map(std::function<const IR::Type *(
                          const IR::Parameter *const &)>(
                    [](const IR::Parameter *const &p) -> const IR::Type * {
                      return p->type;
                    }))
                ->toVector();
        auto nm = me->method->name;
        auto v = *typeVector;
        auto pair = std::pair<cstring, std::vector<const IR::Type *>>(
            nm.name, std::move(v));
        auto EMI = methods.emplace(
            std::make_pair<std::pair<cstring, std::vector<const IR::Type *>>,
                           const IR::Declaration *>(std::move(pair), nullptr));
        if (EMI.second) {
          EMI.first->second = new IR::Method(refMap->newName(nm), newmethod);
        }
        auto args = new IR::Vector<IR::Argument>();
        args->emplace_back(new IR::PathExpression(me->object->getName()));
        for (auto pv : *e->arguments)
          args->push_back(pv->clone());
        return new IR::MethodCallExpression(
            new IR::PathExpression(EMI.first->second->getName()), args);
      }
    }
    return e;
  }
};

class FindImplementations : public Inspector {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  std::map<const IR::Type_Extern *, const IR::Type_Struct *> &impls;

public:
  FindImplementations(
      P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
      std::map<const IR::Type_Extern *, const IR::Type_Struct *> &impls)
      : refMap(refMap), typeMap(typeMap), impls(impls) {}

  void postorder(const IR::Type_Struct *impl) override {
    auto annots = impl->getAnnotations()->where(
        [](const IR::Annotation *annot) { return annot->name.name == "impl"; });
    for (auto an : annots->annotations) {
      auto exp = an->expr[0]->to<IR::StringLiteral>()->value;
      auto decl = findContext<IR::P4Program>()->getDeclsByName(exp);
      for (auto d : *decl) {
        if (d->is<IR::Type_Extern>()) {
          auto canon = typeMap->getTypeType(d->to<IR::Type_Extern>(), true);
          impls[canon->to<IR::Type_Extern>()] =
              typeMap->getTypeType(impl, true)->to<IR::Type_Struct>();
        }
      }
    }
  }
};

class DoImplementation : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  std::map<const IR::Type_Extern *, const IR::Type_Struct *> &impls;
  std::set<const IR::Type_Struct *> already;

public:
  DoImplementation(
      P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
      std::map<const IR::Type_Extern *, const IR::Type_Struct *> &impls)
      : refMap(refMap), typeMap(typeMap), impls(impls) {}

  const IR::Node *postorder(IR::Type_Struct *strt) override {
    auto thestruct = typeMap->getTypeType(getOriginal<IR::Type_Struct>(), true);
    auto I = std::find_if(
        impls.begin(), impls.end(),
        [thestruct](
            const std::pair<const IR::Type_Extern *, const IR::Type_Struct *>
                &bla) { return bla.second == thestruct; });
    if (I != impls.end()) {
      return nullptr;
    }
    return strt;
  }

  const IR::Node *postorder(IR::Type_Extern *doimpl) override {
    auto nodes = new IR::Vector<IR::Node>;
    auto orig = getOriginal<IR::Type_Extern>();
    auto tt = typeMap->getTypeType(orig, true)->to<IR::Type_Extern>();
    auto I = impls.find(tt);
    if (I != impls.end()) {
      if (already.emplace(I->second).second) {
        auto ts = I->second->clone();
        ts->srcInfo = doimpl->srcInfo;
        nodes->push_back(ts);
      }
      for (auto method : tt->methods) {
        // TODO: deal with constructors -> later
        auto newmet = method->clone();
        auto newmettype = newmet->type->clone();
        auto parmlist = new IR::ParameterList;
        parmlist->push_back(new IR::Parameter(
            "self", IR::Direction::InOut, new IR::Type_Name(I->second->name)));
        for (auto old : *newmettype->parameters)
          parmlist->push_back(old);
        newmettype->parameters = parmlist;
        newmet->type = newmettype;
        nodes->push_back(newmet);
      }
      LOG4("implemented " << doimpl << " by " << I->second);
      return nodes;
    }
    return doimpl;
  }

  const IR::Node *postorder(IR::Parameter *decl) override {
    auto orig = getOriginal<IR::Parameter>();
    auto t = typeMap->getType(orig);
    if (auto text = t->to<IR::Type_Extern>()) {
      auto I = impls.find(text);
      if (I != impls.end()) {
        decl->type = new IR::Type_Name(I->second->name);
        decl->direction = IR::Direction::InOut;
      }
    }
    return decl;
  }

  const IR::Node *postorder(IR::MethodCallExpression *mce) override {
    auto orig = getOriginal<IR::MethodCallExpression>();
    auto mi = P4::MethodInstance::resolve(orig, refMap, typeMap);
    if (auto em = mi->to<P4::ExternMethod>()) {
      BUG_CHECK(em->actualExternType == em->originalExternType,
                "can't handle type params");
      auto I = impls.find(em->actualExternType);
      if (I != impls.end()) {
        auto newargs = new IR::Vector<IR::Argument>();
        newargs->emplace_back(mce->method->to<IR::Member>()->expr);
        newargs->insert(newargs->end(), mce->arguments->begin(),
                        mce->arguments->end());
        auto newmce = new IR::MethodCallExpression(
            mce->getSourceInfo(), new IR::PathExpression(em->method->name),
            newargs);
        LOG4("handling " << mce << " -> " << newmce);
        return newmce;
      }
    }
    return mce;
  }
};

class MakeDiePostPartum : public Transform {
  std::map<const IR::Node *, scope *> &scopes;

  const IR::Node *postorder(IR::P4Program *prog) override {
    auto decls = prog->getDeclsByName("dead");
    if (!decls->count()) {
      IR::Vector<IR::Node> newobjects;
      newobjects.push_back(new IR::Method(
          "dead", new IR::Type_Method(new IR::ParameterList({new IR::Parameter(
                      "in", IR::Direction::In, new IR::Type_InfInt)}))));
      newobjects.insert(newobjects.end(), prog->objects.begin(),
                        prog->objects.end());
      prog->objects = newobjects;
    }
    return prog;
  }

  const IR::Statement *kill_one(unsigned x) {
    auto mce = new IR::MethodCallExpression(
        new IR::PathExpression("dead"),
        new IR::Vector<IR::Argument>({new IR::Argument(new IR::Constant(x))}));
    return new IR::MethodCallStatement(mce);
  }

  const IR::BlockStatement *killAllInScope(const scope *s) {
    auto bs = new IR::BlockStatement();
    for (auto &d : s->declarations) {
      bs->push_back(kill_one(d.second));
    }
    return bs;
  }

  const IR::Node *postorder(IR::Node *n) override {
    auto I = scopes.find(getOriginal());
    if (I != scopes.end() && !I->second->declarations.empty()) {
      if (auto fun = n->to<IR::Function>()) {
        auto funcl = fun->clone();
        auto bcl = funcl->body->clone();
        bcl->push_back(killAllInScope(I->second));
        funcl->body = bcl;
        return funcl;
      } else if (auto bs = n->to<IR::BlockStatement>()) {
        auto bscl = bs->clone();
        bscl->push_back(killAllInScope(I->second));
        return bscl;
      } else if (auto ctrl = n->to<IR::P4Control>()) {
        auto ctrlcl = ctrl->clone();
        auto bcl = ctrlcl->body->clone();
        bcl->push_back(killAllInScope(I->second));
        ctrlcl->body = bcl;
        return ctrlcl;
      } else if (auto prs = n->to<IR::P4Parser>()) {
        auto accept =
            prs->states
                .getDeclaration<IR::ParserState>(IR::ParserState::accept)
                ->clone();
        accept->components.push_back(killAllInScope(I->second));
        auto reject =
            prs->states
                .getDeclaration<IR::ParserState>(IR::ParserState::reject)
                ->clone();
        reject->components.push_back(killAllInScope(I->second));
        auto prscl = prs->clone();
        prscl->states.removeByName(IR::ParserState::accept);
        prscl->states.push_back(accept);
        prscl->states.removeByName(IR::ParserState::reject);
        prscl->states.push_back(reject);
        return prscl;
      } else if (auto ps = n->to<IR::ParserState>()) {
        auto pscl = ps->clone();
        pscl->components.push_back(killAllInScope(I->second));
        return pscl;
      }
    }
    return n;
  }

public:
  MakeDiePostPartum(std::map<const IR::Node *, scope *> &scopes)
      : scopes(scopes) {
    setName("MakeDiePostPartum");
  }
};

MakeDie::MakeDie(P4::ReferenceMap *refMap) {
  setName("MakeDie");
  auto scopes = new std::map<const IR::Node *, scope *>;
  addPasses({new BuildScopeTree(*scopes), new MakeDiePostPartum(*scopes),
             new P4::ResolveReferences(refMap)});
}

scope *scope_context::new_scope() { return new scope(this); }

void scope::addDeclaration(const IR::IDeclaration *decl) {
  declarations.emplace(decl, ctx->crtId++);
}

scope::scope(scope_context *context) : ctx(context), parent(nullptr) {}

std::map<const IR::IDeclaration *, unsigned>
variable_declarations(const IR::P4Program *p) {
  std::map<const IR::Node *, scope *> scopes;
  BuildScopeTree buildScopeTree(scopes);
  p->apply(buildScopeTree);
  return variable_declarations(p, scopes);
};

std::map<const IR::Node *, scope *> scopes(const IR::P4Program *prog) {
  std::map<const IR::Node *, scope *> scopes;
  BuildScopeTree buildScopeTree(scopes);
  prog->apply(buildScopeTree);
  return scopes;
}

std::map<const IR::IDeclaration *, unsigned int>
variable_declarations(const IR::P4Program *p,
                      const std::map<const IR::Node *, scope *> &scopes) {
  std::map<const IR::IDeclaration *, unsigned> ret;
  auto progscope = scopes.find(p)->second;
  std::vector<scope *> worklist({progscope});
  while (!worklist.empty()) {
    auto crt = worklist.back();
    worklist.pop_back();
    ret.insert(crt->declarations.begin(), crt->declarations.end());
    for (auto child : crt->children)
      worklist.push_back(child);
  }
  return ret;
}

void BuildScopeTree::mkScope(const IR::Node *node) {
  auto newscope = ctx->new_scope();
  newscope->parent = crtScope;
  if (crtScope) {
    crtScope->children.push_back(newscope);
  }
  crtScope = newscope;
  scopes[node] = crtScope;
}

void BuildScopeTree::pop() { crtScope = crtScope->parent; }

void BuildScopeTree::registerTypeParameters(const IR::TypeParameters *parms) {
  for (auto parm : parms->parameters) {
    crtScope->addDeclaration(parm);
  }
}

void BuildScopeTree::registerParameters(const IR::ParameterList *parms) {
  for (auto parm : *parms) {
    crtScope->addDeclaration(parm);
  }
}

bool BuildScopeTree::preorder(const IR::P4Program *p) {
  mkScope(p);
  return true;
}

bool BuildScopeTree::preorder(const IR::Function *fun) {
  crtScope->addDeclaration(fun);
  mkScope(fun);
  for (auto parm : *fun->getParameters()) {
    crtScope->addDeclaration(parm);
  }
  registerTypeParameters(fun->type->typeParameters);
  visit(fun->body);
  pop();
  return false;
}

bool BuildScopeTree::preorder(const IR::Type_Extern *text) {
  crtScope->addDeclaration(text);
  mkScope(text);
  registerTypeParameters(text->typeParameters);
  visit(text->methods);
  pop();
  return false;
}

bool BuildScopeTree::preorder(const IR::Method *m) {
  crtScope->addDeclaration(m);
  mkScope(m);
  registerTypeParameters(m->type->typeParameters);
  registerParameters(m->getParameters());
  pop();
  return false;
}

bool BuildScopeTree::preorder(const IR::Type_StructLike *sl) {
  crtScope->addDeclaration(sl);
  mkScope(sl);
  for (auto fld : sl->fields) {
    crtScope->addDeclaration(fld);
  }
  pop();
  return false;
}

bool BuildScopeTree::preorder(const IR::P4Control *control) {
  crtScope->addDeclaration(control);
  mkScope(control);
  registerTypeParameters(control->getTypeParameters());
  registerParameters(control->constructorParams);
  registerParameters(control->getApplyParameters());
  for (auto local : control->controlLocals) {
    crtScope->addDeclaration(local);
  }
  visit(control->body);
  pop();
  return false;
}

bool BuildScopeTree::preorder(const IR::P4Parser *control) {
  crtScope->addDeclaration(control);
  mkScope(control);
  registerTypeParameters(control->getTypeParameters());
  registerParameters(control->constructorParams);
  registerParameters(control->getApplyParameters());
  for (auto local : control->parserLocals) {
    crtScope->addDeclaration(local);
  }
  for (auto st : control->states)
    crtScope->addDeclaration(st);
  visit(control->states);
  pop();
  return false;
}

bool BuildScopeTree::preorder(const IR::ParserState *state) {
  mkScope(state);
  visit(state->components);
  visit(state->selectExpression);
  pop();
  return false;
}

bool BuildScopeTree::preorder(const IR::BlockStatement *statement) {
  mkScope(statement);
  auto declvec = statement->getDeclarations()->toVector();
  for (auto d : *declvec) {
    crtScope->addDeclaration(d);
  }
  pop();
  return false;
}

bool BuildScopeTree::preorder(const IR::Node *n) {
  if (n->is<IR::IDeclaration>()) {
    crtScope->addDeclaration(n->to<IR::IDeclaration>());
  }
  return true;
}

BuildScopeTree::BuildScopeTree(std::map<const IR::Node *, scope *> &scopes)
    : ctx(new scope_context), scopes(scopes) {}

MakeImplementations::MakeImplementations(P4::ReferenceMap *refMap,
                                         P4::TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap) {
  setName("MakeImplementations");
  auto mappings =
      new std::map<const IR::Type_Extern *, const IR::Type_Struct *>;
  stop_on_error = false;
  passes.push_back(new P4::TypeInference(refMap, typeMap, false));
  passes.push_back(new FindImplementations(refMap, typeMap, *mappings));
  passes.push_back(new DoImplementation(refMap, typeMap, *mappings));
  passes.push_back(new P4::ResolveReferences(refMap));
  passes.push_back(new P4::ClearTypeMap(typeMap));
  passes.push_back(new P4::TypeInference(refMap, typeMap, false));
}

const IR::Node *DoCreateMutablePacket::postorder(IR::P4Program *prog) {
  auto &instance = analysis::AnalysisLibrary::instance;
  if (!prog->getDeclsByName(instance.mutablePacket.name)->count()) {
    auto packet_in =
        (*prog->getDeclsByName(P4::P4CoreLibrary::instance.packetIn.name)
              ->begin())
            ->to<IR::Type_Extern>();
    auto packet_out =
        (*prog->getDeclsByName(P4::P4CoreLibrary::instance.packetOut.name)
              ->begin())
            ->to<IR::Type_Extern>();
    auto mutable_packet =
        new IR::Type_Extern(prog->srcInfo, instance.mutablePacket.name);
    auto constructor_mt =
        new IR::Type_Method(new IR::ParameterList({new IR::Parameter(
            "size", IR::Direction::None, new IR::Type_InfInt())}));
    auto cons = new IR::Method(instance.mutablePacket.name, constructor_mt);
    mutable_packet->methods.push_back(cons);
    mutable_packet->methods.insert(mutable_packet->methods.end(),
                                   packet_in->methods.begin(),
                                   packet_in->methods.end());
    P4::ClonePathExpressions cpe;
    mutable_packet->methods.insert(mutable_packet->methods.end(),
                                   packet_out->methods.begin(),
                                   packet_out->methods.end());

    auto secConstructor = [&](cstring name) {
      auto parmself =
          new IR::Parameter("self", IR::Direction::None,
                            new IR::Type_Name(instance.mutablePacket.name));
      auto parmother =
          new IR::Parameter("other", IR::Direction::None,
                            new IR::Type_Name(instance.mutablePacket.name));
      parmother->annotations = parmother->annotations->addAnnotation(
          instance.readonly.name, nullptr);
      auto sign = new IR::Type_Method(
          IR::Type_Void::get(), new IR::ParameterList({parmself, parmother}));
      return new IR::Method(prog->srcInfo, name, sign);
    };
    auto nullconstructor = [&](cstring name) {
      auto parmself =
          new IR::Parameter("self", IR::Direction::None,
                            new IR::Type_Name(instance.mutablePacket.name));
      auto sign = new IR::Type_Method(IR::Type_Void::get(),
                                      new IR::ParameterList({parmself}));
      return new IR::Method(prog->srcInfo, name, sign);
    };
    LOG4("created mutable packet " << mutable_packet);
    IR::Vector<IR::Node> newobjects(
        {mutable_packet->apply(cpe), secConstructor(instance.copyPacket.name),
         secConstructor(instance.prependPacket.name),
         nullconstructor(instance.readPacket.name),
         nullconstructor(instance.emptyPacket.name)});
    if (!prog->getDeclsByName(instance.send.name)->count()) {
      auto typeParms = new IR::TypeParameters();
      typeParms->push_back(new IR::Type_Var("H"));
      auto type = new IR::Type_Method(
          typeParms, IR::Type_Void::get(),
          new IR::ParameterList(
              {new IR::Parameter("port", IR::Direction::In,
                                 new IR::Type_Name("H")),
               new IR::Parameter(
                   "pin", IR::Direction::None,
                   new IR::Type_Name(instance.mutablePacket.name))}));
      auto funDecl = new IR::Method(
          prog->getSourceInfo(),
          IR::ID(prog->getSourceInfo(), instance.send.name), type);
      newobjects.push_back(funDecl);
    }
    newobjects.append(prog->objects);
    prog->objects = std::move(newobjects);
  }
  return prog;
}

const IR::Node *DoCreateMutablePacket::postorder(IR::Parameter *param) {
  if (param->direction == IR::Direction::None) {
    if (param->type->is<IR::Type_Name>()) {
      if (param->type->to<IR::Type_Name>()->path->name ==
              P4::P4CoreLibrary::instance.packetIn.name ||
          param->type->to<IR::Type_Name>()->path->name ==
              P4::P4CoreLibrary::instance.packetOut.name) {
        param->type = new IR::Type_Name(
            analysis::AnalysisLibrary::instance.mutablePacket.name);
      }
    }
  }
  return param;
}

const IR::Node *DoAddErrorField::postorder(IR::Type_Parser *tp) {
  if (tp->applyParams->getDeclByName("err")) {
    return tp;
  }
  if (auto ttp =
          tp->applyParams->parameters.back()->type->to<IR::Type_Name>()) {
    if (ttp->path->name.name == IR::Type_Error::error) {
      return tp;
    }
  }
  auto app = tp->applyParams->clone();
  app->push_back(new IR::Parameter("err", IR::Direction::InOut,
                                   new IR::Type_Name("error")));
  tp->applyParams = app;
  return tp;
}

DoCastReplace::DoCastReplace(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap) {}

const IR::Node *DoCastReplace::postorder(IR::MethodCallExpression *mce) {
  if (mce->method->is<IR::PathExpression>()) {
    auto pe = mce->method->to<IR::PathExpression>();
    if (pe->path->name == "do_cast") {
      if (findContext<IR::Statement>()->is<IR::MethodCallStatement>()) {
        BUG("bad place to call do_cast %1%", findContext<IR::Statement>());
      }
      auto srct = typeMap->getType(mce->arguments->at(0));
      auto dstt = typeMap->getType(mce->arguments->at(1));
      if (srct == dstt) {
        return mce->arguments->at(0)->expression;
      } else {
        const IR::Expression *srcReach = mce->arguments->at(0)->expression;
        std::vector<const IR::Type *> srcTraversed, dstTraversed;
        const IR::Type_Bits *nrDst = getBits(dstt, dstTraversed);
        const IR::Type_Bits *nrSrc = getBits(srct, srcTraversed);
        if (!nrSrc && nrDst && srct->is<IR::Type_InfInt>()) {
          if (mce->arguments->at(0)->expression->is<IR::Constant>()) {
            auto ct =
                mce->arguments->at(0)->expression->to<IR::Constant>()->clone();
            ct->type = nrDst;
            nrSrc = nrDst;
            srcReach = ct;
          }
        }
        if (nrSrc != nullptr && nrDst != nullptr) {
          const IR::Expression *srcExp = srcReach;
          for (auto Is = srcTraversed.begin(); Is != srcTraversed.end(); ++Is) {
            auto dstcast = *Is;
            srcExp = cast(srcExp, dstcast);
          }
          if (nrSrc->size != nrDst->size) {
            srcExp = cast(srcExp, nrDst);
          }
          auto Id = dstTraversed.rbegin();
          bool dstCast = false;
          if (Id != dstTraversed.rend()) {
            dstCast = true;
            ++Id;
          }
          for (; Id != dstTraversed.rend(); ++Id) {
            auto dstcast = *Id;
            srcExp = cast(srcExp, dstcast);
          }
          if (dstCast)
            srcExp = cast(srcExp, dstt);
          return srcExp;
        }
      }
    }
  }
  return mce;
}

const IR::Type_Bits *
DoCastReplace::getBits(const IR::Type *srct,
                       std::vector<const IR::Type *> &traversed) const {
  while (srct && !srct->is<IR::Type_InfInt>() && !srct->is<IR::Type_Bits>()) {
    if (srct->is<IR::Type_Typedef>()) {
      srct = typeMap->getTypeType(srct->to<IR::Type_Typedef>()->type, false);
    } else if (srct->is<IR::Type_Newtype>()) {
      srct = typeMap->getTypeType(srct->to<IR::Type_Newtype>()->type, false);
    } else {
      BUG("wrong type %1%", srct);
    }
    if (srct)
      traversed.emplace_back(srct);
  }
  if (!srct)
    return nullptr;
  return srct->to<IR::Type_Bits>();
}

const IR::Expression *DoCastReplace::cast(const IR::Expression *e,
                                          const IR::Type *t) {
  auto tt = t;
  if (t->is<IR::Type_Declaration>()) {
    tt = new IR::Type_Name(t->to<IR::Type_Declaration>()->name);
  }
  return new IR::Cast(tt, e);
}

void DoCastReplace::end_apply(const IR::Node *n) {
  return Transform::end_apply(n);
}

CastReplace::CastReplace(P4::ReferenceMap *refMap, P4::TypeMap *typeMap) {
  passes.push_back(new DoCastReplace(refMap, typeMap));
  passes.push_back(new P4::ClearTypeMap(typeMap));
  passes.push_back(new P4::TypeChecking(refMap, typeMap, false));
}

const IR::Node *RemoveTypedefs::postorder(IR::Type *tt) {
  auto typeOfType = typeMap->getType(getOriginal(), false);
  if (typeOfType && typeOfType->is<IR::Type_Type>()) {
    auto ttt = typeOfType->to<IR::Type_Type>()->type;
    if (ttt->is<IR::Type_Typedef>()) {
      auto td = ttt->to<IR::Type_Typedef>();
      if (!td->getAnnotation("noremove")) {
        return typeMap->getTypeType(td->type, true);
      }
    } else if (ttt->is<IR::Type_Newtype>()) {
      auto tn = ttt->to<IR::Type_Newtype>();
      if (!tn->getAnnotation("noremove")) {
        return typeMap->getTypeType(tn->type, true);
      }
    }
  }
  return tt;
}

class DoNormalize : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

  const IR::Node *contextualize(std::vector<const IR::Node *> before,
                                const IR::Node *last) {
    auto ctx = getContext();
    while (ctx) {
      auto node = ctx->node;
      if (node->is<IR::IfStatement>() || node->is<IR::CaseEntry>()) {
        auto bs = new IR::BlockStatement();
        for (auto b : before) {
          BUG_CHECK(b->is<IR::StatOrDecl>(),
                    "components must be stat or decl, but %1% found", b);
          bs->components.push_back(b->to<IR::StatOrDecl>());
        }
        if (last && last->is<IR::StatOrDecl>())
          bs->push_back(last->to<IR::StatOrDecl>());
        return bs;
      } else if (node->is<IR::IndexedVector<IR::StatOrDecl>>() ||
                 node->is<IR::BlockStatement>() ||
                 node->is<IR::ParserState>()) {
        auto iv = new IR::IndexedVector<IR::StatOrDecl>();
        for (auto b : before) {
          BUG_CHECK(b->is<IR::StatOrDecl>(),
                    "components must be stat or decl, but %1% found", b);
          iv->push_back(b->to<IR::StatOrDecl>());
        }
        if (last && last->is<IR::StatOrDecl>())
          iv->push_back(last->to<IR::StatOrDecl>());
        return iv;
      }
      ctx = ctx->parent;
    }
    BUG("unreachable, no context");
  }

  const IR::Node *postorder(IR::IfStatement *ifs) override {
    auto mets =
        IdentifyMethodCalls::getMethods(ifs->condition, refMap, typeMap);
    if (mets.empty())
      return ifs;
    std::vector<const IR::Node *> before;
    auto nd = normalize(ifs, mets, before);
    if (before.empty()) {
      return nd;
    }
    return contextualize(before, nd);
  }

  const IR::Node *postorder(IR::AssignmentStatement *asg) override {
    auto rv = asg->right;
    auto mets = IdentifyMethodCalls::getMethods(rv, refMap, typeMap);
    if (mets.size() <= 1)
      return asg;
    std::vector<const IR::Node *> before;
    auto nd = normalize(asg, mets, before);
    if (before.empty()) {
      return nd;
    }
    return contextualize(before, nd);
  }

  const IR::Node *postorder(IR::MethodCallStatement *mcs) override {
    auto mets = IdentifyMethodCalls::getMethods(mcs, refMap, typeMap);
    std::vector<const IR::Node *> before;
    auto nd = normalize(mcs, mets, before);
    if (before.empty()) {
      return nd;
    }
    return contextualize(before, nd);
  }

  const IR::Node *normalize(const IR::Node *orig,
                            const std::vector<MethodInstance *> &mets,
                            std::vector<const IR::Node *> &before) const {
    const IR::Node *nxt = orig;
    if (orig->is<IR::MethodCallStatement>() && mets.size() == 1)
      return orig;
    auto actualmets = 0;
    for (auto met : mets) {
      if (met->is<BuiltInMethod>()) {
        // leave is valid be
        if (met->to<BuiltInMethod>()->name == IR::Type_Header::isValid)
          continue;
      }
      ++actualmets;
    }
    if (actualmets <= 1 && !orig->is<IR::IfStatement>())
      return orig;
    if (actualmets == 0 && orig->is<IR::IfStatement>())
      return orig;
    for (auto met : mets) {
      if (met->is<BuiltInMethod>()) {
        // leave is valid be
        if (met->to<BuiltInMethod>()->name == IR::Type_Header::isValid)
          continue;
      }
      if (!met->actualMethodType->returnType ||
          met->actualMethodType->returnType->is<IR::Type_Void>())
        continue;
      auto tmp = refMap->newName("tmp");
      const IR::Type *tt = nullptr;
      if (met->actualMethodType->returnType->is<IR::Type_Declaration>()) {
        tt = new IR::Type_Name(
            met->actualMethodType->returnType->to<IR::Type_Declaration>()
                ->name);
      } else {
        tt = met->actualMethodType->returnType;
      }
      auto decl = new IR::Declaration_Variable(orig->srcInfo, tmp, tt);
      auto v = new IR::PathExpression(new IR::Path(orig->srcInfo, tmp));
      auto asg = new IR::AssignmentStatement(v, met->expr);
      before.push_back(decl);
      before.push_back(asg);
      nxt = ReplaceOccurence::replaceStatic(met->expr, v, nxt);
    }
    return nxt;
  }

public:
  DoNormalize(ReferenceMap *refMap, TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}
};

class AddDefaultCase : public Transform {
  const IR::Node *postorder(IR::SelectExpression *selex) override {
    unsigned i = 0;
    for (; i != selex->selectCases.size(); ++i) {
      auto sc = selex->selectCases[i];
      if (sc->keyset->is<IR::DefaultExpression>()) {
        return selex;
      }
    }
    selex->selectCases.push_back(
        new IR::SelectCase(selex->srcInfo, new IR::DefaultExpression,
                           new IR::PathExpression(IR::ParserState::reject)));
    return selex;
  }
};

Normalize::Normalize(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap) {
  passes.push_back(new AddDefaultCase);
  passes.push_back(new DoNormalize(refMap, typeMap));
  passes.push_back(new P4::ResolveReferences(refMap));
  addPasses({new P4::MoveDeclarations(), new P4::MoveInitializers(),
             new P4::ResolveReferences(refMap)});
  addPasses({new P4::ClearTypeMap(typeMap), new P4::ResolveReferences(refMap),
             new P4::TypeInference(refMap, typeMap, false)});
}

class DoMoveReturns : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

public:
  DoMoveReturns(ReferenceMap *refMap, TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}

private:
  const IR::Node *postorder(IR::AssignmentStatement *asg) override {
    if (asg->right->is<IR::MethodCallExpression>()) {
      auto mce = asg->right->to<IR::MethodCallExpression>();
      auto mi = P4::MethodInstance::resolve(mce, refMap, typeMap);
      if (!mi->is<P4::BuiltInMethod>()) {
        auto mceclone = mce->clone();
        auto nextargs = mceclone->arguments->clone();
        nextargs->push_back(new IR::Argument(asg->left));
        mceclone->arguments = nextargs;
        return new IR::MethodCallStatement(mceclone);
      }
    }
    return asg;
  }

  const IR::Node *postorder(IR::MethodCallStatement *mcs) override {
    auto mi = P4::MethodInstance::resolve(mcs->methodCall, refMap, typeMap);
    if (!mi->is<P4::BuiltInMethod>() && mi->actualMethodType->returnType &&
        !mi->actualMethodType->returnType->is<IR::Type_Void>()) {
      auto decl = new IR::Declaration_Variable(
          refMap->newName("ret__"), mi->originalMethodType->returnType);
      auto mceclone = mcs->methodCall->clone();
      auto args = mceclone->arguments->clone();
      args->push_back(new IR::Argument(new IR::PathExpression(decl->name)));
      mceclone->arguments = args;
      mcs->methodCall = mceclone;
      return new IR::BlockStatement({decl, mcs});
    }
    return mcs;
  }

  const IR::Node *postorder(IR::Method *m) override {
    auto tmb =
        typeMap->getType(getOriginal<IR::Method>())->to<IR::Type_MethodBase>();
    m->type = getMethod(tmb, m->type);
    return m;
  }

  const IR::Type_Method *getMethod(const IR::Type_MethodBase *tmb,
                                   const IR::Type_Method *newmt) const {
    if (tmb->returnType != nullptr && !tmb->returnType->is<IR::Type_Void>()) {
      auto nxtmt = newmt->clone();
      auto newparm =
          new IR::Parameter("ret_", IR::Direction::Out, newmt->returnType);
      auto newparms = newmt->parameters->clone();
      newparms->push_back(newparm);
      nxtmt->returnType = IR::Type_Void::get();
      nxtmt->parameters = newparms;
      newmt = nxtmt;
    }
    return newmt;
  }

  const IR::Node *postorder(IR::Function *fun) override {
    auto tmb = typeMap->getType(getOriginal<IR::Function>())
                   ->to<IR::Type_MethodBase>();
    fun->type = getMethod(tmb, fun->type);
    return fun;
  }
  const IR::Node *postorder(IR::ReturnStatement *ret) override {
    auto functx = findContext<IR::Function>();
    if (functx && ret->expression) {
      return new IR::IndexedVector<IR::StatOrDecl>(
          {new IR::AssignmentStatement(new IR::PathExpression("ret_"),
                                       ret->expression),
           new IR::ReturnStatement(nullptr)});
    }
    return ret;
  }
};

MoveReturnsInward::MoveReturnsInward(ReferenceMap *refMap, TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap) {
  passes.push_back(new DoMoveReturns(refMap, typeMap));
  addPasses({new P4::ClearTypeMap(typeMap), new P4::ResolveReferences(refMap),
             new P4::TypeInference(refMap, typeMap, false)});
}

class DoPacketExtract : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

  const IR::Node *postorder(IR::MethodCallStatement *mcs) override {
    auto orig = getOriginal<IR::MethodCallStatement>();
    auto mi = P4::MethodInstance::resolve(orig, refMap, typeMap);
    if (auto em = mi->to<P4::ExternMethod>()) {
      auto &instance = analysis::AnalysisLibrary::instance;
      if (em->actualExternType->name == instance.mutablePacket.name) {
        if (em->method->name == instance.mutablePacket.extract.name ||
            em->method->name == instance.mutablePacket.emit.name) {
          bool is_emit = em->method->name == instance.mutablePacket.emit.name;
          auto at = mi->expr->arguments->size() - 1;
          auto arg = mi->expr->arguments->at(at)->expression;
          auto argtype = typeMap->getType(arg);
          if (auto strt = argtype->to<IR::Type_Struct>()) {
            auto ishdr = (strt->getAnnotation(instance.headerAnnotation.name) !=
                          nullptr);
            auto isvalid = new IR::Member(arg, "valid_");
            auto mkvalid =
                new IR::AssignmentStatement(isvalid, new IR::BoolLiteral(true));
            auto ivec = new IR::IndexedVector<IR::StatOrDecl>();
            if (ishdr && !is_emit)
              ivec->push_back(mkvalid);
            for (auto sf : strt->fields) {
              if (ishdr && sf->name.name == "valid_")
                continue;
              auto newcall = mcs->methodCall->clone();
              if (!newcall->typeArguments->empty()) {
                newcall->typeArguments = new IR::Vector<IR::Type>();
              }
              newcall->method = newcall->method->clone();
              auto newargs = newcall->arguments->clone();
              newargs->at(at) = new IR::Argument(new IR::Member(arg, sf->name));
              newcall->arguments = newargs;
              auto newmcs = mcs->clone();
              newmcs->methodCall = newcall;
              ivec->push_back(newmcs);
            }
            if (is_emit && ishdr) {
              return new IR::IfStatement(
                  isvalid, new IR::BlockStatement(std::move(*ivec)), nullptr);
            }
            return ivec;
          }
        }
      }
    }
    return mcs;
  }

public:
  DoPacketExtract(ReferenceMap *refMap, TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}
};

PacketExtract::PacketExtract(ReferenceMap *refMap, TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap) {
  passes.push_back(new DoPacketExtract(refMap, typeMap));
  passes.push_back(new P4::BindTypeVariables(refMap, typeMap));
  addPasses({new P4::ClearTypeMap(typeMap), new P4::ResolveReferences(refMap),
             new P4::TypeInference(refMap, typeMap, false)});
}

class DoRenameParameters : public Inspector {
  P4::ReferenceMap *refMap;
  RenameMap *renameMap;

public:
  DoRenameParameters(ReferenceMap *refMap, RenameMap *renameMap)
      : refMap(refMap), renameMap(renameMap) {}

private:
  bool preorder(const IR::Method *) override { return false; }
  bool preorder(const IR::Type_Control *) override {
    return findContext<IR::P4Control>() != nullptr;
  }
  bool preorder(const IR::Type_Parser *) override {
    return findContext<IR::P4Parser>() != nullptr;
  }
  bool preorder(const IR::Type_Package *) override { return false; }
  bool preorder(const IR::P4Action *) override { return false; }
  void postorder(const IR::Parameter *parameter) override {
    auto name = parameter->name.name;
    if (auto prsctx = findContext<IR::P4Parser>()) {
      name = name + "_" + prsctx->name.name;
    } else if (auto ctrlctx = findContext<IR::P4Control>()) {
      name = name + "_" + ctrlctx->name.name;
    } else if (auto functx = findContext<IR::Function>()) {
      name = name + "_" + functx->name.name;
    }
    renameMap->setNewName(parameter, refMap->newName(name));
  }
  void postorder(const IR::Declaration_Variable *v) override {
    auto name = v->name.name;
    if (auto prsctx = findContext<IR::P4Parser>()) {
      name = name + "_" + prsctx->name.name;
    } else if (auto ctrlctx = findContext<IR::P4Control>()) {
      name = name + "_" + ctrlctx->name.name;
    } else if (auto functx = findContext<IR::Function>()) {
      name = name + "_" + functx->name.name;
    }
    renameMap->setNewName(v, refMap->newName(name));
  }
};

class FixMethodImpls : public Transform {
  const IR::Node *postorder(IR::Method *m) override {
    auto im = m->getAnnotation("impl");
    if (im != nullptr) {
      auto funname = im->expr.operator[](0)->to<IR::StringLiteral>()->value;
      auto prog = findOrigCtxt<IR::P4Program>();
      auto funnode = *prog->getDeclsByName(funname)->begin();
      auto function = funnode->to<IR::Function>();
      CHECK_NULL(function);
      auto funparams = function->getParameters();
      auto mettype = m->type->clone();
      auto parclone = new IR::ParameterList();
      BUG_CHECK(mettype->parameters->size() == funparams->size(),
                "method %1% and its implementation must have same arity", m);
      unsigned idx = 0;
      for (auto funparm : *funparams) {
        auto mparm = mettype->parameters->parameters.at(idx)->clone();
        mparm->name = IR::ID(mparm->name.srcInfo, funparm->name.name);
        parclone->push_back(mparm);
        ++idx;
      }
      mettype->parameters = parclone;
      m->type = mettype;
    }
    return m;
  }
};
class RmOriginals : public Transform {
  const IR::Node *postorder(IR::PathExpression *p) override {
    if (p->path->name.originalName != nullptr &&
        p->path->name.name != p->path->name.originalName)
      return new IR::PathExpression(
          IR::ID(p->path->name.srcInfo, p->path->name));
    return p;
  }
};

RenameParameters::RenameParameters(P4::ReferenceMap *refMap,
                                   P4::TypeMap *typeMap)
    : refMap(refMap) {
  passes.push_back(new DoRenameParameters(refMap, &renameMap));
  passes.push_back(new RenameSymbols(refMap, &renameMap, true));
  passes.push_back(new RmOriginals);
  passes.push_back(new FixMethodImpls);
  addPasses({new P4::ClearTypeMap(typeMap), new P4::ResolveReferences(refMap),
             new P4::TypeInference(refMap, typeMap, false)});
}

class DoMaterializeConstants : public Transform {
  P4::ReferenceMap *refMap;

public:
  DoMaterializeConstants(ReferenceMap *refMap) : refMap(refMap) {}

private:
  const IR::Node *postorder(IR::PathExpression *e) override {
    auto decl = refMap->getDeclaration(e->path);
    if (decl->is<IR::Declaration_Constant>()) {
      auto constdecl = decl->to<IR::Declaration_Constant>();
      return constdecl->initializer;
    }
    return e;
  }
};

MaterializeConstants::MaterializeConstants(ReferenceMap *refMap,
                                           TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap) {
  passes.push_back(new DoMaterializeConstants(refMap));
  addPasses({new P4::ClearTypeMap(typeMap), new P4::ResolveReferences(refMap),
             new P4::TypeInference(refMap, typeMap, false)});
}

class DoSplitInouts : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

public:
  DoSplitInouts(ReferenceMap *refMap, TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}

private:
  const IR::Node *postorder(IR::Method *m) override {
    if (m->getAnnotation("impl"))
      return m;
    auto parmlist = new IR::ParameterList();
    for (auto parm : m->type->parameters->parameters) {
      if (parm->direction == IR::Direction::InOut) {
        auto newparmIN = parm->clone();
        newparmIN->direction = IR::Direction::In;
        parmlist->push_back(newparmIN);
        auto newparmOUT = parm->clone();
        newparmOUT->direction = IR::Direction::Out;
        newparmOUT->name =
            IR::ID(newparmOUT->srcInfo, newparmOUT->name + "_out");
        parmlist->push_back(newparmOUT);
      } else {
        parmlist->push_back(parm);
      }
    }
    auto mtclone = m->type->clone();
    mtclone->parameters = parmlist;
    m->type = mtclone;
    return m;
  }
  const IR::Node *postorder(IR::MethodCallExpression *mce) override {
    auto mi = P4::MethodInstance::resolve(
        getOriginal<IR::MethodCallExpression>(), refMap, typeMap);
    if (mi->is<P4::ExternFunction>() || mi->is<P4::ExternMethod>()) {
      const IR::Method *theMethod;
      if (auto ef = mi->to<P4::ExternFunction>()) {
        theMethod = ef->method;
      } else if (auto em = mi->to<P4::ExternMethod>()) {
        theMethod = em->method;
      }
      if (theMethod->getAnnotation("impl")) {
        return mce;
      }
      auto arglist = new IR::Vector<IR::Argument>();
      for (auto parm : mi->getActualParameters()->parameters) {
        auto arg = mi->substitution.lookupByName(parm->name);
        if (parm->direction == IR::Direction::InOut) {
          auto argin = arg->clone();
          auto argou = arg->clone();
          arglist->push_back(argin);
          arglist->push_back(argou);
        } else {
          arglist->push_back(arg);
        }
      }
      mce->arguments = arglist;
    }
    return mce;
  }
};

SplitInouts::SplitInouts(ReferenceMap *refMap, TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap) {
  passes.push_back(new DoSplitInouts(refMap, typeMap));
  addPasses({new P4::ClearTypeMap(typeMap), new P4::ResolveReferences(refMap),
             new P4::TypeInference(refMap, typeMap, false)});
}

class DoDisentangleExternParams : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

public:
  DoDisentangleExternParams(ReferenceMap *refMap, TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}

private:
  const IR::Node *preorder(IR::Method *m) override {
    prune();
    auto plist = new IR::ParameterList();
    bool any = false;
    if (m->getAnnotation("impl"))
      return m;
    for (auto p : m->type->parameters->parameters) {
      auto parmType = typeMap->getType(p);
      std::vector<std::pair<cstring, const IR::Type *>> basics;
      auto flatten = [](const std::vector<cstring> &names) {
        cstring base = cstring::empty;
        for (auto &n : names) {
          base += ("__" + n);
        }
        return base;
      };
      if (parmType->is<IR::Type_Struct>()) {
        any = true;
        std::function<void(const IR::Type *, std::vector<cstring> &)> allTypes;
        allTypes = [&](const IR::Type *t, std::vector<cstring> &stack) {
          if (t->is<IR::Type_StructLike>()) {
            auto sl = t->to<IR::Type_StructLike>();
            for (auto fld : sl->fields) {
              stack.push_back(fld->name);
              allTypes(typeMap->getType(fld), stack);
              stack.pop_back();
            }
          } else {
            if (t->is<IR::Type_Declaration>()) {
              t = new IR::Type_Name(t->to<IR::Type_Declaration>()->name);
            }
            basics.emplace_back(flatten(stack), t);
          }
        };
        std::vector<cstring> stk({p->name.name});
        allTypes(parmType, stk);
        for (auto &basic : basics) {
          auto parm = new IR::Parameter(p->srcInfo,
                                        IR::ID(p->name.srcInfo, basic.first),
                                        p->direction, basic.second);
          plist->push_back(parm);
        }
      } else {
        plist->push_back(p);
      }
    }
    if (!any)
      return m;
    auto newmt = m->type->clone();
    newmt->parameters = plist;
    m->type = newmt;
    return m;
  }

  const IR::Node *preorder(IR::MethodCallExpression *mce) override {
    prune();
    auto mi = P4::MethodInstance::resolve(
        getOriginal<IR::MethodCallExpression>(), refMap, typeMap);
    const IR::Method *m = nullptr;
    if (auto ef = mi->to<P4::ExternMethod>())
      m = ef->method;
    else if (auto em = mi->to<P4::ExternFunction>())
      m = em->method;
    if (!m || m->getAnnotation("impl"))
      return mce;
    bool any = false;
    auto args = new IR::Vector<IR::Argument>();
    for (auto p : mi->getOriginalParameters()->parameters) {
      auto parmType = typeMap->getType(p);
      auto arg = mi->substitution.lookupByName(p->name);
      if (parmType->is<IR::Type_Struct>()) {
        any = true;
        std::function<void(const IR::Type *, std::vector<cstring> &)> allTypes;
        allTypes = [&](const IR::Type *t, std::vector<cstring> &stack) {
          if (t->is<IR::Type_StructLike>()) {
            auto sl = t->to<IR::Type_StructLike>();
            for (auto fld : sl->fields) {
              stack.push_back(fld->name);
              allTypes(typeMap->getType(fld), stack);
              stack.pop_back();
            }
          } else {
            auto crte = arg->expression;
            for (auto &mem : stack) {
              crte = new IR::Member(arg->expression->srcInfo, crte, mem);
            }
            args->push_back(new IR::Argument(crte));
          }
        };
        std::vector<cstring> stk;
        allTypes(parmType, stk);
      } else {
        args->push_back(arg);
      }
    }
    if (!any)
      return mce;
    mce->arguments = args;
    return mce;
  }
};

class SpecializeExterns2 : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  std::map<const IR::Node *, std::vector<const IR::Node *>> add_after;

public:
  SpecializeExterns2(ReferenceMap *refMap, TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}

private:
  const IR::Node *postorder(IR::P4Program *prog) override {
    for (const auto &x : add_after) {
      auto I = std::find(prog->objects.begin(), prog->objects.end(), x.first);
      BUG_CHECK(I != prog->objects.end(), "not found %1%", x.first);
      prog->objects.insert(++I, x.second.begin(), x.second.end());
    }
    return prog;
  }
  const IR::Node *postorder(IR::Declaration_Instance *i) override {
    auto orig = getOriginal<IR::Declaration_Instance>();
    auto mi = P4::Instantiation::resolve(orig, refMap, typeMap);
    if (auto em = mi->to<P4::ExternInstantiation>()) {
      auto et = typeMap->getType(orig);
      if (em->type != et) {
        LOG4("need specialization for " << i << " of type " << et);
        TypeVariableSubstitution typeVariableSubstitution;
        auto prog = findOrigCtxt<IR::P4Program>();
        auto decs = prog->getDeclsByName(em->type->name.name)->toVector();
        BUG_CHECK(decs->size() == 1, "one extern per name, got %1% for %2%",
                  decs->size(), em->type->name.name);
        auto text = decs->at(0)->to<IR::Type_Extern>();
        CHECK_NULL(text);
        unsigned idx = 0;
        for (auto ta : *em->typeArguments) {
          typeVariableSubstitution.setBinding(
              text->typeParameters->parameters.at(idx), ta);
          ++idx;
        }
        P4::SubstituteParameters substituteParameters(
            refMap, new ParameterSubstitution(), &typeVariableSubstitution);
        auto modified =
            text->apply(substituteParameters)->to<IR::Type_Extern>()->clone();
        auto oldname = modified->name;
        modified->name = IR::ID(text->srcInfo, refMap->newName(modified->name));
        auto constructors = modified->getDeclsByName(modified->name);
        for (auto &cons : modified->methods) {
          if (cons->name.name == oldname) {
            auto cl = cons->clone();
            cl->name = IR::ID(cl->srcInfo, modified->name);
            cons = cl;
          }
        }
        add_after[text].push_back(modified);
        i->type = new IR::Type_Name(IR::ID(i->srcInfo, modified->name.name));
      } else {
        LOG4("no need for specialization for " << i);
      }
    }
    return i;
  }
};
class SpecializeMethods2 : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  std::map<const IR::Node *, std::vector<const IR::Node *>> add_after;

public:
  SpecializeMethods2(ReferenceMap *refMap, TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}

private:
  const IR::Node *postorder(IR::P4Program *prog) override {
    for (const auto &x : add_after) {
      auto I = std::find(prog->objects.begin(), prog->objects.end(), x.first);
      BUG_CHECK(I != prog->objects.end(), "not found %1%", x.first);
      prog->objects.insert(++I, x.second.begin(), x.second.end());
    }
    return prog;
  }
  const IR::Node *postorder(IR::MethodCallExpression *e) override {
    auto orig = getOriginal<IR::MethodCallExpression>();
    auto mi = P4::MethodInstance::resolve(orig, refMap, typeMap);
    if (auto em = mi->to<P4::ExternMethod>()) {
      auto et = typeMap->getType(orig);
      if (em->actualMethodType != em->originalMethodType) {
        LOG4("need to specialize for " << e);
      } else {
        LOG4("no need for specialization for " << e);
      }
    }
    return e;
  }
};

DisentangleExternParams::DisentangleExternParams(ReferenceMap *refMap,
                                                 TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap) {
  passes.push_back(new SpecializeExterns2(refMap, typeMap));
  addPasses({new P4::ClearTypeMap(typeMap), new P4::ResolveReferences(refMap),
             new P4::TypeInference(refMap, typeMap, false)});
  passes.push_back(new SpecializeMethods2(refMap, typeMap));
  passes.push_back(new DoDisentangleExternParams(refMap, typeMap));
  addPasses({new P4::ClearTypeMap(typeMap), new P4::ResolveReferences(refMap),
             new P4::TypeInference(refMap, typeMap, false)});
}

RenameImplParameters::RenameImplParameters(P4::ReferenceMap *refMap,
                                           P4::TypeMap *typeMap) {
  addPasses({new FixMethodImpls, new P4::ClearTypeMap(typeMap),
             new P4::ResolveReferences(refMap),
             new P4::TypeInference(refMap, typeMap, false)});
}

class MakeValueSetFunction : public Transform {
  const IR::Node *postorder(IR::P4ValueSet *vs) {
    vs->externalName("");
  }
};

HandleValueSets::HandleValueSets(ReferenceMap *refMap, TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap) {}
}