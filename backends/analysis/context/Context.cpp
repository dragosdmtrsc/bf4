//
// Created by dragos on 08.07.2019.
//

#include "Context.h"
#include <analysis/vTypeChecker.h>
#include <p4/typeChecking/typeChecker.h>

namespace analysis {

class RelinkReferences : public Transform {
  const IR::P4Program *program; // input: TBD is it necessary?
  analysis::Context *ctx;       // input/output: writes actual node
  // assumes type variables are populated,
  P4::ReferenceMap *refMap; // input/output: resolves new references
  P4::TypeMap *typeMap;     // input/output: resolves new Nodes to types
  std::unordered_map<const IR::Node *, const IR::Node *> &modified;
  std::unordered_map<const IR::Node *, const IR::Node *> &revmodified;
  std::set<const IR::Node *> visited;

public:
  RelinkReferences(
      const IR::P4Program *program, analysis::Context *ctx,
      P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
      std::unordered_map<const IR::Node *, const IR::Node *> &modified,
      std::unordered_map<const IR::Node *, const IR::Node *> &revmodified)
      : program(program), ctx(ctx), refMap(refMap), typeMap(typeMap),
        modified(modified), revmodified(revmodified) {}

private:
  const IR::Node *modify(const IR::Node *node) {
    return modify(getOriginal(), node);
  }
  const IR::Node *modify(const IR::Node *original, const IR::Node *final) {
    revmodified.emplace(original, final);
    return modified.emplace(final, original).first->first;
  }
  const IR::Node *apply_visitor(const IR::Node *n, const char *name) override {
    auto res = Transform::apply_visitor(n, name);
    if (res != n) {
      LOG4("modified " << dbp(n) << " -> " << dbp(res));
      return modify(n, res);
    } else {
      if (n->is<IR::P4Parser>()) {
        LOG4("parser");
      }
      LOG4("unmodified " << dbp(n));
    }
    visited.emplace(n);
    return res;
  }
  const IR::Node *postorder(IR::Type_Name *typeName) override {
    auto path = typeName->path;
    auto decl = refMap->getDeclaration(path);
    if (decl->is<IR::Type_Var>()) {
      auto tv = decl->to<IR::Type_Var>();
      auto actual = ctx->substitutions.find(tv);
      BUG_CHECK(actual != ctx->substitutions.end(),
                "couldn't map type var %1% to type", tv);
      if (actual->second->is<IR::Type_Declaration>()) {
        // means: a user-defined type, do relink
        auto newpath = typeName->path->clone();
        newpath->name.name =
            actual->second->to<IR::Type_Declaration>()->name.name;
        newpath->name.originalName =
            actual->second->to<IR::Type_Declaration>()->name.originalName;
        auto tnclone = new IR::Type_Name(newpath);
        refMap->setDeclaration(tnclone->path,
                               actual->second->to<IR::Type_Declaration>());
        auto tt = new IR::Type_Type(actual->second);
        typeMap->setType(tnclone, tt);
        LOG4("changing type " << typeName << " to " << actual->second);
        return tnclone;
      } else {
        // means: a base type, no fuss
        return actual->second;
      }
    }
    return typeName;
  }
  const IR::Node *postorder(IR::Type_Var *tv) override {
    if (ctx->substitutions.count(getOriginal<IR::Type_Var>())) {
      return nullptr;
    }
    //    BUG("can't reach this point: no instance for %1%", tv);
    return tv;
  }

  const IR::Node *postorder(IR::PathExpression *pe) override {
    auto path = pe->path;
    auto decl = refMap->getDeclaration(path);
    auto instanceI = ctx->compileTimeValues.find(decl);
    if (instanceI != ctx->compileTimeValues.end()) {
      auto instantiation = instanceI->second;
      LOG4("for path expression " << pe << " found instance "
                                  << instantiation->instance);
      const IR::IDeclaration *bind = instantiation->instance;
      return deepClone(path, bind);
    }
    if (decl->is<IR::Parameter>() && !visited.count(decl->getNode())) {
      BUG("%1% refers a parameter not part of the current syntactic object %2%",
          pe, decl);
    }
    auto newPointer = revmodified.find(decl->getNode());
    if (newPointer != revmodified.end()) {
      auto maybestate = findContext<IR::ParserState>();
      LOG2("declaration changed "
           << dbp(newPointer->second->to<IR::IDeclaration>()->getNode())
           << " need to change " << dbp(pe) << "@" << dbp(maybestate));
      return deepClone(path, newPointer->second->to<IR::IDeclaration>());
    }
    return pe;
  }

  IR::PathExpression *deepClone(const IR::Path *path,
                                const IR::IDeclaration *bind) const {
    auto clone = new IR::PathExpression(path->clone()->to<IR::Path>());
    if (bind->is<IR::ParserState>()) {
      // refuse binding for this one, need to find a good mechanism
      // to avoid never reaching a fixed point
      bind = nullptr;
    }
    if (bind) {
      refMap->setDeclaration(clone->path, bind);
      LOG4("rebinding " << dbp(clone->path) << " to " << dbp(bind));
    }
    return clone;
  }
  profile_t init_apply(const IR::Node *r) override {
    LOG2("restarting");
    return Transform::init_apply(r);
  }
};

class FixDanglingParserStates : public Inspector {
  P4::ReferenceMap *refMap;
  std::unordered_map<const IR::Node *, const IR::Node *> &revmodified;
  std::unordered_map<const IR::Node *, const IR::Node *> &modified;

public:
  FixDanglingParserStates(
      ReferenceMap *refMap,
      std::unordered_map<const IR::Node *, const IR::Node *> &revmodified,
      std::unordered_map<const IR::Node *, const IR::Node *> &modified)
      : refMap(refMap), revmodified(revmodified), modified(modified) {}

  bool preorder(const IR::PathExpression *pe) override {
    auto Im = modified.find(pe);
    if (Im != modified.end()) {
      auto old = Im->second;
      if (old->is<IR::PathExpression>()) {
        auto oldref =
            refMap->getDeclaration(old->to<IR::PathExpression>()->path);
        if (oldref->is<IR::ParserState>()) {
          auto crt = refMap->getDeclaration(pe->path);
          if (!crt) {
            auto parser = findContext<IR::P4Parser>();
            auto st = parser->states.getDeclaration(pe->path->name);
            LOG4("fixing " << dbp(pe) << " to " << dbp(st));
            refMap->setDeclaration(pe->path, st);
          }
        }
      }
    }
    return false;
  }
};

class RelinkTypes : public Inspector {
  const IR::P4Program *program; // input: TBD is it necessary?
  analysis::Context *ctx;       // input/output: writes actual node
  // assumes type variables are populated,
  P4::ReferenceMap *refMap; // input/output: resolves new references
  P4::TypeMap *typeMap;     // input/output: resolves new Nodes to types
  std::unordered_map<const IR::Node *, const IR::Node *> &modified;

public:
  RelinkTypes(const IR::P4Program *program, analysis::Context *ctx,
              P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
              std::unordered_map<const IR::Node *, const IR::Node *> &modified)
      : program(program), ctx(ctx), refMap(refMap), typeMap(typeMap),
        modified(modified) {}

private:
  bool preorder(const IR::Node *node) override {
    if (modified.count(node)) {
      // learn new types for the instantiated callable
      P4::TypeInference tc(refMap, typeMap, true);
      (void)node->apply(tc);
      return false;
    }
    return true;
  }
};

class InstantiateContext : public PassManager {
  const IR::P4Program *program; // input: TBD is it necessary?
  analysis::Context *ctx;       // input/output: writes actual node
  // assumes type variables are populated,
  P4::ReferenceMap *refMap; // input/output: resolves new references
  P4::TypeMap *typeMap;     // input/output: resolves new Nodes to types
  std::unordered_map<const IR::Node *, const IR::Node *> modified;
  std::unordered_map<const IR::Node *, const IR::Node *> revmodified;

public:
  InstantiateContext(const IR::P4Program *program, analysis::Context *ctx,
                     P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
      : program(program), ctx(ctx), refMap(refMap), typeMap(typeMap) {
    passes.push_back(new PassRepeated({new PassManager(
        {new RelinkReferences(program, ctx, refMap, typeMap, modified,
                              revmodified),
         new FixDanglingParserStates(refMap, revmodified, modified)})}));
    passes.push_back(new RelinkTypes(program, ctx, refMap, typeMap, modified));
  }

  void instantiate() {
    ctx->instantiated = ctx->syntactic->getNode()->apply(*this);
    LOG4("original instance " << dbp(ctx->syntactic->getNode()));
  }
};

void BuildContextFactory::postorder(const IR::MethodCallExpression *mce) {
  auto mi = P4::MethodInstance::resolve(mce, refMap, typeMap);
  auto next = factory->makeContext(mi);
  BuildContextFactory clone(factory, refMap, typeMap);
  clone.currentContext = next;
  next->instantiated->apply(clone);
}

void BuildContextFactory::start(const IR::Function *run) {
  BUG_CHECK(run->getParameters()->empty(), "main must have no parameters");
  BUG_CHECK(run->type->typeParameters->empty(),
            "main must have no type parameters");
  auto first = new analysis::Context;
  first->syntactic = run;
  first->instantiated = run;
  currentContext = first;
  run->apply(*this);
}

BuildContextFactory::BuildContextFactory(ContextFactory *factory,
                                         P4::ReferenceMap *refMap,
                                         P4::TypeMap *typeMap)
    : factory(factory), refMap(refMap), typeMap(typeMap) {}

analysis::Context *ImplementationFactory::implement(const IR::Node *node,
                                                    analysis::Context *crt,
                                                    bool fallback) {
  if (crt->syntactic->is<IR::Method>()) {
    auto met = crt->syntactic->to<IR::Method>();
    if (node->is<IR::Function>()) {
      auto fun = node->to<IR::Function>();
      auto clone = new Context();
      clone->syntactic = node;
      auto tvinitial = met->type->getTypeParameters();
      auto tvfinal = fun->type->getTypeParameters();
      auto numTParms = tvfinal->size();
      if (tvinitial->size() != tvfinal->size()) {
        BUG("can't implement %1% via %2% can't match type params",
            crt->syntactic, node);
      }
      for (unsigned i = 0; i != numTParms; ++i) {
        auto initial = crt->substitutions[tvinitial->parameters.at(i)];
        clone->substitutions.emplace(tvfinal->parameters.at(i), initial);
      }
      auto initialParams = met->getParameters();
      auto finalParams = fun->getParameters();
      if (initialParams->size() != finalParams->size()) {
        BUG("can't implement %1% via %2% can't match params", crt->syntactic,
            node);
      }
      for (unsigned i = 0; i != finalParams->size(); ++i) {
        auto I = crt->compileTimeValues.find(initialParams->parameters.at(i));
        if (I != crt->compileTimeValues.end()) {
          LOG4("parameter " << finalParams->parameters.at(i) << " = "
                            << I->second->instance);
          auto initial = I->second;
          clone->compileTimeValues.emplace(finalParams->parameters.at(i),
                                           initial);
        }
      }
      factory->addContext(clone);
      CHECK_NULL(clone->instantiated);
      LOG4("implementing " << dbp(clone->syntactic) << " to "
                           << dbp(clone->instantiated));
      return clone;
    }
  }
  // fall back:
  if (fallback) {
    LOG4("can't do implementation... falling back");
    return crt;
  }
  BUG("can't implement %1% as %2%", node, crt->instantiated);
}

ImplementationFactory::ImplementationFactory(ContextFactory *factory)
    : factory(factory) {}

bool equivalent(const P4::Instantiation *self, const P4::Instantiation *other) {
  // TODO: deep inspection if need be. Guess is that in reality this shouldn't
  // be necessary
  if (self->instance == other->instance)
    return true;
  for (auto ctp : *self->constructorParameters) {
    auto selfarg = self->substitution.lookup(ctp)->expression;
    auto otherarg = other->substitution.lookupByName(ctp->name)->expression;
    if (selfarg == otherarg)
      continue;
    if (selfarg->is<IR::Constant>() && otherarg->is<IR::Constant>()) {
      auto selfct = selfarg->to<IR::Constant>();
      auto otherct = selfarg->to<IR::Constant>();
      if (selfct->type != otherct->type) {
        return false;
      } else {
        if (selfct->value != otherct->value) {
          return false;
        }
      }
    } else {
      return false;
    }
  }
  return true;
}
}

const IR::Node *
analysis::ContextFactory::instantiate(const P4::MethodInstance *instance) {
  auto ctx = makeContext(instance);
  return ctx->getNode();
}

analysis::Context *
analysis::ContextFactory::makeContext(const P4::MethodInstance *instance) {
  if (instance->originalMethodType == instance->actualMethodType ||
      instance->is<P4::BuiltInMethod>()) {
    // this case is simple (?)
  }
  LOG2("starting instantiation for " << instance->expr);
  std::unordered_map<const IR::Type_Var *, const IR::Type *> typeMappings;
  std::unordered_map<const IR::IDeclaration *, P4::Instantiation *>
      instantiations;
  auto actualParameters = instance->actualMethodType->parameters;
  auto originals = instance->originalMethodType->parameters;
  const IR::TypeParameters *methodTypeParameters = nullptr;
  const IR::ParameterList *methodParameterList = nullptr;
  const IR::IDeclaration *declaration = nullptr;
  const IR::Type_MethodBase *methodType = nullptr;
  const IR::IDeclaration *object = instance->object;
  if (instance->is<P4::FunctionCall>()) {
    auto fc = instance->to<P4::FunctionCall>();
    auto synt = fc->function;
    auto syntMethod = makeSyntactic(synt)->to<IR::Function>();
    methodType = syntMethod->type;
    declaration = synt;
  } else if (instance->is<P4::ExternMethod>()) {
    auto em = instance->to<P4::ExternMethod>();
    auto syntextern =
        makeSyntactic(em->actualExternType)->to<IR::Type_Extern>();
    auto synt =
        syntextern->lookupMethod(em->method->name, instance->expr->arguments);
    methodType = synt->type;
    declaration = synt;
  } else if (instance->is<P4::ApplyMethod>()) {
    auto am = instance->to<P4::ApplyMethod>();
    auto syntObj = makeSyntactic(am->applyObject->to<IR::IDeclaration>())
                       ->to<IR::IApply>();
    methodType = syntObj->getApplyMethodType();
    declaration = am->object;
  } else if (instance->is<P4::ExternFunction>()) {
    auto ef = instance->to<P4::ExternFunction>();
    auto synt = ef->method;
    auto syntMethod = makeSyntactic(synt, [&](const IR::IDeclaration *decl) {
                        return decl->to<IR::IFunctional>()->callMatches(
                            instance->expr->arguments);
                      })->to<IR::Method>();
    methodType = syntMethod->type;
    declaration = synt;
  } else if (instance->is<P4::ActionCall>()) {
    auto ac = instance->to<P4::ActionCall>();
    methodType =
        new IR::Type_Method(new IR::TypeParameters, ac->action->parameters);
    declaration = ac->action;
  } else {
    BUG("unreachable %1%", instance->expr);
  }
  methodTypeParameters = methodType->getTypeParameters();
  methodParameterList = methodType->parameters;
  typeMappings = getTypeMappings(typeMap, instance, methodTypeParameters);
  instantiations =
      getParameterInstances(refMap, typeMap, methodParameterList, originals,
                            actualParameters, instance->substitution);
  Context context;
  if (declaration->is<IR::IFunctional>() && !object) {
    context.syntactic = declaration;
  } else if (object->is<IR::Declaration_Instance>()) {
    // a method which got called against an object
    auto decl = object->to<IR::Declaration_Instance>();
    auto inst = P4::Instantiation::resolve(decl, refMap, typeMap);
    auto oldFunctional = declaration;
    if (inst->is<P4::ControlInstantiation>()) {
      auto ctrli = inst->to<P4::ControlInstantiation>();
      declaration = makeSyntactic(ctrli->control);
    } else if (inst->is<P4::ParserInstantiation>()) {
      auto parseri = inst->to<P4::ParserInstantiation>();
      declaration = makeSyntactic(parseri->parser);
    } else if (inst->is<P4::ExternInstantiation>()) {
      auto externi = inst->to<P4::ExternInstantiation>();
      declaration = makeSyntactic(externi->type);
    } else {
      BUG("unknown instantiation %1%", decl);
    }
    auto maybegeneric = declaration->to<IR::IMayBeGenericType>();
    auto I = inst->typeArguments->begin();
    for (auto tv : maybegeneric->getTypeParameters()->parameters) {
      auto subs = typeMap->getSubstitution(tv);
      if (!subs) {
        BUG_CHECK(I != inst->typeArguments->end(),
                  "can't substitute type variable %1%", tv);
        subs = typeMap->getTypeType(*I, true);
      }
      CHECK_NULL(subs);
      typeMappings.emplace(tv, subs);
      if (I != inst->typeArguments->end())
        ++I;
    }
    for (auto p : inst->constructorParameters->parameters) {
      auto arg = inst->substitution.lookup(p);
      auto path = arg->expression->to<IR::PathExpression>();
      if (!path) {
        if (arg->expression->is<IR::Member>()) {
          auto tne = arg->expression->to<IR::Member>();
          if (tne->expr->is<IR::TypeNameExpression>()) {
            continue;
          }
        }
        // do nothing, not a declaration instance, but a constant
        BUG_CHECK(
            arg->expression->is<IR::Literal>(),
            "parameter %1% not bound to a compile time constant, but to %2%", p,
            arg->expression);
      } else {
        auto ref = refMap->getDeclaration(path->path);
        auto deci = ref->to<IR::Declaration_Instance>();
        CHECK_NULL(deci);
        auto now = Instantiation::resolve(deci, refMap, typeMap);
        instantiations.emplace(p, now);
      }
    }
    // need an extra compile time value for the object against which the apply
    // or
    // extern method is called. Will be bound later
    instantiations[nullptr] = inst;
    if (oldFunctional->is<IR::IFunctional>()) {
      declaration = oldFunctional;
    }
    context.syntactic = declaration;
  } else {
    auto pathe = instance->expr->method->to<IR::Member>()
                     ->expr->to<IR::PathExpression>();
    LOG4("things went wrong for object " << dbp(object) << " from "
                                         << dbp(pathe));
    BUG("unexpected object kind %1%", object);
  }
  CHECK_NULL(declaration);
  CHECK_NULL(context.syntactic);
  context.compileTimeValues = std::move(instantiations);
  context.substitutions = std::move(typeMappings);
  auto ret = new Context(std::move(context));
  addContext(ret);
  CHECK_NULL(ret->instantiated);
  LOG2("instanceof " << dbp(ret->syntactic) << " = " << dbp(ret->instantiated));
  return ret;
}

std::unordered_map<const IR::Type_Var *, const IR::Type *>
analysis::ContextFactory::getTypeMappings(
    P4::TypeMap *typeMap, const P4::MethodInstance *fc,
    const IR::TypeParameters *syntTypeParms) const {
  std::unordered_map<const IR::Type_Var *, const IR::Type *> typeMappings;
  // type variables in synt can't ever be found by type map
  auto I = syntTypeParms->parameters.begin();
  auto mce = fc->expr;
  auto mceTypeArguments = mce->typeArguments->begin();
  for (auto tv : fc->originalMethodType->getTypeParameters()->parameters) {
    auto subs = typeMap->getSubstitution(tv);
    if (!subs) {
      BUG_CHECK(mceTypeArguments != mce->typeArguments->end(),
                "no substitution in the type map, nor type arguments");
      subs = *mceTypeArguments;
    }
    CHECK_NULL(subs);
    // is this guy canonical?
    subs = typeMap->getTypeType(subs, true);
    // inv: subs is canonical
    typeMappings.emplace(*I, subs);
    ++I;
    ++mceTypeArguments;
  }
  return typeMappings;
}

std::unordered_map<const IR::IDeclaration *, P4::Instantiation *>
analysis::ContextFactory::getParameterInstances(
    P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
    const IR::ParameterList *syntParams, const IR::ParameterList *originals,
    const IR::ParameterList *actualParameters,
    const P4::ParameterSubstitution &substitution) {
  std::unordered_map<const IR::IDeclaration *, P4::Instantiation *>
      instantiations;
  for (auto parm : originals->parameters) {
    auto syntacticParameter = syntParams->getParameter(parm->name);
    auto actualParameter = actualParameters->getParameter(parm->name);
    auto actualParameterType = typeMap->getType(actualParameter);
    // inv: actualParameterType is canonical
    if (actualParameterType->is<IR::Type_Extern>()) {
      auto arg = substitution.lookupByName(parm->name)->expression;
      BUG_CHECK(arg->is<IR::PathExpression>(), "can't handle an extern given "
                                               "by anything else other than "
                                               "a path expression, got %1%",
                arg);
      auto path = arg->to<IR::PathExpression>();
      auto decl = refMap->getDeclaration(path->path);
      LOG4("found path " << dbp(path) << " bound to " << dbp(decl)
                         << " rebinding to " << dbp(syntacticParameter));
      CHECK_NULL(decl);
      BUG_CHECK(decl->is<IR::Declaration_Instance>(),
                "need to resolve %1% to an instance, got %2%", path, decl);
      auto instantiation = P4::Instantiation::resolve(
          decl->to<IR::Declaration_Instance>(), refMap, typeMap);
      instantiations.emplace(syntacticParameter, instantiation);
    }
  }
  return instantiations;
}

void analysis::ContextFactory::addContext(analysis::Context *&context) {
  if (!context->instantiated) {
    auto crt = known_contexts.equal_range(context->syntactic);
    auto I = std::find_if(
        crt.first, crt.second,
        [context](const std::pair<const IR::INode *, Context *> &p) {
          return *p.second == *context;
        });
    if (I != crt.second) {
      LOG4("context already instantiated for " << dbp(context->syntactic));
      context = I->second;
      BUG_CHECK(context->instantiated != nullptr,
                "got from map, but no instantiation was given");
      return;
    }
    InstantiateContext instantiateContext(program, context, refMap, typeMap);
    instantiateContext.instantiate();
    known_contexts.emplace(context->syntactic, context);
  }
}

analysis::ContextFactory::ContextFactory(const IR::P4Program *program,
                                         P4::ReferenceMap *refMap,
                                         P4::TypeMap *typeMap)
    : program(program), refMap(refMap), typeMap(typeMap) {}

const IR::IDeclaration *
analysis::ContextFactory::makeSyntactic(const IR::IDeclaration *declaration) {
  return makeSyntactic(declaration,
                       [](const IR::IDeclaration *) { return true; });
}

const IR::IDeclaration *analysis::ContextFactory::makeSyntactic(
    const IR::IDeclaration *declaration,
    std::function<bool(const IR::IDeclaration *)> filter) {
  auto id = declaration->getName();
  auto synt = program->getDeclsByName(id)->where(
      [&](const IR::IDeclaration *const &v) { return filter(v); });
  CHECK_NULL(synt);
  auto I = synt->begin();
  BUG_CHECK(I != synt->end(), "no syntactic declaration %1%", declaration);
  return *I;
}
