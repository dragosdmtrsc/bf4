//
// Created by dragos on 07.05.2019.
//

#include "InstantiatePackageModels.h"
#include <p4/parseAnnotations.h>

namespace analysis {
class GatherPackageModels : public Inspector {
  P4::ReferenceMap *refMap;
  std::map<const IR::Type_Package *, const IR::P4PackageModel *>
      *implementation;

public:
  GatherPackageModels(P4::ReferenceMap *refMap,
                      std::map<const IR::Type_Package *,
                               const IR::P4PackageModel *> *implementation)
      : refMap(refMap), implementation(implementation) {}

  void postorder(const IR::P4PackageModel *model) override {
    auto nm = model->getAnnotation("model");
    if (nm) {
      auto expr = nm->expr[0]->to<IR::StringLiteral>();
      auto top = findContext<IR::P4Program>();
      auto byname = top->getDeclsByName(expr->value);
      auto b = *byname->begin();
      if (auto packtype = b->to<IR::Type_Package>()) {
        (*implementation)[packtype] = model;
        LOG4("found implementation for " << packtype << " = " << model);
      }
    }
  }
};

class FindMissingPackages : public Inspector {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  std::map<const IR::Type_Package *, const IR::P4PackageModel *>
      *implementation;

public:
  FindMissingPackages(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                      std::map<const IR::Type_Package *,
                               const IR::P4PackageModel *> *implementation)
      : refMap(refMap), typeMap(typeMap), implementation(implementation) {}

  void postorder(const IR::Type_Package *package) override {
    auto I = implementation->find(package);
    if (I == implementation->end()) {
      std::map<const IR::Type *, const IR::Parameter *> parmmapping;
      auto actualApplyParams = new IR::ParameterList();
      auto actualConstructorParams = new IR::ParameterList;
      for (auto parm : *package->constructorParams) {
        auto type = typeMap->getType(parm);
        auto baseType = type;
        if (auto specd = type->to<IR::Type_SpecializedCanonical>()) {
          baseType = specd->substituted;
        }
        auto consParm = parm->clone();
        consParm->type = baseType;
        actualConstructorParams->push_back(consParm);
        const IR::ParameterList *applyParms = nullptr;
        if (auto tc = baseType->to<IR::Type_Control>()) {
          applyParms = tc->applyParams;
        } else if (auto tp = baseType->to<IR::Type_Parser>()) {
          applyParms = tp->applyParams;
        } else if (auto tpack = baseType->to<IR::Type_Package>()) {
          auto pack = (*implementation)[tpack];
          CHECK_NULL(pack);
          applyParms = pack->type->applyParams;
        } else {
          BUG("can't handle type %1%", baseType);
        }
        for (auto p : *applyParms) {
          auto tp = typeMap->getTypeType(p->type, false);
          auto ins = parmmapping.emplace(tp, p);
          if (ins.first->second->direction != p->direction) {
            auto cl = ins.first->second->clone();
            if (ins.first->second->direction == IR::Direction::In &&
                (p->direction == IR::Direction::Out ||
                 p->direction == IR::Direction::InOut)) {
              cl->direction = IR::Direction::InOut;
            } else {
              // TODO: add proper logic here
              cl->direction = IR::Direction::InOut;
            }
            ins.first->second = cl;
          }
          if (ins.second) {
            actualApplyParams->push_back(ins.first->second);
          }
        }
      }
      auto typeControl =
          new IR::Type_Control(package->srcInfo, package->name,
                               package->typeParameters, actualApplyParams);
      auto packModel = new IR::P4PackageModel(
          package->srcInfo, package->name, typeControl, actualConstructorParams,
          new IR::BlockStatement());
      (*implementation)[package] = packModel;
    }
  }
};

class MakeInstances : public Inspector {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  std::map<const IR::Type_Package *, const IR::P4PackageModel *>
      *implementation;

public:
  MakeInstances(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                std::map<const IR::Type_Package *, const IR::P4PackageModel *>
                    *implementation)
      : refMap(refMap), typeMap(typeMap), implementation(implementation) {}
};

class ResolveReferencesPP : public P4::ResolveReferences {
  P4::ReferenceMap *refMap;

public:
  ResolveReferencesPP(P4::ReferenceMap *refMap)
      : P4::ResolveReferences(refMap), refMap(refMap) {}

  bool preorder(const IR::P4PackageModel *model) override {
    refMap->usedName(model->name.name);
    addToContext(model->getTypeParameters());
    addToContext(model->getApplyParameters());
    addToContext(model->getConstructorParameters());
    addToContext(model); // add the locals
    visit(model->type);
    visit(model->constructorParams);
    visit(model->controlLocals);
    visit(model->body);
    removeFromContext(model);
    removeFromContext(model->getConstructorParameters());
    removeFromContext(model->getApplyParameters());
    removeFromContext(model->getTypeParameters());
    return false;
  }
};

class TypeInferencePP : public P4::TypeInference {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

public:
  TypeInferencePP(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
      : P4::TypeInference(refMap, typeMap, false), refMap(refMap),
        typeMap(typeMap) {}
  const IR::Node* postorder(IR::Declaration_Variable* decl) override {
    if (done())
      return decl;
    auto type = getTypeType(decl->type);
    if (type == nullptr)
      return decl;

    if (type->is<IR::IMayBeGenericType>()) {
      // Check that there are no unbound type parameters
      const IR::IMayBeGenericType* gt = type->to<IR::IMayBeGenericType>();
      if (!gt->getTypeParameters()->empty()) {
        typeError("Unspecified type parameters for %1% in %2%", gt, decl);
        return decl;
      }
    }

    if (type->is<IR::Type_SpecializedCanonical>())
      type = type->to<IR::Type_SpecializedCanonical>()->baseType;

    auto orig = getOriginal<IR::Declaration_Variable>();
    if (decl->initializer != nullptr) {
      auto init = assignment(decl, type, decl->initializer);
      if (decl->initializer != init) {
        decl->type = type;
        decl->initializer = init;
        LOG2("Created new declaration " << decl);
      }
    }
    setType(decl, type);
    setType(orig, type);
    return decl;
  }
  const IR::Node *preorder(IR::P4PackageModel *model) override {
    visit(model->type);
    visit(model->constructorParams);
    visit(model->controlLocals);
    visit(model->body);
    return model;
  }
};

class FixModelAnnotation : public Transform {
  P4::ReferenceMap *refMap;

public:
  FixModelAnnotation(P4::ReferenceMap *refMap) : refMap(refMap) {}
  const IR::Node *postorder(IR::P4PackageModel *model) override {
    P4::ParseAnnotations::HandlerMap handlers = {PARSE("model", StringLiteral)};
    P4::ParseAnnotations pe("analysis", true, handlers, true);
    auto annots = model->type->annotations->apply(pe)->to<IR::Annotations>();
    model->annotations = annots;
    LOG4("fixed annotations " << model->annotations);
    return model;
  }
};
}

analysis::InstantiatePackageModels::InstantiatePackageModels(
    P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
    P4::EvaluatorPass *evaluator)
    : refMap(refMap), typeMap(typeMap), evaluator(evaluator) {
  passes.push_back(evaluator);
  passes.push_back(new FixModelAnnotation(refMap));
  passes.push_back(new GatherPackageModels(
      refMap,
      new std::map<const IR::Type_Package *, const IR::P4PackageModel *>()));
  passes.push_back(
      new VisitFunctor([this]() { this->evaluator->getToplevelBlock(); }));
}
