//
// Created by dragos on 20.04.2019.
//

#include <p4/methodInstance.h>
#include <common/resolveReferences/resolveReferences.h>
#include <p4/typeChecking/typeChecker.h>
#include "RemoveBuiltins.h"

namespace analysis {
class FindBuiltins : public Inspector {
  BuiltinRegistrar *builtinRegistrar;
public:
  FindBuiltins(BuiltinRegistrar *builtinRegistrar)
      : builtinRegistrar(builtinRegistrar) {}

  void postorder(const IR::MethodCallExpression *mce) override {
    auto crt = getChildContext();
    auto parent = crt->parent;
    while (!parent->node->is<IR::P4Program>()) {
      crt = crt->parent;
      parent = crt->parent;
    }
    builtinRegistrar->add(mce, crt->node);
  }
};

class ReplaceBuiltins : public Transform {
  BuiltinRegistrar *registrar;
public:
  ReplaceBuiltins(BuiltinRegistrar *registrar) : registrar(registrar) {}
  const IR::Node *postorder(IR::MethodCallExpression *mce) override {
    auto orig = getOriginal<IR::MethodCallExpression>();
    auto repl = registrar->reverseInstances.find(orig);
    if (repl != registrar->reverseInstances.end()) {
      auto bim = P4::MethodInstance::resolve(orig, registrar->refMap,
                                             registrar->typeMap)
                     ->to<P4::BuiltInMethod>();
      auto pe = new IR::PathExpression(repl->second->name);
      auto args = new IR::Vector<IR::Argument>();
      args->push_back(new IR::Argument(bim->appliedTo));
      args->insert(args->end(), mce->arguments->begin(), mce->arguments->end());
      return new IR::MethodCallExpression(mce->srcInfo, pe, args);
    }
    return mce;
  }
};

class DeclareBuiltins : public Transform {
  BuiltinRegistrar *registrar;
public:
  DeclareBuiltins(BuiltinRegistrar *registrar) : registrar(registrar) {}

  const IR::Node *preorder(IR::P4Program *program) override {
    std::map<const IR::Method *, unsigned > alreadyDeclared;
    unsigned i = 0;
    for (auto I = program->objects.begin(); I != program->objects.end(); ++I) {
      auto J = registrar->insertionPoints.find(*I);
      if (J != registrar->insertionPoints.end()) {
        for (auto m : J->second) {
          alreadyDeclared.emplace(m, i);
        }
      }
      ++i;
    }
    for (auto &p : alreadyDeclared) {
      program->objects.insert(program->objects.begin() + p.second, p.first);
    }
    prune();
    return program;
  }
};

void BuiltinRegistrar::add(const IR::MethodCallExpression *mce,
                           const IR::Node *addBefore) {
  auto mi = P4::MethodInstance::resolve(mce, refMap, typeMap);
  if (auto bim = mi->to<P4::BuiltInMethod>()) {
    LOG4("builtin found: " << mce);
    auto appliedTo = typeMap->getType(bim->appliedTo);
    auto &appd = methods[appliedTo];
    auto maybeI = appd.emplace(bim->name, nullptr);
    if (maybeI.second) {
      auto oldmethod = bim->actualMethodType;
      auto parmList = new IR::ParameterList();
      auto dir = IR::Direction::InOut;
      if (bim->name == IR::Type_Header::isValid)
        dir = IR::Direction::In;
      parmList->push_back(new IR::Parameter("self", dir, appliedTo));
      for (auto p : *oldmethod->parameters) {
        parmList->push_back(p);
      }
      auto method = new IR::Type_Method(oldmethod->returnType, parmList);
      auto methodName = refMap->newName(bim->name);
      auto met = new IR::Method(methodName, method);
      maybeI.first->second = met;
      met->annotations = met->annotations->addAnnotation(bim->name, nullptr);
      LOG4("making method " << maybeI.first->second);
    }
    BUG_CHECK(appd[bim->name] != nullptr, "why is this happening?");
    LOG4("gonna insert method " << maybeI.first->second << " right before " << addBefore);
    insertionPoints[addBefore].emplace(maybeI.first->second);
    reverseInstances[mce] = maybeI.first->second;
    instances[maybeI.first->second].emplace(mce);
  }
}

BuiltinRegistrar::BuiltinRegistrar(P4::ReferenceMap *refMap,
                                   P4::TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap) {}
}

analysis::RemoveBuiltins::RemoveBuiltins(P4::ReferenceMap *refMap,
                                         P4::TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap), builtinRegistrar(refMap, typeMap) {
  setName("MidEnd_bins");
  passes.push_back(new FindBuiltins(&builtinRegistrar));
  passes.push_back(new DeclareBuiltins(&builtinRegistrar));
  passes.push_back(new ReplaceBuiltins(&builtinRegistrar));
  addPasses({
              new P4::ClearTypeMap(typeMap),
              new P4::ResolveReferences(refMap),
              new P4::TypeInference(refMap, typeMap, false),
              new P4::ApplyTypesToExpressions(typeMap),
              new P4::ResolveReferences(refMap)
            });
}
