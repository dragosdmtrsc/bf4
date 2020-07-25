//
// Created by dragos on 18.04.2019.
//

#include "ExternSpecialization.h"
#include <p4/evaluator/evaluator.h>
#include <p4/typeChecking/typeChecker.h>

void analysis::FindExternSpecializations::postorder(
    const IR::ConstructorCallExpression *cce) {
  auto tp = specializations->typeMap->getTypeType(cce->constructedType, true);
  if (auto specd = tp->to<IR::Type_SpecializedCanonical>()) {
    if (specd->substituted->is<IR::Type_Extern>()) {
      LOG4("found substitution " << cce << " of type " << specd->substituted);
      ExternSpecialization spec(specd->baseType, specd, cce);
      findContext(spec);
      specializations->specializations.emplace_back(spec);
    }
  }
}

void analysis::FindExternSpecializations::postorder(
    const IR::Declaration_Instance *decl) {
  auto tp = specializations->typeMap->getType(decl, true);
  if (auto specd = tp->to<IR::Type_SpecializedCanonical>()) {
    if (specd->substituted->is<IR::Type_Extern>()) {
      LOG4("found substitution " << decl << " of type " << specd->substituted);
      ExternSpecialization spec(specd->baseType, specd, decl);
      findContext(spec);
      specializations->specializations.emplace_back(spec);
    }
  }
}

void analysis::FindExternSpecializations::findContext(
    ExternSpecialization &spec) {
  auto crt = getChildContext();
  auto parent = crt->parent;
  while (!parent->node->is<IR::P4Program>()) {
    crt = parent;
    parent = crt->parent;
  }
  spec.justBefore = crt->node;
  LOG4("found insertion point " << spec.justBefore);
}

namespace analysis {
class DoSpecialize : public Transform {
  ExternSpecializations *specs;
  std::map<ExternSpecialization *, cstring> nameMap;

  const IR::Node *preorder(IR::P4Program *prog) override {
    for (auto &spec : specs->specializations) {
      auto I = std::find(prog->objects.begin(), prog->objects.end(),
                         spec.justBefore);
      auto decl = spec.actual;
      if (auto td = decl->baseType->to<IR::Type_Declaration>()) {
        auto newname = specs->refMap->newName(td->name);
        auto specialized = decl->substituted->to<IR::Type_Extern>()->clone();
        specialized->name = newname;
        IR::Vector<IR::Method> methods;
        for (auto method : specialized->methods) {
          if (method->name == td->name) {
            auto newmethod = method->clone();
            newmethod->name = newname;
            methods.push_back(newmethod);
          } else {
            methods.push_back(method);
          }
        }
        specialized->methods = std::move(methods);
        nameMap.emplace(&spec, newname);
        prog->objects.insert(I, specialized);
      }
    }
    return prog;
  }

  ExternSpecialization *findSpec(const IR::Node *n) {
    for (auto &spec : specs->specializations) {
      if (spec.instance == n || spec.constructor == n) {
        return &spec;
      }
    }
    return nullptr;
  }

  const IR::Node *postorder(IR::ConstructorCallExpression *cce) override {
    auto theSpec = findSpec(getOriginal());
    if (theSpec) {
      auto typeName = nameMap.find(theSpec)->second;
      cce->constructedType = new IR::Type_Name(typeName);
    }
    return cce;
  }

  const IR::Node *postorder(IR::Declaration_Instance *dec) override {
    auto theSpec = findSpec(getOriginal());
    if (theSpec) {
      auto typeName = nameMap.find(theSpec)->second;
      dec->type = new IR::Type_Name(typeName);
    }
    return dec;
  }

public:
  DoSpecialize(ExternSpecializations *specs) : specs(specs) {}
};
}

analysis::SpecializeExterns::SpecializeExterns(P4::ReferenceMap *refMap,
                                               P4::TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap), specs(refMap, typeMap) {
  setName("MidEnd_Specialize");
  passes.push_back(new FindExternSpecializations(&specs));
  passes.push_back(new DoSpecialize(&specs));
  passes.push_back(new P4::ClearTypeMap(typeMap));
  passes.push_back(new P4::TypeChecking(refMap, typeMap, true));
  passes.push_back(new P4::Evaluator(refMap, typeMap));
}
