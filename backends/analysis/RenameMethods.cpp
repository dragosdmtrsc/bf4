//
// Created by dragos on 11.06.2019.
//

#include <p4/methodInstance.h>
#include <p4/typeChecking/typeChecker.h>
#include "RenameMethods.h"

namespace analysis {
class FindMethods : public Inspector {
  P4::ReferenceMap *refMap;
  P4::RenameMap *renameMap;

public:
  FindMethods(P4::ReferenceMap *refMap, P4::RenameMap *renameMap)
      : refMap(refMap), renameMap(renameMap) {}

  void doDecl(const IR::Declaration *decl) {
    cstring newName = refMap->newName(decl->getName());
    renameMap->setNewName(decl, newName);
  }
  void postorder(const IR::Method *decl) override {
    auto text = findContext<IR::Type_Extern>();
    if (text) {
      if (decl->name == text->name) return;
    }
    doDecl(decl);
  }
  void postorder(const IR::Function *fun) override { doDecl(fun); }
};

class DoRenameMethods : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  P4::RenameMap *renameMap;
  IR::ID* getName() const {
    auto orig = getOriginal<IR::IDeclaration>();
    if (!renameMap->toRename(orig))
      return nullptr;
    auto newName = renameMap->getName(orig);
    auto name = new IR::ID(orig->getName().srcInfo, newName, orig->getName().originalName);
    return name;
  }
public:
  DoRenameMethods(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                  P4::RenameMap *renameMap)
      : refMap(refMap), typeMap(typeMap), renameMap(renameMap) {}

  const IR::Node *postorder(IR::Function *fun) override {
    if (auto newid = getName()) {
      fun->name = *newid;
    }
    return fun;
  }
  const IR::Node *postorder(IR::Method *method) override {
    if (auto newid = getName()) {
      method->name = *newid;
    }
    return method;
  }

  const IR::Node *postorder(IR::MethodCallExpression *expression) override {
    auto mi = P4::MethodInstance::resolve(getOriginal<IR::MethodCallExpression>(), refMap, typeMap);
    if (auto em = mi->to<P4::ExternMethod>()) {
      if (renameMap->toRename(em->method)) {
        auto rename = renameMap->getName(em->method);
        auto mem = expression->method->to<IR::Member>()->clone();
        mem->member = rename;
        expression->method = mem;
      }
    } else if (auto ef = mi->to<P4::ExternFunction>()) {
      if (renameMap->toRename(ef->method)) {
        auto rename = renameMap->getName(ef->method);
        auto cl = expression->method->to<IR::PathExpression>()->clone();
        auto pcl = cl->path->clone();
        pcl->name = rename;
      }
    } else if (auto ff = mi->to<P4::FunctionCall>()) {
      if (renameMap->toRename(ff->function)) {
        auto rename = renameMap->getName(ff->function);
        auto cl = expression->method->to<IR::PathExpression>()->clone();
        auto pcl = cl->path->clone();
        pcl->name = rename;
      }
    }
    return expression;
  }
};
}

analysis::RenameMethods::RenameMethods(P4::ReferenceMap *refMap,
                                       P4::TypeMap *typeMap)
    : renameMap(new P4::RenameMap) {
  setName("RenameMethods_MidEnd");
  passes.emplace_back(new P4::ResolveReferences(refMap));
  passes.emplace_back(new P4::TypeChecking(refMap, typeMap));
  passes.emplace_back(new FindMethods(refMap, renameMap));
  passes.emplace_back(new DoRenameMethods(refMap, typeMap, renameMap));
  passes.emplace_back(new P4::ClearTypeMap(typeMap));
  passes.emplace_back(new P4::ResolveReferences(refMap));
  passes.emplace_back(new P4::TypeChecking(refMap, typeMap));
}
