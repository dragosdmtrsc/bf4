//
// Created by dragos on 11.06.2019.
//

#include "Interpreter.h"
#include <common/resolveReferences/resolveReferences.h>
#include <p4/createBuiltins.h>

analysis::Interpreter::Interpreter(const IR::P4Program *program)
    : program(program) {
  init();
}

void analysis::Interpreter::build_cfgs() {
  auto runfun = *program->getDeclsByName("run")->begin();
  std::vector<const IR::IFunctional *> functionals(
      {runfun->to<IR::Function>()});
  std::set<const IR::IFunctional *> visited({runfun->to<IR::Function>()});
}

void analysis::Interpreter::init() {
  PassManager passManager(
      {new P4::CreateBuiltins(), new P4::ResolveReferences(&cctx.refMap, true)});
  program = program->apply(passManager);
}

const IR::Type *
analysis::DynamicTypeHolder::declaredType(const IR::IDeclaration *decl) {
  if (decl->is<IR::Parameter>()) {
    return decl->to<IR::Parameter>()->type;
  } else if (decl->is<IR::Declaration_Variable>()) {
    return decl->to<IR::Declaration_Variable>()->type;
  } else if (decl->is<IR::Declaration_Instance>()) {
    return decl->to<IR::Declaration_Instance>()->type;
  } else if (decl->is<IR::Declaration_ID>()) {
    return nullptr;
  }
  return nullptr;
}

const IR::Type *analysis::DynamicTypeHolder::solve(const IR::Type *t) {
  if (t->is<IR::Type_Name>()) {
    return refMap->getDeclaration(t->to<IR::Type_Name>()->path)
        ->to<IR::Type_Declaration>();
  }
  return t;
}

void analysis::DynamicTypeHolder::postorder(const IR::PathExpression *pe) {
  auto decl = refMap->getDeclaration(pe->path, true);
  auto tp = solve(declaredType(decl));
  typeMap.emplace(pe, tp);
}

const IR::Type *analysis::DynamicTypeHolder::getType(const IR::Expression *expr,
                                                     bool notNull) {
  expr->apply(*this);
  auto I = typeMap.find(expr);
  if (I != typeMap.end()) {
    return I->second;
  } else {
    if (!notNull)
      return nullptr;
    BUG("%1% has no type", expr);
  }
}

const IR::IFunctional *analysis::DynamicTypeHolder::getMethod(
    const IR::Expression *, const IR::Vector<IR::Argument> *) {
  return nullptr;
}

void analysis::DynamicTypeHolder::postorder(const IR::Member *mem) {
  auto ltype = typeMap[mem->expr];
  if (ltype->is<IR::Type_Extern>()) {
    ltype->to<IR::Type_Extern>()->lookupMethod(mem->member, nullptr);
  } else if (ltype->is<IR::Type_Struct>()) {
    auto sf = ltype->to<IR::Type_Struct>()->getDeclByName(mem->member)->to<IR::StructField>();
    auto tp = solve(sf->type);
    typeMap.emplace(mem, tp);
  }
}

analysis::ctx::ctx() : dynamicTypeHolder(&refMap) {}
