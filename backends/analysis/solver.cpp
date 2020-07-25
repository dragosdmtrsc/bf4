//
// Created by dragos on 15.10.2018.
//

#include "sovler.h"
#include <analysis/constprop/constant_propagation.h>
#include <common/constantFolding.h>
#include <fstream>
#include <p4/evaluator/evaluator.h>
#include <z3++.h>

using namespace P4;
namespace analysis {

const IR::Node *DoGenerateAssertions::postorder(IR::AssignmentStatement *asg) {
  WhatCanGoWrong whatCanGoWrong(refMap, typeMap);
  asg->right->apply(whatCanGoWrong);
  auto cd = whatCanGoWrong.get(asg->right);
  asg->left->apply(whatCanGoWrong);
  auto cdl = whatCanGoWrong.get(asg->left);
  auto fullCondition = new IR::LAnd(asg->getSourceInfo(), cd, cdl);
  auto ctProp = DoConstantFolding(refMap, typeMap);
  auto expr = fullCondition->apply(ctProp);
  auto mcs = analysis::call_bug();
  if (auto bl = expr->to<IR::BoolLiteral>()) {
    if (!bl->value) {
      return mcs;
    } else {
      return asg;
    }
  }
  auto bs = new IR::BlockStatement(
      {new IR::IfStatement(asg->getSourceInfo(), expr, asg, mcs)});
  stats->push_back(bs);
  return bs;
}

const IR::Node *DoGenerateAssertions::postorder(IR::MethodCallStatement *mcs) {
  auto orig = getOriginal<IR::MethodCallStatement>();
  analysis::ValidityCheck validityCheck(refMap, typeMap);
  const IR::Expression *valid = nullptr;
  if (auto mi = P4::MethodInstance::resolve(orig, refMap, typeMap)) {
    if (mi->is<P4::ExternFunction>() || mi->is<P4::ExternMethod>()) {
      for (auto arg : *mcs->methodCall->arguments) {
        auto parm = mi->substitution.findParameter(arg);
        if (parm->direction == IR::Direction::In ||
            parm->direction == IR::Direction::InOut) {
          auto v = validityCheck.is_valid(arg->expression);
          if (!valid)
            valid = v;
          else
            valid = validityCheck.smart_and(v, valid);
        }
      }
      if (valid) {
        if (auto v = valid->to<IR::BoolLiteral>()) {
          if (!v->value)
            return analysis::call_bug();
          else
            return mcs;
        }
        return new IR::IfStatement(valid, mcs, analysis::call_bug());
      }
    }
  }
  return mcs;
}

GenerateAssertions::GenerateAssertions(ReferenceMap *refMap, TypeMap *typeMap,
                                       bool instrument_keys,
                                       bool instrument_ifs)
    : refMap(refMap), typeMap(typeMap) {
  setName("MidEnd_genassert");
  auto eval = new EvaluatorPass(refMap, typeMap);
  passes.push_back(new CreateAnalysisHelpers);
  if (instrument_ifs) {
    passes.push_back(new DoInstrumentIfStatements(refMap, typeMap));
    passes.push_back(eval);
  }
  passes.push_back(new ConvertHeaderAssignments(refMap, typeMap));
  passes.push_back(eval);
  passes.push_back(new DoGenerateAssertions(refMap, typeMap, &stats));
  passes.push_back(eval);
  if (instrument_keys) {
    passes.push_back(
        new InstrumentKeyMatches(refMap, typeMap, &key_expansions));
    passes.push_back(eval);
    passes.push_back(new RemoveUnreachables2(refMap, typeMap, &key_expansions));
  }
}

const IR::Node *RemoveUnreachables2::preorder(IR::BlockStatement *bs) {
  auto I = statements->find(getOriginal<IR::BlockStatement>());
  if (I != statements->end()) {
    z3::context ctx;
    z3::expr initial = ctx.bool_val(true);
    P4ToSmt p4smt(refMap, typeMap, &ctx, &initial);
    bs->apply(p4smt);
    z3::solver slv(ctx);
    slv.add(!to_expr(ctx, initial));
    auto cr = slv.check();
    switch (cr) {
    case check_result::sat:
      LOG4("keeping block " << bs);
      return bs;
    case check_result::unsat:
      LOG4("slashing block " << bs);
      return nullptr;
    case check_result::unknown:
      BUG("unkown sat result");
    }
  }
  return bs;
}

const IR::Node *InstrumentKeyMatches::postorder(IR::MethodCallStatement *mcs) {
  if (analysis::is_key_match(getOriginal<IR::MethodCallStatement>(), refMap,
                             typeMap)) {
    auto arg = *mcs->methodCall->arguments->begin();
    ValidityCheck validityCheck(refMap, typeMap);
    auto expr = validityCheck.is_valid(arg->expression);
    auto bs = new IR::BlockStatement();
    if (auto bl = expr->to<IR::BoolLiteral>()) {
      if (!bl->value) {
        return analysis::call_bug();
      } else {
        return nullptr;
      }
    }
    auto check_key = new IR::IfStatement(expr, mcs, analysis::call_bug());
    bs->components.push_back(check_key);
    stats->emplace(bs);
    return bs;
  }
  return mcs;
}

const IR::Node *InstrumentKeyMatches::postorder(IR::P4Table *tab) {
  tab->annotations = tab->annotations->addOrReplace(
      analysis::AnalysisLibrary::instance.instrumentKeysAnnotation.name,
      nullptr);
  return tab;
}

InstrumentIfStatements::InstrumentIfStatements(ReferenceMap *refMap,
                                               TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap) {
  passes.push_back(new DoInstrumentIfStatements(refMap, typeMap, &statements));
  passes.push_back(new EvaluatorPass(refMap, typeMap));
  passes.push_back(new RemoveUnreachables(refMap, typeMap, &statements));
}

const IR::Expression *ValidityCheck::get(const IR::Expression *e) {
  auto I = valids.find(e);
  if (I != valids.end())
    return I->second;
  return nullptr;
}

void ValidityCheck::set(const IR::Expression *e, const IR::Expression *v) {
  valids.emplace(e, v);
}

void ValidityCheck::postorder(const IR::LAnd *a) {
  set(a, combine(a->left, a->right,
                 [](const IR::Expression *e) { return new IR::LNot(e); }));
}

void ValidityCheck::postorder(const IR::Operation_Unary *u) {
  auto e = get(u->expr);
  set(u, e);
}

const IR::Expression *WhatCanGoWrong::orer(const IR::Expression *l,
                                           const IR::Expression *r) {
  auto lv = l;
  auto rv = r;
  if (lv->is<IR::BoolLiteral>()) {
    auto lval = lv->to<IR::BoolLiteral>();
    if (!lval->value) {
      return rv;
    } else {
      return new IR::BoolLiteral(true);
    }
  } else {
    if (rv->is<IR::BoolLiteral>()) {
      auto rval = rv->to<IR::BoolLiteral>();
      if (!rval->value) {
        return lv;
      } else {
        return new IR::BoolLiteral(true);
      }
    }
  }
  return new IR::LOr(l, r);
}

const IR::Expression *WhatCanGoWrong::neger(const IR::Expression *l) {
  if (l->is<IR::BoolLiteral>()) {
    return new IR::BoolLiteral(!l->to<IR::BoolLiteral>()->value);
  }
  return new IR::Neg(l);
}

const IR::Expression *WhatCanGoWrong::ander(const IR::Expression *l,
                                            const IR::Expression *r) {
  auto lv = l;
  auto rv = r;
  if (lv->is<IR::BoolLiteral>()) {
    auto lval = lv->to<IR::BoolLiteral>();
    if (lval->value) {
      return rv;
    } else {
      return new IR::BoolLiteral(false);
    }
  } else {
    if (rv->is<IR::BoolLiteral>()) {
      auto rval = rv->to<IR::BoolLiteral>();
      if (rval->value) {
        return lv;
      } else {
        return new IR::BoolLiteral(false);
      }
    }
  }
  return new IR::LAnd(l, r);
}

void WhatCanGoWrong::postorder(const IR::LAnd *) {}

void WhatCanGoWrong::postorder(const IR::LOr *) {}

void WhatCanGoWrong::postorder(const IR::LNot *op) {
  condition[op] = get(op->expr);
}

void WhatCanGoWrong::postorder(const IR::MethodCallExpression *mce) {
  auto mi = MethodInstance::resolve(mce, refMap, typeMap);
  if (mi->is<BuiltInMethod>()) {
    auto bim = mi->to<BuiltInMethod>();
    auto applyKind = typeMap->getType(bim->appliedTo);
    if (applyKind->is<IR::Type_Header>()) {
      if (bim->name.name == IR::Type_Header::isValid) {
        condition[mce] = new IR::BoolLiteral(true);
      }
    }
  } else if (mi->is<ExternMethod>()) {
    auto em = mi->to<ExternMethod>();
    if (em->method->name.name == "lookahead") {
      condition[mce] = new IR::BoolLiteral(true);
    } else {
      condition[mce] = get(mce->method);
    }
  } else if (mi->is<ExternFunction>()) {
    condition[mce] = new IR::BoolLiteral(true);
  }
}

void WhatCanGoWrong::postorder(const IR::BAnd *op) {
  auto rtype = typeMap->getType(op->right);
  auto constant = new IR::Constant(rtype, 0);
  auto neg = orer(ander(get(op->right), new IR::Equ(op->right, constant)),
                  ander(get(op->left), new IR::Equ(op->left, constant)));
  condition[op] = orer(ander(get(op->left), get(op->right)), neg);
}

void WhatCanGoWrong::postorder(const IR::Member *mem) {
  auto applied_to = typeMap->getType(mem->expr);
  if (applied_to->is<IR::Type_Header>()) {
    if (mem->member.name != IR::Type_Header::isValid) {
      auto method = new IR::Member(mem->expr, IR::ID(IR::Type_Header::isValid));
      auto result =
          new IR::MethodCallExpression(IR::Type::Boolean::get(), method);
      condition[mem] = result;
      return;
    }
  }
}

void WhatCanGoWrong::postorder(const IR::Add *op) {
  condition[op] = ander(get(op->left), get(op->right));
}

void WhatCanGoWrong::postorder(const IR::Sub *op) {
  condition[op] = ander(get(op->left), get(op->right));
}

void WhatCanGoWrong::postorder(const IR::Equ *op) {
  condition[op] = ander(get(op->left), get(op->right));
}

void WhatCanGoWrong::postorder(const IR::Leq *op) {
  condition[op] = ander(get(op->left), get(op->right));
}

void WhatCanGoWrong::postorder(const IR::Geq *op) {
  condition[op] = ander(get(op->left), get(op->right));
}

void WhatCanGoWrong::postorder(const IR::Cmpl *op) {
  condition[op] = get(op->expr);
}

void WhatCanGoWrong::postorder(const IR::ArrayIndex *op) {
  condition[op] = ander(get(op->left), get(op->right));
}

void WhatCanGoWrong::postorder(const IR::BXor *op) {
  condition[op] = ander(get(op->left), get(op->right));
}

void WhatCanGoWrong::postorder(const IR::Slice *slice) {
  condition[slice] = get(slice->e0);
}

void WhatCanGoWrong::postorder(const IR::BOr *op) {
  condition[op] = ander(get(op->left), get(op->right));
}

void WhatCanGoWrong::postorder(const IR::Cast *cast) {
  condition[cast] = get(cast->expr);
}

void WhatCanGoWrong::postorder(const IR::Neq *op) {
  condition[op] = ander(get(op->left), get(op->right));
}

void WhatCanGoWrong::postorder(const IR::PathExpression *pathExpression) {
  condition[pathExpression] = new IR::BoolLiteral(true);
}

void WhatCanGoWrong::postorder(const IR::Shl *op) {
  condition[op] = ander(get(op->left), get(op->right));
}

const IR::Expression *WhatCanGoWrong::get(const IR::Expression *iex) {
  //            if (!condition.condition.count(iex))
  //                return nullptr;
  return condition[iex]->clone();
}

void CreateAnalysisHelpers::mkVoidFun(cstring name, IR::P4Program *program) {
  if (!program->getDeclsByName(name)->count()) {
    auto type =
        new IR::Type_Method(IR::Type_Void::get(), new IR::ParameterList());
    auto funDecl = new IR::Method(program->getSourceInfo(),
                                  IR::ID(program->getSourceInfo(), name), type);
    program->objects.insert(program->objects.begin(), funDecl);
  }
}

void CreateAnalysisHelpers::mkAssertFun(cstring name, IR::P4Program *program) {
  if (!program->getDeclsByName(name)->count()) {
    auto type = new IR::Type_Method(
        IR::Type_Void::get(),
        new IR::ParameterList({new IR::Parameter("condition", IR::Direction::In,
                                                 IR::Type_Boolean::get())}));
    auto funDecl = new IR::Method(program->getSourceInfo(),
                                  IR::ID(program->getSourceInfo(), name), type);
    program->objects.insert(program->objects.begin(), funDecl);
  }
}

const IR::Node *CreateAnalysisHelpers::preorder(IR::P4Program *program) {
  auto &inst = analysis::AnalysisLibrary::instance;
  mkVoidFun(inst.drop.name, program);
  mkVoidFun(inst.dontCare.name, program);
  mkVoidFun(inst.oob.name, program);
  mkVoidFun(inst.bug.name, program);
  mkAssertFun(inst.assume.name, program);
  mkAssertFun(inst.angelicAssert.name, program);
  mkAssertFun(inst.assrt.name, program);
  mkAssertFun(inst.keyMatch.name, program);
  auto decls = program->getDeclsByName(inst.havoc.name);
  if (!decls->count()) {
    auto typeParams = new IR::TypeParameters();
    auto tvar = new IR::Type_Var(IR::ID("H"));
    typeParams->push_back(tvar);
    auto type = new IR::Type_Method(typeParams, tvar, new IR::ParameterList());
    auto funDecl =
        new IR::Method(program->getSourceInfo(),
                       IR::ID(program->getSourceInfo(), inst.havoc.name), type);
    program->objects.insert(program->objects.begin(), funDecl);
  }

  return program;
}

void InstrumentTableCalls::mk_table_abstraction(
    const IR::P4Table *table, IR::PathExpression *local_var_ref,
    IR::Vector<IR::Expression> &exprs) {
  auto struct_name = "flow_def_" + table->externalName().replace(".", "__");
  auto key = table->getKey();
  if (key) {
    for (auto k : key->keyElements) {
      auto type = typeMap->getType(k->expression);
      auto nm = k->getAnnotation("name");
      if (auto strlit = nm->expr.at(0)->to<IR::StringLiteral>()) {
        auto cp_name = strlit->value.replace(".", "__");
        if (k->matchType->path->name == "ternary") {
          auto maskMember =
              new IR::Member(local_var_ref, IR::ID(cp_name + "__mask"));
          auto ifzero = new IR::Equ(maskMember, new IR::Constant(type, 0));
          exprs.push_back(ifzero);
        } else if (k->matchType->path->name == "selector" ||
                   k->matchType->path->name == "exact") {
          if (auto mce = k->expression->to<IR::MethodCallExpression>()) {
            auto mi = MethodInstance::resolve(mce, refMap, typeMap);
            if (auto bim = mi->to<P4::BuiltInMethod>()) {
              if (bim->name.name == IR::Type_Header::isValid) {
                exprs.push_back(new IR::Member(local_var_ref, IR::ID(cp_name)));
              }
            }
          }
        } else if (k->matchType->path->name == "lpm") {
          auto prefmember =
              new IR::Member(local_var_ref, IR::ID(cp_name + "__prefix"));
          auto ifzero = new IR::Equ(prefmember, new IR::Constant(type, 0));
          exprs.push_back(ifzero);
        } else if (k->matchType->path->name == "range") {
          // nothing to do
        } else {
          LOG1("don't know how to handle this match kind yet " << k->matchType);
        }
      }
    }
  }
  if (table->getActionList()) {
    auto actionRunMem =
        new IR::Member(local_var_ref, IR::Type_Table::action_run);
    for (const auto ale : table->getActionList()->actionList) {
      auto declid = ale->getName().name;
      auto rv = new IR::Member(
          new IR::PathExpression(IR::ID(struct_name + "__action_type_t")),
          IR::ID(declid));
      exprs.push_back(new IR::Equ(actionRunMem, rv));
    }
  }
}

const IR::Node *ConvertHeaderAssignments::preorder(IR::AssignmentStatement *asg) {
  auto tl = typeMap->getType(asg->left);
  if (tl->is<IR::Type_Header>()) {
    if (asg->right->is<IR::MethodCallExpression>()) {
      return asg;
    }
    if (asg->right->is<IR::StructInitializerExpression>()) {
      auto rsi = asg->right->to<IR::StructInitializerExpression>();
      auto bs = new IR::BlockStatement();
      for (const auto &ne : rsi->components) {
        auto a = new IR::AssignmentStatement(
          new IR::Member(asg->left, ne->name), ne->expression);
        bs->components.push_back(a);
      }
      return bs;
    }
    auto bs = new IR::BlockStatement();
    auto tl_ = tl->to<IR::Type_Header>();

    bs->components.push_back(
      new IR::MethodCallStatement(new IR::MethodCallExpression(
        new IR::Member(asg->left, IR::ID(IR::Type_Header::setValid)))));
    for (auto fld : tl_->fields) {
      auto meml = new IR::Member(asg->left, fld->name);
      auto memr = new IR::Member(asg->right, fld->name);
      bs->components.push_back(new IR::AssignmentStatement(meml, memr));
    }
    auto iftargetInvalid = new IR::IfStatement(
      new IR::MethodCallExpression(
        new IR::Member(asg->left, IR::ID(IR::Type_Header::isValid))),
      analysis::call_bug(),
      new IR::MethodCallStatement(
        new IR::MethodCallExpression(new IR::PathExpression(
          AnalysisLibrary::instance.dontCare.name))));
    return new IR::IfStatement(
      new IR::MethodCallExpression(
        new IR::Member(asg->right, IR::ID(IR::Type_Header::isValid))),
      bs, iftargetInvalid);
  }
  return asg;
}
}