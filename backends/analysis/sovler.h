//
// Created by dragos on 15.10.2018.
//

#ifndef P4C_SOVLER_H
#define P4C_SOVLER_H

#include "analysis_helpers.h"
#include "cegis.h"
#include "cfg_algos.h"
#include "version_propagator.h"
#include <chrono>
#include <fstream>
#include <iostream>
#include <p4/tableApply.h>
#include <z3++.h>

using namespace z3;

namespace analysis {

class CreateAnalysisHelpers : public Transform {
  void mkVoidFun(cstring name, IR::P4Program *program);
  void mkAssertFun(cstring name, IR::P4Program *program);
  const IR::Node *preorder(IR::P4Program *program) override;
};

struct ConditionWrapper {
  std::map<const IR::Expression *, const IR::Expression *> condition;
  const IR::Expression *&operator[](const IR::Expression *what) {
    auto p = condition.emplace(what, new IR::BoolLiteral(true));
    return p.first->second;
  }
};

class WhatCanGoWrong : public Inspector {
  ReferenceMap *refMap;
  TypeMap *typeMap;
  ConditionWrapper condition;

public:
  const IR::Expression *get(const IR::Expression *iex);
  WhatCanGoWrong(ReferenceMap *refMap, TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}

  const IR::Expression *orer(const IR::Expression *l, const IR::Expression *r);

  const IR::Expression *neger(const IR::Expression *l);
  const IR::Expression *ander(const IR::Expression *l, const IR::Expression *r);

  void postorder(const IR::LAnd *op) override;
  void postorder(const IR::LOr *op) override;
  void postorder(const IR::LNot *op) override;
  void postorder(const IR::MethodCallExpression *mce) override;
  void postorder(const IR::Add *op) override;
  void postorder(const IR::Sub *op) override;
  void postorder(const IR::Equ *op) override;
  void postorder(const IR::Leq *op) override;
  void postorder(const IR::Geq *op) override;
  void postorder(const IR::BAnd *op) override;
  void postorder(const IR::Cmpl *op) override;
  void postorder(const IR::ArrayIndex *op) override;
  void postorder(const IR::BXor *op) override;
  void postorder(const IR::Slice *slice) override;
  void postorder(const IR::Cast *cast) override;
  void postorder(const IR::BOr *op) override;
  void postorder(const IR::Neq *op) override;
  void postorder(const IR::PathExpression *pathExpression) override;
  void postorder(const IR::Shl *op) override;
  void postorder(const IR::Member *mem) override;
};

class GenerateDeclAssign : public Inspector {
  ReferenceMap *refMap;
  TypeMap *typeMap;
  bool preorder(const IR::Expression *atomic) override {
    WhatCanGoWrong whatCanGoWrong(refMap, typeMap);
    atomic->apply(whatCanGoWrong);
    auto condition = whatCanGoWrong.get(atomic);
    auto plus_bool = new IR::Type_Bits(2, false);
    auto zero = new IR::Constant(plus_bool, 0);
    auto one = new IR::Constant(plus_bool, 1);
    auto undef = new IR::Constant(plus_bool, 2);
    auto decl =
        new IR::Declaration_Variable(IR::ID(refMap->newName("tmp")), plus_bool);
    auto expr = new IR::Mux(condition, new IR::Mux(atomic, one, zero), undef);
    exprMappings.emplace(atomic, std::make_pair(decl, expr));
    stats.push_back(decl);
    stats.push_back(
        new IR::AssignmentStatement(new IR::PathExpression(decl->name), expr));
    return false;
  }
  bool preorder(const IR::LNot *) override { return true; }
  bool preorder(const IR::LAnd *) override { return true; }
  bool preorder(const IR::LOr *) override { return true; }
  void postorder(const IR::LNot *lnot) override {
    auto n = exprMappings[lnot->expr];
    auto npe = new IR::PathExpression(n.first->name);
    auto plus_bool = new IR::Type_Bits(2, false);
    auto zero = new IR::Constant(plus_bool, 0);
    auto one = new IR::Constant(plus_bool, 1);
    auto undef = new IR::Constant(plus_bool, 2);
    auto decl =
        new IR::Declaration_Variable(IR::ID(refMap->newName("tmp")), plus_bool);
    auto expr = new IR::Mux(new IR::Equ(npe, one), zero,
                            new IR::Mux(new IR::Equ(npe, zero), one, undef));
    stats.push_back(decl);
    stats.push_back(
        new IR::AssignmentStatement(new IR::PathExpression(decl->name), expr));
    exprMappings.emplace(lnot, std::make_pair(decl, expr));
  }
  void postorder(const IR::LOr *lor) override {
    auto lv = exprMappings[lor->left];
    auto rv = exprMappings[lor->right];
    auto lpe = new IR::PathExpression(lv.first->name);
    auto rpe = new IR::PathExpression(rv.first->name);
    auto plus_bool = new IR::Type_Bits(2, false);
    auto zero = new IR::Constant(plus_bool, 0);
    auto one = new IR::Constant(plus_bool, 1);
    auto undef = new IR::Constant(plus_bool, 2);
    auto decl =
        new IR::Declaration_Variable(IR::ID(refMap->newName("tmp")), plus_bool);
    auto expr =
        new IR::Mux(new IR::LOr(new IR::Equ(lpe, one), new IR::Equ(rpe, one)),
                    one, new IR::Mux(new IR::LAnd(new IR::Equ(lpe, zero),
                                                  new IR::Equ(rpe, zero)),
                                     zero, undef));
    stats.push_back(decl);
    stats.push_back(
        new IR::AssignmentStatement(new IR::PathExpression(decl->name), expr));
    exprMappings.emplace(lor, std::make_pair(decl, expr));
  }
  void postorder(const IR::LAnd *lAnd) override {
    auto lv = exprMappings[lAnd->left];
    auto rv = exprMappings[lAnd->right];
    auto lpe = new IR::PathExpression(lv.first->name);
    auto rpe = new IR::PathExpression(rv.first->name);
    auto plus_bool = new IR::Type_Bits(2, false);
    auto zero = new IR::Constant(plus_bool, 0);
    auto one = new IR::Constant(plus_bool, 1);
    auto undef = new IR::Constant(plus_bool, 2);
    auto decl = new IR::Declaration_Variable(IR::ID(refMap->newName("tmp")),
                                             new IR::Type_Bits(2, false));
    auto expr = new IR::Mux(
        new IR::LOr(new IR::Equ(lpe, zero), new IR::Equ(rpe, zero)), zero,
        new IR::Mux(new IR::LAnd(new IR::Equ(lpe, one), new IR::Equ(rpe, one)),
                    one, undef));
    stats.push_back(decl);
    stats.push_back(
        new IR::AssignmentStatement(new IR::PathExpression(decl->name), expr));
    exprMappings.emplace(lAnd, std::make_pair(decl, expr));
  }

public:
  IR::IndexedVector<IR::StatOrDecl> stats;
  std::map<const IR::Expression *,
           std::pair<const IR::Declaration *, const IR::Expression *>>
      exprMappings;
  GenerateDeclAssign(ReferenceMap *refMap, TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}

  std::pair<std::vector<const IR::StatOrDecl *>, const IR::Declaration *>
  instrument_condition(const IR::Expression *expr) {
    std::vector<const IR::StatOrDecl *> nodes;
    stats.clear();
    exprMappings.clear();
    expr->apply(*this);
    auto &decl = exprMappings.find(expr)->second.first;
    nodes.insert(nodes.end(), stats.begin(), stats.end());
    return std::make_pair(nodes, decl);
  }
};

class ValidityCheck : public Inspector {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  std::map<const IR::Expression *, const IR::Expression *> valids;
  const IR::Expression *get(const IR::Expression *e);
  void set(const IR::Expression *e, const IR::Expression *v);
  template <typename Transformer>
  const IR::Expression *combine(const IR::Expression *lv,
                                const IR::Expression *rv,
                                Transformer transformer) {
    auto l = get(lv);
    auto r = get(rv);
    if (auto bl = l->to<IR::BoolLiteral>()) {
      if (bl->value) {
        if (auto br = r->to<IR::BoolLiteral>()) {
          if (br->value)
            return new IR::BoolLiteral(true);
          else
            return transformer(lv);
        }
        return new IR::LOr(r, transformer(lv));
      } else {
        if (auto br = r->to<IR::BoolLiteral>()) {
          if (!br->value)
            return new IR::BoolLiteral(false);
          else
            return transformer(rv);
        }
        return new IR::LAnd(r, transformer(rv));
      }
    } else if (auto br = r->to<IR::BoolLiteral>()) {
      if (br->value) {
        return new IR::LOr(l, transformer(rv));
      } else {
        return new IR::LAnd(l, transformer(lv));
      }
    } else {
      return new IR::LOr(
          new IR::LOr(new IR::LAnd(l, r), new IR::LAnd(l, transformer(lv))),
          new IR::LAnd(r, transformer(rv)));
    }
  }

  void postorder(const IR::LAnd *a) override;
  void postorder(const IR::LOr *a) override {
    set(a,
        combine(a->left, a->right, [](const IR::Expression *e) { return e; }));
  }
  void postorder(const IR::PathExpression *e) {
    set(e, new IR::BoolLiteral(true));
  }
  void postorder(const IR::Operation_Unary *u) override;

public:
  const IR::Expression *smart_and(const IR::Expression *e0,
                                  const IR::Expression *e1) {
    if (auto b0 = e0->to<IR::BoolLiteral>()) {
      if (b0->value) {
        return e1;
      } else {
        return new IR::BoolLiteral(false);
      }
    } else if (auto b1 = e1->to<IR::BoolLiteral>()) {
      if (b1->value) {
        return e0;
      } else {
        return new IR::BoolLiteral(false);
      }
    } else {
      return new IR::LAnd(e0, e1);
    }
  }

private:
  //  void postorder(const IR::StructInitializerExpression *init) override {
  //    init->
  //  }

  void postorder(const IR::Operation_Binary *t) override {
    set(t, smart_and(get(t->left), get(t->right)));
  }
  void postorder(const IR::Operation_Ternary *t) override {
    auto e0 = get(t->e0);
    auto e1 = get(t->e1);
    auto e2 = get(t->e2);
    // TODO: sema rules for ternaries
    set(t, smart_and(smart_and(e0, e1), e2));
  }
  void postorder(const IR::Literal *l) { set(l, new IR::BoolLiteral(true)); }
  void postorder(const IR::Member *m) {
    auto mt = typeMap->getType(m);
    if (mt->is<IR::Type_Method>()) {
      return;
    }
    auto e = m->expr;
    auto et = typeMap->getType(e);
    if (et->is<IR::Type_Header>()) {
      set(m, new IR::MethodCallExpression(
                 new IR::Member(e, IR::Type_Header::isValid)));
    } else {
      set(m, new IR::BoolLiteral(true));
    }
  }
  void postorder(const IR::MethodCallExpression *mce) {
    if (is_is_valid(mce, refMap, typeMap)) {
      set(mce, new IR::BoolLiteral(true));
    } else {
      const IR::Expression *crt = nullptr;
      if (auto m = mce->method->to<IR::Member>()) {
        crt = get(m);
      }
      if (mce->arguments) {
        for (auto arg : *mce->arguments) {
          if (!crt)
            crt = get(arg->expression);
          else
            crt = new IR::LAnd(crt, get(arg->expression));
        }
      }
      if (!crt)
        crt = new IR::BoolLiteral(true);
      set(mce, crt);
    }
  }
  void postorder(const IR::BOr *a) override {
    auto tb = typeMap->getType(a->left)->to<IR::Type_Bits>();
    auto ctzero = new IR::Cmpl(new IR::Constant(tb, 0));
    set(a, combine(a->left, a->right, [ctzero](const IR::Expression *e) {
          return new IR::Equ(e, ctzero);
        }));
  }
  void postorder(const IR::BAnd *a) override {
    auto tb = typeMap->getType(a->left)->to<IR::Type_Bits>();
    auto ctzero = new IR::Constant(tb, 0);
    set(a, combine(a->left, a->right, [ctzero](const IR::Expression *e) {
          return new IR::Equ(e, ctzero);
        }));
  }
  void postorder(const IR::ListExpression *lexp) override {
    const IR::Expression *v = nullptr;
    for (auto e : lexp->components) {
      auto crt = get(e);
      if (!v)
        v = crt;
      else
        v = smart_and(crt, v);
    }
    set(lexp, v);
  }

public:
  ValidityCheck(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}
  const IR::Expression *is_valid(const IR::Expression *e) {
    e->apply(*this);
    return get(e);
  }
};

class Cloner : public Transform {
  ReferenceMap *refMap;
  TypeMap *typeMap;
  std::map<const IR::IDeclaration *, const IR::Expression *> mapping;

public:
  Cloner(ReferenceMap *refMap, TypeMap *typeMap,
         std::map<const IR::IDeclaration *, const IR::Expression *> &&mapping)
      : refMap(refMap), typeMap(typeMap), mapping(mapping) {}

  const IR::Node *postorder(IR::PathExpression *path) override {
    auto orig = getOriginal()->to<IR::PathExpression>();
    auto ref = refMap->getDeclaration(orig->path);
    if (ref) {
      auto I = mapping.find(ref);
      if (I != mapping.end())
        return I->second->clone();
    }
    return path;
  }
};

class InstrumentTableCalls : public Inspector {
  ReferenceMap *refMap;
  TypeMap *typeMap;
  std::map<const IR::Statement *, IR::Statement *> *add_before;
  bool default_actions;

public:
  InstrumentTableCalls(
      ReferenceMap *refMap, TypeMap *typeMap,
      std::map<const IR::Statement *, IR::Statement *> *add_before,
      bool default_actions = false)
      : refMap(refMap), typeMap(typeMap), add_before(add_before),
        default_actions(default_actions) {}

  IR::Declaration *generate_declaration(const IR::P4Table *table) {
    auto struct_name = "flow_def_" + table->externalName().replace(".", "__");
    auto path = new IR::Path(IR::ID(struct_name));
    auto struct_type = new IR::Type_Name(path);
    auto local_var_name = "pre_call_" + table->name.name.replace(".", "__");
    auto decl =
        new IR::Declaration_Variable(IR::ID(local_var_name), struct_type);
    return decl;
  }

  IR::Expression *
  generate_key_instrumentation(const IR::P4Table *table,
                               IR::PathExpression *local_var_ref) {
    auto key = table->getKey();
    std::vector<const IR::Expression *> conditions;
    if (key) {
      for (auto k : key->keyElements) {
        auto type = typeMap->getType(k->expression);
        auto nm = k->getAnnotation("name");
        if (auto strlit = nm->expr.at(0)->to<IR::StringLiteral>()) {
          auto cp_name = strlit->value.replace(".", "__");
          if (k->matchType->path->name == "ternary") {
            auto maskMember =
                new IR::Member(local_var_ref, IR::ID(cp_name + "__mask"));
            auto expr = new IR::Equ(
                new IR::BAnd(k->expression, maskMember),
                new IR::BAnd(
                    new IR::Member(local_var_ref, IR::ID(cp_name + "__val")),
                    maskMember));
            conditions.push_back(expr);
          } else if (k->matchType->path->name == "selector" ||
                     k->matchType->path->name == "exact") {
            auto expr = new IR::Equ(
                k->expression, new IR::Member(local_var_ref, IR::ID(cp_name)));
            conditions.push_back(expr);
          } else if (k->matchType->path->name == "lpm") {
            auto prefmember =
                new IR::Member(local_var_ref, IR::ID(cp_name + "__prefix"));

            auto sb =
                new IR::Sub(new IR::Shl(new IR::Constant(type, 1), prefmember),
                            new IR::Constant(type, 1));
            auto expr = new IR::Equ(
                new IR::BAnd(k->expression, sb),
                new IR::BAnd(
                    new IR::Member(local_var_ref, IR::ID(cp_name + "__val")),
                    sb));
            conditions.push_back(expr);
          } else if (k->matchType->path->name == "range") {
            auto mine =
                new IR::Member(local_var_ref, IR::ID(cp_name + "__min"));
            auto maxe =
                new IR::Member(local_var_ref, IR::ID(cp_name + "__max"));
            auto expr = new IR::LAnd(new IR::Leq(k->expression, maxe),
                                     new IR::Geq(k->expression, mine));
            conditions.push_back(expr);
          } else {
            LOG1("don't know how to handle this match kind yet "
                 << k->matchType);
          }
        }
      }
    }

    IR::Expression *crt = nullptr;
    for (auto cd : conditions) {
      if (crt)
        crt = new IR::LAnd(crt, cd);
      else
        crt = cd->clone();
    }
    return crt;
  }

  void mk_table_abstraction(const IR::P4Table *table,
                            IR::PathExpression *local_var_ref,
                            IR::Vector<IR::Expression> &exprs);

  IR::Statement *generate_action_code(const IR::P4Table *table,
                                      bool allow_default = false) {
    auto struct_name = "flow_def_" + table->externalName().replace(".", "__");
    auto local_var_name = "pre_call_" + table->name.name.replace(".", "__");
    auto local_var_ref = new IR::PathExpression(IR::ID(local_var_name));
    std::vector<std::pair<IR::Expression *, IR::Statement *>> actions;
    if (table->getActionList()) {
      auto vec = IR::IndexedVector<IR::Declaration_ID>();
      auto actionRunMem =
          new IR::Member(local_var_ref, IR::Type_Table::action_run);
      for (const auto ale : table->getActionList()->actionList) {
        if (ale->getAnnotation("defaultOnly") && !allow_default) {
          continue;
        }
        auto declid = ale->getName().name;
        const IR::Statement *extra = nullptr;
        auto rv = new IR::Member(
            new IR::PathExpression(IR::ID(struct_name + "__action_type_t")),
            IR::ID(declid));
        auto guard = new IR::Equ(actionRunMem, rv);
        // run the action with the supplied parms
        auto bs = new IR::BlockStatement();
        auto expr = ale->expression;
        if (expr->is<IR::MethodCallExpression>()) {
          auto mce = expr->to<IR::MethodCallExpression>();
          auto mi = MethodInstance::resolve(mce, refMap, typeMap);
          std::map<const IR::IDeclaration *, const IR::Expression *> varMapping;
          if (mi->is<ActionCall>()) {
            auto action = mi->to<P4::ActionCall>()->action;
            auto actName = action->name.name;
            for (const auto param : action->getParameters()->parameters) {
              if (param->direction == IR::Direction::None) {
                auto fullName = actName + "." + param->name.name;
                auto cp_name = cstring(fullName).replace(".", "__");
                varMapping[param] =
                    new IR::Member(local_var_ref, IR::ID(cp_name));
              }
            }
            Cloner c(refMap, typeMap, std::move(varMapping));
            for (const auto inner_statement : action->body->components)
              bs->push_back(inner_statement->apply(c)->to<IR::StatOrDecl>());
            if (extra)
              bs->push_back(extra);
          }
        }
        actions.emplace_back(guard, bs);
      }
    }
    auto I = actions.rbegin();
    IR::Statement *actionCode = new IR::EmptyStatement();
    if (I != actions.rend()) {
      actionCode = I->second;
      ++I;
    }
    for (; I != actions.rend(); ++I)
      actionCode = new IR::IfStatement(I->first, I->second, actionCode);
    return actionCode;
  }

  IR::Statement *
  generate_statement(const IR::P4Table *table,
                     const std::map<cstring, const IR::Statement *> &,
                     const IR::Statement *hit, const IR::Statement *miss) {
    auto *stat = new IR::BlockStatement();
    auto struct_name = "flow_def_" + table->externalName().replace(".", "__");
    auto path = new IR::Path(IR::ID(struct_name));
    auto struct_type = new IR::Type_Name(path);
    auto local_var_name = "pre_call_" + table->name.name.replace(".", "__");
    auto local_var_ref = new IR::PathExpression(IR::ID(local_var_name));
    auto havoc =
        new IR::MethodCallExpression(new IR::PathExpression("havoc"),
                                     new IR::Vector<IR::Type>({struct_type}),
                                     new IR::Vector<IR::Argument>());

    stat->components.push_back(
        new IR::AssignmentStatement(local_var_ref, havoc));
    stat->components.push_back(new IR::AssignmentStatement(
        new IR::Member(local_var_ref, "reach"), new IR::BoolLiteral(true)));
    IR::Vector<IR::Expression> exprs;
    mk_table_abstraction(table, local_var_ref, exprs);
    stat->push_back(analysis::call_assert_point(exprs));
    auto match_condition = generate_key_instrumentation(table, local_var_ref);
    IR::Vector<IR::Expression> args;
    auto actionCode = generate_action_code(table);
    auto do_miss = (default_actions) ? generate_action_code(table, true)
                                     : new IR::EmptyStatement();
    if (hit) {
      actionCode = new IR::BlockStatement({actionCode, hit});
    } else {
      actionCode = new IR::BlockStatement({actionCode});
    }
    // TODO: how to relate axioms to this thing?
    const IR::Statement *guard_assumption = nullptr;
    const IR::Statement *default_assumption = nullptr;
    if (match_condition) {
      guard_assumption = call_assert(match_condition);
      unsigned tab_size = 4096;
      if (table->getSizeProperty())
        tab_size = table->getSizeProperty()->asUnsigned();
      if (default_actions)
        default_assumption =
            call_assert(call_forall(struct_type, local_var_ref, tab_size,
                                    new IR::LNot(match_condition)));
    }
    const IR::Expression *guard =
        new IR::Equ(new IR::Member(local_var_ref, IR::Type_Table::hit),
                    new IR::BoolLiteral(true));
    const IR::Statement *guard_hit = nullptr;
    if (guard) {
      const IR::Statement *miss_stat = nullptr;
      if (miss)
        miss_stat = new IR::BlockStatement({do_miss, miss});
      else
        miss_stat = do_miss;
      auto engarde = new IR::BlockStatement();
      if (guard_assumption) {
        engarde->push_back(guard_assumption);
      }
      if (match_condition) {
        engarde->push_back(analysis::call_key_match(match_condition));
      }
      engarde->push_back(actionCode);
      if (default_assumption) {
        miss_stat = new IR::BlockStatement({default_assumption, miss_stat});
      }

      guard_hit = new IR::IfStatement(guard, engarde, miss_stat);
      //                guard_hit = new IR::BlockStatement({ /*mcs,actionCode*/
      //                ;
    } else {
      guard_hit = actionCode;
    }
    stat->push_back(guard_hit);
    stat->annotations->add(new IR::Annotation(
        IR::ID("model"), {new IR::PathExpression(table->name)}));
    return stat;
  }

  IR::Statement *generate_statement(
      const IR::P4Table *table,
      const std::map<cstring, const IR::Statement *> &extra_instructions) {
    return generate_statement(table, extra_instructions, nullptr, nullptr);
  }
  IR::Statement *generate_statement(const IR::P4Table *table,
                                    const IR::Statement *hit,
                                    const IR::Statement *miss) {
    const std::map<cstring, const IR::Statement *> extra_instructions;
    return generate_statement(table, extra_instructions, hit, miss);
  }

  IR::Statement *generate_statement(const IR::P4Table *table) {
    std::map<cstring, const IR::Statement *> extra;
    return generate_statement(table, extra);
  }

  bool preorder(const IR::MethodCallExpression *mce) override {
    auto mi = MethodInstance::resolve(mce, refMap, typeMap);
    if (mi->isApply()) {
      auto am = mi->to<ApplyMethod>();
      if (am->isTableApply()) {
        auto tab = am->object->to<IR::P4Table>();
        auto stat = generate_statement(tab);
        auto parent = findContext<IR::Statement>();
        if (parent->is<IR::MethodCallStatement>()) {
          add_before->emplace(parent, stat);
        } else if (parent->is<IR::SwitchStatement>()) {
          add_before->emplace(parent, stat);
        } else {
          add_before->emplace(parent, stat);
          LOG1("don't know this kind of parent " << parent);
        }
        return false;
      }
    }
    return true;
  }
};

class InstrumentKeyMatches : public Transform {
  ReferenceMap *refMap;
  TypeMap *typeMap;
  std::set<const IR::BlockStatement *> *stats;

public:
  InstrumentKeyMatches(ReferenceMap *refMap, TypeMap *typeMap,
                       std::set<const IR::BlockStatement *> *stats)
      : refMap(refMap), typeMap(typeMap), stats(stats) {}
  const IR::Node *postorder(IR::P4Table *tab) override;
  const IR::Node *postorder(IR::MethodCallStatement *mcs) override;
};

class ReplaceAllTableCalls : public Transform {
  ReferenceMap *refMap;
  TypeMap *typeMap;
  InstrumentTableCalls itc;
  std::vector<IR::Declaration *> pulled_declarations;

public:
  ReplaceAllTableCalls(ReferenceMap *refMap, TypeMap *typeMap,
                       bool default_actions = false)
      : refMap(refMap), typeMap(typeMap),
        itc(refMap, typeMap, nullptr, default_actions) {}

  const IR::Node *postorder(IR::IfStatement *ifs) override {
    if (auto tab =
            P4::TableApplySolver::isHit(ifs->condition, refMap, typeMap)) {
      auto hs = ifs->ifTrue;
      auto ms = ifs->ifFalse;
      auto new_i = itc.generate_statement(tab, hs, ms);
      pulled_declarations.emplace_back(itc.generate_declaration(tab));
      return new_i;
    }
    return ifs;
  }

  const IR::Node *postorder(IR::P4Control *ctrl) override {
    auto old_components = ctrl->body->components;
    auto bs = new IR::BlockStatement();
    for (auto decl : pulled_declarations) {
      bs->components.push_back(decl);
      auto declname = decl->name.name;
      auto pe = new IR::PathExpression(declname);
      auto mem = new IR::Member(pe, "reach");
      bs->components.push_back(
          new IR::AssignmentStatement(mem, new IR::BoolLiteral(false)));
      mem = new IR::Member(pe, IR::Type_Table::hit);
      bs->components.push_back(
          new IR::AssignmentStatement(mem, new IR::BoolLiteral(false)));
    }
    bs->components.insert(bs->components.end(), old_components.begin(),
                          old_components.end());
    ctrl->body = bs;
    return ctrl;
  }
  const IR::Node *preorder(IR::P4Control *ctrl) override {
    pulled_declarations.clear();
    return ctrl;
  }

  const IR::Node *preorder(IR::P4Action *act) override {
    prune();
    return act;
  }
  const IR::Node *preorder(IR::P4Table *t) override {
    prune();
    return t;
  }
  const IR::Node *preorder(IR::P4Parser *p) override {
    prune();
    return p;
  }
  const IR::Node *postorder(IR::MethodCallStatement *stat) override {
    auto mi = MethodInstance::resolve(stat->methodCall, refMap, typeMap);
    if (mi->isApply() && mi->to<ApplyMethod>()->isTableApply()) {
      auto tab = mi->object->to<IR::P4Table>();
      pulled_declarations.emplace_back(itc.generate_declaration(tab));
      auto new_i = itc.generate_statement(tab);
      return new_i;
    }
    return stat;
  }
  const IR::Node *postorder(IR::SwitchStatement *stat) override {
    std::map<cstring, const IR::Statement *> stats;
    const IR::Statement *def = nullptr;
    std::set<cstring> all_actions;
    if (auto tab = P4::TableApplySolver::isActionRun(stat->expression, refMap,
                                                     typeMap)) {
      auto struct_name = "flow_def_" + tab->externalName().replace(".", "__");
      auto local_var_name = "pre_call_" + tab->name.name.replace(".", "__");
      auto enum_expr =
          new IR::PathExpression(IR::ID(struct_name + "__action_type_t"));
      pulled_declarations.emplace_back(itc.generate_declaration(tab));
      auto i1 = itc.generate_statement(tab);
      auto action_run =
          new IR::Member(new IR::PathExpression(cstring(local_var_name)),
                         IR::ID("action_run"));
      std::vector<std::pair<const IR::Expression *, const IR::Statement *>>
          guarded_stats;
      for (auto c : stat->cases) {
        if (c->label->is<IR::PathExpression>()) {
          auto act_name = c->label->to<IR::PathExpression>()->path->name.name;
          auto mem = new IR::Member(enum_expr, act_name);
          guarded_stats.emplace_back(new IR::Equ(action_run, mem),
                                     c->statement);
        } else if (c->label->is<IR::DefaultExpression>()) {
          def = c->statement;
        } else {
          BUG("can't handle this kind of label %1%", c->label);
        }
      }
      const IR::Statement *case_solver = nullptr;
      if (guarded_stats.empty()) {
        if (def) {
          if (i1->is<IR::BlockStatement>()) {
            auto clone = i1->to<IR::BlockStatement>()->clone();
            clone->push_back(def);
            return clone;
          }
          return new IR::BlockStatement({i1, def});
        }
        return i1;
      } else {
        case_solver = def;
        for (auto I = guarded_stats.rbegin(); I != guarded_stats.rend(); ++I)
          case_solver = new IR::IfStatement(I->first, I->second, case_solver);
        if (i1->is<IR::BlockStatement>()) {
          auto clone = i1->to<IR::BlockStatement>()->clone();
          clone->push_back(case_solver);
          return clone;
        }
        return new IR::BlockStatement({i1, case_solver});
      }
    }
    return stat;
  }
};

class GenerateInstrumentationCode : public Transform {
  ReferenceMap *refMap;
  TypeMap *typeMap;
  std::map<const IR::Statement *, IR::Statement *> add_before;

public:
  GenerateInstrumentationCode(ReferenceMap *refMap, TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}

  const IR::Node *preorder(IR::P4Program *prog) override {
    auto inst = InstrumentTableCalls(refMap, typeMap, &add_before);
    getOriginal()->apply(inst);
    return prog;
  }

  const IR::Node *postorder(IR::Statement *where) override {
    auto orig = getOriginal();
    auto I = add_before.find(orig->to<IR::Statement>());
    if (I != add_before.end()) {
      auto bs = I->second->to<IR::BlockStatement>()->clone();
      if (where->is<IR::SwitchStatement>()) {
        auto ss = where->to<IR::SwitchStatement>();
        auto mce = ss->expression->to<IR::Member>()
                       ->expr->to<IR::MethodCallExpression>();
        auto mi = MethodInstance::resolve(mce, refMap, typeMap);
        const IR::P4Table *table = nullptr;
        if (mi->isApply()) {
          auto am = mi->to<ApplyMethod>();
          if (am->isTableApply()) {
            table = am->object->to<IR::P4Table>();
          }
        }
        CHECK_NULL(table);
        auto local_var_name = "pre_call_" + table->name.name.replace(".", "__");
        auto local_var_ref = new IR::PathExpression(IR::ID(local_var_name));
        auto main_struct_name =
            "flow_def_" + table->externalName().replace(".", "__");
        auto action_type_name = main_struct_name + "__action_type_t";
        auto enum_type = new IR::PathExpression(IR::ID(action_type_name));

        std::vector<const IR::Expression *> stat_expr;
        IR::Vector<IR::SwitchCase> new_cases;
        const IR::SwitchCase *defaultcase = nullptr;
        for (auto cs : ss->cases) {
          if (cs->label->is<IR::DefaultExpression>()) {
            defaultcase = cs;
          } else {
            auto pe = cs->label->to<IR::PathExpression>();
            CHECK_NULL(pe);
            cstring label = pe->path->name.name;
            auto enummember = new IR::Member(enum_type, IR::ID(label));
            auto structfield = new IR::Member(
                local_var_ref, IR::ID(IR::Type_Table::action_run));
            auto expr = new IR::Equ(enummember, structfield);
            stat_expr.push_back(expr);
            new_cases.push_back(new IR::SwitchCase(
                cs->label, new IR::BlockStatement({new IR::IfStatement(
                               expr, cs->statement, nullptr)})));
          }
        }
        if (defaultcase) {
          if (stat_expr.empty()) {
            new_cases.push_back(defaultcase);
          } else {
            const IR::Expression *neg;
            if (stat_expr.size() == 1) {
              neg = new IR::LNot(stat_expr[0]);
            } else {
              auto IT = stat_expr.begin();
              auto crt = *IT;
              ++IT;
              for (; IT != stat_expr.end(); ++IT)
                crt = new IR::LAnd(crt, *IT);
              neg = new IR::LNot(crt);
            }
            auto case_stat = defaultcase->clone();
            case_stat->statement = new IR::BlockStatement(
                {new IR::IfStatement(neg, defaultcase->statement, nullptr)});
            new_cases.push_back(case_stat);
          }
        }
        auto switch_stat_mutable = ss->clone();
        switch_stat_mutable->cases = new_cases;
        where = switch_stat_mutable;
      }
      bs->components.push_back(where);
      return bs;
    }
    return where;
  }
};

class P4ToSmt : public Inspector {
  ReferenceMap *refMap;
  TypeMap *typeMap;
  z3::context *context;
  z3::ast *currentAst;
  bool failure_conditions;

public:
  std::map<cstring, z3::ast> variables;

  P4ToSmt(ReferenceMap *refMap, TypeMap *typeMap, z3::context *context,
          z3::ast *ast, bool failure_conditions = false)
      : refMap(refMap), typeMap(typeMap), context(context), currentAst(ast),
        failure_conditions(failure_conditions) {}
  void destroyParms(cstring prefix, const IR::Type *type) {
    if (type->is<IR::Type_Header>()) {
      auto varname = prefix + "." + IR::Type_Header::isValid;
      auto constant = context->constant(varname.c_str(), context->bool_sort());
      variables.erase(varname);
    }
    if (type->is<IR::Type_Stack>()) {
      auto ash = type->to<IR::Type_Stack>();
      auto sz = ash->getSize();
      auto type = typeMap->getType(ash->elementType);
      if (type->is<IR::Type_Type>())
        type = type->to<IR::Type_Type>()->type;
      for (unsigned i = 0; i != sz; ++i) {
        std::stringstream sstream;
        sstream << prefix << "[" << i << "]";
        destroyParms(sstream.str(), type);
      }
    } else if (type->is<IR::Type_StructLike>()) {
      auto ash = type->to<IR::Type_StructLike>();
      for (const auto fld : ash->fields) {
        auto type = typeMap->getType(fld);
        if (type->is<IR::Type_Type>())
          type = type->to<IR::Type_Type>()->type;
        destroyParms(prefix + "." + fld->name.name, type);
      }
    } else if (type->is<IR::Type_Bits>()) {
      variables.erase(prefix);
    } else if (type->is<IR::Type_Boolean>()) {
      variables.erase(prefix);
    }
  }
  void getParms(cstring prefix, const IR::Type *type) {
    if (type->is<IR::Type_Header>()) {
      auto varname = prefix + "." + IR::Type_Header::isValid;
      auto constant = context->constant(varname.c_str(), context->bool_sort());
      variables.emplace(varname, constant);
    }
    if (type->is<IR::Type_Stack>()) {
      auto ash = type->to<IR::Type_Stack>();
      auto sz = ash->getSize();
      auto type = typeMap->getType(ash->elementType);
      if (type->is<IR::Type_Type>())
        type = type->to<IR::Type_Type>()->type;
      for (unsigned i = 0; i != sz; ++i) {
        std::stringstream sstream;
        sstream << prefix << "[" << i << "]";
        getParms(sstream.str(), type);
      }
    } else if (type->is<IR::Type_StructLike>()) {
      auto ash = type->to<IR::Type_StructLike>();
      for (const auto fld : ash->fields) {
        auto type = typeMap->getType(fld);
        if (type->is<IR::Type_Type>())
          type = type->to<IR::Type_Type>()->type;
        getParms(prefix + "." + fld->name.name, type);
      }
    } else if (type->is<IR::Type_Bits>()) {
      auto ash = type->to<IR::Type_Bits>();
      auto varname = prefix;
      auto ast =
          context->bv_const(varname, static_cast<unsigned int>(ash->size));
      variables.emplace(varname, ast);
    } else if (type->is<IR::Type_Boolean>()) {
      auto ast = context->bool_const(prefix);
      variables.emplace(prefix, ast);
    }
  }
  bool preorder(const IR::MethodCallExpression *mce) override {
    auto mi = MethodInstance::resolve(mce, refMap, typeMap);
    if (mi->is<ActionCall>()) {
      // no op here - should be handled by model
    } else if (mi->isApply()) {
      // no op here - should be handled by model in the case of table apply
      // or should input more code if this is not the case
      if (mi->to<ApplyMethod>()->isTableApply()) {
        // no op
      } else {
        auto am = mi->to<ApplyMethod>();
        auto type = typeMap->getType(am->object->getNode());
        // calling into the control block
        if (type->is<IR::Type_Control>() || type->is<IR::Type_Parser>()) {
          LOG1("calling into p4control || parser");
        } else {
          BUG("can't handle apply method %1% against %2%", mce, am->object);
        }
      }
    } else if (mi->is<BuiltInMethod>()) {
      auto extm = mi->to<BuiltInMethod>();
      if (extm->name == IR::Type_Header::setValid ||
          extm->name == IR::Type_Header::setInvalid) {
        auto mem = new IR::Member(extm->appliedTo, IR::Type_Header::isValid);
        IRExprToSMT visi(refMap, typeMap, context, &variables);
        mem->apply(visi);
        auto expr = to_expr(*context, *visi.get(mem));
        expr_vector src = expr_vector(*context);
        src.push_back(expr);
        expr_vector dst = expr_vector(*context);
        dst.push_back(
            context->bool_val(extm->name == IR::Type_Header::setValid));
        *currentAst = to_expr(*context, *currentAst).substitute(src, dst);
      }
    } else if (mi->is<ExternFunction>()) {
      auto extfun = mi->to<ExternFunction>();
      if (extfun->method->name.name == "bug") {
        *currentAst = context->bool_val(failure_conditions);
      } else if (extfun->method->name.name == "mark_to_drop" ||
                 extfun->method->name.name == "recirculate" ||
                 extfun->method->name.name == "resubmit" ||
                 extfun->method->name.name.startsWith("clone")) {
        // no op -> means success (i.e. no undef behavior)
      } else if (extfun->method->name.name == "assume") {
        IRExprToSMT e2smt(refMap, typeMap, context, &variables);
        (*mce->arguments)[0]->expression->apply(e2smt);
        auto smt_expr = e2smt.get((*mce->arguments)[0]->expression);
        if (failure_conditions)
          *currentAst =
              to_expr(*context, *smt_expr) && to_expr(*context, *currentAst);
        else
          *currentAst = implies(to_expr(*context, *smt_expr),
                                to_expr(*context, *currentAst));
      } else if (extfun->method->name.name == "assert") {
        IRExprToSMT e2smt(refMap, typeMap, context, &variables);
        (*mce->arguments)[0]->expression->apply(e2smt);
        auto smt_expr = e2smt.get((*mce->arguments)[0]->expression);
        *currentAst =
            to_expr(*context, *smt_expr) && to_expr(*context, *currentAst);
      } else {
        LOG1("can't handle extern method " << mce);
      }
    }
    return false;
  }

  bool preorder(const IR::EmptyStatement *) override { return false; }
  bool preorder(const IR::MethodCallStatement *) override { return true; }
  bool preorder(const IR::SwitchStatement *ss) override {
    auto new_bs = new IR::BlockStatement();
    for (auto sc : ss->cases) {
      new_bs->components.push_back(sc->statement);
    }
    visit(new_bs);
    return false;
  }

  bool preorder(const IR::Statement *stm) override {
    BUG("unknown statement => can't handle it %1%", stm);
    return false;
  }
  bool preorder(const IR::IfStatement *ifStatement) override {
    auto copyf = *currentAst;
    auto vst = new IRExprToSMT(refMap, typeMap, context, &variables);
    ifStatement->condition->apply(*vst);
    auto cdtt = to_expr(*context, *vst->get(ifStatement->condition));
    auto cdff = !cdtt;
    visit(ifStatement->ifTrue);
    auto copyt = (failure_conditions)
                     ? (cdtt && to_expr(*context, *currentAst))
                     : (implies(cdtt, to_expr(*context, *currentAst)));
    *currentAst = copyf;
    visit(ifStatement->ifFalse);
    auto forfalse = (failure_conditions)
                        ? (cdff && to_expr(*context, *currentAst))
                        : (implies(cdff, to_expr(*context, *currentAst)));
    *currentAst = (failure_conditions) ? copyt || forfalse : copyt && forfalse;
    return false;
  }
  bool preorder(const IR::AssignmentStatement *asg) override {
    auto left = asg->left;
    auto leftType = typeMap->getType(left);
    LOG1("assigning " << asg);
    if (leftType->is<IR::Type_StructLike>()) {
      auto lv = asg->right->to<IR::MethodCallExpression>();
      if (lv) {
        auto mi = MethodInstance::resolve(lv, refMap, typeMap);
        if (mi->is<ExternFunction>() &&
            mi->to<ExternFunction>()->method->name.name == "havoc") {
          auto pe = left->to<IR::PathExpression>();
          if (pe) {
            auto path = pe->path;
            auto ref = refMap->getDeclaration(path);
            getParms(ref->getName().name, leftType);
          }
        }
      }
    } else if (leftType->is<IR::Type_Bits>() ||
               leftType->is<IR::Type_Boolean>()) {
      IRExprToSMT vst(refMap, typeMap, context, &variables);
      asg->right->apply(vst);
      auto rv = vst.get(asg->right);
      asg->left->apply(vst);
      auto lv = vst.get(asg->left);

      expr_vector src = expr_vector(*context);
      src.push_back(to_expr(*context, *lv));
      expr_vector dst = expr_vector(*context);
      dst.push_back(to_expr(*context, *rv));
      try {
        *currentAst = to_expr(*context, *currentAst).substitute(src, dst);
      } catch (const z3::exception &exc) {
        BUG("%1% %2%", asg, exc.msg());
      }
    } else {
      LOG1("unknown type to handle " << leftType);
    }
    return false;
  }

  bool preorder(const IR::BlockStatement *bs) override {
    for (auto I = bs->components.rbegin(); I != bs->components.rend(); ++I) {
      auto stm = *I;
      if (stm->is<IR::Statement>())
        visit(stm);
    }
    return false;
  }

  void initializeControlBlock(const IR::P4Control *block) {
    variables.clear();
    for (const auto param : block->getApplyParameters()->parameters) {
      auto type = typeMap->getType(param);
      if (type->is<IR::Type_Type>())
        type = type->to<IR::Type_Type>()->type;
      getParms(param->name.name, type);
    }
    for (const auto local : block->controlLocals) {
      auto type = typeMap->getType(local);
      if (type->is<IR::Type_Type>())
        type = type->to<IR::Type_Type>()->type;
      auto name = local->name.name;
      getParms(name, type);
    }
  }
};

class DoInstrumentIfStatements : public Transform {
  ReferenceMap *refMap;
  TypeMap *typeMap;
  std::vector<const IR::BlockStatement *> *statements;

public:
  DoInstrumentIfStatements(
      ReferenceMap *refMap, TypeMap *typeMap,
      std::vector<const IR::BlockStatement *> *statements = nullptr)
      : refMap(refMap), typeMap(typeMap), statements(statements) {}

  const IR::Node *postorder(IR::IfStatement *ifs) override {
    ValidityCheck validityCheck(refMap, typeMap);
    auto vcheck =
        validityCheck.is_valid(getOriginal<IR::IfStatement>()->condition);
    if (auto bl = vcheck->to<IR::BoolLiteral>()) {
      if (bl->value) {
        return ifs;
      } else {
        return analysis::call_bug();
      }
    } else {
      ifs = new IR::IfStatement(vcheck, ifs, analysis::call_bug());
    }
    return ifs;
  }
};
class RemoveUnreachables : public Transform {
  ReferenceMap *refMap;
  TypeMap *typeMap;
  std::vector<const IR::BlockStatement *> *statements;

public:
  RemoveUnreachables(ReferenceMap *refMap, TypeMap *typeMap,
                     std::vector<const IR::BlockStatement *> *statements)
      : refMap(refMap), typeMap(typeMap), statements(statements) {}

  const IR::Node *preorder(IR::BlockStatement *bs) override {
    auto I = std::find(statements->begin(), statements->end(),
                       getOriginal<IR::BlockStatement>());
    if (I != statements->end()) {
      auto components = (*I)->components;
      auto componentIt = std::find_if(components.begin(), components.end(),
                                      [](const IR::StatOrDecl *what) {
                                        return what->is<IR::IfStatement>();
                                      });
      BUG_CHECK(componentIt != components.end(), "nasty business");
      auto tempBs = new IR::BlockStatement();
      tempBs->components.insert(tempBs->components.begin(), components.begin(),
                                componentIt);
      auto ifcond = (*componentIt)->to<IR::IfStatement>();
      auto pathExpr = ifcond->condition;
      z3::context ctx;
      IRExprToSMT irtosmt(refMap, typeMap, &ctx,
                          new std::map<cstring, z3::ast>());
      pathExpr->apply(irtosmt);
      z3::ast initial = to_expr(ctx, *irtosmt.get(pathExpr));
      P4ToSmt p4smt(refMap, typeMap, &ctx, &initial);
      tempBs->apply(p4smt);
      z3::solver slv(ctx);
      slv.add(to_expr(ctx, initial));
      auto cr = slv.check();
      switch (cr) {
      case check_result::sat:
        LOG1("current response is SAT. need to keep block");
        return bs;
      case check_result::unsat:
        LOG1("current response is UNSAT. need to slash block");
        return ifcond->ifFalse;
      case check_result::unknown:
        BUG("unkown sat result");
      }
    }
    return bs;
  }
};

class RemoveUnreachables2 : public Transform {
  ReferenceMap *refMap;
  TypeMap *typeMap;
  std::set<const IR::BlockStatement *> *statements;

public:
  RemoveUnreachables2(ReferenceMap *refMap, TypeMap *typeMap,
                      std::set<const IR::BlockStatement *> *statements)
      : refMap(refMap), typeMap(typeMap), statements(statements) {}

  const IR::Node *preorder(IR::BlockStatement *bs) override;
};

class DoGenerateAssertions : public Transform {
  ReferenceMap *refMap;
  TypeMap *typeMap;
  std::vector<const IR::BlockStatement *> *stats;

public:
  DoGenerateAssertions(ReferenceMap *refMap, TypeMap *typeMap,
                       std::vector<const IR::BlockStatement *> *stats)
      : refMap(refMap), typeMap(typeMap), stats(stats) {}

  const IR::Node *postorder(IR::AssignmentStatement *asg) override;
  const IR::Node *postorder(IR::MethodCallStatement *mcs) override;
};

class ConvertHeaderAssignments : public Transform {
  ReferenceMap *refMap;
  TypeMap *typeMap;

public:
  ConvertHeaderAssignments(ReferenceMap *refMap, TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}

  const IR::Node *preorder(IR::AssignmentStatement *asg) override;
};
class GenerateAssertions : public PassManager {
  ReferenceMap *refMap;
  TypeMap *typeMap;
  std::set<const IR::BlockStatement *> key_expansions;
  std::vector<const IR::BlockStatement *> stats;

public:
  GenerateAssertions(ReferenceMap *refMap, TypeMap *typeMap,
                     bool instrument_keys = true, bool instrument_ifs = true);
};
class InstrumentIfStatements : public PassManager {
  ReferenceMap *refMap;
  TypeMap *typeMap;
  std::vector<const IR::BlockStatement *> statements;

public:
  InstrumentIfStatements(ReferenceMap *refMap, TypeMap *typeMap);
};
class P4ToSmtControl : public Inspector {
  ReferenceMap *refMap;
  TypeMap *typeMap;
  std::ofstream ofs;

public:
  expr_vector atomic_formulas(const expr &e) {
    expr_vector retval(e.ctx());
    if (e.get_sort().is_bool()) {
      if (e.is_app()) {
        auto app = e.decl();
        if (app.decl_kind() != Z3_OP_AND && app.decl_kind() != Z3_OP_OR &&
            app.decl_kind() != Z3_OP_XOR && app.decl_kind() != Z3_OP_NOT &&
            app.decl_kind() != Z3_OP_IMPLIES) {
          if (app.decl_kind() != Z3_OP_TRUE && app.decl_kind() != Z3_OP_FALSE &&
              !e.is_const()) {
            auto num = e.num_args();
            if (num >= 1 && e.arg(0).get_sort().is_bv() &&
                e.arg(0).get_sort().bv_size() >= 2) {
              retval.push_back(e);
            }
          }
        } else {
          auto num = e.num_args();
          for (unsigned i = 0; i != num; ++i) {
            auto arg = e.arg(i);
            auto vec = atomic_formulas(arg);
            unsigned sz = vec.size();
            for (unsigned j = 0; j != sz; ++j) {
              retval.push_back(vec[j]);
            }
          }
        }
      }
    }
    return retval;
  }

  z3::expr get_expr(const z3::model &new_model) const {
    auto sz = new_model.size();
    expr_vector and_fun(new_model.ctx());
    for (unsigned i = 0; i != sz; ++i) {
      auto const_decl = new_model.get_const_decl(i);
      if (const_decl.name().str().find("pre_call") != std::string::npos) {
        and_fun.push_back(const_decl() ==
                          new_model.get_const_interp(const_decl));
      }
    }
    return mk_and(and_fun);
  }

  P4ToSmtControl(ReferenceMap *refMap, TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap), ofs("tab_mappings.txt") {}
  ~P4ToSmtControl() { ofs.close(); }
  bool preorder(const IR::MethodCallExpression *mce) override {
    auto mi = MethodInstance::resolve(mce, refMap, typeMap);
    if (mi->isApply()) {
      auto am = mi->to<ApplyMethod>();
      if (am->isTableApply()) {
        auto stat = findContext<IR::BlockStatement>();
        auto tab = am->object->to<IR::P4Table>();
        CHECK_NULL(stat);
        auto what = findContext<IR::Statement>();
        auto where =
            std::find(stat->components.begin(), stat->components.end(), what);
        auto model = new IR::BlockStatement();
        IR::IndexedVector<IR::StatOrDecl> extra_assumptions;
        for (auto I = stat->components.begin(); I != where; ++I) {
          model->push_back(*I);
        }
        auto local_var_name = "pre_call_" + tab->name.name.replace(".", "__");
        z3::context ctx;
        auto postcondition = ctx.bool_const((local_var_name + ".hit").c_str());
        auto initial = ctx.bool_val(true);
        auto p42smt = P4ToSmt(refMap, typeMap, &ctx, &initial, false);
        model->apply(p42smt);
        auto ok_cond = to_expr(ctx, initial);

        auto wp = P4ToSmt(refMap, typeMap, &ctx, &postcondition, false);
        model->apply(wp);
        auto ok_and_hit = to_expr(ctx, postcondition);

        auto slv = z3::solver(ctx);
        slv.add(!ok_cond.simplify());
        auto cr = slv.check();
        ofs << "model:\n"
            << model << "\n=============\n"
            << "formula:\n"
            << slv.to_smt2() << '\n'
            << "status:" << cr << '\n';
        switch (cr) {
        case check_result::sat: {
          auto hvars = [](const std::string &v) {
            return v.find("pre_call") == std::string::npos;
          };
          auto neg = (!ok_cond).simplify();
          auto forall = convert_to_forall(neg, hvars);
          z3::solver slv_forall(ctx);
          slv_forall.add(forall);
          if (slv_forall.check() == check_result::sat) {
            cegis cneg(neg);
            auto negs = cneg.simplify(neg).simplify();
            cneg = cegis(negs);
            auto Q = (!cneg.run()).simplify();
            // Q is the strongest correct behavior preservant => i.e. whatever
            // path was previously correct with table_hit == tt, Q keeps it
            // alive
            // And it is strongest <=> it cuts down as many failures as
            // possible
            slv.add(Q);
            ofs << "necessary precondition: " << Q.simplify() << '\n';
            if (slv.check() == check_result::sat) {
              ofs << "Bad. Q is correct behavior preservant, but keeps "
                     "unwanted behaviors"
                  << '\n';
            } else {
              ofs << "Good. Q is correct behavior preservant and kills all "
                     "unwanted behaviors"
                  << '\n';
            }
          } else {
            ofs << "Bad. No Q is correct behavior preservant." << '\n';
            ofs << slv_forall << '\n';
          }
        }
          LOG1("table " << am->object->getName().name << " could go wrong");
          ofs.flush();
          return false;
        case check_result::unsat:
          ofs.flush();
          LOG1("table " << am->object->getName().name << " can never go wrong");
          return false;
        case check_result::unknown:
          BUG("unknown result ");
        }
        return false;
      }
    }
    return true;
  }
};

class ReachEquations : public Inspector {
  ReferenceMap *refMap;
  TypeMap *typeMap;
  z3::context *ctx;
  std::map<const IR::Statement *, z3::expr> pre;
  std::map<const IR::Statement *, z3::expr> post;
  std::map<cstring, z3::ast> vars;
  IRExprToSMT smtTransformer;

public:
  ReachEquations(ReferenceMap *refMap, TypeMap *typeMap, z3::context *ctx)
      : refMap(refMap), typeMap(typeMap), ctx(ctx),
        smtTransformer(refMap, typeMap, ctx, &vars) {}

  z3::expr find_reach_conditions(const IR::Statement *target,
                                 const IR::Statement *in) {
    pre.clear();
    post.clear();
    pre.emplace(target, ctx->bool_val(true));
    in->apply(*this);
    auto in_pre = get_pre(in);
    CHECK_NULL(in_pre);
    return *in_pre;
  }

  z3::expr
  find_reach_conditions(const std::vector<const IR::Statement *> &targets,
                        const IR::Statement *in) {
    pre.clear();
    post.clear();
    for (auto target : targets)
      pre.emplace(target, ctx->bool_val(true));
    in->apply(*this);
    auto in_pre = get_pre(in);
    CHECK_NULL(in_pre);
    return *in_pre;
  }

  const z3::expr *get(const IR::Statement *stat,
                      const std::map<const IR::Statement *, z3::expr> &dict) {
    auto maybe_post = dict.find(stat);
    const z3::expr *what = nullptr;
    if (maybe_post != dict.end()) {
      what = &(maybe_post->second);
    }
    return what;
  }
  const z3::expr *get_post(const IR::Statement *stat) {
    return get(stat, post);
  }
  const z3::expr *get_pre(const IR::Statement *stat) { return get(stat, pre); }

  z3::expr compute_pre(const IR::Statement *stat, const z3::expr *post) {
    z3::expr pre = *post;
    bool semaOrientation = false;
    if (auto mcs = stat->to<IR::MethodCallStatement>()) {
      auto mi = P4::MethodInstance::resolve(mcs->methodCall, refMap, typeMap);
      if (auto ef = mi->to<ExternFunction>()) {
        if (ef->method->name.name == "assume") {
          semaOrientation = true;
        }
      }
    }
    P4ToSmt sema(refMap, typeMap, ctx, &pre, semaOrientation);
    stat->apply(sema);
    return pre;
  }

  bool preorder(const IR::Statement *stat) override {
    auto my_post = get_post(stat);
    if (!my_post) {
      return false;
    } else {
      pre.emplace(stat, compute_pre(stat, my_post));
    }
    return false;
  }

  bool preorder(const IR::IfStatement *stat) override {
    const z3::expr *my_post = get_post(stat);
    if (my_post) {
      post.emplace(stat->ifTrue, *my_post);
      visit(stat->ifTrue);

      z3::expr pre_f = *my_post;
      if (stat->ifFalse) {
        post.emplace(stat->ifFalse, *my_post);
        visit(stat->ifFalse);
        pre_f = *get_pre(stat->ifFalse);
      }
      auto cd = smtTransformer.evaluate(stat->condition);
      pre.emplace(
          stat, ((*get_pre(stat->ifTrue) && cd) || (pre_f && !cd)).simplify());
    } else {
      visit(stat->ifTrue);
      const z3::expr *left = get_pre(stat->ifTrue);
      const z3::expr *right = nullptr;
      if (stat->ifFalse) {
        visit(stat->ifFalse);
        right = get_pre(stat->ifFalse);
      }
      if (!left && !right) {
        return false;
      } else {
        auto cd = smtTransformer.evaluate(stat->condition);
        if (left && !right) {
          pre.emplace(stat, *left && cd);
        } else if (right && !left) {
          pre.emplace(stat, *right && !cd);
        } else {
          pre.emplace(stat, (*left && cd) || (*right && !cd));
        }
      }
    }
    return false;
  }

  bool preorder(const IR::BlockStatement *stat) override {
    const z3::expr *what = get_post(stat);
    for (auto I = stat->components.rbegin(); I != stat->components.rend();
         ++I) {
      if (auto crt = (*I)->to<IR::Statement>()) {
        if (what) {
          post.emplace(crt, *what);
        }
        visit(crt);
        what = get_pre(crt);
      }
    }
    if (what)
      pre.emplace(stat, *what);
    return false;
  }
};

class ReachableBugs : public Inspector {
  ReferenceMap *refMap;
  TypeMap *typeMap;
  std::map<const IR::P4Control *, z3::solver *> *conditions;
  std::vector<const IR::Statement *> targets;
  const IR::P4Control *enclosingControl = nullptr;

public:
  ReachableBugs(ReferenceMap *refMap, TypeMap *typeMap,
                std::map<const IR::P4Control *, z3::solver *> *conditions)
      : refMap(refMap), typeMap(typeMap), conditions(conditions) {}

  bool preorder(const IR::P4Control *control) override {
    visit(control->body);
    return false;
  }

  z3::expr get_bug_condition(const IR::P4Control *control) {
    enclosingControl = control;
    auto &ctx = (*conditions)[control]->ctx();
    targets.clear();
    control->apply(*this);
    z3::expr quoi = ctx.bool_val(false);
    for (auto t : targets) {
      ReachEquations reachEquations(refMap, typeMap, &ctx);
      quoi = quoi || reachEquations.find_reach_conditions(t, control->body);
    }
    return quoi.simplify();
  }

  std::vector<const IR::Statement *> get_targets(const IR::P4Control *control) {
    targets.clear();
    control->apply(*this);
    return std::move(targets);
  }

  void postorder(const IR::MethodCallStatement *mcs) override {
    if (is_bug(mcs)) {
      targets.emplace_back(mcs);
    }
  }
};

inline std::set<const IR::Node *> next_join_point(const IR::Node *starting_from,
                                                  EdgeHolder *eh) {
  auto edgeIT = eh->find(starting_from);
  if (edgeIT == eh->end()) {
    return {starting_from};
  } else {
    auto &nexts = edgeIT->second;
    if (nexts.empty())
      return {starting_from};
    if (nexts.size() == 1) {
      return next_join_point(nexts[0].first, eh);
    } else {
      std::set<const IR::Node *> nodes;
      for (auto &x : nexts) {
        nodes.emplace(x.first);
      }
      return nodes;
    }
  }
}
}

#endif // P4C_SOVLER_H
