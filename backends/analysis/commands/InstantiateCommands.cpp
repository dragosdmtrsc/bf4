//
// Created by dragos on 01.07.2019.
//

#include "InstantiateCommands.h"
#include <analysis/InlineActionsInControls.h>
#include <common/resolveReferences/resolveReferences.h>
#include <p4/actionsInlining.h>
#include <p4/inlining.h>
#include <p4/simplifyDefUse.h>
#include <p4/tableApply.h>
#include <p4/typeChecking/typeChecker.h>
#include <p4/unusedDeclarations.h>

namespace analysis {
class ControlPlaneInterface {
  P4::ReferenceMap *refMap;
  std::map<const IR::P4Table *, std::map<cstring, const IR::P4Action *>>
      actions;
  std::map<const IR::P4Table *, const IR::P4Action *> default_only;
  std::map<const IR::P4Table *, cstring> implementation_map;

public:
  ControlPlaneInterface(P4::ReferenceMap *refMap) : refMap(refMap) {}
  void clear() {
    actions.clear();
    default_only.clear();
    implementation_map.clear();
  }
  cstring implementation(const IR::P4Table *table) {
    auto I = implementation_map.find(table);
    if (I != implementation_map.end()) {
      return I->second;
    }
    auto impl = table->properties->getProperty("implementation");
    if (impl) {

      if (impl->value->is<IR::ExpressionValue>()) {
        auto pv = impl->value->to<IR::ExpressionValue>();
        if (pv && pv->expression->is<IR::PathExpression>()) {
          auto path = pv->expression->to<IR::PathExpression>()->path;
          auto decl = refMap->getDeclaration(path);
          return decl->controlPlaneName("");
        }
      }
    }
    return "";
  }
  const IR::P4Action *findAction(const IR::P4Table *table, cstring cpname) {
    auto &crt = actions[table];
    auto emi = crt.emplace(cpname, nullptr);
    if (emi.second) {
      for (auto ale : table->getActionList()->actionList) {
        auto decl = refMap->getDeclaration(ale->getPath())->to<IR::P4Action>();
        if (decl->controlPlaneName("") == cpname) {
          emi.first->second = decl;
        }
      }
    }
    return emi.first->second;
  }
  const IR::P4Action *defaultOnly(const IR::P4Table *table) {
    auto &crt = default_only[table];
    if (!crt) {
      for (auto ale : table->getActionList()->actionList) {
        if (ale->getAnnotation("defaultonly")) {
          auto decl =
              refMap->getDeclaration(ale->getPath())->to<IR::P4Action>();
          return (crt = decl);
        }
      }
    }
    return crt;
  }
};

const std::vector<ActionProfileAdd *> *
detail_action_profile(ControlPlaneInterface &cpi, const IR::P4Table *tab,
                      Commands &commands) {
  auto impl = cpi.implementation(tab);
  if (impl) {
    return &commands.profileMembers(impl);
  }
  return nullptr;
}

template <typename Variant>
std::vector<const ActionCall *>
get_actions(ControlPlaneInterface &cpi, const IR::P4Table *tab,
            Commands &commands, const Variant &v) {
  std::vector<const ActionCall *> tentative_calls;
  auto profile_entries = detail_action_profile(cpi, tab, commands);
  if (v.type() == typeid(ActionCall)) {
    auto &acall = boost::get<ActionCall>(v);
    tentative_calls.emplace_back(&acall);
  } else if (v.type() == typeid(Member)) {
    auto &memcall = boost::get<Member>(v);
    if (profile_entries) {
      auto ent = profile_entries->operator[](memcall.member);
      tentative_calls.emplace_back(&ent->action);
    }
  }
  return tentative_calls;
}

class FindReferredActions : public Inspector {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  analysis::Commands &commands;
  std::set<const IR::P4Action *> &actions;
  ControlPlaneInterface &cpi;

public:
  FindReferredActions(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                      Commands &commands,
                      std::set<const IR::P4Action *> &actions,
                      ControlPlaneInterface &cpi)
      : refMap(refMap), typeMap(typeMap), commands(commands), actions(actions),
        cpi(cpi) {}

public:

  void postorder(const IR::MethodCallStatement *mcs) override {
    auto mi = P4::MethodInstance::resolve(mcs, refMap, typeMap);
    if (auto acall = mi->to<P4::ActionCall>()) {
      auto ctxt = findContext<IR::P4Table>();
      if (!ctxt) {
        actions.emplace(acall->action);
      }
    }
  }

  void postorder(const IR::P4Table *tab) override {
    auto tn = tab->controlPlaneName("");
    auto &entries = commands.tableEntries(tn);
    auto profile_entries = detail_action_profile(cpi, tab, commands);
    auto def = commands.defaultAction(tn);
    bool useful = def != nullptr || !entries.empty();
    if (useful) {
      LOG4("useful table  " << tab->name.name << ' ' << tn);
      if (def)
        handleEntry(tab, profile_entries, def->action);
      for (auto &e : entries) {
        handleEntry(tab, profile_entries, e->action);
      }
    } else {
      LOG4("useless table  " << tab->name.name << " " << tn
                             << " which has no control plane entry");
      for (auto ale : tab->getActionList()->actionList) {
        auto decl = refMap->getDeclaration(ale->getPath())->to<IR::P4Action>();
        actions.emplace(decl);
      }
    }
  }

  template <typename Variant>
  void handleEntry(const IR::P4Table *tab,
                   const std::vector<ActionProfileAdd *> *profile_entries,
                   const Variant &v) const {
    LOG3("in table " << tab->name.name);
    std::vector<const ActionCall *> tentative_calls;
    if (v.type() == typeid(ActionCall)) {
      auto &acall = boost::get<ActionCall>(v);
      tentative_calls.emplace_back(&acall);
    } else if (v.type() == typeid(Member)) {
      auto &memcall = boost::get<Member>(v);
      if (profile_entries) {
        LOG3("got member " << memcall.member);
        auto ent = profile_entries->operator[](memcall.member);
        tentative_calls.emplace_back(&ent->action);
      }
    }
    for (auto acall : tentative_calls) {
      if (acall->actName == ActionCall::EMPTY) {
        actions.emplace(cpi.defaultOnly(tab));
      } else {
        actions.emplace(cpi.findAction(tab, acall->actName));
      }
    }
  }
};

class RemoveUnusedActions : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  analysis::Commands &commands;
  std::set<const IR::P4Action *> &actions;
  ControlPlaneInterface &cpi;

public:
  RemoveUnusedActions(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                      Commands &commands,
                      std::set<const IR::P4Action *> &actions,
                      ControlPlaneInterface &cpi)
      : refMap(refMap), typeMap(typeMap), commands(commands), actions(actions),
        cpi(cpi) {}

  const IR::Node *postorder(IR::SwitchCase *sc) override {
    auto ss = findOrigCtxt<IR::SwitchStatement>();
    if (!sc->label->is<IR::PathExpression>()) {
      return sc;
    }
    auto pe = sc->label->to<IR::PathExpression>();
    auto tab =
        P4::TableApplySolver::isActionRun(ss->expression, refMap, typeMap);
    auto act = tab->getActionList()->getDeclaration(pe->path->name);
    auto decl = refMap->getDeclaration(act->getPath())->to<IR::P4Action>();
    if (!actions.count(decl))
      return nullptr;
    return sc;
  }

  const IR::Node *postorder(IR::Property *prop) override {
    if (prop->name == IR::TableProperties::defaultActionPropertyName) {
      auto tab = findOrigCtxt<IR::P4Table>();
      if (tab) {
        auto def = commands.defaultAction(tab->controlPlaneName(""));
        if (def) {
          auto acts = get_actions(cpi, tab, commands, def->action);
          for (auto act : acts) {
            auto &acall = *act;
            if (acall.actName != ActionCall::EMPTY) {
              LOG4("at table " << tab->name.name << "got default action "
                               << acall);
              auto args = new IR::Vector<IR::Argument>;
              for (auto &arg : acall.args) {
                auto constant = new IR::Constant(arg);
                args->emplace_back(constant);
              }
              prop->value = new IR::ExpressionValue(
                  tab->srcInfo,
                  new IR::MethodCallExpression(
                      tab->srcInfo,
                      new IR::PathExpression(
                          tab->srcInfo,
                          new IR::Path(
                              tab->srcInfo,
                              IR::ID(
                                  tab->srcInfo,
                                  cpi.findAction(tab, acall.actName)->name))),
                      args));
            }
          }
        }
      }
    }
    return prop;
  }
  const IR::Node *postorder(IR::P4Action *act) override {
    if (!actions.count(getOriginal<IR::P4Action>())) {
      return nullptr;
    }
    return act;
  }
  const IR::Node *postorder(IR::ActionListElement *ale) override {
    auto ref = refMap->getDeclaration(ale->getPath())->to<IR::P4Action>();
    if (!actions.count(ref))
      return nullptr;
    return ale;
  }
};

const IR::MethodCallStatement *getMethodCall(IR::SwitchStatement *ss) {
  auto expr = ss->expression->to<IR::Member>();
  if (expr && expr->member == IR::Type_Table::action_run) {
    auto body = expr->expr->to<IR::MethodCallExpression>();
    return new IR::MethodCallStatement(ss->srcInfo, body);
  }
  return nullptr;
}

class RemoveEmptySwitchStatements : public Transform {

public:
  const IR::Node *postorder(IR::SwitchStatement *ss) override {
    if (ss->cases.empty()) {
      if (auto mcs = analysis::getMethodCall(ss)) {
        LOG4("chopping simple switch statement: " << ss);
        return mcs;
      }
    } else if (ss->cases.size() == 1) {
      auto mcs = analysis::getMethodCall(ss);
      if (mcs) {
        auto the_case = ss->cases.at(0);
        if (the_case->label->is<IR::DefaultExpression>()) {
          auto ctx = findContext<IR::Statement>();
          auto ivec =
              new IR::IndexedVector<IR::StatOrDecl>({mcs, the_case->statement});
          LOG4("chopping simple switch statement: "
               << ss << " -> " << new IR::BlockStatement(*ivec));
          if (ctx->is<IR::BlockStatement>()) {
            return ivec;
          } else {
            return new IR::BlockStatement(*ivec);
          }
        }
      }
    }
    return ss;
  }
};

class TableHelperMixIn {
  Commands &commands;
  ControlPlaneInterface &cpi;

public:
  TableHelperMixIn(Commands &commands, ControlPlaneInterface &cpi)
      : commands(commands), cpi(cpi) {}
  const ActionCall *defaultOnly(const IR::P4Table *table) {
    auto cpname = table->controlPlaneName("");
    auto &entries = commands.tableEntries(cpname);
    if (entries.empty()) {
      auto def = commands.defaultAction(cpname);
      if (!def) return nullptr;
      auto acts = get_actions(cpi, table, commands, def->action);
      return *acts.begin();
    }
    return nullptr;
  }
};

class RemoveDefaultOnlyTables : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  Commands &commands;
  ControlPlaneInterface &cpi;
  TableHelperMixIn tableHelper;

public:
  RemoveDefaultOnlyTables(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                          Commands &commands, ControlPlaneInterface &cpi)
      : refMap(refMap), typeMap(typeMap), commands(commands), cpi(cpi),
        tableHelper(commands, cpi) {}

public:
  const IR::Node *postorder(IR::IfStatement *stat) override {
    if (auto tab =
            P4::TableApplySolver::isHit(stat->condition, refMap, typeMap)) {
      if (tableHelper.defaultOnly(tab)) {
        LOG4("chopping if hit statement: " << stat);
        return stat->ifFalse;
      }
    }
    return stat;
  }
  const IR::Node *postorder(IR::AssignmentStatement *stat) override {
    if (auto tab =
      P4::TableApplySolver::isHit(stat->right, refMap, typeMap)) {
      if (tableHelper.defaultOnly(tab)) {
        LOG4("chopping hit asg: " << stat);
        stat->right = new IR::BoolLiteral(false);
      }
    }
    return stat;
  }
  const IR::Node *postorder(IR::SwitchStatement *ss) override {
    if (auto tab = P4::TableApplySolver::isActionRun(ss->expression, refMap,
                                                     typeMap)) {
      if (auto entry = tableHelper.defaultOnly(tab)) {
        LOG4("chopping action_run asg: " << ss);
        const IR::SwitchCase *def = nullptr;
        const IR::SwitchCase *useful = nullptr;
        for (auto cs : ss->cases) {
          if (cs->label->is<IR::PathExpression>()) {
            auto ale = tab->getActionList()->getDeclaration(
                cs->label->to<IR::PathExpression>()->path->name);
            auto act =
                refMap->getDeclaration(ale->getPath())->to<IR::P4Action>();
            if (act->controlPlaneName("") == entry->actName) {
              useful = cs;
            }
          } else if (cs->label->is<IR::DefaultExpression>()) {
            def = cs;
          }
        }
        if (!def) {
          // assume that the default action in a switch statement
          // is a no-op
          def = new IR::SwitchCase(new IR::DefaultExpression, nullptr);
        }
        auto ivec = new IR::IndexedVector<IR::StatOrDecl>();
        auto the_one = def;
        if (useful)
          the_one = useful;
        auto mcs = analysis::getMethodCall(ss);
        auto stat = the_one->statement;
        ivec->push_back(mcs);
        if (stat)
          ivec->push_back(stat);
        auto ctx = findContext<IR::Statement>();
        LOG4("chopping switch statement: " << ss << " -> "
                                           << new IR::BlockStatement(*ivec));
        if (ctx->is<IR::BlockStatement>()) {
          return ivec;
        } else {
          return new IR::BlockStatement(*ivec);
        }
      }
    }
    return ss;
  }
};

class RemoveSimpleTableApply : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  Commands &commands;
  ControlPlaneInterface &cpi;
  TableHelperMixIn tableHelper;

public:
  RemoveSimpleTableApply(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                         Commands &commands, ControlPlaneInterface &cpi)
      : refMap(refMap), typeMap(typeMap), commands(commands), cpi(cpi),
        tableHelper(commands, cpi) {}

public:
  const IR::Node *postorder(IR::MethodCallStatement *mcs) override {
    auto mi = P4::MethodInstance::resolve(mcs, refMap, typeMap);
    if (auto am = mi->to<P4::ApplyMethod>()) {
      if (am->isTableApply()) {
        auto tab = am->object->to<IR::P4Table>();
        if (tableHelper.defaultOnly(tab)) {
          auto default_act = tab->getDefaultAction();
          if (default_act->is<IR::MethodCallExpression>()) {
            LOG4("chopping table apply: " << mcs);
            return new IR::MethodCallStatement(
                mcs->srcInfo, default_act->to<IR::MethodCallExpression>());
          }
        }
      }
    }
    return mcs;
  }
};

class RemoveUseless : public Transform {
  bool emptyStatement(const IR::Statement *stat) {
    if (!stat) return true;
    if (stat->is<IR::BlockStatement>()) {
      auto bs = stat->to<IR::BlockStatement>();
      return std::all_of(bs->components.begin(), bs->components.end(),
                         [this](const IR::StatOrDecl *s) {
                           return s->is<IR::Statement>() &&
                                  emptyStatement(s->to<IR::Statement>());
                         });
    } else if (stat->is<IR::IfStatement>()) {
      auto ifs = stat->to<IR::IfStatement>();
      return emptyStatement(ifs->ifTrue) && emptyStatement(ifs->ifFalse);
    } else if (stat->is<IR::SwitchStatement>()) {
      auto ss = stat->to<IR::SwitchStatement>();
      return std::all_of(ss->cases.begin(), ss->cases.end(),
                         [this](const IR::SwitchCase *sc) {
                           return emptyStatement(sc->statement);
                         });
    } else if (stat->is<IR::EmptyStatement>()) {
      return true;
    }
    return false;
  }
  bool canKill(const IR::Statement *orig) {
    auto ifs = findContext<IR::Statement>();
    if (!ifs)
      return false;
    if (!ifs->is<IR::IfStatement>())
      return true;
    return ifs->to<IR::IfStatement>()->ifTrue != orig;
  }
  const IR::Node *preorder(IR::P4Action *a) override {
    prune();
    return a;
  }
  const IR::Node *preorder(IR::Function *f) override {
    prune();
    return f;
  }
  const IR::Node *preorder(IR::P4Parser *p) override {
    prune();
    return p;
  }

  const IR::Node *preorder(IR::IfStatement *stat) override {
    if (emptyStatement(stat)) {
      prune();
      return nullptr;
    }
    return stat;
  }

  const IR::Node *preorder(IR::BlockStatement *stat) override {
    if (canKill(getOriginal<IR::Statement>()) && emptyStatement(stat)) {
      prune();
      return nullptr;
    }
    return stat;
  }
  const IR::Node *preorder(IR::EmptyStatement *stat) override {
    if (canKill(getOriginal<IR::EmptyStatement>())) {
      return nullptr;
    }
    return stat;
  }
  const IR::Node *preorder(IR::SwitchStatement *ss) override {
    if (emptyStatement(ss)) {
      auto mcs = getMethodCall(ss);
      return mcs;
    }
    return ss;
  }
};
class PullBlockStatements : public Transform {
  const IR::Node *postorder(IR::BlockStatement *stat) override {
    auto ctx = getContext();
    if (ctx->node->is<IR::BlockStatement>()) {
      return stat->components.clone();
    }
    return stat;
  }
};
}

analysis::InstantiateCommands::InstantiateCommands(P4::ReferenceMap *refMap,
                                                   P4::TypeMap *typeMap,
                                                   analysis::Commands &commands)
    : refMap(refMap), typeMap(typeMap), commands(commands) {
  auto cpi = new ControlPlaneInterface(refMap);
  passes.push_back(
      new FindReferredActions(refMap, typeMap, commands, actions, *cpi));
  passes.push_back(
      new RemoveUnusedActions(refMap, typeMap, commands, actions, *cpi));
  passes.push_back(new RemoveEmptySwitchStatements);
  addPasses({new P4::ResolveReferences(refMap),
             new P4::TypeInference(refMap, typeMap, false),
             new P4::ApplyTypesToExpressions(typeMap),
             new P4::ResolveReferences(refMap)});
  passes.push_back(new VisitFunctor([cpi]() { cpi->clear(); }));
  passes.push_back(
      new RemoveDefaultOnlyTables(refMap, typeMap, commands, *cpi));
  passes.push_back(new RemoveSimpleTableApply(refMap, typeMap, commands, *cpi));
  addPasses({new P4::ResolveReferences(refMap),
             new P4::TypeInference(refMap, typeMap, false),
             new P4::ApplyTypesToExpressions(typeMap),
             new P4::ResolveReferences(refMap)});
  passes.push_back(new P4::RemoveAllUnusedDeclarations(refMap, false));
  passes.push_back(new P4::ResolveReferences(refMap));
  auto evaluator = new P4::EvaluatorPass(refMap, typeMap);
  passes.push_back(evaluator);
  passes.push_back(new P4::Inline(refMap, typeMap, evaluator));
  passes.push_back(new P4::InlineActions(refMap, typeMap));
  passes.push_back(new P4::InlineActionsInControls(refMap, typeMap));
  passes.push_back(new RemoveUseless);
  passes.push_back(new PassRepeated({new PullBlockStatements}));
  passes.push_back(evaluator);
}
