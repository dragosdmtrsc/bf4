//
// Created by dragos on 06.05.2019.
//

#include <p4/evaluator/substituteParameters.h>
#include "InlineActionsInControls.h"

void P4::DiscoverActionsControlInlining::postorder(const IR::MethodCallStatement *mcs) {
  auto mi = P4::MethodInstance::resolve(mcs, refMap, typeMap);
  CHECK_NULL(mi);
  auto ac = mi->to<P4::ActionCall>();
  if (ac == nullptr)
    return;
  auto caller = findContext<IR::P4Control>();
  if (caller == nullptr) {
    if (findContext<IR::P4Parser>() != nullptr) {
      ::error(ErrorType::ERR_UNSUPPORTED, "action invocation in parser", mcs);
    } else if (findContext<IR::P4Action>() == nullptr) {
      BUG("%1%: unexpected action invocation", mcs);
    }
    return;
  }

  auto aci = new ActionControlCallInfo(caller, ac->action, mcs);
  toInline->add(aci);
}

Visitor::profile_t P4::ActionsControlInliner::init_apply(const IR::Node *node) {
  P4::ResolveReferences solver(refMap, true);
  node->apply(solver);
  LOG2("ActionsInliner " << toInline);
  return Transform::init_apply(node);
}

const IR::Node *P4::ActionsControlInliner::preorder(IR::P4Control *action) {
  if (toInline->sites.count(getOriginal<IR::P4Control>()) == 0)
    prune();
  replMap = &toInline->sites[getOriginal<IR::P4Control>()];
  LOG2("Visiting: " << getOriginal());
  return action;
}

const IR::Node *P4::ActionsControlInliner::postorder(IR::P4Control *action) {
  if (toInline->sites.count(getOriginal<IR::P4Control>()) > 0)
    list->replace(getOriginal<IR::P4Control>(), action);
  replMap = nullptr;
  return action;
}

const IR::Node *P4::ActionsControlInliner::preorder(IR::MethodCallStatement *statement) {
  auto orig = getOriginal<IR::MethodCallStatement>();
  LOG2("Visiting " << orig);
  if (replMap == nullptr)
    return statement;

  auto callee = get(*replMap, orig)->to<IR::P4Action>();
  if (callee == nullptr)
    return statement;

  LOG2("Inlining: " << callee);
  IR::IndexedVector<IR::StatOrDecl> body;
  ParameterSubstitution subst;
  TypeVariableSubstitution tvs;  // empty

  std::map<const IR::Parameter*, cstring> paramRename;
  ParameterSubstitution substitution;
  substitution.populate(callee->parameters, statement->methodCall->arguments);

  // evaluate in and inout parameters in order
  for (auto param : callee->parameters->parameters) {
    auto argument = substitution.lookup(param);
    cstring newName = refMap->newName(param->name);
    paramRename.emplace(param, newName);
    if (param->direction == IR::Direction::In || param->direction == IR::Direction::InOut) {
      auto vardecl = new IR::Declaration_Variable(newName, param->annotations,
                                                  param->type, argument->expression);
      body.push_back(vardecl);
      subst.add(param, new IR::Argument(
        argument->srcInfo, argument->name, new IR::PathExpression(newName)));
    } else if (param->direction == IR::Direction::None) {
      // This works because there can be no side-effects in the evaluation of this
      // argument.
      subst.add(param, argument);
    } else if (param->direction == IR::Direction::Out) {
      // uninitialized variable
      auto vardecl = new IR::Declaration_Variable(newName,
                                                  param->annotations, param->type);
      subst.add(param, new IR::Argument(
        argument->srcInfo, argument->name, new IR::PathExpression(newName)));
      body.push_back(vardecl);
    }
  }

  SubstituteParameters sp(refMap, &subst, &tvs);
  auto clone = callee->apply(sp);
  if (::errorCount() > 0)
    return statement;
  CHECK_NULL(clone);
  BUG_CHECK(clone->is<IR::P4Action>(), "%1%: not an action", clone);
  auto actclone = clone->to<IR::P4Action>();
  body.append(actclone->body->components);

  // copy out and inout parameters
  for (auto param : callee->parameters->parameters) {
    auto left = substitution.lookup(param);
    if (param->direction == IR::Direction::InOut || param->direction == IR::Direction::Out) {
      cstring newName = ::get(paramRename, param);
      auto right = new IR::PathExpression(newName);
      auto copyout = new IR::AssignmentStatement(left->expression, right);
      body.push_back(copyout);
    }
  }

  auto annotations = callee->annotations->where(
    [](const IR::Annotation* a) { return a->name != IR::Annotation::nameAnnotation; });
  auto result = new IR::BlockStatement(statement->srcInfo, annotations, body);
  LOG2("Replacing " << orig << " with " << result);
  return result;
}
