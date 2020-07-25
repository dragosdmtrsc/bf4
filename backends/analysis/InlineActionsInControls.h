//
// Created by dragos on 06.05.2019.
//

#ifndef P4C_INLINEACTIONSINCONTROLS_H
#define P4C_INLINEACTIONSINCONTROLS_H

#include "vTypeChecker.h"
#include <common/resolveReferences/referenceMap.h>
#include <p4/commonInlining.h>
#include <p4/typeChecking/typeChecker.h>
#include <p4/typeMap.h>
#include <p4/unusedDeclarations.h>

namespace P4 {

typedef SimpleCallInfo<IR::Node, IR::MethodCallStatement> ActionControlCallInfo;
typedef SimpleInlineWorkList<IR::Node, IR::MethodCallStatement,
                             ActionControlCallInfo>
    AControlInlineWorkList;
typedef SimpleInlineList<IR::Node, ActionControlCallInfo,
                         AControlInlineWorkList>
    ActionsControlInlineList;

class DiscoverActionsControlInlining : public Inspector {
  ActionsControlInlineList *toInline; // output
  P4::ReferenceMap *refMap;           // input
  P4::TypeMap *typeMap;               // input
public:
  DiscoverActionsControlInlining(ActionsControlInlineList *toInline,
                                 P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
      : toInline(toInline), refMap(refMap), typeMap(typeMap) {
    CHECK_NULL(toInline);
    CHECK_NULL(refMap);
    CHECK_NULL(typeMap);
    setName("DiscoverActionsInlining");
  }
  bool preorder(const IR::P4Parser *) override { return false; } // skip
  void postorder(const IR::MethodCallStatement *mcs) override;
};

// General-purpose actions inliner.
class ActionsControlInliner
    : public AbstractInliner<ActionsControlInlineList, AControlInlineWorkList> {
  P4::ReferenceMap *refMap;
  std::map<const IR::MethodCallStatement *, const IR::Node *> *replMap;

public:
  explicit ActionsControlInliner(bool isv1)
      : refMap(new P4::ReferenceMap()), replMap(nullptr) {
    refMap->setIsV1(isv1);
  }
  Visitor::profile_t init_apply(const IR::Node *node) override;
  const IR::Node *preorder(IR::P4Parser *cont) override {
    prune();
    return cont;
  } // skip
  const IR::Node *preorder(IR::P4Control *action) override;
  const IR::Node *postorder(IR::P4Control *action) override;
  const IR::Node *preorder(IR::MethodCallStatement *statement) override;
};

typedef InlineDriver<ActionsControlInlineList, AControlInlineWorkList>
    InlineActionsControlDriver;

class InlineActionsInControls : public PassManager {
  ActionsControlInlineList actionsToInline;

public:
  InlineActionsInControls(ReferenceMap *refMap, TypeMap *typeMap) {
    passes.push_back(new P4::TypeChecking(refMap, typeMap));
    passes.push_back(
        new DiscoverActionsControlInlining(&actionsToInline, refMap, typeMap));
    passes.push_back(new InlineActionsControlDriver(
        &actionsToInline, new ActionsControlInliner(refMap->isV1())));
    passes.push_back(new RemoveAllUnusedDeclarations(refMap));
    addPasses({new P4::ResolveReferences(refMap),
               new P4::TypeInference(refMap, typeMap, false),
               new ApplyTypesToExpressions(typeMap),
               new P4::ResolveReferences(refMap)});
    setName("InlineActions");
  }
};

} // namespace P4

#endif // P4C_INLINEACTIONSINCONTROLS_H
