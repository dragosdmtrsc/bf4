//
// Created by dragos on 13.06.2019.
//

#include "TypeConstructors.h"
#include <p4/typeChecking/typeSubstitutionVisitor.h>

namespace analysis {
class ReplaceParms : public Transform {
  std::map<cstring, const IR::CompileTimeValue *> &parameterSubstitution;
public:
  ReplaceParms(
      std::map<cstring, const IR::CompileTimeValue *> &parameterSubstitution)
      : parameterSubstitution(parameterSubstitution) {}
  const IR::Node *postorder(IR::PathExpression *p) override {
    auto I = parameterSubstitution.find(p->path->name);
    if (I->second->is<IR::Literal>()) {
      return I->second->to<IR::Literal>();
    }
    return p;
  }
};
}

analysis::P4NodeConstructor::P4NodeConstructor(
    const IR::Node *type, const IR::TypeParameters *parms,
    const IR::ParameterList *paramList)
    : base(type), parms(parms), paramList(paramList) {}

analysis::P4NodeConstructor *analysis::P4NodeConstructor::operator()(
    P4::TypeVariableSubstitution typeVariableSubstitution,
    std::map<cstring, const IR::CompileTimeValue *> parameterSubstitution) {
  auto newparms = parms->clone();
  P4::TypeVariableSubstitutionVisitor typeVariableSubstitutionVisitor(
      &typeVariableSubstitution, true);
  auto newbase = base->apply(typeVariableSubstitutionVisitor);
  bool change = false;
  if (newbase != base)
    change = true;
  for (auto p : parms->parameters) {
    if (typeVariableSubstitution.containsKey(p)) {
      newparms->parameters.removeByName(p->name);
    }
  }
  change = change || (*newparms) != (*parms);
  ReplaceParms replaceParms(parameterSubstitution);
  newbase = newbase->apply(replaceParms);
  change = change || newbase != base;
  auto newctparams = paramList->clone();
  for (auto p : parameterSubstitution) {
    if (newctparams->getDeclByName(p.first))
      newctparams->parameters.removeByName(p.first);
  }
  change = change || (*newctparams) != (*paramList);
  if (!change) return this;
  auto instantiated = new P4NodeConstructor(newbase, newparms, newctparams);
  instantiated->parent = this;
  return instantiated;
}