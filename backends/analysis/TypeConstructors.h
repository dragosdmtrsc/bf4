//
// Created by dragos on 13.06.2019.
//

#ifndef P4C_TYPECONSTRUCTORS_H
#define P4C_TYPECONSTRUCTORS_H

#include "ir/ir.h"
#include <common/resolveReferences/referenceMap.h>
#include <p4/parameterSubstitution.h>
#include <p4/typeChecking/typeSubstitution.h>
#include <p4/typeMap.h>

namespace analysis {

struct P4TypeInstance;
// represents a constructible node
// for each extern T<T1, ..., Tn> { ... T(p1, ... pm) ... } one
// P4NodeConstructor
// parms = { T1, ..., Tn }
// paramList = { p1, ..., pm }

// for each extern R method<T1, ..., Tn>(p1, ..., pm) one P4NodeConstructor
// parms = {T1, ..., Tn}
// paramList = { pi | type(pi) is type_extern }

// for each extern T<TT1, TT2, ..., TTp> {  ... T(pp1, pp2, ..., ppq) ...
// R method<T1, ..., Tn>(p1, ..., pm) ... },
// one P4NodeConstructor with type parameters = { TT1, TT2, ..., TTp }
// { T1, ..., Tn } and paramList = { pi | type(pi) is type_extern } \union
// { pp1, pp2, ..., ppq }

// custom P4NodeConstructor:
// takes a base node of whatever kind such that:
// parmList and parms MUST be specified. This is sort of a function
// Mind you, all params in the paramList MUST be of type_extern
struct P4NodeConstructor {
  P4NodeConstructor *parent = nullptr;
  const IR::Node *base;
  const IR::TypeParameters *parms;
  const IR::ParameterList *paramList;

  P4NodeConstructor(const IR::Node *type, const IR::TypeParameters *parms,
                    const IR::ParameterList *paramList);
  P4NodeConstructor *operator()(
      P4::TypeVariableSubstitution typeVariableSubstitution,
      std::map<cstring, const IR::CompileTimeValue *> parameterSubstitution);
};

// Invariants: Must have the same signatures as
class SafeSubstitutions {
  // means: I can safely unify c1 with c2
  bool operator()(const P4NodeConstructor &c1, const P4NodeConstructor &c2);
};
}

#endif // P4C_TYPECONSTRUCTORS_H
