//
// Created by dragos on 11.06.2019.
//

#ifndef P4C_INTERPRETER_H
#define P4C_INTERPRETER_H

#include "cfg_algos.h"
#include <p4/parameterSubstitution.h>

#include <utility>

namespace analysis {

class ImplementationInfo {
  std::map<const IR::Node *, const IR::Node *> implMap;
};

class DynamicTypeHolder : public Inspector {
  P4::ReferenceMap *refMap;
  std::map<const IR::Expression *, const IR::Type *> typeMap;

  const IR::Type *declaredType(const IR::IDeclaration *decl);

  const IR::Type *solve(const IR::Type *t);

  void postorder(const IR::PathExpression *pe) override;
  void postorder(const IR::Member *mem) override;

public:
  DynamicTypeHolder(ReferenceMap *refMap) : refMap(refMap) {}

  const IR::Type *getType(const IR::Expression *expr, bool notNull = true);
  const IR::IFunctional *getMethod(const IR::Expression *method,
                                   const IR::Vector<IR::Argument> *arguments);
};


// initially: contains all user declared implementations
// fills in on the fly with good information about implementations

struct ctx {
  P4::ReferenceMap refMap;
  CFGs cfgs;
  DynamicTypeHolder dynamicTypeHolder;
  const IR::P4Program *prog;
  ctx();
};

class Interpreter {
  const IR::P4Program *program;
  ctx cctx;
  void init();

public:
  Interpreter(const IR::P4Program *program);
  void build_cfgs();
};
}

#endif // P4C_INTERPRETER_H
