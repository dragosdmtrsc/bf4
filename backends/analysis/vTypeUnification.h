//
// Created by a-drdum on 6/22/2019.
//

#ifndef P4C_VTYPEUNIFICATION_H
#define P4C_VTYPEUNIFICATION_H

#include "ir/ir.h"

namespace analysis {
  class TypeConstraints;
/**
Hindley-Milner type unification algorithm
(See for example, http://cs.brown.edu/~sk/Publications/Books/ProgLangs/2007-04-26/plai-2007-04-26.pdf, page 280.)
Attempts to unify two types.  As a consequence it generates constraints on other sub-types.
Constraints are solved at the end.
Solving a constraint generates type-variable substitutions
(where a type variable is replaced with another type - which could still contain type variables inside).
All substitutions are composed together.
Constraint solving can fail, which means that the program does not type-check.
*/
  class TypeUnification final {
    TypeConstraints*  constraints;

    bool unifyCall(const IR::Node* errorPosition,
                   const IR::Type_MethodBase* dest,
                   const IR::Type_MethodCall* src,
                   bool reportErrors);
    bool unifyFunctions(const IR::Node* errorPosition,
                        const IR::Type_MethodBase* dest,
                        const IR::Type_MethodBase* src,
                        bool reportErrors,
                        bool skipReturnValues = false);
    bool unifyBlocks(const IR::Node* errorPosition,
                     const IR::Type_ArchBlock* dest,
                     const IR::Type_ArchBlock* src,
                     bool reportErrors);

  public:
    explicit TypeUnification(TypeConstraints* constraints) : constraints(constraints) {}
    /**
     * Return false if unification fails right away.
     * Generates a set of type constraints.
     * If it returns true unification could still fail later.
     * @param dest         Destination type.
     * @param src          Source type.
     * @param reportErrors If true report errors caused by unification.
     * @return     False if unification fails immediately.
     */
    bool unify(const IR::Node* errorPosition, const IR::Type* dest,
               const IR::Type* src, bool reportErrors);
  };
}


#endif //P4C_VTYPEUNIFICATION_H
