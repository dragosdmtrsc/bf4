//
// Created by a-drdum on 6/22/2019.
//

#ifndef P4C_VTYPECONSTRAINTS_H
#define P4C_VTYPECONSTRAINTS_H

#include <sstream>
#include "ir/ir.h"
#include "vTypeUnification.h"
#include "frontends/p4/typeChecking/typeSubstitution.h"
#include "frontends/p4/typeChecking/typeSubstitutionVisitor.h"

namespace analysis {
  using namespace P4;
  // A list of equality constraints on types.
  class TypeConstraints final {
    /// Requires two types to be equal.
    class EqualityConstraint : public IHasDbPrint {
    public:
      const IR::Type* left;
      const IR::Type* right;
      /// Constraint which produced this one.  May be nullptr.
      const EqualityConstraint* derivedFrom;
      EqualityConstraint(const IR::Type* left, const IR::Type* right,
                         EqualityConstraint* derivedFrom)
        : left(left), right(right), derivedFrom(derivedFrom) {
        CHECK_NULL(left); CHECK_NULL(right);
        if (left->is<IR::Type_Name>() || right->is<IR::Type_Name>())
          BUG("Unifying type names %1% and %2%", left, right);
        LOG3(this);
      }
      void dbprint(std::ostream& out) const override
      { out << "Constraint:" << dbp(left) << " = " << dbp(right); }
    };

  private:
    /*
     * Not all type variables that appear in unification can be bound:
     * only the ones in this set can be.
     *
     * Consider this example:
     *
     * extern void f(in bit x);
     * control p<T>(T data) { f(data); }
     *
     * This example should not typecheck: because T cannot be constrained in the invocation of f.
     * While typechecking the f(data) call, T is not a type variable that can be unified.
     */
    std::set<const IR::ITypeVar*> unifiableTypeVariables;
    std::vector<EqualityConstraint*> constraints;
    TypeUnification *unification;
    const TypeVariableSubstitution* definedVariables;

  public:
    TypeVariableSubstitutionVisitor replaceVariables;

    explicit TypeConstraints(const TypeVariableSubstitution* definedVariables) :
      unification(new TypeUnification(this)), definedVariables(definedVariables),
      replaceVariables(definedVariables) {}

    // Mark this variable as being free.
    void addUnifiableTypeVariable(const IR::ITypeVar* typeVariable)
    { unifiableTypeVariables.insert(typeVariable); }

    /// True if type is a type variable that can be unified.
    /// A variable is unifiable if it is marked so and it not already
    /// part of definedVariables.
    bool isUnifiableTypeVariable(const IR::Type* type);
    void addEqualityConstraint(
      const IR::Type* left, const IR::Type* right, EqualityConstraint* derivedFrom = nullptr);

    /*
     * Solve the specified constraint.
     * @param root       Element where error is signalled if necessary.
     * @param subst      Variable substitution which is updated with new constraints.
     * @param constraint Constraint to solve.
     * @return           True on success.
     */
    bool solve(const IR::Node* root, EqualityConstraint *constraint,
               TypeVariableSubstitution *subst);
    TypeVariableSubstitution* solve(const IR::Node* root);
    void dbprint(std::ostream& out) const;
  };
}


#endif //P4C_VTYPECONSTRAINTS_H
