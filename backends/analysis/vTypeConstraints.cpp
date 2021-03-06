//
// Created by a-drdum on 6/22/2019.
//

#include "vTypeConstraints.h"
#include "vTypeUnification.h"

namespace analysis {
  using namespace P4;
  void TypeConstraints::addEqualityConstraint(
    const IR::Type* left, const IR::Type* right, EqualityConstraint* derivedFrom) {
    auto c = new EqualityConstraint(left, right, derivedFrom);
    constraints.push_back(c);
  }

  TypeVariableSubstitution* TypeConstraints::solve(const IR::Node* root) {
    LOG3("Solving constraints:\n" << *this);

    auto tvs = new TypeVariableSubstitution();
    while (!constraints.empty()) {
      auto last = constraints.back();
      constraints.pop_back();
      bool success = solve(root, last, tvs);
      if (!success)
        return nullptr;
    }
    LOG3("Constraint solution:\n" << tvs);
    return tvs;
  }

  bool TypeConstraints::isUnifiableTypeVariable(const IR::Type* type) {
    auto tv = type->to<IR::ITypeVar>();
    if (tv == nullptr)
      return false;
    if (definedVariables->containsKey(tv))
      return false;
    if (tv->is<IR::Type_InfInt>())
      // These are always unifiable
      return true;
    return unifiableTypeVariables.count(tv) > 0;
  }

  bool TypeConstraints::solve(const IR::Node* root, EqualityConstraint *constraint,
                              TypeVariableSubstitution *subst) {
    if (isUnifiableTypeVariable(constraint->left)) {
      auto leftTv = constraint->left->to<IR::ITypeVar>();
      if (constraint->left == constraint->right)
        return true;

      // check to see whether we already have a substitution for leftTv
      const IR::Type* leftSubst = subst->lookup(leftTv);
      if (leftSubst == nullptr) {
        auto right = constraint->right->apply(replaceVariables)->to<IR::Type>();
        LOG3("Binding " << leftTv << " => " << right);
        return subst->compose(root, leftTv, right);
      } else {
        addEqualityConstraint(leftSubst, constraint->right, constraint);
        return true;
      }
    }

    if (isUnifiableTypeVariable(constraint->right)) {
      auto rightTv = constraint->right->to<IR::ITypeVar>();
      const IR::Type* rightSubst = subst->lookup(rightTv);
      if (rightSubst == nullptr) {
        auto left = constraint->left->apply(replaceVariables)->to<IR::Type>();
        LOG3("Binding " << rightTv << " => " << left);
        return subst->compose(root, rightTv, left);
      } else {
        addEqualityConstraint(constraint->left, rightSubst, constraint);
        return true;
      }
    }

    bool success = unification->unify(root, constraint->left, constraint->right, true);
    // this may add more constraints
    return success;
  }

  void TypeConstraints::dbprint(std::ostream& out) const {
    bool first = true;
    if (unifiableTypeVariables.size() != 0) {
      out << "Variables: ";
      for (auto tv : unifiableTypeVariables) {
        if (!first) out << ", ";
        auto node = tv->getNode();
        out << dbp(node);
        first = false;
      }
    }
    if (constraints.size() != 0) {
      out << "Constraints: ";
      for (auto c : constraints)
        out << std::endl << c;
    }
  }
}