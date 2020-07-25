//
// Created by dragos on 08.07.2019.
//

#ifndef P4C_CONTEXT_H
#define P4C_CONTEXT_H

#include <ir/ir.h>
#include <p4/methodInstance.h>

namespace analysis {

bool equivalent(const P4::Instantiation *self, const P4::Instantiation *other);

struct Context {
  const IR::INode *syntactic;
  // maps declarations from the syntactic Node -> Instantiation
  // refers to the calling context-specific: i.e. parameters,
  // other declarations will be context independent => their types
  // have been resolved already and are in the typeMap
  std::unordered_map<const IR::IDeclaration *, P4::Instantiation *>
      compileTimeValues;
  // maps type_var from the syntactic Node -> canonical types
  std::unordered_map<const IR::Type_Var *, const IR::Type *> substitutions;

  // all instaces bound -> the context factory will produce this value
  // it is in its responsibility to refresh the type map and reference map
  const IR::Node *instantiated = nullptr;

public:
  bool operator==(const Context &other) const {
    for (auto &subs : substitutions) {
      auto I = other.substitutions.find(subs.first);
      BUG_CHECK(
          I != other.substitutions.end(),
          "not comparing apples with apples: type var %1% not found in other",
          subs.first);
      auto tp = I->second;
      if (!P4::TypeMap::equivalent(tp, subs.second)) {
        return false;
      }
    }
    for (auto &subs : other.substitutions) {
      auto I = substitutions.find(subs.first);
      BUG_CHECK(
          I != substitutions.end(),
          "not comparing apples with apples: type var %1% not found in this",
          subs.first);
    }

    for (auto &tvm : compileTimeValues) {
      auto I = other.compileTimeValues.find(tvm.first);
      BUG_CHECK(
          I != other.compileTimeValues.end(),
          "not comparing apples with apples: instance %1% not found in other",
          tvm.first);
      auto instance = I->second;
      if (!analysis::equivalent(instance, tvm.second)) {
        return false;
      }
    }
    for (auto &tvm : other.compileTimeValues) {
      auto I = compileTimeValues.find(tvm.first);
      BUG_CHECK(
          I != compileTimeValues.end(),
          "not comparing apples with apples: instance %1% not found in this",
          tvm.first);
    }
    return true;
  }
  const IR::Node *getNode() { return instantiated; }
};

class ContextFactory {
public:
  const IR::P4Program *program;
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

  // keeps a map from a syntactic object to a set of
  // contexts (instantiations) of a given syntactic object =>
  // context should implement the operator==(const Context &).
  // If the number of contexts is small (and most likely it will be),
  // then no need to complicate it with hashing
  std::unordered_multimap<const IR::INode *, Context *> known_contexts;

  ContextFactory(const IR::P4Program *program, P4::ReferenceMap *refMap,
                 P4::TypeMap *typeMap);

  const IR::IDeclaration *makeSyntactic(const IR::IDeclaration *declaration);
  const IR::IDeclaration *
  makeSyntactic(const IR::IDeclaration *declaration,
                std::function<bool(const IR::IDeclaration *)> filter);
  Context *makeContext(const P4::MethodInstance *instance);
  Context *getContext(const P4::MethodInstance *instance);
  void addContext(Context *&context);
  std::unordered_map<const IR::Type_Var *, const IR::Type *>
  getTypeMappings(P4::TypeMap *typeMap, const P4::MethodInstance *fc,
                  const IR::TypeParameters *syntTypeParms) const;

  std::unordered_map<const IR::IDeclaration *, P4::Instantiation *>
  getParameterInstances(P4::ReferenceMap *, P4::TypeMap *,
                        const IR::ParameterList *syntacticals,
                        const IR::ParameterList *originals,
                        const IR::ParameterList *actuals,
                        const P4::ParameterSubstitution &);

  const IR::Node *instantiate(const P4::MethodInstance *instance);
};

class ImplementationFactory {
  ContextFactory *factory;

public:
  ImplementationFactory(ContextFactory *factory);

public:
  analysis::Context *implement(const IR::Node *node, analysis::Context *crt,
                               bool fallback);
};

class BuildContextFactory : public Inspector {
  ContextFactory *factory;
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

  analysis::Context *currentContext;

public:
  BuildContextFactory(ContextFactory *factory, P4::ReferenceMap *refMap,
                      P4::TypeMap *typeMap);

public:
  void postorder(const IR::MethodCallExpression *mce) override;
  void start(const IR::Function *run);
};
}

#endif // P4C_CONTEXT_H
