//
// Created by dragos on 20.04.2019.
//

#ifndef P4C_REMOVEBUILTINS_H
#define P4C_REMOVEBUILTINS_H

#include <ir/visitor.h>
#include <common/resolveReferences/referenceMap.h>
#include <p4/typeMap.h>

namespace analysis {
class BuiltinRegistrar {
public:
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  std::map<const IR::Type *, std::map<cstring, const IR::Method *>> methods;
  std::map<const IR::Method *, std::set<const IR::MethodCallExpression *>> instances;
  std::map<const IR::MethodCallExpression *, const IR::Method *> reverseInstances;

  std::map<const IR::Node *, std::set<const IR::Method *>> insertionPoints;

  BuiltinRegistrar(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
  void add(const IR::MethodCallExpression *mce, const IR::Node *addBefore);
};

class RemoveBuiltins : public PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  BuiltinRegistrar builtinRegistrar;
public:
  RemoveBuiltins(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};
}



#endif //P4C_REMOVEBUILTINS_H
