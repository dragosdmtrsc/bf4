//
// Created by dragos on 06.05.2019.
//

#ifndef P4C_SPECIALIZEEXTERNFUNCTIONS_H
#define P4C_SPECIALIZEEXTERNFUNCTIONS_H

#include <common/resolveReferences/referenceMap.h>
#include <p4/typeMap.h>

namespace analysis {

class ExternFunMap {
public:
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  std::map<const IR::Method *, std::set<const IR::Type_Method *>> specMap;
  std::map<const IR::Type_Method *, const IR::Method *> revSpecMap;
  std::map<const IR::MethodCallExpression *, const IR::Type_Method *> functionsToReplace;
  std::map<const IR::Type_Method *, std::set<const IR::IDeclaration *>> typeDependencies;
  std::map<const IR::IDeclaration *, std::set<const IR::Type_Method *>> revTypeDependencies;

  void put(const IR::MethodCallExpression *mce,
           const IR::Method *met,
           const IR::Type_Method *methodType);

  ExternFunMap(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};

class SpecializeExternFunctions : public PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  ExternFunMap funMap;
public:
  SpecializeExternFunctions(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};
}

#endif //P4C_SPECIALIZEEXTERNFUNCTIONS_H
