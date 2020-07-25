//
// Created by dragos on 20.04.2019.
//

#ifndef P4C_HANDLESTACKS_H
#define P4C_HANDLESTACKS_H

#include <common/resolveReferences/referenceMap.h>
#include <p4/typeMap.h>


namespace analysis {
class StackRegistrar {
public:
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  std::map<std::pair<const IR::Type *, unsigned>, std::set<const IR::Node *>> reverseInsertionPoints;
  std::map<const IR::Node *, std::set<std::pair<const IR::Type *, unsigned>>> insertPoints;

  StackRegistrar(P4::ReferenceMap *refMap,
                 P4::TypeMap *typeMap);

  void put(const IR::Declaration *decl, const IR::Node *insPoint);
};
class HandleStacks : public PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  StackRegistrar registrar;
public:
  HandleStacks(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};
}



#endif //P4C_HANDLESTACKS_H
