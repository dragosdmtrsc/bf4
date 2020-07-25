//
// Created by dragos on 20.04.2019.
//

#ifndef P4C_REMOVETABLECALLS_H
#define P4C_REMOVETABLECALLS_H

#include <common/resolveReferences/referenceMap.h>
#include <p4/typeMap.h>

namespace analysis {
class RemoveTableCalls : public PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  std::map<const IR::P4Table *, std::vector<const IR::Node *>> please_add;
public:
  RemoveTableCalls(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};

class MakePopulatedTables : public PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
public:
  MakePopulatedTables(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};
}



#endif //P4C_REMOVETABLECALLS_H
