//
// Created by dragos on 12.12.2019.
//

#ifndef P4C_GENERATEMETHODS_H
#define P4C_GENERATEMETHODS_H

#include <common/resolveReferences/referenceMap.h>
#include <p4/typeMap.h>

namespace analysis {
class GenerateMethods : public PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

public:
  GenerateMethods(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};
}

#endif // P4C_GENERATEMETHODS_H
