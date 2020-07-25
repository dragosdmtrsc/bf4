//
// Created by a-drdum on 4/24/2019.
//

#ifndef P4C_PARSERSUNROLL_H
#define P4C_PARSERSUNROLL_H

#include <common/resolveReferences/referenceMap.h>
#include <p4/typeMap.h>

namespace analysis {
class ParsersUnroll : PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
public:
  ParsersUnroll(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};
}

#endif //P4C_PARSERSUNROLL_H
