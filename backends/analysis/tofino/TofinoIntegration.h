//
// Created by dragos on 06.02.2020.
//

#ifndef P4C_TOFINOINTEGRATION_H
#define P4C_TOFINOINTEGRATION_H

#include <common/resolveReferences/referenceMap.h>
#include <p4/typeMap.h>
#include <p4/evaluator/evaluator.h>

namespace analysis {
class HandleTofino : public PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

public:
  HandleTofino(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};

class TofinoBugs : public PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

public:
  TofinoBugs(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};

class CleanupTofinoBackend : public PassManager {
  P4::ReferenceMap refMap;
  P4::TypeMap typeMap;
  cstring to;

public:
  CleanupTofinoBackend(cstring to);
};

class IntegrateTofino : public PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  cstring templateFile, out;

public:
  IntegrateTofino(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                  const cstring &templateFile, cstring out);
  void render(P4::Evaluator *);
};
}

#endif // P4C_TOFINOINTEGRATION_H
