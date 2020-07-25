//
// Created by dragos on 29.08.2019.
//

#ifndef P4C_MUTEXINSTRUMENT_H
#define P4C_MUTEXINSTRUMENT_H

#include <common/resolveReferences/referenceMap.h>
#include <ir/pass_manager.h>
#include <p4/typeMap.h>

namespace analysis {

struct MutexHeaders {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

  MutexHeaders(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};

class MutexInstrument : public PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  cstring parser;
  cstring control;
  MutexHeaders mutexHeaders;

 public:
  MutexInstrument(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                  cstring parser, cstring control);
};
}

#endif  // P4C_MUTEXINSTRUMENT_H
