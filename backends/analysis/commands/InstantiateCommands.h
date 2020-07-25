//
// Created by dragos on 01.07.2019.
//

#ifndef P4C_INSTANTIATECOMMANDS_H
#define P4C_INSTANTIATECOMMANDS_H

#include "CommandParser.h"
#include <common/resolveReferences/referenceMap.h>
#include <p4/typeMap.h>

namespace analysis {

class InstantiateCommands : public PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  Commands &commands;
  std::set<const IR::P4Action *> actions;

public:
  InstantiateCommands(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                      Commands &commands);
};
}

#endif // P4C_INSTANTIATECOMMANDS_H
