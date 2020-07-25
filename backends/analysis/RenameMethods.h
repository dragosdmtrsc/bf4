//
// Created by dragos on 11.06.2019.
//

#ifndef P4C_RENAMEMETHODS_H
#define P4C_RENAMEMETHODS_H


#include <ir/pass_manager.h>
#include <common/resolveReferences/referenceMap.h>
#include <p4/typeMap.h>
#include <p4/uniqueNames.h>

namespace analysis {
class RenameMethods : public PassManager {
  P4::RenameMap *renameMap;
public:
  RenameMethods(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};
}

#endif //P4C_RENAMEMETHODS_H
