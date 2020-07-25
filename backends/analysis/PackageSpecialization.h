//
// Created by dragos on 19.04.2019.
//

#ifndef P4C_PACKAGESPECIALIZATION_H
#define P4C_PACKAGESPECIALIZATION_H

#include <common/resolveReferences/referenceMap.h>
#include <p4/typeMap.h>
#include <p4/methodInstance.h>

namespace analysis {
class PackageSpecialization : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
public:
  PackageSpecialization(P4::ReferenceMap *refMap, P4::TypeMap *typeMap) :
    refMap(refMap), typeMap(typeMap) {}

  const IR::Node *preorder(IR::Declaration_Instance *di) override;

};
}



#endif //P4C_PACKAGESPECIALIZATION_H
