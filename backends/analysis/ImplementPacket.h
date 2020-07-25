//
// Created by dragos on 19.09.2019.
//

#ifndef P4C_IMPLEMENTPACKET_H
#define P4C_IMPLEMENTPACKET_H

#include <common/resolveReferences/referenceMap.h>
#include <p4/typeMap.h>
#include <common/resolveReferences/resolveReferences.h>
#include <p4/typeChecking/typeChecker.h>

namespace analysis {
class ImplementPacket : public PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

public:
  ImplementPacket(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
  static const IR::Type *packetType() {
    return new IR::Type_Bits(12, false);
  }
};
}

#endif //P4C_IMPLEMENTPACKET_H
