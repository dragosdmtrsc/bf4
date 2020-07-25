//
// Created by dragos on 19.01.2020.
//

#ifndef P4C_EGRESSSPECNOTSET_H
#define P4C_EGRESSSPECNOTSET_H

#include <bmv2/simple_switch/simpleSwitch.h>
#include <common/resolveReferences/referenceMap.h>
#include <p4/typeMap.h>

namespace analysis {

class ApplyIfV1 : public PassManager {
protected:
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  BMV2::V1ProgramStructure structure;
  P4::Evaluator evaluator;
  bool isv1 = false;

public:
  PassManager innerPassManager;
  ApplyIfV1(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};

// assumes an inlined ingress control - i.e. all control calls and function
// calls
// must have been inlined
// control ingress(inout H hdr, inout M metadata, inout standard_metadata_t
// standard_metadata) {
//    ...
// } ->
// control ingress(inout H hdr, inout M metadata, inout standard_metadata_t
// standard_metadata) {
//    setundef(standard_metadata.egress_spec);
//    ...
//    if (isundef(standard_metadata.egress_spec)) { bug(); }
// }
class EgressSpecNotSet : public ApplyIfV1 {
public:
  EgressSpecNotSet(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};

// bound checks all calls to indexed based externals
class RegistersOutOfBounds : public ApplyIfV1 {
public:
  RegistersOutOfBounds(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};

class RemoveV1Controls : public ApplyIfV1 {
public:
  RemoveV1Controls(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};

};

#endif // P4C_EGRESSSPECNOTSET_H
