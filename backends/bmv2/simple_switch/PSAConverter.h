//
// Created by dragos on 31.05.2019.
//

#ifndef P4C_PSACONVERTER_H
#define P4C_PSACONVERTER_H

#include "simpleSwitch.h"
#include <bmv2/common/options.h>
#include <common/resolveReferences/referenceMap.h>
#include <p4/typeMap.h>

namespace BMV2 {
class PSAConverter {
  BMV2Options &options;
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  P4V1::V1Model &v1model;
  V1ProgramStructure *structure;
  const IR::P4Program *newprogram;
  const IR::P4Program *oldProgram;

  IR::Type_Name *metaTypeName;
  const IR::P4Parser *ingressParser;
  const IR::P4Parser *egressParser;
  const IR::Type_Declaration *headertype;
public:

  std::string readHeader(const char* filename, bool preprocess = false);

  const IR::P4Program *convert(const IR::P4Program *prog);

  void makeExplicitFieldLists(const IR::P4Program *program);

  void makeIngressParser();
  void makeIngressPipeline();
  void makeIngressDeparser();
  void makeEgressParser();
  void makeEgressPipeline();
  void makeEgressDeparser();
  void replaceStandardMeta();
  void initializeParserMetas();
  void initializeForwardingMetas();
  void declareMain();
  void declareForwardingMeta();
  void declareExternMethods();
  void declareExternInstances();
  void declareStructsAndExterns();
  void declareMetaType();

  void dump_new_program(cstring name) const;

  PSAConverter(BMV2Options &options, P4::ReferenceMap *refMap,
               P4::TypeMap *typeMap, P4V1::V1Model &v1model,
               V1ProgramStructure *structure);


};

class RescueClone : public PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
public:
  RescueClone(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};

}

#endif // P4C_PSACONVERTER_H
