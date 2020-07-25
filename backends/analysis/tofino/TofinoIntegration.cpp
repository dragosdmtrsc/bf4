//
// Created by dragos on 06.02.2020.
//

#include "TofinoIntegration.h"
#include <analysis/analysis_helpers.h>
#include <common/resolveReferences/resolveReferences.h>
#include <fstream>
#include <p4/evaluator/substituteParameters.h>
#include <p4/methodInstance.h>
#include <p4/toP4/toP4.h>
#include <p4/typeChecking/typeChecker.h>
#include <p4/unusedDeclarations.h>

namespace analysis {

HandleTofino::HandleTofino(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap) {
  //TODO: stub
  addPasses({new P4::ClearTypeMap(typeMap), new P4::ResolveReferences(refMap),
             new P4::TypeInference(refMap, typeMap, false)});
}

CleanupTofinoBackend::CleanupTofinoBackend(cstring to) : to(to) {
  addPasses({new P4::ResolveReferences(&refMap),
             new P4::TypeInference(&refMap, &typeMap, false)});
  auto ofs = new std::ofstream(to);
  passes.push_back(new HandleTofino(&refMap, &typeMap));
  passes.push_back(new P4::RemoveAllUnusedDeclarations(&refMap));
  passes.push_back(new P4::ToP4(ofs, false));
}

class InstrumentTofinoBugs : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

public:
  InstrumentTofinoBugs(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}

private:
  const IR::Node *postorder(IR::MethodCallStatement *mcs) override {
    //TODO: stub
    return mcs;
  }
};

TofinoBugs::TofinoBugs(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap) {
  addPasses({new InstrumentTofinoBugs(refMap, typeMap),
             new P4::ClearTypeMap(this->typeMap),
             new P4::ResolveReferences(this->refMap),
             new P4::TypeInference(this->refMap, this->typeMap, false),
             new P4::ResolveReferences(this->refMap)});
}

IntegrateTofino::IntegrateTofino(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                                 const cstring &templateFile, cstring out)
    : refMap(refMap), typeMap(typeMap), templateFile(templateFile), out(out) {}

void IntegrateTofino::render(P4::Evaluator *ev) {}
}