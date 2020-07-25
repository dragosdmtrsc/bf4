//
// Created by dragos on 09.12.2019.
//

#ifndef P4C_PROGRAMDATABASE_H
#define P4C_PROGRAMDATABASE_H

#include <analysis/cfg_algos.h>
#include <analysis/context/InterproceduralCFGs.h>
#include <analysis/ub/AnalysisContext.h>
#include <common/resolveReferences/referenceMap.h>
#include <p4/typeMap.h>

namespace analysis {
class ProgramDatabase {
  // INPUTS:
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  const IR::P4Program *program;
  cstring startFunction;

  NodeToFunctionMap funMap;
  CFG *main;
  std::unordered_map<const IR::Node *, std::pair<CFG, CFG>> basic_blocks;
  CFGs cfgs;
  ContextFactory contextFactory;
  BuildIPCFG builder;

public:
  ProgramDatabase(ReferenceMap *refMap, TypeMap *typeMap,
                  const IR::P4Program *program, const cstring &startFunction);

  CFG *method(const IR::Node *method_id);
  const IR::Node *mainFunction();
  CFG *graph() { return main; }
  const IR::Node *method(const node_t &node) { return builder.getMethod(node); }
  const IR::MethodCallStatement *isControlled(const node_t &node) {
    if (auto mcs = is_extern_method_call(node)) {
      if (is_controlled(mcs->methodCallStatement, refMap, typeMap))
        return mcs->methodCallStatement;
    }
    return nullptr;
  }
};
}

#endif // P4C_PROGRAMDATABASE_H
