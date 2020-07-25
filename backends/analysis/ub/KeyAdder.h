//
// Created by dragos on 29.01.2020.
//

#ifndef P4C_KEYADDER_H
#define P4C_KEYADDER_H

#include <analysis/cfg_algos.h>
#include <analysis/version_propagator.h>
#include <analysis/versions.h>
#include <ir/visitor.h>

namespace analysis {
class KeyAdder : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  NodeValues<PathSet> patches;
  std::unordered_map<cstring, PathSet> method2keys;
  PathTypes pt;
  PathGetter pg;

  void init();

  const IR::Node *postorder(IR::Method *met) override;

  const IR::Node *postorder(IR::MethodCallStatement *stat) override;

public:
  KeyAdder(ReferenceMap *refMap, TypeMap *typeMap,
           NodeValues<std::set<analysis::MemPath>> patches);
};
}

#endif // P4C_KEYADDER_H
