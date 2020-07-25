//
// Created by dragos on 29.05.2019.
//

#ifndef P4C_DEPENDENCYGRAPH_H
#define P4C_DEPENDENCYGRAPH_H

#include "cfg_algos.h"
#include <common/resolveReferences/referenceMap.h>
#include <p4/typeMap.h>

namespace analysis {

struct CFGHolder {
  EdgeHolder *fw;
  EdgeHolder *bw;
  NodeValues<std::unordered_set<node_t>> cdg;
  std::map<node_t, std::set<node_t>> ddg;
  std::map<node_t, std::set<node_t>> *imm_postdominators =
      nullptr;

public:
  CFGHolder(EdgeHolder *fw, EdgeHolder *bw,
            const NodeValues<std::unordered_set<node_t>> &cdg);

  std::ostream &print(std::ostream &os, bool printcdg, bool printddg) const;

  friend std::ostream &operator<<(std::ostream &, const CFGHolder &);
};
class DependencyGraph : public PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

public:
  DependencyGraph(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};
}

#endif // P4C_DEPENDENCYGRAPH_H
