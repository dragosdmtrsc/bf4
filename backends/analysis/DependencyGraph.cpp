//
// Created by dragos on 29.05.2019.
//

#include <fstream>
#include <p4/moveDeclarations.h>
#include <p4/uniqueNames.h>
#include <analysis/ub/StorageLattice.h>
#include "DependencyGraph.h"
#include "cfg_algos.h"
#include "analysis_helpers.h"
#include "DataDependencies.h"

namespace analysis {
class ComputeDependencyGraph : public Inspector {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

public:
  ComputeDependencyGraph(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}
  void postorder(const IR::P4Control *control) override {
    ComputeGraph cg(refMap);
    auto fw = cg.get_forward(control);
    auto bw = cg.get_backward(control);
    NodeValues<std::unordered_set<node_t>> dependencies;
    analysis::compute_cdg(fw, bw, dependencies);
    CFGHolder holder(fw, bw, dependencies);
    AllDefinitions allDefinitions(refMap, typeMap);
    ComputeWriteSet computeWriteSet(&allDefinitions);
    control->apply(computeWriteSet);
    HasUses hasUses;
    FindUninitialized funi(&allDefinitions, &hasUses);
    control->apply(funi);
    holder.ddg = std::move(hasUses.usages);
    std::stringstream ss;
    ss << "controldep_" << control->name.name << ".dot";
    std::ofstream of(ss.str());
    of << holder;
    of.close();
  }
};

CFGHolder::CFGHolder(
    EdgeHolder *fw, EdgeHolder *bw,
    const NodeValues<std::unordered_set<node_t>> &cdg)
    : fw(fw), bw(bw), cdg(cdg) {}

std::ostream &operator<<(std::ostream &os, const CFGHolder &h) {
  return h.print(os, true, true);
}

std::ostream &CFGHolder::print(std::ostream &os, bool printcdg, bool printddg) const {
  os << "digraph G {\n";
  analysis::print_graph(fw, false, os);
  if (printcdg) {
    for (auto &d : cdg) {
      for (auto dependent : d.second) {
        os << "\"" << analysis::id(d.first) << "\" -> \"" << analysis::id(dependent) << "\" [color=red];\n";
      }
    }
  }
  if (printddg) {
    for (auto &d : ddg) {
      for (auto dependent : d.second) {
        os << "\"" << analysis::id(d.first) << "\" -> \"" << analysis::id(dependent) << "\" [color=blue];\n";
      }
    }
  }
  os << "}\n";
  return os;
}
}

analysis::DependencyGraph::DependencyGraph(P4::ReferenceMap *refMap,
                                           P4::TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap) {
  passes.push_back(new MoveDeclarations);
  passes.push_back(new UniqueNames(refMap));
  passes.push_back(new TypeChecking(refMap, typeMap, true));
  passes.push_back(new ComputeDependencyGraph(refMap, typeMap));
}
