//
// Created by dragos on 17.12.2019.
//

#ifndef P4C_CONTROLLATTICE_H
#define P4C_CONTROLLATTICE_H

#include <analysis/cfg_algos.h>
#include <analysis/lattice/Lattice.h>

namespace analysis {

class ReachControls {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  const CFG *cfg;
  NodeToFunctionMap *funmap;

public:
  typedef NodeSet Lattice;

private:
  NodeValues<NodeSet> run();

public:
  ReachControls(ReferenceMap *refMap, TypeMap *typeMap, const CFG *cfg,
                NodeToFunctionMap *funmap);
  // factory method
  Lattice operator()() { return analysis::ReachControls::Lattice(); }

  Lattice operator()(node_t n, const Edge &, const Lattice &l) {
    auto cpy = l;
    for (auto instr : instructions(n)) {
      if (auto mcs = is_extern_method_call(instr)) {
        if (is_controlled(mcs->methodCallStatement, refMap, typeMap)) {
          cpy.emplace(instr);
        }
      }
    }
    return cpy;
  }

  Lattice operator()(node_t, const Edge &, const Lattice &, const Lattice &) {
    BUG("unreachable");
  }

  Lattice operator()(const Lattice &l, Lattice r) {
    r.insert(l.begin(), l.end());
    return std::move(r);
  }

  static NodeValues<NodeSet> reachControls(ReferenceMap *refMap,
                                           TypeMap *typeMap, EdgeHolder &g,
                                           const node_t &start,
                                           NodeToFunctionMap *funmap) {
    auto cfg = new CFG(nullptr, std::move(g));
    cfg->start_node = start;
    ReachControls reachControls(refMap, typeMap, cfg, funmap);
    auto res = reachControls.run();
    g = std::move(cfg->holder);
    return res;
  }
};

struct control_struct {
  std::set<std::vector<node_t>> control_nodes;
  bool operator!=(const control_struct &x) const {
    return control_nodes != x.control_nodes;
  }
  control_struct() {}
};

class ControlLattice {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  const CFG *cfg;
  NodeToFunctionMap *funmap;

  NodeValues<control_struct> run();
  ControlLattice(ReferenceMap *refMap, TypeMap *typeMap, const CFG *g,
                 NodeToFunctionMap *funmap);

public:
  typedef control_struct Lattice;
  // factory method
  Lattice operator()();

  Lattice operator()(node_t n, const Edge &, const Lattice &l);
  Lattice operator()(node_t n, const Edge &, const Lattice &, const Lattice &);
  Lattice operator()(const Lattice &l, Lattice r);

  static NodeValues<control_struct> controlPaths(ReferenceMap *refMap,
                                                 TypeMap *typeMap, const CFG *g,
                                                 NodeToFunctionMap *funmap);
  static NodeValues<control_struct>
  controlPaths(ReferenceMap *refMap, TypeMap *typeMap, EdgeHolder &g,
               const node_t &start, NodeToFunctionMap *funmap);
};
}

#endif // P4C_CONTROLLATTICE_H
