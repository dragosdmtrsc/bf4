//
// Created by dragos on 17.12.2019.
//

#include "ControlLattice.h"

#include "AnalysisContext.h"

namespace analysis {
ControlLattice::ControlLattice(ReferenceMap *refMap, TypeMap *typeMap,
                               const CFG *g, NodeToFunctionMap *funmap)
    : refMap(refMap), typeMap(typeMap), cfg(g), funmap(funmap) {}

NodeValues<control_struct> ControlLattice::run() {
  DefaultDiscipline dd(&cfg->holder, cfg->start_node);
  auto init = this->operator()();
  init.control_nodes.emplace();
  NodeValues<control_struct> res({{cfg->start_node, init}});
  auto rr = std::ref(*this);
  WorklistAlgo<control_struct, decltype(rr), DefaultDiscipline, decltype(rr),
               decltype(rr)>
      algo(*cfg, rr, dd, rr, rr);
  algo(cfg->start_node, res);
  return std::move(res);
}

ControlLattice::Lattice ControlLattice::operator()() {
  return analysis::ControlLattice::Lattice();
}

ControlLattice::Lattice ControlLattice::
operator()(node_t n, const Edge &, const ControlLattice::Lattice &l) {
  if (std::any_of(instructions(n).begin(), instructions(n).end(),
                  [this](const IR::Node *n) {
                    return is_controlled(node_t(n), refMap, typeMap);
                  })) {
    control_struct cpy;
    for (auto path : l.control_nodes) {
      path.push_back(n);
      cpy.control_nodes.emplace(path);
    }
    return std::move(cpy);
  }
  return l;
}

ControlLattice::Lattice ControlLattice::
operator()(node_t, const Edge &, const ControlLattice::Lattice &,
           const ControlLattice::Lattice &) {
  BUG("should not reach this point");
}

ControlLattice::Lattice ControlLattice::
operator()(const ControlLattice::Lattice &l, ControlLattice::Lattice r) {
  if (l.control_nodes.empty())
    return std::move(r);
  if (r.control_nodes.empty())
    return l;
  for (const auto &x : l.control_nodes)
    r.control_nodes.emplace(x);
  return std::move(r);
}

NodeValues<control_struct>
ControlLattice::controlPaths(ReferenceMap *refMap, TypeMap *typeMap,
                             const CFG *g, NodeToFunctionMap *funmap) {
  ControlLattice controlLattice(refMap, typeMap, g, funmap);
  return controlLattice.run();
}

NodeValues<control_struct>
ControlLattice::controlPaths(ReferenceMap *refMap, TypeMap *typeMap,
                             EdgeHolder &g, const node_t &start,
                             NodeToFunctionMap *funmap) {
  auto cfg = new CFG(nullptr, std::move(g));
  cfg->start_node = start;
  auto ret = controlPaths(refMap, typeMap, cfg, funmap);
  g = std::move(cfg->holder);
  return std::move(ret);
}

NodeValues<NodeSet> ReachControls::run() {
  DefaultDiscipline dd(&cfg->holder, cfg->start_node);
  auto init = this->operator()();
  NodeValues<Lattice> res({{cfg->start_node, init}});
  auto rr = std::ref(*this);
  WorklistAlgo<Lattice, decltype(rr), DefaultDiscipline, decltype(rr),
               decltype(rr)>
      algo(*cfg, rr, dd, rr, rr);
  algo(cfg->start_node, res);
  return std::move(res);
}

ReachControls::ReachControls(ReferenceMap *refMap, TypeMap *typeMap,
                             const CFG *cfg, NodeToFunctionMap *funmap)
    : refMap(refMap), typeMap(typeMap), cfg(cfg), funmap(funmap) {}
}