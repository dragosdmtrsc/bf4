//
// Created by dragos on 15.09.2019.
//

#include "IOLattice.h"

namespace analysis {

bool IOLattice::operator==(const IOLattice &other) const {
  return edges == other.edges;
}
IOLattice IOLattice::operator+(const IOLattice &other) const {
  auto nedges = edges;
  nedges.insert(other.edges.begin(), other.edges.end());
  return nedges;
}
bool IOLattice::isBottom() const { return edges.empty(); }
IOLattice::IOLattice(std::unordered_set<FullEdge_t> edges)
    : edges(std::move(edges)) {}
IOLattice IOTransfer::operator()(node_t n, const Edge &e,
                                 const IOLattice &other) {
  auto cp = other;
  if (!rev) {
    cp.edges.emplace(n, e);
  } else {
    cp.edges.emplace(e.first, n, e.second);
  }
  return std::move(cp);
}
IOLattice IOTransfer::operator()(node_t n, const Edge &e, const IOLattice &,
                                 const IOLattice &lend) {
  auto cp = lend;
  cp.edges.emplace(n, e);
  return std::move(cp);
}
IOTransfer::IOTransfer(bool rev) : rev(rev) {}

template <typename FwdIt>
void compute(FwdIt I, FwdIt E, NodeValues<IOLattice> &ins, EdgeHolder *fw,
             IOTransfer iotransfer) {
  for (; I != E; ++I) {
    auto &n = *I;
    auto &inn = ins[n];
    auto NIt = fw->find(n);
    if (NIt != fw->end()) {
      for (auto &e : NIt->second) {
        IOLattice &l = ins[e.first];
        auto transf = iotransfer(n, e, inn);
        if (l.edges.empty()) l.edges = std::move(transf.edges);
        else l.edges.insert(transf.edges.begin(), transf.edges.end());
      }
    }
  }
}

NodeIOs getNodeIOs(EdgeHolder *fw, EdgeHolder *bw,
                   const std::vector<node_t> &sorted) {
  NodeIOs nios;
  NodeValues<size_t> prios;
  compute(sorted.rbegin(), sorted.rend(), nios.ins, fw, false);
  compute(sorted.begin(), sorted.end(), nios.outs, bw, true);
  return std::move(nios);
}
std::unordered_set<FullEdge_t> NodeIOs::between(node_t s, node_t d) {
  auto &outss = outs[s];
  auto &ind = ins[d];
  std::unordered_set<FullEdge_t> intersection;
  for (auto &o : outss.edges) {
    if (ind.edges.count(o)) intersection.emplace(o);
  }
  return intersection;
}
}