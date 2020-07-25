//
// Created by dragos on 02.09.2019.
//

#ifndef P4C_LOOP_H
#define P4C_LOOP_H

#include <analysis/lattice/Lattice.h>

#include "StorageLattice.h"
#include <utility>

namespace analysis {

struct IPCPath {
  bool oob = false;
  std::vector<FullEdge_t> edges;

  IPCPath(bool oob) : oob(oob) {}

  IPCPath() {}

  IPCPath(std::vector<FullEdge_t> edges) : edges(std::move(edges)) {}

  void push(FullEdge_t fe) { edges.push_back(fe); }

  void remove(const FullEdge_t &fe) {
    std::vector<FullEdge_t> nxt;
    std::copy_if(edges.begin(), edges.end(), std::back_inserter(nxt),
                 [&fe](const FullEdge_t &x) { return fe != x; });
    edges = std::move(nxt);
  }

  bool operator==(const IPCPath &other) const {
    if (oob && other.oob)
      return true;
    if (oob != other.oob)
      return false;
    return edges == other.edges;
  }

  friend std::ostream &operator<<(std::ostream &os, const IPCPath &p) {
    if (p.oob)
      return os << "_|_";
    for (auto x : p.edges) {
      os << x << ";";
    }
    return os;
  }
};

std::size_t hash_value(const IPCPath &e);
}

namespace std {
template <> struct hash<analysis::IPCPath> {
  std::size_t operator()(const analysis::IPCPath &p) const {
    return analysis::hash_value(p);
  }
};
}

namespace analysis {
class LoopLattice : public LatticeElement<LoopLattice> {
public:
  std::unordered_set<IPCPath> paths;
  LoopLattice() {}
  LoopLattice(std::unordered_set<IPCPath> paths);

  bool operator==(const LoopLattice &other) const override;
  LoopLattice operator+(const LoopLattice &other) const override;
  bool isBottom() const override;
};

class Transfer : public Propagate<LoopLattice> {
  const NodeValues<unsigned> &sccs;
  const std::vector<std::unordered_set<node_t>> &rev_sccs;
  const std::vector<std::unordered_set<FullEdge_t>> &back;
  const std::unordered_map<FullEdge_t, unsigned> &limits;

  bool same_scc(node_t s, node_t d) const {
    return analysis::get<unsigned>(sccs, s) == analysis::get<unsigned>(sccs, d);
  }

  bool is_back(const FullEdge_t &fe) const {
    auto sccs = analysis::get<unsigned>(this->sccs, fe.source);
    auto sccd = analysis::get<unsigned>(this->sccs, fe.source);
    if (sccs != sccd)
      return false;
    if (sccs < back.size())
      return back[sccs].count(fe) != 0;
    return false;
  }

  const std::unordered_set<FullEdge_t> *back_edges(node_t s) const {
    auto sccs = analysis::get<unsigned>(this->sccs, s);
    if (sccs < back.size())
      return &back[sccs];
    return nullptr;
  }

  bool is_out_of_bounds(const IPCPath &p) const;

public:
  boost::optional<IPCPath> transfer(FullEdge_t fe, const IPCPath &l) const;

  Transfer(const NodeValues<unsigned int> &sccs,
           const std::vector<std::unordered_set<node_t>> &rev_sccs,
           const std::vector<std::unordered_set<FullEdge_t>> &back,
           const std::unordered_map<FullEdge_t, unsigned int> &limits);

  LoopLattice operator()(node_t n, const Edge &e,
                         const LoopLattice &other) override;

  LoopLattice operator()(node_t n, const Edge &e, const LoopLattice &lcall,
                         const LoopLattice &lend) override;
};

void unroll(EdgeHolder *holder, node_t &start, NodeToFunctionMap *funMap,
            unsigned max_out, bool is_bug = false,
            NodeValues<node_t> *parents = nullptr);
}

#endif // P4C_LOOP_H
