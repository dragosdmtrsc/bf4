//
// Created by dragos on 15.09.2019.
//

#ifndef P4C_IOLATTICE_H
#define P4C_IOLATTICE_H

#include <analysis/cfg_algos.h>
#include <analysis/lattice/Lattice.h>
#include <unordered_set>
#include "StorageLattice.h"

namespace analysis {
struct IOLattice : public LatticeElement<IOLattice> {
  std::unordered_set<FullEdge_t> edges;
  IOLattice() = default;
  IOLattice(std::unordered_set<FullEdge_t> edges);
  bool operator==(const IOLattice &other) const override;
  IOLattice operator+(const IOLattice &other) const override;
  bool isBottom() const override;
};

class IOTransfer : public Propagate<IOLattice> {
  bool rev;

 public:
  IOTransfer(bool rev);
  IOLattice operator()(node_t n, const Edge &e,
                       const IOLattice &other) override;
  IOLattice operator()(node_t n, const Edge &e, const IOLattice &lcall,
                       const IOLattice &lend) override;
};

struct NodeIOs {
  NodeValues<IOLattice> ins;
  NodeValues<IOLattice> outs;

  std::unordered_set<FullEdge_t> between(node_t s, node_t d);
};

NodeIOs getNodeIOs(EdgeHolder *fw, EdgeHolder *bw,
                   const std::vector<node_t> &sorted);
}

#endif  // P4C_IOLATTICE_H
