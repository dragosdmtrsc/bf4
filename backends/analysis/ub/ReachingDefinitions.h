//
// Created by dragos on 18.09.2019.
//

#ifndef P4C_REACHINGDEFINITIONS_H
#define P4C_REACHINGDEFINITIONS_H

#include "ssa.h"
#include <analysis/bvset/bvset.h>
#include <analysis/lattice/Lattice.h>
namespace analysis {

class LiveVariables {
  // INPUTS
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  const EdgeHolder *g;
  node_t start;

  // COMPUTED
public:
  ReadSet rs;
  WriteSet ws;

  Index<MemPath> *indices = nullptr;
  NodeValues<analysis::bvset<MemPath>> def;
  NodeValues<analysis::bvset<MemPath>> use;
  NodeValues<analysis::bvset<MemPath>> in;
  NodeValues<analysis::bvset<MemPath>> out;

private:
  void buildIndex();

public:
  LiveVariables(ReferenceMap *refMap, TypeMap *typeMap, const EdgeHolder *g,
                const node_t &start, NodeToFunctionMap *funmap);
  bool live(const node_t &n, const MemPath &mp);
};

class ReachingDefinitions {
  // INPUTS
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  const EdgeHolder *g;
  node_t start;

  // COMPUTED
  ReadSet rs;
  WriteSet ws;
  std::unordered_map<MemPath, std::vector<node_t>> reverse_writes;
  std::unordered_map<MemPath, Index<node_t> *> indices;
  Index<std::pair<MemPath, node_t>> *main_index;
  bvset<std::pair<MemPath, node_t>> *undefined = nullptr;

  void compute_reverse();
  Index<node_t> *index(const MemPath &mp);

  bvset<node_t> fresh(const MemPath &mp);

public:
  typedef bvset<std::pair<MemPath, node_t>> Lattice;
  // factory method
  Lattice operator()();

  Lattice operator()(node_t n, const Edge &, const Lattice &l);
  Lattice operator()(node_t n, const Edge &, const Lattice &, const Lattice &);
  Lattice operator()(const Lattice &l, Lattice r);
  ReachingDefinitions(ReferenceMap *refMap, TypeMap *typeMap,
                      const EdgeHolder *g, const node_t &start,
                      NodeToFunctionMap *funmap);

  static NodeValues<Lattice> reachingDefinitions(ReferenceMap *refMap,
                                                 TypeMap *typeMap, const CFG &g,
                                                 NodeToFunctionMap *funmap);
  static NodeValues<Lattice>
  reachingDefinitions(ReferenceMap *refMap, TypeMap *typeMap, EdgeHolder &g,
                      const node_t &start, NodeToFunctionMap *funmap);
};

struct easy_index;
struct iterable_index {
  easy_index *idx;
  bvset<std::pair<MemPath, node_t>> *valof;

  unsigned count(const MemPath &mp);
  std::vector<node_t> of(const MemPath &mp);

  iterable_index(easy_index *idx, bvset<std::pair<MemPath, node_t>> *valof);
};
struct easy_index {
  Index<std::pair<MemPath, node_t>> *main_index;
  std::unordered_map<MemPath, std::unordered_map<node_t, size_t>> hierarchical;

  easy_index(Index<std::pair<analysis::MemPath, analysis::node_t>> *main_index);

  iterable_index with(bvset<std::pair<MemPath, node_t>> *valof);
};
}

#endif // P4C_REACHINGDEFINITIONS_H
