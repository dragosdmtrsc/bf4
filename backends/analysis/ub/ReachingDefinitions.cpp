//
// Created by dragos on 18.09.2019.
//

#include "ReachingDefinitions.h"

namespace analysis {

void ReachingDefinitions::compute_reverse() {
  traverse_df_pernode(g, start, [&](const node_t &at) {
    for (auto instr : instructions(at)) {
      auto &w = ws[instr];
      for (auto &mp : w)
        reverse_writes[mp].push_back(instr);
    }
  });
  traverse_df_pernode(g, start, [&](const node_t &at) {
    for (auto instr : instructions(at)) {
      auto &r = rs[instr];
      for (auto &mp : r) {
        reverse_writes.emplace(mp, NodeVector());
      }
    }
  });
  size_t max = 0;
  main_index = new Index<std::pair<MemPath, node_t>>();
  size_t mainidx = 0;
  for (auto &mpw : reverse_writes) {
    size_t idx = 0;
    Index<node_t> *&crt = indices[mpw.first];
    if (!crt)
      crt = new Index<node_t>();
    crt->emplace(node_t::before(), idx++);
    main_index->emplace(std::make_pair(mpw.first, node_t::before()), mainidx++);
    for (auto &x : mpw.second) {
      crt->emplace(x, idx++);
      BUG_CHECK(
          main_index->emplace(std::make_pair(mpw.first, x), mainidx++).second,
          "%1% writes twice to %2%", x, mpw.first);
    }
    max += idx;
  }
  undefined = new Lattice(main_index);
  for (auto &rw : reverse_writes) {
    undefined->arr.set(
        undefined->idx->at({rw.first, analysis::node_t::before()}));
  }
  LOG4("#mem paths " << indices.size() << " max size: " << max);
}
Index<node_t> *ReachingDefinitions::index(const MemPath &mp) {
  auto I = indices.find(mp);
  BUG_CHECK(I != indices.end(), "%1% memory path not indexed");
  return I->second;
}
bvset<node_t> ReachingDefinitions::fresh(const MemPath &mp) {
  return {index(mp)};
}
ReachingDefinitions::Lattice ReachingDefinitions::operator()() {
  return *undefined;
}
ReachingDefinitions::ReachingDefinitions(ReferenceMap *refMap, TypeMap *typeMap,
                                         const EdgeHolder *g,
                                         const node_t &start,
                                         NodeToFunctionMap *funMap)
    : refMap(refMap), typeMap(typeMap), g(g), start(start),
      rs(refMap, typeMap, funMap), ws(refMap, typeMap, funMap) {
  compute_reverse();
}
NodeValues<ReachingDefinitions::Lattice>
ReachingDefinitions::reachingDefinitions(ReferenceMap *refMap, TypeMap *typeMap,
                                         const CFG &g,
                                         NodeToFunctionMap *funmap) {
  DefaultDiscipline dd(&g.holder, g.start_node);
  ReachingDefinitions rd(refMap, typeMap, &g.holder, g.start_node, funmap);
  NodeValues<Lattice> res({{g.start_node, rd()}});
  auto rr = std::ref(rd);
  WorklistAlgo<Lattice, decltype(rr), DefaultDiscipline, decltype(rr),
               decltype(rr)>
      algo(g, rr, dd, rr, rr);
  algo(g.start_node, res);
  return std::move(res);
}

ReachingDefinitions::Lattice ReachingDefinitions::
operator()(node_t n, const Edge &e, const ReachingDefinitions::Lattice &l) {
  if (is_basic_block(n)) {
    auto crt = l;
    for (auto instr : instructions(n)) {
      crt = operator()(instr, e, crt);
    }
    return crt;
  }
  auto &w = ws[n];
  auto c = l;
  for (auto &x : w) {
    c.arr.set(main_index->find({x, n})->second);
    for (auto &other : *(indices[x])) {
      if (other.first != n)
        c.arr.reset(main_index->find({x, other.first})->second);
    }
  }
  return c;
}

ReachingDefinitions::Lattice ReachingDefinitions::
operator()(const ReachingDefinitions::Lattice &l,
           ReachingDefinitions::Lattice r) {
  r.arr |= l.arr;
  return r;
}

ReachingDefinitions::Lattice ReachingDefinitions::
operator()(node_t n, const Edge &, const ReachingDefinitions::Lattice &,
           const ReachingDefinitions::Lattice &) {
  BUG("%1% should not be reachable", n);
}

NodeValues<analysis::bvset<std::pair<analysis::MemPath, analysis::node_t>>>
ReachingDefinitions::reachingDefinitions(ReferenceMap *refMap, TypeMap *typeMap,
                                         EdgeHolder &g, const node_t &start,
                                         NodeToFunctionMap *funmap) {
  auto cfg = new CFG(nullptr, std::move(g));
  cfg->start_node = start;
  auto ret = reachingDefinitions(refMap, typeMap, *cfg, funmap);
  g = std::move(cfg->holder);
  return std::move(ret);
}

LiveVariables::LiveVariables(ReferenceMap *refMap, TypeMap *typeMap,
                             const EdgeHolder *g, const node_t &start,
                             NodeToFunctionMap *funmap)
    : refMap(refMap), typeMap(typeMap), g(g), start(start),
      rs(refMap, typeMap, funmap), ws(refMap, typeMap, funmap) {
  buildIndex();
}

void LiveVariables::buildIndex() {
  indices = new analysis::Index<MemPath>();
  // 0: postorder traversal of graph
  auto sorted = analysis::topo_sort(g, start);
  // 1: build up mempath indices
  for (const auto &n : sorted) {
    for (auto instr : instructions(n)) {
      auto &rds = rs[instr];
      auto &wts = ws[instr];
      for (auto &r : rds)
        indices->emplace(r, indices->size());
      for (auto &w : wts)
        indices->emplace(w, indices->size());
    }
  }
  // 2: compute per basic block stuff
  bvset<MemPath> wrts(indices);
  bvset<MemPath> rdds(indices);
  bvset<MemPath> shallPreclude(indices);
  for (const auto &n : sorted) {
    auto DEMI = def.emplace(n, indices);
    auto UEMI = use.emplace(n, indices);
    shallPreclude.arr.reset();
    for (auto instr : instructions(n)) {
      auto &rds = rs[instr];
      auto &wts = ws[instr];
      wrts.arr.reset();
      rdds.arr.reset();
      for (auto &r : rds) {
        auto XX = indices->find(r);
        rdds.arr.set(XX->second);
      }
      for (auto &w : wts) {
        auto XX = indices->find(w);
        wrts.arr.set(XX->second);
      }
      if (DEMI.second)
        DEMI.first->second.arr |= wrts.arr;
      if (UEMI.second)
        UEMI.first->second.arr |= (rdds.arr & ~shallPreclude.arr);
      shallPreclude.arr |= DEMI.first->second.arr;
    }
  }

  // 3: chaotic iterations in postorder
  bool change = true;
  bvset<MemPath> old(indices);
  while (change) {
    change = false;
    for (auto &n : sorted) {
      // traverse in postorder to quicken convergence
      auto outEMI = out.emplace(n, indices);
      auto &inN = in.emplace(n, indices).first->second;
      auto &outN = outEMI.first->second;
      auto Isucc = g->find(n);
      if (Isucc != g->end()) {
        if (!outEMI.second)
          outN.arr.reset();
        for (auto &succ : Isucc->second) {
          outN.arr |= getOrEmplace(in, succ.first, [this]() {
                        return bvset<MemPath>(indices);
                      }).first.arr;
        }
      }
      // avoid copying if change is set
      if (!change)
        old.arr = inN.arr;
      inN.arr = use[n].arr | (outN.arr & ~def[n].arr);
      if (!change && old.arr != inN.arr) {
        change = true;
      }
    }
  }
}

bool LiveVariables::live(const node_t &n, const MemPath &mp) {
  auto I = in.find(n);
  if (I != in.end())
    return I->second.arr[indices->at(mp)];
  return false;
}

unsigned iterable_index::count(const MemPath &mp) {
  unsigned sum = 0;
  for (const auto &nd : idx->hierarchical[mp])
    if (valof->arr[nd.second])
      ++sum;
  return sum;
}

iterable_index::iterable_index(easy_index *idx,
                               bvset<std::pair<MemPath, node_t>> *valof)
    : idx(idx), valof(valof) {}

std::vector<node_t> iterable_index::of(const MemPath &mp) {
  std::vector<node_t> v;
  for (const auto &nd : idx->hierarchical[mp])
    if (valof->arr[nd.second])
      v.emplace_back(nd.first);
  return std::move(v);
}

easy_index::easy_index(
    Index<std::pair<analysis::MemPath, analysis::node_t>> *main_index)
    : main_index(main_index) {
  for (const auto &pr : *main_index)
    hierarchical[pr.first.first][pr.first.second] = pr.second;
}

iterable_index easy_index::with(bvset<std::pair<MemPath, node_t>> *valof) {
  return {this, valof};
}
}