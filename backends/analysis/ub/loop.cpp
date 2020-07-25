//
// Created by dragos on 02.09.2019.
//

#include "loop.h"

namespace analysis {

bool LoopLattice::operator==(const LoopLattice &other) const {
  return paths == other.paths;
}
LoopLattice LoopLattice::operator+(const LoopLattice &other) const {
  std::unordered_set<IPCPath> united = paths;
  united.insert(other.paths.begin(), other.paths.end());
  return united;
}
bool LoopLattice::isBottom() const { return paths.empty(); }
LoopLattice::LoopLattice(std::unordered_set<IPCPath> paths)
    : paths(std::move(paths)) {}

LoopLattice Transfer::operator()(node_t n, const Edge &e,
                                 const LoopLattice &other) {
  std::unordered_set<IPCPath> next_paths;
  for (auto &q : other.paths) {
    if (q.oob)
      continue;
    if (auto p = transfer({n, e}, q)) {
      next_paths.emplace(std::move(*p));
    }
  }
  return next_paths;
}

LoopLattice Transfer::operator()(node_t n, const Edge &e, const LoopLattice &,
                                 const LoopLattice &lend) {
  return this->operator()(n, e, lend);
}

boost::optional<IPCPath> Transfer::transfer(FullEdge_t fe,
                                            const IPCPath &l) const {
  if (l.oob)
    return IPCPath(l.oob);
  auto lprime = l;
  auto bes = back_edges(fe.source);
  if (same_scc(fe.source, fe.dst)) {
    if (bes && bes->find(fe) != bes->end()) {
      lprime.push(fe);
    }
    if (is_out_of_bounds(lprime)) {
      return IPCPath(true);
    }
    return lprime;
  } else {
    if (bes) {
      for (auto &be : *bes) {
        lprime.remove(be);
      }
    }
    return lprime;
  }
}

bool Transfer::is_out_of_bounds(const IPCPath &p) const {
  std::unordered_map<FullEdge_t, unsigned> occs;
  for (auto &x : p.edges) {
    occs[x]++;
  }
  for (auto &fe : occs) {
    auto I = limits.find(fe.first);
    if (I != limits.end())
      if (I->second < fe.second)
        return true;
  }
  return false;
}

Transfer::Transfer(const NodeValues<unsigned int> &sccs,
                   const std::vector<std::unordered_set<node_t>> &rev_sccs,
                   const std::vector<std::unordered_set<FullEdge_t>> &back,
                   const std::unordered_map<FullEdge_t, unsigned int> &limits)
    : sccs(sccs), rev_sccs(rev_sccs), back(back), limits(limits) {}

void change_node(EdgeHolder *holder, const node_t &n, const node_t &to) {
  auto I = holder->find(n);
  if (I != holder->end()) {
    auto ens = std::move(I->second);
    holder->erase(I->first);
    (*holder)[to] = std::move(ens);
  }
  for (auto &x : *holder) {
    for (auto &nn : x.second) {
      if (nn.first == n)
        nn.first = to;
    }
  }
}

// ensures invariant: for each pair [CALL] -> [RETURN]
// label(CALL) == label(RETURN)
void fix_holder(EdgeHolder *holder) {
  std::unordered_map<node_t, node_t> call_to_return;
  for (auto &n : *holder) {
    for (auto &nn : n.second) {
      if (edgeType(nn) == EdgeType::CALL_TO_RETURN)
        call_to_return.emplace(n.first, nn.first);
    }
  }
  for (auto &c2r : call_to_return) {
    auto old = c2r.second;
    old.label = c2r.first.label;
    change_node(holder, c2r.second, old);
  }
}

void unroll(EdgeHolder *holder, node_t &start, NodeToFunctionMap *funMap,
            unsigned max_out, bool is_bug, NodeValues<node_t> *parents) {
  START(unroll);
  auto thisgraph = mkCallGraph(holder);
  std::vector<node_t> sorted;
  std::vector<std::unordered_set<node_t>> sccs;
  auto loops = thisgraph.sccSort(start, sorted, sccs);

  struct Cloner {
    NodeToFunctionMap *funMap;
    NodeValues<std::unordered_map<IPCPath, node_t>> clones;
    NodeValues<node_t> *parents;

    Cloner(NodeToFunctionMap *funMap, NodeValues<node_t> *parents)
        : funMap(funMap), parents(parents) {}

    node_t clone(node_t n, const IPCPath &p) {
      auto &X = clones[n];
      auto I = X.emplace(p, n);
      if (I.second) {
        I.first->second.label = ++node_t::LABEL;
        if (n.type != NodeType::RETURN) {
          if (auto clee = funMap->callee(n)) {
            funMap->put(I.first->second, clee, funMap->instance(n));
          }
        }
      }
      auto &nd = I.first->second;
      if (parents) parents->emplace(nd, n);
      return nd;
    }
    node_t clone(node_t n) { return clone(n, {}); }
  };
  Cloner cloner(funMap, parents);

  if (loops) {
    LOG4("loops found, going to handle them");
    auto copy = *holder;
    auto newstart = start;
    bool changed = false;
    auto idxes = sccIndices(sccs);
    for (auto &scc : sccs) {
      if (scc.size() > 1) {
        // this is a loop
        // find loop head - if !unique, then for each entry:
        // remove subgraph from nodes
        std::unordered_map<node_t, std::unordered_set<node_t>> entries;
        for (auto &n : scc) {
          auto callers = thisgraph.getCallers(n);
          if (callers) {
            for (auto &c : *callers) {
              if (idxes[c] != idxes[n]) {
                entries[n].emplace(c);
              }
            }
          }
        }
        if (entries.size() > 1) {
          changed = true;
          // step 1: remove subgraph from copy
          EdgeHolder nxt;
          for (auto &f : copy) {
            if (scc.count(f.first))
              continue;
            EdgeEnumerator edgeEnumerator;
            for (auto &x : f.second) {
              if (!scc.count(x.first))
                edgeEnumerator.emplace_back(x.first, x.second);
            }
            nxt[f.first] = std::move(edgeEnumerator);
          }
          copy = std::move(nxt);
          // step 2: for each e entry point, clone scc
          // and for each edge(x, y) do not add it if
          // y an entry point to scc different from e
          for (auto &entry : entries) {
            for (auto &x : *holder) {
              if (scc.count(x.first)) {
                auto xprime = cloner.clone(x.first);
                if (x.first == start)
                  newstart = xprime;
                auto &neighsprime = copy[xprime];
                for (auto &y : x.second) {
                  auto yprime = y.first;
                  if (scc.count(y.first)) {
                    yprime = cloner.clone(y.first);
                  }
                  neighsprime.emplace_back(yprime, y.second);
                }
              } else {
                for (auto &y : x.second) {
                  if (scc.count(y.first)) {
                    if (y.first == entry.first) {
                      copy[x.first].emplace_back(cloner.clone(y.first),
                                                 y.second);
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
    if (changed) {
      thisgraph = mkCallGraph(&copy);
      sorted.clear();
      sccs.clear();
      loops = thisgraph.sccSort(start, sorted, sccs);
    }
    if (loops) {
      std::vector<analysis::FullEdge_t> tree;
      std::vector<analysis::FullEdge_t> cross;
      std::vector<analysis::FullEdge_t> back;
      analysis::find_back_edges(&copy, newstart, back, tree, cross);
      std::vector<std::unordered_set<FullEdge_t>> scc2backs(sccs.size());
      std::unordered_map<FullEdge_t, unsigned> limits;
      for (auto &ed : back) {
        LOG4("back edge: " << ed);
        scc2backs[idxes[ed.source]].emplace(ed);
        limits[ed] = max_out;
      }
      CFG cfg(nullptr, std::move(copy), true);
      cfg.start_node = newstart;
      Transfer transfer(idxes, sccs, scc2backs, limits);
      DefaultDiscipline defaultDiscipline(&cfg, newstart);
      WorklistAlgo<Transfer::LatticeType, Transfer, DefaultDiscipline>
          worklistAlgo(cfg, transfer, defaultDiscipline);
      NodeValues<Transfer::LatticeType> res(
          {{newstart, LoopLattice({IPCPath()})}});
      worklistAlgo(newstart, res);

      auto pnext = new EdgeHolder();
      auto &next = *pnext;
      cstring metname = analysis::AnalysisLibrary::instance.oob.name;
      if (is_bug)
        metname = analysis::AnalysisLibrary::instance.bug.name;

      auto oob = [&](const node_t &parent) {
        node_t oob_node(analysis::mcs_call(metname, {}), NodeType::NORMAL);
        oob_node = oob_node.clone(++node_t::LABEL);
        if (parents) (*parents)[oob_node] = parent;
        return oob_node;
      };
      for (auto &nv : res) {
        auto candidates = cfg[nv.first];
        if (!candidates.empty()) {
          for (auto neigh : candidates) {
            auto fledge = FullEdge_t(nv.first, neigh);
            for (const auto &xval : nv.second.paths) {
              auto xxnode = cloner.clone(nv.first, xval);
              if (nv.first == newstart && !xval.oob && xval.edges.empty()) {
                start = xxnode;
              }
              auto &xxneighs = next[xxnode];
              if (auto transd = transfer.transfer(fledge, xval)) {
                if (transd->oob) {
                  xxneighs.emplace_back(oob(xxnode), neigh.second);
                } else {
                  for (const auto &yval : res[neigh.first].paths) {
                    if (*transd == yval) {
                      auto yynode = cloner.clone(neigh.first, yval);
                      xxneighs.emplace_back(yynode, neigh.second);
                    }
                  }
                }
              }
            }
          }
        }
      }
      *holder = std::move(*pnext);
      removeDeadNodes(holder, start);
      fix_holder(holder);
      for (auto &n : *holder) {
        if (n.first.type == NodeType::RETURN) {
          node_t caller(n.first, NodeType::CALL);
          funMap->put(n.first, funMap->callee(caller),
                      funMap->instance(caller));
        }
        for (auto &nn : n.second) {
          if (nn.first.type == NodeType::RETURN) {
            node_t caller(nn.first, NodeType::CALL);
            funMap->put(nn.first, funMap->callee(caller),
                        funMap->instance(caller));
          }
        }
      }
    } else {
      BUG("can't be");
    }
  }
  END(unroll);
  auto dr = DURATION(unroll);
  std::cerr << "done unrolling " << loops << " " << holder->size() << " in "
            << dr << "ms\n";
}

std::size_t hash_value(const IPCPath &e) {
  if (e.oob) {
    return 0;
  }
  auto bh = boost::hash_range(e.edges.begin(), e.edges.end());
  if (bh == 0)
    bh++;
  return bh;
}
}