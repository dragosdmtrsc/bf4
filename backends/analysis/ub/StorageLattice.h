//
// Created by dragos on 14.08.2019.
//

#ifndef P4C_STORAGELATTICE_H
#define P4C_STORAGELATTICE_H

#include <analysis/lattice/Lattice.h>
#include <analysis/version_propagator.h>
#include <p4/def_use.h>

namespace analysis {
class GetStorage : public Inspector {
  const P4::StorageMap *storageMap;
  std::map<const IR::Expression *, const LocationSet *> locations;

 public:
  GetStorage(const P4::StorageMap *storageMap) : storageMap(storageMap) {
    visitDagOnce = false;
  }

  const LocationSet *locationSet(const P4::StorageMap *storageMap,
                                 const IR::Expression *expr) {
    this->storageMap = storageMap;
    locations.clear();
    expr->apply(*this);
    auto I = locations.find(expr);
    if (I != locations.end()) {
      return I->second;
    } else {
      return nullptr;
    }
  }

 private:
  void postorder(const IR::PathExpression *pe) override {
    auto pref = storageMap->refMap->getDeclaration(pe->path);
    auto storage = storageMap->getStorage(pref);
    if (!storage) {
      return;
    }
    locations.emplace(pe, new LocationSet({storage}));
  }

  void postorder(const IR::Member *mem) override {
    auto memt = storageMap->typeMap->getType(mem);
    if (memt->is<IR::Type_MethodBase>()) {
      if (mem->member == IR::Type_Header::isValid) {
        locations[mem] = locations[mem->expr]->getValidField();
      }
    } else {
      if (!locations[mem->expr]) return;
      locations[mem] = locations[mem->expr]->getField(mem->member);
    }
  }

  void postorder(const IR::ArrayIndex *aindex) override {
    if (aindex->right->is<IR::Constant>()) {
      locations[aindex] = locations[aindex->left]->getIndex(
          aindex->right->to<IR::Constant>()->asUnsigned());
    } else {
      locations[aindex] = locations[aindex->left]->allElements();
    }
  }
};

struct limited_call_string {
  size_t k;
  std::vector<const IR::Node *> stack;
  limited_call_string(size_t k);
  limited_call_string push(const IR::Node *n) const;
  operator P4::ProgramPoint() const;
  size_t hash() const;
  bool operator==(const limited_call_string &lcs) const;
};
struct EdgeVersions {
  std::map<FullEdge_t, unsigned> edges;

  EdgeVersions(const std::map<FullEdge_t, unsigned int> &edges)
      : edges(edges) {}

  bool operator<(const EdgeVersions &ev) const { return edges < ev.edges; }
  EdgeVersions zeros() const {
    auto m = edges;
    for (auto &x : m) x.second = 0;
    return m;
  }

  bool operator==(const EdgeVersions &ev) const { return edges == ev.edges; }

  unsigned &operator[](const FullEdge_t &x) { return edges[x]; }
};
}

namespace std {
template <>
struct hash<analysis::EdgeVersions> {
  size_t operator()(const analysis::EdgeVersions &ev) const {
    return boost::hash_range(ev.edges.begin(), ev.edges.end());
  }
};
template <>
struct hash<analysis::limited_call_string> {
  typedef analysis::limited_call_string argument_type;
  typedef std::size_t result_type;
  result_type operator()(argument_type const &s) const { return s.hash(); }
};
};  // namespace std

namespace analysis {
template <typename V>
using EdgeVersionLattice = MapLattice<EdgeVersions, V>;

template <typename V, typename VPropagator>
class VersionPropagator : private VPropagator {
  EdgeVersions limits;

 public:
  using LatticeType = EdgeVersionLattice<V>;

  VersionPropagator(VPropagator &&prop, EdgeVersions limits)
      : VPropagator(std::move(prop)), limits(std::move(limits)) {}

 private:
  bool beyond(const EdgeVersions &o) const {
    for (auto &l : limits.edges) {
      auto oval = o.edges.find(l.first);
      unsigned crt = 0;
      if (oval != o.edges.end()) crt = oval->second;
      if (crt > l.second) {
        return true;
      }
    }
    return false;
  }
  bool isInteresting(const FullEdge_t &fe) const {
    auto I = limits.edges.find(fe);
    return I != limits.edges.end();
  }

 public:
  EdgeVersionLattice<V> operator()(node_t start, const Edge &e,
                                   const EdgeVersionLattice<V> &ev) {
    FullEdge_t fe(start, e);
    EdgeVersionLattice<V> retv;
    auto interestingEdge = isInteresting(fe);
    for (auto &x : ev.mapping) {
      auto versions = x.first;
      if (interestingEdge) {
        versions[fe]++;
      }
      if (interestingEdge && beyond(versions)) {
        retv.mapping[versions] = LatticeOps<V>().bottom();
      } else {
        retv.mapping[versions] = VPropagator::operator()(start, e, x.second);
      }
    }
    return retv;
  }

  EdgeVersionLattice<V> operator()(node_t caller, const Edge &e,
                                   const EdgeVersionLattice<V> &lcall,
                                   const EdgeVersionLattice<V> &lend) {
    FullEdge_t fe(caller, e);
    EdgeVersionLattice<V> retv;
    auto interestingEdge = isInteresting(fe);
    for (auto &x : lend.mapping) {
      auto versions = x.first;
      if (interestingEdge) {
        LOG4("found interesting edge " << fe);
        versions[fe]++;
      }
      auto I = lcall.mapping.find(x.first);
      auto II = lend.mapping.find(x.first);
      if (interestingEdge && beyond(versions)) {
        LOG4("interesting edge above the top " << fe);
        retv.mapping[versions] = LatticeOps<V>().bottom();
      } else {
        if (I != lcall.mapping.end() && II != lend.mapping.end()) {
          retv.mapping[versions] =
              VPropagator::operator()(caller, e, I->second, II->second);
        }
      }
    }
    return retv;
  }
};

template <typename V>
using CallStringLattice = MapLattice<limited_call_string, V>;

template <typename V, typename VPropagator>
class CallStringPropagate : private VPropagator {
  NodeToFunctionMap *funMap;

  CallStringPropagate(VPropagator &&prop, NodeToFunctionMap *funMap)
      : VPropagator(std::move(prop)), funMap(funMap) {}

  CallStringLattice<V> operator()(node_t nod, const Edge &e,
                                  const CallStringLattice<V> &v) {
    CallStringLattice<V> nxtv;
    if (nod.type == NodeType::CALL) {
      for (auto &p : v.mapping) {
        auto ctxprime = p.first.push(nod);
        nxtv.mapping[ctxprime] = VPropagator::operator()(nod, e, p.second);
      }
    } else {
      for (auto &p : v.mapping) {
        nxtv.mapping[p.first] = VPropagator::operator()(nod, e, p.second);
      }
    }
    return nxtv;
  }
  CallStringLattice<V> operator()(node_t node, const Edge &edge,
                                  const CallStringLattice<V> &lcall,
                                  const CallStringLattice<V> &lend) {
    CallStringLattice<V> ml;
    for (auto &avail : lend.mapping) {
      auto &currentContext = avail.first;
      auto &defs = avail.second;
      node_t caller(edge.first, NodeType::CALL);
      if (lcall.isBottom()) return ml;
      // if [[ caller ]] is unreach => this is definitely not the
      // caller
      // we are looking for
      for (auto &p : lcall.mapping) {
        auto ctxprime = p.first;
        auto ctxsecond = ctxprime.push(caller.node);
        if (ctxsecond == currentContext) {
          ml.mapping[ctxprime] =
              VPropagator::operator()(node, edge, p.second, avail.second);
        }
      }
    }
    return ml;
  }
};

template <typename V, typename VPropagator>
struct DeadAwarePropagation : public VPropagator {
  const NodeValues<bool> &dead;

 public:
  using LatticeType = V;
  DeadAwarePropagation(VPropagator &&prop, const NodeValues<bool> &dead)
      : VPropagator(std::move(prop)), dead(dead) {}

 private:
  bool isdead(const node_t n) const {
    auto I = dead.find(n);
    if (I != dead.end()) return I->second;
    return false;
  }

 public:
  V operator()(node_t n, const Edge &e, const V &v) {
    if (isdead(e.first)) return LatticeOps<V>().bottom();
    return VPropagator::operator()(n, e, v);
  }
  V operator()(node_t n, const Edge &e, const V &lcall, const V &lend) {
    if (isdead(e.first)) return LatticeOps<V>().bottom();
    return VPropagator::operator()(n, e, lcall, lend);
  }
};

template <typename V, typename VPropagator>
DeadAwarePropagation<V, VPropagator> make_dead_propagator(
    VPropagator prop, const NodeValues<bool> &dead) {
  return DeadAwarePropagation<V, VPropagator>(std::move(prop), dead);
};
};

#endif  // P4C_STORAGELATTICE_H
