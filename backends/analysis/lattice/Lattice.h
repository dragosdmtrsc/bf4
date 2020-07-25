//
// Created by dragos on 29.07.2019.
//

#ifndef P4C_LATTICE_H
#define P4C_LATTICE_H

#include <analysis/cfg_algos.h>
#include <analysis/context/InterproceduralCFGs.h>
#include <p4/callGraph.h>

namespace analysis {

template <typename Elem>
class LatticeElement {
 public:
  virtual bool operator==(const Elem &other) const = 0;
  virtual bool operator!=(const Elem &o) const { return !operator==(o); }
  virtual Elem operator+(const Elem &other) const = 0;
  virtual bool isBottom() const = 0;
  operator bool() const { return !isBottom(); }
};

template <typename L>
class LatticeOps {
 public:
  virtual L bottom() const { return L(); };

  template <typename _It>
  L LUB(_It begin, _It end) const {
    L _x = bottom();
    for (; begin != end; ++begin) {
      _x = _x + *begin;
    }
    return _x;
  }

  template <typename Container>
  const L *find(const Container &pernode, node_t n) {
    auto IV = pernode.find(n);
    if (IV != pernode.end()) {
      return &IV->second;
    }
    return nullptr;
  }
  template <typename Container>
  L *find(Container &pernode, node_t n) {
    auto IV = pernode.find(n);
    if (IV != pernode.end()) {
      return &IV->second;
    }
    return nullptr;
  }
  template <typename Container>
  void set(Container &pernode, node_t n, L val) {
    pernode[n] = val;
  }
};

template <std::size_t... S>
struct seq {};

template <std::size_t N, std::size_t... S>
struct gens : gens<N - 1, N - 1, S...> {};

template <std::size_t... S>
struct gens<0, S...> {
  typedef seq<S...> type;
};

template <typename... Ls>
bool isBottomHelp(const std::tuple<Ls...> &t, seq<>) {
  return true;
}
template <typename... Ls, std::size_t S1, std::size_t... S>
bool isBottomHelp(const std::tuple<Ls...> &t, seq<S1, S...>) {
  return std::get<S1>(t).isBottom() && isBottomHelp(t, seq<S...>());
}

template <typename... Ls>
class TupleLattice : public LatticeElement<TupleLattice<Ls...>> {
 public:
  std::tuple<Ls...> t;
  TupleLattice(Ls... ls) : t(ls...) {}
  bool operator==(const TupleLattice<Ls...> &other) const override {
    return t == other.t;
  }

  template <std::size_t... S>
  static std::tuple<Ls...> plus_help(const std::tuple<Ls...> &t1,
                                     const std::tuple<Ls...> &t2, seq<S...>) {
    return std::tuple<Ls...>((std::get<S>(t1) + std::get<S>(t2))...);
  }

  TupleLattice<Ls...> operator+(
      const TupleLattice<Ls...> &other) const override {
    return plus_help(t, other.t, typename gens<sizeof...(Ls)>::type());
  }
  bool isBottom() const override {
    return isBottomHelp(t, typename gens<sizeof...(Ls)>::type());
  }
};

template <typename Context, typename L>
class MapLattice : public LatticeElement<MapLattice<Context, L>> {
 public:
  using MapType = std::unordered_map<Context, L>;
  MapType mapping;
  static std::unordered_map<Context, L> lmerge(
      const std::unordered_map<Context, L> &l,
      const std::unordered_map<Context, L> &r) {
    std::unordered_map<Context, L> nxt;
    for (auto &elem : l) {
      auto I = r.find(elem.first);
      if (I != r.end()) {
        nxt[elem.first] = std::move(I->second + elem.second);
      } else {
        nxt[elem.first] = elem.second;
      }
    }
    return nxt;
  };

 public:
  MapLattice() {}
  MapLattice(const std::unordered_map<Context, L> &mapping)
      : mapping(mapping) {}
  MapLattice(std::unordered_map<Context, L> &&mapping) : mapping(mapping) {}

  bool operator==(const MapLattice<Context, L> &other) const override {
    if (isBottom() != other.isBottom()) return false;
    if (isBottom()) return true;
    return other.mapping == mapping;
  }
  MapLattice<Context, L> operator+(
      const MapLattice<Context, L> &other) const override {
    auto ml = lmerge(mapping, other.mapping);
    auto mr = lmerge(other.mapping, std::move(ml));
    return std::move(mr);
  }
  bool isBottom() const override { return mapping.empty(); }
};

template <typename L>
struct _DefaultMerge {
  L operator()(const L &l1, L l2) { return l1 + l2; }
};

template <typename L>
struct _DefaultFactory {
  L operator()() { return L(); }
};

template <
    typename L, typename Transfer, typename Discipline = std::less<node_t>,
    typename Merge = _DefaultMerge<L>, typename Factory = _DefaultFactory<L>>
class WorklistAlgo {
  const CFG &current;
  Transfer xfer;
  Discipline discipline;
  LatticeOps<L> lops;
  Merge merge;
  Factory factory;

 public:
  WorklistAlgo(const CFG &current, Transfer xfer)
      : current(current), xfer(xfer), discipline(Discipline()) {}
  WorklistAlgo(const CFG &current, Transfer xfer, Discipline discipline)
      : current(current), xfer(xfer), discipline(discipline) {}
  WorklistAlgo(const CFG &current, Transfer xfer, Discipline discipline,
               LatticeOps<L> lops)
      : current(current), xfer(xfer), discipline(discipline), lops(lops) {}
  WorklistAlgo(const CFG &current, Transfer xfer, Discipline discipline,
               Merge merge)
      : current(current), xfer(xfer), discipline(discipline), merge(merge) {}
  WorklistAlgo(const CFG &current, Transfer xfer, Discipline discipline,
               Merge merge, Factory factory)
      : current(current),
        xfer(xfer),
        discipline(discipline),
        merge(merge),
        factory(factory) {}

  void operator()(node_t start, std::unordered_map<node_t, L> &result) {
    std::set<node_t, Discipline> worklist({start}, discipline);
    auto nriters = 0;
    START(chaotic);
    while (!worklist.empty()) {
      nriters++;
      auto nowat = *worklist.begin();
      worklist.erase(worklist.begin());
      auto val = lops.find(result, nowat);
      if (!val) continue;
      auto neighs = current[nowat];
      if (neighs) {
        bool is_ret_call = nowat.type == NodeType::END;
        for (auto n : *neighs) {
          L nxtval(factory());
          if (is_ret_call && edgeType(n) == EdgeType::RETURN) {
            auto callnode = node_t(n.first, NodeType::CALL);
            auto at_call = lops.find(result, callnode);
            if (at_call) {
              nxtval = xfer(nowat, n, *at_call, *val);
            }
          } else {
            nxtval = xfer(nowat, n, *val);
          }
          auto old = lops.find(result, n.first);
          if (old) {
            auto merged = merge(*old, std::move(nxtval));
            if (merged != *old) {
              *old = std::move(merged);
              worklist.emplace(n.first);
            }
          } else {
            //            if (!nxtval.isBottom()) {
            result.emplace(n.first, nxtval);
            worklist.emplace(n.first);
            //            }
          }
        }
      }
    }
    END(chaotic);
    auto dr = DURATION(chaotic);
    std::cerr << "done chaotic iterations " << current.holder.size()
              << ", iters: " << nriters << " in " << dr << " ms\n";
  }
};

class DefaultDiscipline {
 public:
  const CFG *graph;
  std::vector<node_t> sorted;
  std::unordered_map<node_t, unsigned> priorities;

  void buildDiscipline(node_t start);

  DefaultDiscipline(const EdgeHolder *holder, node_t start);
  DefaultDiscipline(const CFG *graph, node_t start);
  bool operator()(node_t l, node_t r);
};

template <typename V>
class Propagate {
 public:
  using LatticeType = V;
  virtual V operator()(node_t n, const Edge &e, const V &other) = 0;
  virtual V operator()(node_t n, const Edge &e, const V &lcall,
                       const V &lend) = 0;
};
}

#endif  // P4C_LATTICE_H
