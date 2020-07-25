//
// Created by dragos on 17.12.2018.
//

#ifndef P4C_CFG_ALGOS_H
#define P4C_CFG_ALGOS_H

#include "analysis_helpers.h"
#include <boost/functional/hash.hpp>
#include <boost/variant.hpp>
#include <common/resolveReferences/referenceMap.h>
#include <frontends/p4/callGraph.h>
#include <p4/methodInstance.h>
#include <p4/typeMap.h>

namespace analysis {
using namespace P4;

enum class NodeType { NORMAL, CALL, RETURN, START, END, UNKNOWN };
struct node_t {
  static size_t LABEL;
  const IR::Node *node;
  NodeType type;
  size_t label;
  node_t() : node(nullptr), type(NodeType::NORMAL), label(0) {}
  node_t(const IR::Node *node) : node(node), type(NodeType::NORMAL), label(0) {}
  node_t(const IR::Node *node, NodeType type)
      : node(node), type(type), label(0) {}
  node_t(node_t n, NodeType type) : node(n.node), type(type), label(n.label) {}
  static node_t before() { return {nullptr, NodeType::UNKNOWN}; }
  node_t clone(size_t lbl) const {
    auto n = *this;
    n.label = lbl;
    return n;
  }
  const IR::Node *operator->() const;
  operator const IR::Node *() const { return node; }
  bool operator<(const node_t &other) const;
  bool operator==(const node_t &other) const {
    return node == other.node && type == other.type && label == other.label;
  }
  std::string nodeId() const;
  friend std::ostream &operator<<(std::ostream &, const node_t &);
};

struct assign_t {
  const IR::Expression *lv;
  const IR::Expression *rv;
  assign_t(const IR::AssignmentStatement *asg)
      : lv(asg->left), rv(asg->right) {}
};
struct assign_ret_t {
  const IR::Expression *lv;
  const IR::MethodCallExpression *rv;
  NodeType nodeType;

  assign_ret_t(const IR::Expression *lv, const IR::MethodCallExpression *rv,
               NodeType nt)
      : lv(lv), rv(rv), nodeType(nt) {}
};
struct condition_t {
  const IR::Expression *cond;
  bool tt;

  condition_t(const IR::Expression *cond, bool tt) : cond(cond), tt(tt) {}
};

struct selex_case {
  std::vector<const IR::Expression *> exprs;
  std::vector<const IR::Expression *> match;

  selex_case(std::vector<const IR::Expression *> exprs,
             std::vector<const IR::Expression *> match)
      : exprs(std::move(exprs)), match(std::move(match)) {}
};
struct selex_default {
  std::vector<selex_case> cases;
  selex_default(std::vector<selex_case> cases) : cases(std::move(cases)) {}
};

typedef boost::variant<selex_case, selex_default> selex_t;

struct method_call_t {
  const IR::MethodCallStatement *methodCallStatement;
  NodeType type;

  method_call_t(const IR::MethodCallStatement *methodCallStatement,
                NodeType type)
      : methodCallStatement(methodCallStatement), type(type) {}
};
struct var_decl_t {
  const IR::Declaration *decl;
  var_decl_t(const IR::Declaration *decl) : decl(decl) {}
};
struct return_t {
  const IR::Expression *expression;
  return_t(const IR::Expression *expression) : expression(expression) {}
};

inline const IR::Node *actual_node(node_t n) {
  if (n.node->is<IR::IfStatement>()) {
    return n.node->to<IR::IfStatement>()->condition;
  }
  return n.node;
}

boost::optional<assign_t> is_assign(node_t n);
boost::optional<assign_ret_t> is_assign_ret(node_t n);
boost::optional<assign_ret_t> is_extern_assign_ret(node_t n);
boost::optional<return_t> is_return(node_t n);
boost::optional<method_call_t> is_method_call(node_t n);
boost::optional<method_call_t> is_extern_method_call(node_t n);
boost::optional<var_decl_t> is_var_decl(node_t n);
const IR::Vector<IR::Node> *is_basic_block(node_t n);

struct node_iterator {
  const IR::Vector<IR::Node> *nodes = nullptr;
  const IR::Node *singleton = nullptr;

  node_iterator(const IR::Vector<IR::Node> *nodes);
  node_iterator(const IR::Node *singleton);

  const IR::Node *const *begin() {
    if (nodes)
      return nodes->begin().base();
    return &singleton;
  }
  const IR::Node *const *end() {
    if (nodes)
      return nodes->end().base();
    return (&singleton) + 1;
  }
};

node_iterator instructions(node_t n);
inline size_t nr_instructions(node_t n) {
  return instructions(n).end() - instructions(n).begin();
}
const IR::Node *instruction_at(node_t n, unsigned);
inline const IR::Node *first(node_t n) { return instruction_at(n, 0); }
inline const IR::Node *last(node_t n) {
  auto Ivec = n.node->to<IR::Vector<IR::Node>>();
  if (!Ivec)
    return n.node;
  if (Ivec->empty())
    return nullptr;
  return Ivec->back();
}

inline std::size_t hash_value(const node_t &n) {
  std::size_t seed = 0;
  boost::hash_combine(seed, n.node);
  boost::hash_combine(seed, n.type);
  boost::hash_combine(seed, n.label);
  return seed;
}
}

namespace std {
template <> struct hash<analysis::node_t> {
  size_t operator()(const analysis::node_t &n) const {
    return analysis::hash_value(n);
  }
};
}

namespace analysis {

enum class EdgeType { NORMAL, CALL, RETURN, CALL_TO_RETURN, GOTO, UNKNOWN };
typedef std::pair<node_t, int> Edge;

std::vector<const IR::Expression *> getMatch(const IR::SelectCase *selcase);

#define selex_node(n)                                                          \
  (n.type == NodeType::NORMAL && n.node->is<IR::SelectExpression>())

boost::optional<selex_t> is_selex(node_t n, const Edge &e);

inline const IR::SelectExpression *match_selex(node_t n) {
  if (n.type == NodeType::NORMAL && n.node->is<IR::SelectExpression>())
    return n.node->to<IR::SelectExpression>();
  return nullptr;
}

boost::optional<condition_t> is_if(node_t n, const Edge &e,
                                   P4::TypeMap *typeMap);

EdgeType edgeType(int et);

EdgeType edgeType(const Edge &e);

inline int toNumber(EdgeType e) {
  switch (e) {
  case EdgeType::NORMAL:
    return 0;
  case EdgeType::CALL:
    return -1;
  case EdgeType::RETURN:
    return -2;
  case EdgeType::CALL_TO_RETURN:
    return -3;
  case EdgeType::GOTO:
    return -4;
  default:
    return -255;
  }
}

template <typename Node> struct AbsEdge {
  Node source;
  Node dst;
  int label;

  EdgeType type() const { return edgeType(label); }

  AbsEdge() = default;
  AbsEdge(Node source, Edge e)
      : source(source), dst(e.first), label(e.second) {}

  AbsEdge(Node source, Node dst, int label)
      : source(source), dst(dst), label(label) {}

  bool operator==(const AbsEdge<Node> &other) const {
    return source == other.source && dst == other.dst && label == other.label;
  }

  bool operator<(const AbsEdge<Node> &other) const {
    if (source != other.source)
      return source < other.source;
    if (dst != other.dst)
      return dst < other.dst;
    return label < other.label;
  }

  bool operator!=(const AbsEdge<Node> &other) const {
    return !operator==(other);
  }

  friend std::ostream &operator<<(std::ostream &os, const AbsEdge<Node> &ed) {
    return os << ed.source << " -> " << ed.dst << "[" << ed.label << "]";
  }
};

using FullEdge_t = AbsEdge<node_t>;
boost::optional<condition_t> is_if(const FullEdge_t &, P4::TypeMap *typeMap);
inline boost::optional<condition_t> is_if(node_t n, P4::TypeMap *typeMap) {
  return is_if(FullEdge_t(n, node_t::before(), 0), typeMap);
}
boost::optional<method_call_t> is_method_return(const FullEdge_t &);

std::size_t hash_value(const FullEdge_t &e);
}

namespace std {
template <> struct hash<analysis::FullEdge_t> {
  size_t operator()(const analysis::FullEdge_t &e) const {
    return analysis::hash_value(e);
  }
};
}

namespace analysis {

template <typename Container> class reverse_container {
  const Container &container;

public:
  reverse_container(const Container &container) : container(container) {}

  typename Container::const_reverse_iterator begin() const {
    return container.rbegin();
  }
  typename Container::const_reverse_iterator end() const {
    return container.rend();
  }
};
template <typename Container>
reverse_container<Container> make_reverse(const Container &c) {
  return {c};
}
bool isCall(const IR::Node *node);
class IdentifyMethodCalls : public Inspector {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  std::vector<P4::MethodInstance *> instances;

  void postorder(const IR::MethodCallExpression *mce) override {
    auto mi = P4::MethodInstance::resolve(mce, refMap, typeMap);
    instances.push_back(mi);
  }

public:
  IdentifyMethodCalls(ReferenceMap *refMap, TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}

  std::vector<P4::MethodInstance *> getMethods(const IR::Node *n) {
    instances.clear();
    n->apply(*this);
    return std::move(instances);
  }
  static std::vector<P4::MethodInstance *> getMethods(const IR::Node *n,
                                                      P4::ReferenceMap *refMap,
                                                      P4::TypeMap *typeMap) {
    IdentifyMethodCalls imc(refMap, typeMap);
    return imc.getMethods(n);
  }
};

typedef std::vector<Edge> EdgeEnumerator;
typedef std::map<node_t, EdgeEnumerator> EdgeHolder;
template <typename V> using NodeValues = std::unordered_map<node_t, V>;
using NodeSet = std::unordered_set<node_t>;
using NodeVector = std::vector<node_t>;

template <typename V> using EdgeValues = std::unordered_map<FullEdge_t, V>;

std::vector<analysis::node_t> topo_sort(const EdgeHolder *fwgraph);
std::vector<analysis::node_t> topo_sort(const EdgeHolder *fwgraph,
                                        node_t start);

template <typename ProcessNode, typename ProcessEdge>
void traverse_df(const EdgeHolder *graph, node_t start_node, ProcessNode pn,
                 ProcessEdge p) {
  std::vector<node_t> stack({start_node});
  std::set<node_t> visited;
  while (!stack.empty()) {
    start_node = stack.back();
    stack.pop_back();
    if (visited.emplace(start_node).second) {
      pn(start_node);
      auto neighIt = graph->find(start_node);
      if (neighIt != graph->end()) {
        for (auto &neigh : neighIt->second) {
          p(start_node, neigh);
          stack.emplace_back(neigh.first);
        }
      }
    }
  }
}

template <typename Filter>
EdgeHolder subgraph(const EdgeHolder *graph, Filter filter) {
  EdgeHolder next;
  for (auto &n : *graph) {
    if (filter(n.first)) {
      auto &neighs = next[n.first];
      for (auto &neigh : n.second) {
        if (filter(neigh.first))
          neighs.push_back(neigh);
      }
    }
  }
  return next;
}

template <typename ProcessNode, typename ProcessEdge>
void traverse_df_with_check(const EdgeHolder *graph, node_t start_node,
                            ProcessNode pn, ProcessEdge p) {
  std::vector<node_t> stack({start_node});
  std::set<node_t> visited;
  while (!stack.empty()) {
    start_node = stack.back();
    stack.pop_back();
    if (visited.emplace(start_node).second) {
      pn(start_node);
      auto neighIt = graph->find(start_node);
      if (neighIt != graph->end()) {
        for (auto &neigh : neighIt->second) {
          if (p(start_node, neigh))
            stack.emplace_back(neigh.first);
        }
      }
    }
  }
}

template <typename ProcessNode>
void traverse_df_pernode(const EdgeHolder *graph, node_t start_node,
                         ProcessNode p) {
  traverse_df(
      graph, start_node, p,
      [](const IR::Node *, const std::pair<const IR::Node *, int> &) {});
}

template <typename ProcessEdge>
void traverse_df(const EdgeHolder *graph, node_t start_node, ProcessEdge p) {
  traverse_df(graph, start_node, [](const IR::Node *) {}, p);
}

template <typename Label> struct _Default {
  Label operator()() { return Label(); }
};
std::set<node_t> find_start_nodes(const analysis::EdgeHolder *graph);
node_t find_start_node(const EdgeHolder *graph);

inline EdgeHolder *reverse(const EdgeHolder *graph) {
  auto bw = new EdgeHolder();
  for (auto &p : *graph) {
    for (auto &neigh : p.second) {
      auto EMI = bw->emplace(neigh.first, EdgeEnumerator());
      EMI.first->second.emplace_back(p.first, neigh.second);
    }
  }
  return bw;
}

void print_graph(const EdgeHolder *graph, bool withHeader, std::ostream &);

void classify(const EdgeHolder *graph, node_t,
              std::map<node_t, int> &start_times,
              std::map<node_t, int> &end_times);
void find_back_edges(const EdgeHolder *graph, node_t start,
                     std::vector<FullEdge_t> &back,
                     std::vector<FullEdge_t> &tree,
                     std::vector<FullEdge_t> &cross);

EdgeEnumerator neighbors_or_empty(const EdgeHolder &hld, node_t nd);
const EdgeEnumerator *neighbors_or_null(const EdgeHolder &hld, node_t nd);
size_t nr_neighbors(const EdgeHolder &hld, node_t nd);
bool neighbors_empty(const EdgeHolder &hld, node_t nd);

void compute_dominators(const EdgeHolder *graph, const EdgeHolder *bw,
                        node_t start,
                        std::map<node_t, std::set<node_t>> &dominators);

template <typename Boundary>
std::pair<EdgeHolder, node_t>
summarize(const EdgeHolder &g, node_t start,
          const NodeValues<node_t> &control_boundary, Boundary controlInstr,
          NodeValues<node_t> &summaries) {
  EdgeHolder summarized;
  node_t newstart = start;
  NodeValues<node_t> preambles;
  traverse_df_pernode(&g, start, [&](const node_t &nd) {
    auto cbI = control_boundary.find(nd);
    auto isBound = (cbI != control_boundary.end());
    if (isBound) {
      auto it = controlInstr(nd);
      auto newvec = new IR::Vector<IR::Node>();
      std::copy(instructions(nd).begin(), it, std::back_inserter(*newvec));
      node_t tabnode = new IR::Vector<IR::Node>();
      node_t newnode(newvec);
      if (nd == start)
        newstart = tabnode;
      summaries[tabnode] = nd;
      summarized[newnode].emplace_back(tabnode, 0);
      if (cbI->first != cbI->second) {
        summarized[tabnode].emplace_back(cbI->second, 0);
      } else {
        summarized[tabnode] = neighbors_or_empty(g, nd);
      }
      preambles[nd] = newnode;
    } else {
      summarized[nd] = neighbors_or_empty(g, nd);
    }
  });
  for (auto &neds : summarized) {
    for (auto &ed : neds.second) {
      auto cbI = control_boundary.find(ed.first);
      if (cbI != control_boundary.end()) {
        ed.first = preambles[ed.first];
      }
    }
  }
  return {summarized, start};
};

void compute_cdg(EdgeHolder *graph, EdgeHolder *bw,
                 NodeValues<std::unordered_set<analysis::node_t>> &dominators);

template <typename Label, typename Transformer, typename Merger,
          typename DefaultConstructor = _Default<Label>>
void label_maker(const EdgeHolder *graph, node_t start_node,
                 const std::vector<node_t> &sorted,
                 std::map<node_t, Label> &labels, Transformer t, Merger m,
                 DefaultConstructor _dc = DefaultConstructor()) {
  if (!start_node)
    start_node = sorted.back();
  auto I = std::find(sorted.rbegin(), sorted.rend(), start_node);
  for (; I != sorted.rend(); ++I) {
    auto crt = *I;
    auto labIT = labels.find(crt);
    if (labIT != labels.end()) {
      const auto &label = labIT->second;
      auto neighs = graph->find(crt);
      if (neighs != graph->end()) {
        const auto &neighvec = neighs->second;
        for (const auto &neigh : neighvec) {
          Label dst = _dc();
          if (t(crt, neigh, label, dst)) {
            auto EX = labels.find(neigh.first);
            if (EX == labels.end()) {
              labels.emplace(neigh.first, dst);
            } else {
              m(EX->second, dst);
            }
          }
        }
      }
    }
  }
};

struct CFG {
  const IR::Node *maps_to;
  EdgeHolder holder;
  node_t start_node;
  node_t end_node;
  CFG(const IR::Node *maps_to, EdgeHolder holder, bool noret = false);
  CFG(const IR::Node *maps_to);
  bool operator<(const CFG &other) const;
  void add(EdgeHolder *other);
  friend std::ostream &operator<<(std::ostream &os, const CFG &cfg);
  const std::vector<Edge> *operator[](const node_t &n) const {
    auto I = holder.find(n);
    if (I != holder.end()) {
      return &I->second;
    }
    return nullptr;
  }
  const std::vector<Edge> *get(const node_t &n) const { return operator[](n); }
  std::vector<Edge> &operator[](const node_t &n) { return holder[n]; }

  struct DefaultNodePrint {
    void operator()(std::ostream &os, node_t node) {
      os << node.nodeId() << "[label=\"" << node << "\"];\n";
    }
  };
  struct DefaultEdgePrint {
    void operator()(std::ostream &os, const FullEdge_t &fullEdge) {
      os << fullEdge.source.nodeId() << " -> " << fullEdge.dst.nodeId();
      if (fullEdge.type() == EdgeType::RETURN ||
          fullEdge.type() == EdgeType::CALL) {
        //        os << "[constraint=false]";
      }
      os << ";\n";
    }
  };

  struct DefaultGraphHeader {
    std::ostream &os;
    DefaultGraphHeader(std::ostream &os) : os(os) { os << "digraph G {\n"; }
    ~DefaultGraphHeader() { os << "}"; }
  };

  template <typename NodePrint = DefaultNodePrint,
            typename EdgePrint = DefaultEdgePrint,
            typename GraphHeader = DefaultGraphHeader>
  void toDot(std::ostream &os, NodePrint nodePrint = NodePrint(),
             EdgePrint edgePrint = EdgePrint(),
             const std::vector<node_t> *sorted = nullptr) const {
    std::unordered_set<node_t> nodes;
    GraphHeader gh(os);
    for (auto &n : holder) {
      if (nodes.emplace(n.first).second) {
        nodePrint(os, n.first);
      }
      for (auto neigh : n.second) {
        if (nodes.emplace(neigh.first).second) {
          nodePrint(os, neigh.first);
        }
        edgePrint(os, FullEdge_t(n.first, neigh.first, neigh.second));
      }
    }
    if (sorted && !sorted->empty()) {
      unsigned idx = 0;
      auto first = sorted->at(idx);
      ++idx;
      for (; idx != sorted->size(); ++idx) {
        auto nxt = sorted->at(idx);
        os << first.nodeId() << " -> " << nxt.nodeId()
           << "[style=\"invis\"];\n";
        first = nxt;
      }
    }
  };

  void write_node(const analysis::node_t &nd,
                  const std::unordered_map<analysis::node_t, bool> *dead,
                  std::unordered_set<analysis::node_t> &nodes, node_t first,
                  std::ostream &post_cprop) const;
};

template <typename NodePrint = CFG::DefaultNodePrint,
          typename EdgePrint = CFG::DefaultEdgePrint,
          typename GraphHeader = CFG::DefaultGraphHeader>
void toDot(analysis::EdgeHolder &hld, std::ostream &os,
           NodePrint nodePrint = NodePrint(), EdgePrint edgePrint = EdgePrint(),
           const std::vector<node_t> *sorted = nullptr) {
  CFG c(nullptr, std::move(hld));
  c.toDot(os, nodePrint, edgePrint, sorted);
  hld = std::move(c.holder);
};

template <typename Node> struct Graph {
  using Edge = std::pair<Node, int>;
  using FullEdge_t = AbsEdge<Node>;

  std::unordered_map<Node, std::vector<Edge>> nodes;
};

class ComputeGraph : public Inspector {
  ReferenceMap *refMap;
  EdgeHolder forward;
  std::map<const IR::P4Control *, EdgeHolder> forward_graphs;
  std::map<const IR::P4Control *, EdgeHolder> reverse_graphs;
  std::vector<std::pair<EdgeHolder::iterator, int>> outstanding;
  node_t create(const IR::Node *thisnode, NodeType tp = NodeType::NORMAL);
  EdgeHolder *mk_cfg(const IR::P4Control *ctrl);
  void makeOutstanding();
  EdgeHolder::iterator addNode(node_t stat);
  void compute_cfg(const IR::P4Parser *ctrl, const IR::ParserState *state,
                   std::map<const IR::ParserState *, node_t> &,
                   std::vector<node_t> &);

public:
  ComputeGraph(ReferenceMap *refMap) : refMap(refMap) {}
  EdgeHolder *get_forward(const IR::P4Control *ctrl);
  EdgeHolder *get_backward(const IR::P4Control *ctrl);

  EdgeHolder *get_forward(const IR::P4Parser *p4Parser);

  EdgeHolder *get_forward(const IR::Function *fun);
  EdgeHolder *get_forward(const IR::Statement *fun);

  bool preorder(const IR::EmptyStatement *) override { return false; }
  bool preorder(const IR::IfStatement *stat) override;
  bool preorder(const IR::StatOrDecl *n) override;
  bool preorder(const IR::ParserState *n) override;
  bool preorder(const IR::BlockStatement *) override { return true; }
  bool preorder(const IR::MethodCallStatement *mcs) override;
};

template <typename F> std::pair<EdgeHolder, bool> gmap(EdgeHolder h, F f) {
  EdgeHolder c;
  bool change = false;
  for (auto &n : h) {
    auto res = f(n.first);
    if (res != n.first)
      change = true;
    auto &neighs = (c[res] = std::move(n.second));
    for (auto &e : neighs) {
      auto c = f(e.first);
      if (c != e.first)
        change = true;
      e.first = c;
    }
  }
  return std::make_pair(c, change);
}

EdgeHolder take_starting_from(const EdgeHolder &h, node_t last, unsigned limit);

EdgeHolder freshClone(EdgeHolder h, node_t &start, node_t &end,
                      NodeValues<node_t> *parents = nullptr);

template <typename F>
std::pair<EdgeHolder, bool> gfilter(EdgeHolder h,
                                    const std::vector<node_t> &sorted, F f) {
  bool change = false;
  auto bw = std::move(*reverse(&h));
  // invariant n \keys(c) => f(n) == tt
  for (auto n : sorted) {
    if (!f(n)) {
      auto succs = std::move(h[n]);
      auto &preds = bw[n];
      change = true;
      h.erase(n);
      // link predecessors to the unique successor
      BUG_CHECK(succs.size() <= 1, "can't remove multi successor node %1%", n);
      for (auto p : preds) {
        for (auto s : succs) {
          auto &hp = h[p.first];
          auto I = std::find_if(hp.begin(), hp.end(), [&n, &p](const Edge &e) {
            return e.first == n && e.second == p.second;
          });
          I->first = s.first;
        }
      }
    }
  }
  // invariant n\in keys(c) <=> f(n) == tt
  for (auto &n : h) {
    auto I = std::remove_if(n.second.begin(), n.second.end(),
                            [&f](const Edge &e) { return !f(e.first); });
    if (I != n.second.end())
      change = true;
    n.second.erase(I, n.second.end());
  }
  // invariant (u, v) \in c <=> f(u) && f(v)
  return std::make_pair(std::move(h), change);
}

bool is_a_dag(EdgeHolder *holder, node_t start, std::vector<node_t> &sorted);

// context insensitive worklist algorithm
// fp is an extra parameter which has an apply operator
// taking (T, T) as input and returning true if fixed
// point was indeed reached. NB: may need to work
// out some widening/narrowing operator
// Transformer : bool(const IR::Node *, const std::pair<const IR::Node *> &,
// const T &mine, T &result)
// Merger : (const IR::Node *, const std::pair<const IR::Node *> &, const T
// &mine, T &result)
template <typename T, typename Transformer, typename Merger,
          typename FixedPoint, typename DefaultConstructor = _Default<T>>
void chaotic_iterations(std::map<node_t, T> &lattice, node_t start,
                        EdgeHolder *holder, Transformer t, Merger m,
                        FixedPoint fp,
                        DefaultConstructor _dc = DefaultConstructor()) {
  std::vector<node_t> sorted;
  auto isdag = is_a_dag(holder, start, sorted);
  if (isdag) {
    label_maker(holder, start, sorted, lattice, t, m, _dc);
  } else {
    std::map<node_t, unsigned> priorities;
    auto compare = [&priorities](const IR::Node *l, const IR::Node *r) {
      if (l == r)
        return false;
      return priorities[l] < priorities[r];
    };
    std::set<node_t, decltype(compare)> heap(compare);
    heap.emplace(start);
    while (!heap.empty()) {
      auto top = *heap.begin();
      heap.erase(heap.begin());
      auto crtI = lattice.find(top);
      if (crtI != lattice.end()) {
        auto N = holder->find(top);
        for (auto nxt : N->second) {
          auto dst = _dc();
          auto propd = t(top, nxt, crtI->second, dst);
          if (propd) {
            auto nxtI = lattice.emplace(nxt.first, dst);
            if (!nxtI.second) {
              if (!fp(nxtI.first->second, dst, nxt.first)) {
                m(nxtI.first->second, dst);
                heap.emplace(nxtI.first->first);
              }
            } else {
              heap.emplace(nxtI.first->first);
            }
          }
        }
      }
    }
  }
}

class CFGs {
  ComputeGraph graphs;
  CFG main;
  std::map<const IR::Node *, CFG *> startToGraph;

public:
  CFGs() : graphs(nullptr), main(nullptr) {}
  std::map<const IR::Node *, CFG> cfgs;
  // tries to build a CFG for node, returns nullptr
  // if flag
  CFG *get(const IR::Node *node, bool nullIfCantbuild);
  bool hasCFG(const IR::Node *node) const;
  bool built(const IR::Node *node) const;
  const CFG *getMain() const { return &main; }
  CFG *getMain() { return &main; }
  void commit();
  const CFG *getCFG(const IR::Node *starting) { return startToGraph[starting]; }
  void interproceduralEdge(node_t n, Edge new_edge);
};

std::unordered_map<node_t, unsigned>
sccIndices(std::vector<std::unordered_set<node_t>> &sccs);
P4::CallGraph<node_t> mkCallGraph(const EdgeHolder *holder);
EdgeHolder clone(EdgeHolder *holder, node_t &newstart);
void setLabel(EdgeHolder *holder, std::size_t L);
inline void setLabel(EdgeHolder *holder) { setLabel(holder, ++node_t::LABEL); }

template <typename Dead>
void removeDeadNodes(EdgeHolder *holder, node_t start, Dead d) {
  START(remove_dead);
  auto inisize = holder->size();
  std::unordered_set<node_t> found;
  traverse_df_pernode(holder, start, [&d, &found](node_t n) {
    if (!d(n)) {
      found.emplace(n);
    }
  });
  auto sg =
      subgraph(holder, [&found](node_t n) { return found.count(n) != 0; });
  *holder = std::move(sg);
  END(remove_dead);
  auto dr = DURATION(remove_dead);
  LOG4("removed dead nodes for cfg " << inisize << " now " << holder->size()
                                     << " in " << dr << " ms");
}
inline void removeDeadNodes(EdgeHolder *holder, node_t start) {
  removeDeadNodes(holder, start, [](node_t) { return false; });
}

std::unordered_set<node_t> findEndNodes(EdgeHolder *holder, node_t start);
std::unordered_set<node_t> terminals(const EdgeHolder &holder);

using BasicBlock = std::vector<node_t>;

void basic_blocks(const EdgeHolder &graph, const EdgeHolder &rgraph,
                  const node_t &start, EdgeHolder &basicBlockGraph,
                  EdgeHolder &rBasicBlockGraph, node_t &basicBlockStart);

void basic_blocks(const EdgeHolder &graph, const node_t &start,
                  EdgeHolder &basicBlockGraph, EdgeHolder &rBasicBlockGraph,
                  node_t &basicBlockStart);

void ensure_basic_blocks(EdgeHolder &basicBlockGraph,
                         EdgeHolder &rBasicBlockGraph, node_t &basicBlockStart);

void trans_remove_empty(EdgeHolder &hcopy, const node_t &start,
                        const std::vector<node_t> &newsort,
                        NodeValues<node_t> *transforms = nullptr);
inline bool isEmpty(const node_t &nd) { return nr_instructions(nd) == 0; }
void dom_frontier(const EdgeHolder &graph, const EdgeHolder &rgraph,
                  const node_t &start,
                  std::unordered_map<node_t, std::vector<node_t>> &children,
                  EdgeHolder &domf);
};

#endif // P4C_CFG_ALGOS_H
