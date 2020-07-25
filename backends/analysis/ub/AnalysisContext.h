//
// Created by dragos on 08.09.2019.
//

#ifndef P4C_ANALYSISCONTEXT_H
#define P4C_ANALYSISCONTEXT_H

#include "ReachingDefinitions.h"
#include "ssa.h"
#include <analysis/VersionedExpression.h>
#include <analysis/cfg_algos.h>
#include <analysis/context/Context.h>
#include <analysis/context/InterproceduralCFGs.h>
#include <common/constantFolding.h>
#include <common/resolveReferences/referenceMap.h>
#include <p4/typeChecking/typeChecker.h>
#include <p4/typeMap.h>

namespace analysis {
class Analysis {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  const IR::P4Program *program;
  cstring startFunction;

  // computed variables
  CFGs cfgs;
  CFG *main = nullptr;
  NodeToFunctionMap funMap;

public:
  Analysis(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
           const IR::P4Program *program, cstring startFunction);

  NodeToFunctionMap *getFunMap() {
    if (!main) {
      getMain();
    }
    return &funMap;
  }
  CFG *getMain() {
    if (!main) {
      ContextFactory contextFactory(program, refMap, typeMap);
      auto fun = program->getDeclsByName(startFunction)
                     ->begin()
                     .
                     operator*()
                     ->to<IR::Function>();
      auto fungraph = cfgs.get(fun, false);
      BuildIPCFG builder(refMap, typeMap, program, &contextFactory, &cfgs,
                         &funMap);
      main = builder.build(fungraph);
    }
    return main;
  }
};

class SelectToExpression {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  P4::TypeInference tc;
  std::unordered_map<std::pair<const IR::SelectExpression *, int>,
                     const IR::Expression *,
                     boost::hash<std::pair<const IR::SelectExpression *, int>>>
      expressions;
  const IR::Expression *selectCaseOne(const IR::Expression *chosen_head,
                                      const IR::Expression *component);
  const IR::Expression *selectCase(const IR::ListExpression *select,
                                   const IR::SelectCase *selcase);
  const IR::Expression *computeExpression(const IR::SelectExpression *selex,
                                          int what);

public:
  SelectToExpression(ReferenceMap *refMap, TypeMap *typeMap);

  const IR::Expression *operator()(const IR::SelectExpression *selex, int what);
};

class MultiAssignment {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  P4::TypeInference tc;
  std::unordered_map<std::pair<const IR::Node *, const IR::Node *>,
                     std::vector<const IR::AssignmentStatement *>,
                     boost::hash<std::pair<const IR::Node *, const IR::Node *>>>
      cache;

  void fixExpression(const IR::Expression *e, const IR::Type *t, bool lv);

  const IR::Expression *exp(const IR::Node *n, bool lv);

  void recurseExprs(const IR::Expression *le, const IR::Expression *re,
                    std::vector<const IR::AssignmentStatement *> &vec);

  void compute(const IR::Node *l, const IR::Node *r,
               std::vector<const IR::AssignmentStatement *> &vec);

public:
  MultiAssignment(ReferenceMap *refMap, TypeMap *typeMap);

  const std::vector<const IR::AssignmentStatement *> *
  operator()(const IR::Node *l, const IR::Node *r);
};

CFG push_ifs(const CFG &main, P4::ReferenceMap *refMap, P4::TypeMap *typeMap);

void make_ssa(EdgeHolder &basicBlocks, EdgeHolder &rBasicBlocks,
              node_t basicBlockStart, P4::ReferenceMap *refMap,
              P4::TypeMap *typeMap, NodeToFunctionMap *funMap,
              bool livevaropt = true);
inline IR::Vector<IR::Node> *mutate(const node_t &n) {
  auto v = n.node->to<IR::Vector<IR::Node>>();
  CHECK_NULL(v);
  return const_cast<IR::Vector<IR::Node> *>(v);
}

template <typename F>
void rminstrIf(EdgeHolder &basicBlocks, node_t basicBlockStart, F f) {
  traverse_df_pernode(&basicBlocks, basicBlockStart, [&](const node_t &nd) {
    auto mut = mutate(nd);
    unsigned idx = 0;
    for (auto instr : instructions(nd)) {
      if (!f(instr)) {
        mut->at(idx++) = instr;
      }
    }
    mut->resize(idx);
  });
};
void domtree_simplifications(EdgeHolder &basicBlocks, node_t &basicBlockStart,
                             P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                             NodeToFunctionMap *funMap);

void intra_basic_block_simplifications(EdgeHolder &basicBlocks,
                                       node_t &basicBlockStart,
                                       P4::ReferenceMap *refMap,
                                       P4::TypeMap *typeMap,
                                       NodeToFunctionMap *funMap);

inline bool is_controlled(const node_t &nd, P4::ReferenceMap *refMap,
                          P4::TypeMap *typeMap) {
  if (auto mcs = is_extern_method_call(nd)) {
    return is_controlled(mcs->methodCallStatement, refMap, typeMap);
  }
  return false;
}

void simplify_ifs(EdgeHolder &graph, const node_t &start,
                  P4::ReferenceMap *refMap, P4::TypeMap *typeMap);

const IR::Node *if_to_dnf(const IR::Node *instr, P4::ReferenceMap *refMap,
                          P4::TypeMap *typeMap);
const IR::Node *if_to_nnf(const IR::Node *instr, P4::ReferenceMap *refMap,
                          P4::TypeMap *typeMap);

std::set<const IR::Expression *> get_atoms(const IR::Expression *exp,
                                              P4::ReferenceMap *,
                                              P4::TypeMap *typeMap);

void ifs_to_dnf(EdgeHolder &graph, const node_t &start,
                P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
void ifs_to_nnf(EdgeHolder &graph, const node_t &start,
                P4::ReferenceMap *refMap, P4::TypeMap *typeMap);

class Cuber : public PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

public:
  Cuber(ReferenceMap *refMap, TypeMap *typeMap);
};

class cubes {
  bool lor;
  const IR::Expression *expr;
  std::vector<const IR::Expression *> _cubes;
  void recurse(const IR::Expression *e);
  cubes(bool lor, const IR::Expression *expr) : lor(lor) { recurse(expr); }

public:
  std::size_t size() const { return _cubes.size(); }
  std::vector<const IR::Expression *>::iterator begin() {
    return _cubes.begin();
  }
  std::vector<const IR::Expression *>::iterator end() { return _cubes.end(); }
  static cubes break_ors(const IR::Expression *expr) { return {true, expr}; }
  static cubes break_ands(const IR::Expression *expr) { return {false, expr}; }
};

class domtree_iterator {
  NodeValues<node_t> &parent;
  NodeValues<node_t>::iterator Iparent;

public:
  domtree_iterator(NodeValues<analysis::node_t> &parent,
                   NodeValues<analysis::node_t>::iterator Iparent)
      : parent(parent), Iparent(Iparent) {}

public:
  bool operator!=(const domtree_iterator &other) const {
    return Iparent != other.Iparent;
  }
  bool operator==(const domtree_iterator &other) const {
    return !operator!=(other);
  }
  node_t &operator*() const { return Iparent->second; }
  domtree_iterator &operator++();
};

class domtree_iterable {
  NodeValues<node_t> &parent;
  node_t of;

public:
  domtree_iterable(NodeValues<analysis::node_t> &parent, node_t of);
  domtree_iterator begin() const { return {parent, parent.find(of)}; }
  domtree_iterator end() const { return {parent, parent.end()}; }
};
NodeSet dominees_of(const NodeValues<NodeVector> &domtree, node_t nd);
domtree_iterable dominators_for(NodeValues<node_t> &parent, node_t nd);
node_t make_artificial_end(EdgeHolder &graph, EdgeHolder &rgraph, node_t start);

class WithArtificialEnd {
  EdgeHolder &graph;
  EdgeHolder &rgraph;
  node_t artiend;

public:
  const node_t &getEnd() const;
  WithArtificialEnd(EdgeHolder &graph, EdgeHolder &rgraph, const node_t &start);
  ~WithArtificialEnd();
};

NodeValues<node_t> get_parents(const NodeValues<NodeVector> &domtree);
bool dominates(const NodeValues<node_t> &parents, const node_t &x,
               const node_t &by);
void pdom_frontier(const EdgeHolder &graph, const EdgeHolder &rgraph,
                   const node_t &start,
                   std::unordered_map<node_t, std::vector<node_t>> &children,
                   EdgeHolder &domf);
};

#endif // P4C_ANALYSISCONTEXT_H
