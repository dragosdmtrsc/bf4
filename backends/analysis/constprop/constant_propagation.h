//
// Created by dragos on 11.01.2019.
//

#ifndef P4C_CONSTANT_PROPAGATION_H
#define P4C_CONSTANT_PROPAGATION_H

#include <analysis/analysis_helpers.h>
#include <analysis/cfg_algos.h>
#include <analysis/context/InterproceduralCFGs.h>
#include <analysis/lattice/Lattice.h>
#include <common/resolveReferences/referenceMap.h>
#include <gmpxx.h>
#include <ir/node.h>
#include <midend/interpreter.h>
#include <p4/typeMap.h>

namespace analysis {
bool is_known(P4::SymbolicValue *sv);
class FindInterestingAtoms : public Inspector {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  std::set<const IR::Expression *> atoms;
  bool preorder(const IR::LAnd *) override { return true; }
  bool preorder(const IR::LOr *) override { return true; }
  bool preorder(const IR::LNot *) override { return true; }
  bool preorder(const IR::Expression *expression) override {
    atoms.emplace(expression);
    return false;
  }
  bool preorder(const IR::Neq *n) override {
    atoms.emplace(n);
    return false;
  }
  bool preorder(const IR::BoolLiteral *) override { return false; }
  bool preorder(const IR::Equ *e) override {
    atoms.emplace(e);
    return false;
  }
  bool preorder(const IR::Operation_Relation *) override { return false; }
  bool preorder(const IR::Operation_Ternary *) override { return false; }

 public:
  FindInterestingAtoms(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}
  std::set<const IR::Expression *> find_interesting_atoms(
      const IR::Expression *e);
  std::map<const IR::Expression *, bool> find_implied_equalities(
      const IR::Expression *e, int what);
};

class FlatLattice : public LatticeElement<FlatLattice> {
 public:
  P4::ValueMap *valueMap;
  FlatLattice() : valueMap(nullptr) {}
  FlatLattice(ValueMap *valueMap);

  bool operator==(const FlatLattice &other) const override;
  FlatLattice operator+(const FlatLattice &other) const override;
  bool isBottom() const override;
};

class ConstantPropagate {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  NodeToFunctionMap *functionMap;
  P4::SymbolicValueFactory svf;

 public:
  using LatticeType = FlatLattice;
  ConstantPropagate(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                    NodeToFunctionMap *funMap)
      : refMap(refMap), typeMap(typeMap), functionMap(funMap), svf(typeMap) {}

  P4::ValueMap *handleBoolExpression(const IR::Expression *crt, int what,
                                     P4::ValueMap *valueMap);
  P4::SymbolicBool *handleSelectCase(const IR::Expression *k,
                                     const IR::Expression *caselabel,
                                     P4::ValueMap *valueMap);
  P4::SymbolicBool *handleSelectExpression(
      const IR::SelectExpression *selectExpression, int what,
      P4::ValueMap *vmap);

  virtual P4::SymbolicValue *handle_havoc(const IR::Type *);

  bool operator()(node_t crt, const Edge &neigh, P4::ValueMap *oldex,
                  P4::ValueMap *&newex);
  P4::ValueMap *operator()() { return nullptr; }
  void operator()(P4::ValueMap *&into, const P4::ValueMap *from);

  FlatLattice operator()(node_t crt, const Edge &neigh, FlatLattice v);
  FlatLattice operator()(node_t call, const Edge &neigh,
                         const FlatLattice &lcall, const FlatLattice &lend);

  ValueMap *handleMethodCall(const ValueMap *oldex,
                             const IR::MethodCallExpression *mce,
                             const std::pair<node_t, int> &neigh);
};
template <typename Discipline>
void constant_propagate(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                        const CFG *graph, Discipline &d,
                        std::unordered_map<node_t, FlatLattice> &result,
                        NodeToFunctionMap &functionMap,
                        node_t start_node = nullptr) {
  if (!start_node.node) start_node = graph->start_node;
  ConstantPropagate cp(refMap, typeMap, &functionMap);
  WorklistAlgo<FlatLattice, ConstantPropagate, Discipline> algo(*graph, cp, d);
  algo(start_node, result);
}
void constant_propagate(const IR::IApply *control,
                        const IR::IndexedVector<IR::Declaration> &extra_decls,
                        const analysis::EdgeHolder *forward_graph,
                        std::map<node_t, P4::ValueMap *> *reachingVersions,
                        std::vector<node_t> *sorted, P4::ReferenceMap *refMap,
                        P4::TypeMap *typeMap);
}

#endif  // P4C_CONSTANT_PROPAGATION_H
