//
// Created by dragos on 10.09.2019.
//

#ifndef P4C_CONSTANTPROPAGATION_H
#define P4C_CONSTANTPROPAGATION_H

#include <analysis/context/InterproceduralCFGs.h>
#include <analysis/lattice/Lattice.h>
#include <analysis/ub/AnalysisContext.h>
#include <analysis/ub/StorageLattice.h>
#include <analysis/ub/ssa.h>
#include <analysis/version_propagator.h>
#include <analysis/versions.h>
#include <common/constantFolding.h>
#include <common/resolveReferences/referenceMap.h>
#include <p4/enumInstance.h>
#include <p4/typeMap.h>

namespace analysis {
enum class ScalarState { TOP, BOTTOM, CONSTANT };

struct ScalarValue {
  ScalarState state = ScalarState::BOTTOM;
  // INVARIANT: state == Constant => (value != nullptr &&
  // (value->is<IR::Literal>() || EnumInstance::resolve(value, typeMap) !=
  // nullptr))
  // INVARIANT: state <> Constant => !(value != nullptr &&
  // (value->is<IR::Literal>() || EnumInstance::resolve(value, typeMap) !=
  // nullptr))
  const IR::Expression *value = nullptr;
  ScalarValue() {}
  ScalarValue(ScalarState st) : state(st), value(nullptr) {
    BUG_CHECK(st != ScalarState::CONSTANT, "can't set to constant");
  }
  ScalarValue(ScalarState st, const IR::Expression *e) : state(st), value(e) {}
  ScalarValue(const IR::Expression *constant)
      : state(ScalarState::CONSTANT), value(constant) {}

  const IR::Constant *constant() const;
  const IR::BoolLiteral *bconstant() const;
  const IR::Expression *enumMember() const { return value; }

  bool operator==(const ScalarValue &sv) const;
  ScalarValue operator+(const ScalarValue &sv) const;
  ScalarValue &operator+=(const ScalarValue &sv);

  static ScalarValue fromExpression(const IR::Expression *expr,
                                    P4::TypeMap *typeMap);

  friend std::ostream &operator<<(std::ostream &os, const ScalarValue &sv) {
    switch (sv.state) {
      case ScalarState::BOTTOM:
        return os << "B";
      case ScalarState::TOP:
        return os << "T";
      default:
        return os << sv.value;
    }
  }
};

class EvaluateExpression_;

struct ConstLattice : public LatticeElement<ConstLattice> {
  const std::unordered_map<MemPath, size_t> *idx;
  std::vector<ScalarValue> values;
  bool unreach = false;

  ConstLattice() : idx(nullptr), unreach(true) {}

  ConstLattice(const std::unordered_map<MemPath, size_t> *idx)
      : idx(idx), values(idx->size()) {}

  ConstLattice(const std::unordered_map<MemPath, size_t> *idx,
               std::vector<ScalarValue> values)
      : idx(idx), values(std::move(values)) {}
  ScalarValue operator()(const MemPath &mp) const;
  bool operator==(const ConstLattice &o) const override;
  ScalarValue &operator[](const MemPath &mp);
  const ScalarValue &operator[](const MemPath &mp) const;
  ConstLattice operator+(const ConstLattice &) const override {
    BUG("FIXME: bad design, use move semantics");
  }

  bool isBottom() const override { return unreach; }
};
class ConstantPropagation : public Propagate<ConstLattice> {
  // INPUTS
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  NodeToFunctionMap *functionMap;
  const CFG *cfg;

  // COMPUTED
  ReadSet readSet;
  WriteSet writeSet;
  PathGetter pathGetter;
  IsLv isLv;
  SelectToExpression selectToExpression;
  std::unordered_map<MemPath, size_t> *idx;

  bool handleCondition(const IR::Expression *cd, bool tt, ConstLattice &ret,
                       EvaluateExpression_ *);
  void initialize();

 public:
  ConstLattice operator()() { return {idx}; }
  ConstantPropagation(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                      const CFG &g, NodeToFunctionMap *funMap);

  ConstLattice operator()(node_t n, const Edge &e,
                          const ConstLattice &other) override;

  ConstLattice operator()(node_t n, const Edge &e, const ConstLattice &lcall,
                          const ConstLattice &lend) override;

  ConstLattice operator()(const ConstLattice &l, ConstLattice r);

 private:
  NodeValues<ConstLattice> run();

 public:
  static NodeValues<ConstLattice> propagate_constants(
      P4::ReferenceMap *refMap, P4::TypeMap *typeMap, const CFG &g,
      NodeToFunctionMap *funMap);
  static NodeValues<ConstLattice> propagate_and_simplify(
      P4::ReferenceMap *refMap, P4::TypeMap *typeMap, CFG &g,
      NodeToFunctionMap *funMap, NodeValues<node_t> *parents = nullptr);
};

class Fold : public Transform {
  // INPUTS
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  ConstLattice *constants;

  // COMPUTED
  P4::TypeInference tc;
  EvaluateExpression_ *eeval;
  std::unordered_map<const IR::Expression *, const IR::Expression *> cache;
  const IR::Node *preorder(IR::Expression *te) override;

 public:
  Fold(P4::ReferenceMap *refMap, P4::TypeMap *typeMap, ConstLattice *constants);
  const IR::Expression *operator()(const IR::Expression *e);
};

class EvalAt {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  NodeValues<ConstLattice> *constants;
  NodeValues<Fold> folds;

 public:
  const IR::Expression *operator()(node_t n, const IR::Expression *e);
  EvalAt(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
         NodeValues<ConstLattice> *constants)
      : refMap(refMap), typeMap(typeMap), constants(constants) {}
};

void constant_propagate(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                        const CFG *graph, NodeValues<ConstLattice> &result,
                        NodeToFunctionMap *functionMap, node_t start_node);
}

#endif  // P4C_CONSTANTPROPAGATION_H
