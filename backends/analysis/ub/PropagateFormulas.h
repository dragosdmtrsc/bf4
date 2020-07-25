//
// Created by dragos on 30.08.2019.
//

#ifndef P4C_PROPAGATEFORMULAS_H
#define P4C_PROPAGATEFORMULAS_H

#include "AnalysisContext.h"
#include "StorageLattice.h"
#include "ssa.h"
#include <analysis/cegis.h>
#include <analysis/constprop/ConstantPropagation.h>
#include <analysis/lattice/Lattice.h>
#include <z3++.h>

namespace analysis {

class FormulaFactory;
class EdgeFormulas {
  // INPUTS
  P4::TypeMap *typeMap;
  P4::ReferenceMap *refMap;
  NodeToFunctionMap *funMap;
  z3::context *context;

  // COMPUTED
public:
  FormulaFactory *factory;
  SelectToExpression selectToExpression;
  MultiAssignment multiAssignment;

  // COMPUTED: packet
  packet_theory packetTheory;

private:
  struct NodeLabels {
    z3::context *context;
    NodeValues<z3::expr> exprs;
    std::string prefix;
    z3::expr operator[](node_t n);

    NodeLabels(z3::context *context, std::string prefix);
  };
  // OUTPUTS
  NodeLabels nodeLabels;
  NodeValues<z3::expr> expressions;
  void mkFormula(const node_t &n, z3::expr &e);

public:
  EdgeFormulas(TypeMap *typeMap, ReferenceMap *refMap, z3::context *context, std::string s = "");
  SmtTypeWrapper &getWrapper();
  const z3::expr &node(const node_t &edge) {
    auto EMI = expressions.emplace(edge, context->bool_val(true));
    if (EMI.second)
      mkFormula(edge, EMI.first->second);
    return EMI.first->second;
  }
  z3::expr nodeLabel(node_t n) { return nodeLabels[n]; }
  z3::expr toSMT(const IR::Expression *e);
  z3::expr toSMT(const MemPath &mp);

  const IR::Node *translate(const z3::expr &e);
};
}

#endif // P4C_PROPAGATEFORMULAS_H
