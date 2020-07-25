//
// Created by dragos on 04.07.2019.
//

#ifndef P4C_EXPLICITUB_H
#define P4C_EXPLICITUB_H

#include <analysis/cegis.h>
#include <analysis/cfg_algos.h>
#include <common/resolveReferences/referenceMap.h>
#include <ir/pass_manager.h>
#include <p4/def_use.h>
#include <p4/typeMap.h>
#include "AnalysisContext.h"
#include "PropagateFormulas.h"
#include "ssa.h"

namespace analysis {

class ExplicitUB : public PassManager {
  NodeValues<unsigned> bugids;
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

  ReadSet *p_readSet;
  WriteSet *p_writeSet;

  static void deadnodeprint(std::ostream &os, node_t node);
  bool isControl(const IR::Node *nd);
  const IR::Node *const *controlInstr(const node_t &nd);

  std::string prettyInstr(const IR::Node *nd, unsigned lim);
  void bbNodePrint(std::ostream &os, node_t node);
  void bbNodePrintWStart(std::ostream &os, node_t node, const node_t &start);
  std::tuple<EdgeHolder, node_t, node_t> mkslice(
      const analysis::EdgeHolder &basicBlocks,
      const analysis::node_t &basicBlockStart, const analysis::node_t &bg,
      bool relax, std::unordered_map<MemPath, NodeVector> &writes,
      std::function<NodeSet(const MemPath &)> &depends,
      NodeValues<node_t> *transforms = nullptr);
  ReadSet &rss() { return *p_readSet; }
  WriteSet &wss() { return *p_writeSet; }

  NodeValues<std::pair<node_t, unsigned>> getInstr2bb(const EdgeHolder &h,
                                                      node_t start);

  bool anycontrol(const node_t &nd);

  struct dec_tree {
    EdgeHolder h;
    node_t start;
    std::vector<const IR::Expression *> edgeLabels;

    dec_tree(EdgeHolder h, node_t start,
             std::vector<const IR::Expression *> edgeLabels);
  };

  struct dec_tree_holder {
    mutable std::unordered_map<MemPath, dec_tree> decision_trees;
    mutable std::unordered_map<MemPath, NodeSet> depends;
    NodeSet operator()(const MemPath &mp) const;
  };

  dec_tree_holder computeDT(const EdgeHolder &basicBlocks,
                            const EdgeHolder &rBasicBlocks,
                            node_t basicBlockStart,
                            std::unordered_map<MemPath, NodeVector> &);

  std::unordered_map<MemPath, NodeVector> getWrites(
      const EdgeHolder &basicBlocks, node_t basicBlockStart);

  bool endsInBug(const node_t &nd);
  bool endsInTerminal(const node_t &nd, const EdgeHolder &basicBlocks);
  bool isDontCare(const node_t &nd, const EdgeHolder &basicBlocks);

  void buildSolver(packet_solver_ &direct, const EdgeHolder &basicBlocks,
                   node_t basicBlockStart, const NodeVector &sorted,
                   EdgeFormulas &edgeFormulas);
  void avoid(packet_solver_ &direct, const node_t &nd,
             EdgeFormulas &edgeFormulas);

  void avoidAll(packet_solver_ &direct, const EdgeHolder &basicBlocks,
                node_t basicBlockStart,
                std::function<bool(const node_t &)> &filter,
                EdgeFormulas &edgeFormulas);

  void addSpecs(
      packet_solver_ &direct,
      const std::vector<std::pair<NodeVector, const IR::Expression *>> &specs,
      EdgeFormulas &edgeFormulas,
      NodeValues<std::pair<analysis::node_t, unsigned>> &i2bb);
  ;

  NodeSet allBugs(const EdgeHolder &basicBlocks, const node_t &start);

  std::vector<node_t> getPath(z3::model model, const EdgeHolder &basicBlocks,
                              const node_t &basicBlockStart,
                              EdgeFormulas &edgeFormulas);

  bool solve_for_packet(z3::model &model,
                        z3::solver &slv,
                        const EdgeHolder &basicBlocks,
                        const node_t &basicBlockStart,
                        EdgeFormulas &edgeFormulas);
  static bool isPacketMethod(cstring nm, bool all);
  bool ispackMethod_(const IR::Node *instr, bool all);;

 public:
  ExplicitUB(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
  void analyzeProgram(const IR::P4Program *program);
};
}
#endif  // P4C_EXPLICITUB_H
