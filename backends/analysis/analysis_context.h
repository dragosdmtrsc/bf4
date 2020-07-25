//
// Created by dragos on 20.01.2019.
//

#ifndef P4C_ANALYSIS_CONTEXT_H
#define P4C_ANALYSIS_CONTEXT_H

#include <analysis/constprop/constant_propagation.h>
#include <common/resolveReferences/referenceMap.h>
#include <midend/interpreter.h>
#include <p4/typeMap.h>
#include "cfg_algos.h"
#include "smt_helpers.h"
#include "version_propagator.h"
#include "versions.h"

namespace analysis {
class Analyzer {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  const IR::P4Parser *parser = nullptr;
  const IR::P4Control *control = nullptr;
  const IR::P4Program *prog;
  ComputeGraph cg;

  // locals:
  z3::context *context;
  analysis::EdgeHolder *fw = nullptr, *bw = nullptr;
  SmtTypeWrapper *smttypewrapper = nullptr;
  std::map<node_t, P4::ValueMap *> *p_vals = nullptr;
  std::vector<node_t> *p_sorted = nullptr;
  std::map<std::pair<node_t, int>, z3::expr> *p_transformers = nullptr;
  std::map<node_t, z3::expr> *p_labels = nullptr;
  std::set<node_t> *p_assertion_points = nullptr;

  std::set<node_t> *p_bug_points = nullptr;
  std::set<node_t> *p_ok_points = nullptr;

  std::map<node_t, std::vector<node_t>> *p_control_to_bugs = nullptr;

  // config
  bool do_full_constant_propagation = true;

  const IR::IApply *apply();
  void compute_transformers();
  void compute_assertion_points();
  void init();
  void propagate_constants();
  void compute_reachability();
  void compute_finals();
  void compute_control_to_bugs();
  void pre_init();
  void print_node(std::ostream &os, node_t n);

  const IR::IndexedVector<IR::Declaration> &locals();

 public:
  void print_cfg(std::ostream &os, bool orig = false,
                 node_t start_from = nullptr);
  std::map<std::pair<node_t, int>, z3::expr> &transformers();
  std::map<node_t, z3::expr> &labels();
  std::map<node_t, std::vector<node_t>> &control_to_bugs();
  std::map<node_t, P4::ValueMap *> &vals();
  std::vector<node_t> &sorted();
  std::set<node_t> &assertion_points();
  std::set<node_t> &bug_points();
  z3::expr bug();
  std::set<node_t> &ok_points();
  z3::context &ctx() { return *context; }
  SmtTypeWrapper &typeWrapper();
  EdgeHolder &forward_cfg();
  EdgeHolder &backward_cfg();

  // assumption: a bug() statement composed as follows:
  // if (...) { real_statement } else { bug(); }
  // goal: retrieve real_statement or null if this format is not found
  node_t get_problem_root(node_t bug);

  Analyzer(P4::ReferenceMap *refMap, TypeMap *typeMap,
           const IR::P4Parser *parser, const IR::P4Program *prog,
           bool cprop = true);

  Analyzer(ReferenceMap *refMap, TypeMap *typeMap, const IR::P4Parser *parser,
           const IR::P4Program *prog, z3::context *context,
           bool do_full_constant_propagation);

  Analyzer(ReferenceMap *refMap, TypeMap *typeMap, const IR::P4Control *control,
           const IR::P4Program *prog, bool do_full_constant_propagation);

  Analyzer(ReferenceMap *refMap, TypeMap *typeMap, const IR::P4Control *control,
           const IR::P4Program *prog, z3::context *context,
           bool do_full_constant_propagation);
};
}

#endif  // P4C_ANALYSIS_CONTEXT_H
