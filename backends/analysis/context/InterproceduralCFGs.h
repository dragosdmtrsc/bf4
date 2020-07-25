//
// Created by dragos on 29.07.2019.
//

#ifndef P4C_INTERPROCEDURALCFGS_H
#define P4C_INTERPROCEDURALCFGS_H

#include "Context.h"
#include <analysis/cfg_algos.h>
#include <common/resolveReferences/referenceMap.h>

namespace analysis {
struct NodeToFunctionMap {
  // maps a node to a callee
  std::unordered_map<node_t, const IR::Node *> functionMappings;
  std::unordered_map<node_t, P4::MethodInstance *> instances;

  bool put(node_t n, const IR::Node *fun, P4::MethodInstance *mi);

  P4::MethodInstance *instance(node_t cfgn);
  const IR::Node *callee(node_t cfgn) const;

  bool hasReturn(node_t cfgn);
  const IR::Type *returnType(node_t cfgn);
  const IR::IndexedVector<IR::Declaration> *locals(node_t cfgn);
  const IR::ParameterList *calleeParameters(node_t cfgn);
};

class ITracker {
public:
  static const IR::Function *findFunction(const IR::P4Program *prog,
                                          cstring name);

  static const IR::Function *getImplementation(const IR::P4Program *program,
                                               const IR::Method *method);
};

class BuildIPCFG {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  const IR::P4Program *program;
  ContextFactory *contextFactory;
  CFGs *cfgs;
  NodeToFunctionMap *funMap;
  bool lazy_link = false;
  NodeValues<node_t> parents;
  NodeValues<const IR::Node *> node_to_method;

  std::unordered_map<const IR::Node *,
                     NodeValues<std::tuple<node_t, node_t, CFG *>>>
      remaining_gotos;

  std::unordered_map<const IR::Node *, std::unordered_set<const IR::Node *>>
      gotos;
  NodeValues<std::tuple<node_t, node_t, CFG *>> caller_to_fun;
  const std::vector<const IR::Statement *>
  pass_params(const IR::ParameterList *parms, P4::MethodInstance *call,
              bool ret, bool);
  CFG replace_inouts(CFG c, const IR::ParameterList *parms,
                     P4::MethodInstance *call, node_t &start, node_t &end);

  void
  linkCFG(CFG *,
          const std::unordered_map<node_t, std::tuple<node_t, node_t, CFG *>>
              &caller_to_fun);
  void link_gotos(
      CFG *,
      const std::unordered_map<node_t, std::tuple<node_t, node_t, CFG *>> &);

  void labelNode(const node_t &, const IR::Node *);
  void labelCFG(const CFG *, const IR::Node *);

public:
  friend class ProgramDatabase;
  void doBuild(CFG *);
  void fixGraph(const analysis::CFG *);

  BuildIPCFG(ReferenceMap *refMap, TypeMap *typeMap,
             const IR::P4Program *program, ContextFactory *contextFactory,
             CFGs *cfgs, NodeToFunctionMap *funMap, bool lazy = false);

  const IR::Node *getMethod(const node_t &nd);

  CFG *build(CFG *current);
};
}

#endif // P4C_INTERPROCEDURALCFGS_H
