//
// Created by dragos on 29.08.2019.
//

#ifndef P4C_SSA_H
#define P4C_SSA_H

#include <analysis/lattice/Lattice.h>
#include <analysis/versions.h>
#include "StorageLattice.h"

namespace analysis {

template <bool RW>
class Reads {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  NodeToFunctionMap *funMap;

  NodeValues<std::unordered_set<MemPath>> reads;
  LVs lvs;
  PathGetter pathGetter;

  void read(std::unordered_set<MemPath> &res, const IR::Expression *rvex);
  void handle_in_params(std::unordered_set<MemPath> &res, const node_t &, bool,
                        bool);
  void compute_reads(const node_t &n, std::unordered_set<MemPath> &res);

 public:
  Reads(ReferenceMap *refMap, TypeMap *typeMap, NodeToFunctionMap *funMap);
  std::unordered_set<MemPath> &operator[](const node_t &n);
  std::unordered_set<MemPath> operator()(const IR::Expression *nd);
};

using ReadSet = Reads<true>;
using WriteSet = Reads<false>;
// replaces all occurences of LV expressions specified in replacements
// with corresponding expressions
class Replace : public Transform {
  friend class ReplaceAll;
  // INPUTS:
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  P4::TypeInference tc;
  std::unordered_map<MemPath, const IR::Expression *> replacements;
  // COMPUTED:
  IsLv isLv;
  PathGetter pathGetter;
  const IR::Node *preorder(IR::Argument *arg) override;
  const IR::Node *preorder(IR::Expression *expression) override;

 public:
  bool readonly = true;
  Replace(ReferenceMap *refMap, TypeMap *typeMap,
          std::unordered_map<MemPath, const IR::Expression *> replacements)
      : refMap(refMap),
        typeMap(typeMap),
        tc(refMap, typeMap, true),
        replacements(std::move(replacements)),
        isLv(refMap, typeMap),
        pathGetter(refMap, typeMap) {}

  const IR::Node *operator()(const IR::Node *e);
};

class ReplaceAll : public Transform {
  // INPUTS:
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  std::unordered_map<const IR::Node *, const IR::Node *> transforms;

  // COMPUTED:
  PathTypes pathTypes;
  TypeInference tc;
  Replace rreplace;
  Replace wreplace;

  const IR::Node *preorder(IR::AssignmentStatement *asg) override;
  const IR::Node *preorder(IR::IfStatement *ifs) override;
  const IR::Node *preorder(IR::SelectExpression *sexp) override;
  const IR::Node *preorder(IR::Node *d) override;
  const IR::Node *preorder(IR::MethodCallStatement *expression) override;

 public:
  ReplaceAll(
      ReferenceMap *refMap, TypeMap *typeMap,
      std::unordered_map<MemPath, const IR::Expression *> rreplacements,
      std::unordered_map<MemPath, const IR::Expression *> wreplacements);
  const IR::Node *operator()(const IR::Node *n);
};

struct select {
  std::unordered_set<node_t> sel;

  void add(node_t n) { sel.emplace(n); }
  void flatten(node_t at) {
    if (sel.size() == 1) return;
    sel = {at};
  }
  select(node_t at) : sel({at}) {}
  select() : sel({node_t::before()}) {}
};

std::unordered_set<MemPath> all(const EdgeHolder &g, const node_t &start,
                                P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                                NodeToFunctionMap *funMap);
}

#endif  // P4C_SSA_H
