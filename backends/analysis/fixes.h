//
// Created by dragos on 19.01.2019.
//

#ifndef P4C_FIXES_H
#define P4C_FIXES_H

#include "cegis.h"
#include "cfg_algos.h"
#include "smt_helpers.h"
#include "version_propagator.h"
#include "versions.h"
#include <analysis/constprop/constant_propagation.h>
#include <chrono>
#include <common/resolveReferences/referenceMap.h>
#include <fstream>
#include <ir/pass_manager.h>
#include <midend/interpreter.h>
#include <p4/tableKeyNames.h>
#include <p4/typeMap.h>
#include <z3++.h>

namespace analysis {

class DoComputeFixes : public Inspector {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  z3::context *context;
  std::map<node_t, std::vector<const IR::Expression *>> *simple_fixes;
  ComputeGraph graph_computer;
  std::ofstream ofs;

public:
  DoComputeFixes(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                 z3::context *context,
                 std::map<node_t, std::vector<const IR::Expression *>>
                     *simple_fixes)
      : refMap(refMap), typeMap(typeMap), context(context),
        simple_fixes(simple_fixes), graph_computer(refMap),
        ofs("compute_fixes.txt") {}

  static const IR::Expression *str_to_expr(const std::string &s);

  bool preorder(const IR::P4Parser *parser) override;
};

class Node2StateAndTable : public Inspector {
  std::map<node_t, std::vector<const IR::Expression *>> *simple_fixes;
  std::map<std::pair<cstring, cstring>, std::vector<const IR::Expression *>>
      *fixes;

  bool preorder(const IR::Node *node) override;

public:
  Node2StateAndTable(
      std::map<node_t, std::vector<const IR::Expression *>>
          *simple_fixes,
      std::map<std::pair<cstring, cstring>, std::vector<const IR::Expression *>>
          *fixes)
      : simple_fixes(simple_fixes), fixes(fixes) {}
};

class DoFixOldProgram : public Transform {
  std::map<const IR::Node *, std::vector<const IR::Expression *>> *simple_fixes;
  std::map<std::pair<cstring, cstring>, std::vector<const IR::Expression *>>
      *fixes;

  const IR::Node *preorder(IR::P4Table *table) override;

public:
  DoFixOldProgram(std::map<std::pair<cstring, cstring>,
                           std::vector<const IR::Expression *>> *fixes)
      : simple_fixes(nullptr), fixes(fixes) {}
};

class Fixes : public PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  z3::context context;
  std::map<std::pair<cstring, cstring>, std::vector<const IR::Expression *>>
      fixes;
  std::map<node_t, std::vector<const IR::Expression *>> simple_fixes;
  const IR::P4Program *&old_program;
  DoFixOldProgram *fix_gen;

public:
  Fixes(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
        const IR::P4Program *&old_program)
      : refMap(refMap), typeMap(typeMap), old_program(old_program),
        fix_gen(new DoFixOldProgram(&fixes)) {
    passes.push_back(
        new DoComputeFixes(refMap, typeMap, &context, &simple_fixes));
    passes.push_back(new Node2StateAndTable(&simple_fixes, &fixes));
    passes.push_back(
        new VisitFunctor([this](const IR::Node *) -> const IR::Node * {
          return this->old_program->apply(*fix_gen);
        }));
  }
};
}

#endif // P4C_FIXES_H
