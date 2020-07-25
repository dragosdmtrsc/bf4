//
// Created by dragos on 02.01.2020.
//

#ifndef P4C_SYMBEX_H
#define P4C_SYMBEX_H

#include <analysis/cfg_algos.h>
#include <analysis/context/InterproceduralCFGs.h>
#include <analysis/versions.h>

namespace analysis {
struct pc_t {
  node_t nd;
  int at;
  pc_t(const node_t &nd, int at);
  bool is_end() const;
  bool operator==(const pc_t &other) const;
  pc_t next() const;
  const IR::Node *operator*() const;
};

typedef std::vector<const IR::Expression *> path_condition_t;

struct state_t {
  pc_t location;
  std::vector<const IR::MethodCallStatement *> called;
  path_condition_t path_condition;
  std::unordered_map<MemPath, const IR::Expression *> store;
  state_t(pc_t location) : location(location) {}
  const IR::Expression *condition() const;
};

std::vector<pc_t> neighbors(const EdgeHolder &hld, const pc_t &loc);
std::vector<state_t> execute(pc_t next, state_t st, P4::ReferenceMap *refMap,
                             P4::TypeMap *typeMap, NodeToFunctionMap *);

struct tab_summary {
  std::string name;
  PathSet read;
  PathSet directWrites;
  PathSet written;
  std::vector<std::pair<path_condition_t, PathSet>> conditionals;
  tab_summary(const std::unordered_set<MemPath> &read) : read(read.begin(), read.end()) {}
  PathSet &newConditional(path_condition_t pc);
  std::map<PathSet, std::vector<path_condition_t>> shard_writes();

  void summarize();
  friend std::ostream &operator<<(std::ostream &os, const tab_summary &ts);
};
const IR::Expression *getExpression(const path_condition_t &pc);
const IR::Expression *expressPathConditions(const std::vector<path_condition_t> &pcs);
}

#endif // P4C_SYMBEX_H
