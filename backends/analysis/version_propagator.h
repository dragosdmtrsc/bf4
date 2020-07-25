//
// Created by dragos on 18.12.2018.
//

#ifndef P4C_VERSION_PROPAGATOR_H
#define P4C_VERSION_PROPAGATOR_H

#include <ir/ir.h>
#include <z3++.h>
#include "cfg_algos.h"
#include "smt_helpers.h"
#include "versions.h"

namespace analysis {
cstring basic_name(const IR::Expression *lv, P4::TypeMap *typeMap);

class Z3Propagate {
  z3::context *context;
  const std::map<std::pair<node_t, int>, z3::expr> *transformer;

 public:
  Z3Propagate(z3::context *context,
              const std::map<std::pair<node_t, int>, z3::expr> *transformer)
      : context(context), transformer(transformer) {}
  bool operator()(const IR::Node *crt,
                  const std::pair<const IR::Node *, int> &neigh,
                  const z3::expr &oldex, z3::expr &newex) {
    if (neigh.second < 0) return false;
    newex =
        transformer->find(std::make_pair(crt, neigh.second))->second && oldex;
    return true;
  }
  z3::expr operator()() { return context->bool_val(true); }
  void operator()(z3::expr &into, const z3::expr &from) { into = into || from; }
};

typedef std::tuple<node_t, int, z3::expr> HistoryRecord;
typedef std::vector<HistoryRecord> History;
typedef History::const_iterator HistoryIterator;

void flatten_history(z3::expr &ret, HistoryIterator I, HistoryIterator E);

class SmartZ3Propagate {
  z3::context *context;
  const std::map<std::pair<node_t, int>, z3::expr> *transformer;

 public:
  SmartZ3Propagate(
      z3::context *context,
      const std::map<std::pair<node_t, int>, z3::expr> *transformer)
      : context(context), transformer(transformer) {}
  bool operator()(const IR::Node *crt,
                  const std::pair<const IR::Node *, int> &neigh,
                  const History &oldex, History &newex);

  bool label_eq(const HistoryRecord &t1, const HistoryRecord &t2);

  void operator()(History &into, const History &from);
};

void reachability_conditions_compute(
    const analysis::EdgeHolder *forward_graph,
    const std::vector<node_t> &sorted, node_t start,
    const std::map<std::pair<node_t, int>, z3::expr> &node_transformers,
    z3::context &context, std::map<node_t, z3::expr> *);

void reachability_conditions_compute(
    const analysis::EdgeHolder *forward_graph,
    const std::vector<node_t> &sorted,
    const std::map<std::pair<node_t, int>, z3::expr> &node_transformers,
    z3::context &context, std::map<node_t, z3::expr> *);

cstring to_string(const MemPath &adj);
const IR::Type *get_type(const MemPath &path, const TypeMap *typeMap, bool replace = true);


template <typename V, typename Fun>
class PathValues {
  std::unordered_map<MemPath, V> values;

 public:
  V &operator[](const MemPath &mp) {
    auto I = values.find(mp);
    if (I != values.end()) return I->second;
    return values.emplace(mp, (static_cast<Fun *>(this))->operator()(mp))
        .first->second;
  }
  V *get(const MemPath &mp) const {
    auto I = values.find(mp);
    if (I != values.end()) return &I->second;
    return nullptr;
  }
};

class PathTypes : public PathValues<const IR::Type *, PathTypes> {
  P4::TypeMap *typeMap;
  bool replace = true;

 public:
  PathTypes(TypeMap *typeMap) : typeMap(typeMap) {}
  PathTypes(TypeMap *typeMap, bool replace) : typeMap(typeMap), replace(replace) {}
  const IR::Type *operator()(const MemPath &mp) {
    return analysis::get_type(mp, typeMap, replace);
  }
};
}

#endif  // P4C_VERSION_PROPAGATOR_H
