#ifndef P4C_DJ_SET_EXPL_H
#define P4C_DJ_SET_EXPL_H

#include <cmath>
#include <vector>
#include <map>
#include <tuple>
#include <boost/variant.hpp>

namespace analysis {
typedef long id_t;
typedef unsigned eqid_t;
typedef int oriented_eq_t;

class dj_set_expl {
private:
  id_t latestId = 0;

  // ground equations
  std::vector<std::pair<id_t, id_t>> equations;

  // union find stuff
  std::vector<id_t> sizes;
  mutable std::vector<id_t> parents;

  // union find no compression
  std::vector<id_t> raw_parents;
  std::vector<oriented_eq_t> parent_equation;

  static std::vector<id_t> ancestors(const std::vector<id_t> &vs, id_t e);

 public:
  friend struct congruence_closure_t;
  // O(k) implementation of explain
  void explain(id_t xid, id_t yid,
               std::vector<std::pair<long, long>> &eqns) const;
  std::vector<std::pair<long, long>> explain(id_t xid, id_t yid) const;

  id_t rep(id_t a) const;
  int set_union(id_t xid, id_t yid);
  id_t newid();
  dj_set_expl() {}
};

// from paper: Proof-producing congruence closure
struct congruence_closure_t {
public:
  typedef size_t representative_t;
  typedef size_t var_t;

  struct var_eq_t {
    var_t left, right;
    var_eq_t(var_t left, var_t right) : left(left), right(right) {}
    var_eq_t() = default;
  };
  struct var_fun_eq_t {
    // equivalent to f(a1, a2) == a, where
    // a1, a2, a are variables
    var_t a1, a2, a;
    var_fun_eq_t(var_t a1, var_t a2, var_t a) : a1(a1), a2(a2), a(a) {}
    var_fun_eq_t() = default;
  };

  typedef std::vector<representative_t> representatives_t;
  representatives_t representatives;

  // map a representative to all constants 
  typedef std::map<representative_t, std::vector<var_t>> class_list_t;
  class_list_t class_list;

  // pending equalities. Pending a==b due to distinct reasons
  typedef std::pair<var_fun_eq_t, var_fun_eq_t> fun_eq_pair_t;
  typedef boost::variant<var_eq_t, fun_eq_pair_t> reason_for_equality_t;
  std::vector<reason_for_equality_t> pending;

  // use_lists(a) == all var_fun_equations which are using a
  typedef std::vector<var_fun_eq_t> use_list_t;
  std::map<representative_t, use_list_t> use_lists;

  // lookup(b, c) == (f(a1, a2) = a and representatives(a1) == b and
  // representatives(a2) == c)
  typedef std::map<std::pair<representative_t, representative_t>, var_fun_eq_t>
      lookup_table_t;
  lookup_table_t lookup;

  dj_set_expl proof_forest;
  std::map<int, reason_for_equality_t> proof_forest_edge_labels;

  representative_t get_representative(var_t x) const {
    return representatives[x];
  }
  
  // returns the pair (a, b) implied by this reason for equality
  // the reason is the stuff held by pending which will translate
  // to representatives and friends
  std::pair<var_t, var_t> get_reason(const reason_for_equality_t &reason);
  void propagate();
  void add_equality(const boost::variant<var_eq_t, var_fun_eq_t> &eq);
  bool equal(var_t v1, var_t v2) const {
    return representatives[v1] == representatives[v2];
  }

  var_t create_new_var();
};

template <typename T>
struct variable_context_t {
  typedef congruence_closure_t::var_t var_t;
  congruence_closure_t cc;
  std::map<T, var_t> vars;
  std::map<var_t, T> revvars;
  T for_variable(var_t v) const { return revvars.find(v)->second; }
  var_t var(T v) {
    auto I = vars.find(v);
    if (I != vars.end()) return I->second;
    auto nv = cc.create_new_var();
    vars.emplace(v, nv);
    revvars.emplace(nv, v);
    return nv;
  }
};
}
#endif