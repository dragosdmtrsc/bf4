
#include "dj_set_expl.h"

namespace analysis {
std::vector<id_t> dj_set_expl::ancestors(const std::vector<id_t> &vs, id_t e) {
  std::vector<id_t> ancs;
  while (e > 0) {
    ancs.push_back(e);
    e = vs[e];
  }
  return ancs;
}

void dj_set_expl::explain(id_t xid, id_t yid,
                          std::vector<std::pair<id_t, id_t>> &eqns) const {
  if (xid == yid)
    return;
  auto ancs_x = ancestors(raw_parents, xid);
  auto ancs_y = ancestors(raw_parents, yid);
  auto I = ancs_x.rbegin();
  auto J = ancs_y.rbegin();
  for (; I != ancs_x.rend() && J != ancs_y.rend() && *I == *J; ++I, ++J) {
  }
  --I;
  for (auto x = xid; x != *I; x = raw_parents[x]) {
    eqns.emplace_back(x, raw_parents[x]);
  }
  for (auto y = yid; y != *I; y = raw_parents[y]) {
    eqns.emplace_back(y, raw_parents[y]);
  }
}

std::vector<std::pair<id_t, id_t>> dj_set_expl::explain(id_t xid,
                                                        id_t yid) const {
  auto rxid = rep(xid);
  auto ryid = rep(yid);
  if (rxid != ryid) return {};
  std::vector<std::pair<id_t, id_t>> eqns;
  explain(xid, yid, eqns);
  return eqns;
}

id_t dj_set_expl::rep(id_t a) const {
  auto p = a;
  while (parents[p] > 0)
    p = parents[p];
  auto rt = p;
  p = a;
  // do path compression
  while (p != rt) {
    parents[p] = rt;
    p = parents[p];
  }
  return rt;
}

int dj_set_expl::set_union(id_t xid, id_t yid) {
  auto rxid = rep(xid);
  auto ryid = rep(yid);
  // check if current equation is redundant
  if (rxid == ryid)
    return -1;
  auto s1 = sizes[rxid];
  auto s2 = sizes[ryid];
  // int factor = 1;
  if (s1 < s2) {
    std::swap(rxid, ryid);
    std::swap(xid, yid);
    std::swap(s1, s2);
    // factor = -1;
  }
  equations.emplace_back(xid, yid);
  int eq_id = equations.size() - 1;
  // size(rxid) > size(ryid)
  sizes[rxid] += sizes[ryid];
  parents[ryid] = rxid;
  // this is for O(k * log(n)) implementation
  // raw_parents[ryid] = rxid;
  // parent_equation[ryid] = factor * eq_id;

  // this is for O(k) implementation
  auto yancestors = ancestors(raw_parents, yid);
  // reverse path from y to its root
  for (auto I = yancestors.rbegin(); I != yancestors.rend(); ++I) {
    auto rp = raw_parents[*I];
    raw_parents[rp] = *I;
  }
  // create edge y -> x
  raw_parents[yid] = xid;
  return eq_id;
}

id_t dj_set_expl::newid() {
  parents.push_back(-1);
  raw_parents.push_back(-1);
  sizes.push_back(1);
  return latestId++;
}

std::pair<congruence_closure_t::var_t, congruence_closure_t::var_t>
congruence_closure_t::get_reason(
    const congruence_closure_t::reason_for_equality_t &reason) {
  if (auto vet = boost::get<var_eq_t>(&reason)) {
    return {vet->left, vet->right};
  } else if (auto fep = boost::get<fun_eq_pair_t>(&reason)) {
    return {fep->first.a, fep->second.a};
  } else {
    assert(false);
  }
}

void congruence_closure_t::propagate() {
  while (!pending.empty()) {
    auto E = pending.back();
    pending.pop_back();
    var_t a, b;
    std::tie(a, b) = get_reason(E);
    auto aprime = get_representative(a);
    auto bprime = get_representative(b);
    if (aprime != bprime) {
      auto &cls_list_a = class_list[aprime];
      auto &cls_list_b = class_list[bprime];
      if (cls_list_a.size() > cls_list_b.size()) {
        std::swap(aprime, bprime);
        std::swap(a, b);
        std::swap(cls_list_a, cls_list_b);
      }
      // INSERT edge (a, b) in proof forest
      auto eqid = proof_forest.set_union(a, b);
      if (eqid >= 0) {
        proof_forest_edge_labels[eqid] = E;
        for (auto c : cls_list_a) {
          representatives[c] = bprime;
        }
        cls_list_b.insert(cls_list_b.end(), cls_list_a.begin(),
                          cls_list_a.end());
        class_list.erase(aprime);
        auto &ause_lists = use_lists[aprime];
        auto &buse_lists = use_lists[bprime];
        for (const auto &e : ause_lists) {
          auto c1_ = get_representative(e.a1);
          auto c2_ = get_representative(e.a2);
          auto Jlp = lookup.find(std::make_pair(c1_, c2_));
          if (Jlp != lookup.end()) {
            pending.push_back(std::make_pair(Jlp->second, e));
          } else {
            lookup.emplace(std::make_pair(c1_, c2_), e);
            buse_lists.push_back(e);
          }
        }
        ause_lists.clear();
      }
    }
  }
}

void congruence_closure_t::add_equality(
    const boost::variant<congruence_closure_t::var_eq_t,
                         congruence_closure_t::var_fun_eq_t> &eq) {
  if (const var_eq_t *veq = boost::get<var_eq_t>(&eq)) {
    pending.push_back(*veq);
    propagate();
  } else if (const var_fun_eq_t *vfe = boost::get<var_fun_eq_t>(&eq)) {
    auto a1_ = get_representative(vfe->a1);
    auto a2_ = get_representative(vfe->a2);
    auto Jlp = lookup.find(std::make_pair(a1_, a2_));
    if (Jlp != lookup.end()) {
      pending.emplace_back(std::make_pair(*vfe, Jlp->second));
      propagate();
    } else {
      lookup.emplace(std::make_pair(a1_, a2_), *vfe);
      use_lists[a1_].push_back(*vfe);
      use_lists[a2_].push_back(*vfe);
    }
  } else {
    assert(false);
  }
}

congruence_closure_t::var_t congruence_closure_t::create_new_var() {
  auto id = representatives.size();
  representatives.push_back(id);
  class_list[id] = {id};
  proof_forest.newid();
  return id;
}

}; // namespace analysis