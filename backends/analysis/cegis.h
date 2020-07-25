//
// Created by dragos on 31.10.2018.
//

#ifndef P4C_CEGIS_H
#define P4C_CEGIS_H

#include <lib/exceptions.h>
#include <lib/log.h>
#include <z3++.h>
#include <map>
#include <set>
#include <unordered_set>
#include <vector>
#include "analysis_helpers.h"

class cegis {
  z3::expr sigma;
  unsigned long crt = 0;
  z3::context &ctx() { return sigma.ctx(); }

  std::string next() {
    auto str = std::to_string(crt++);
    return "tmp__" + str;
  }

 public:
  cegis(const z3::expr &sigma) : sigma(sigma) {}

  z3::expr replace_constants(const z3::expr &old);

  std::map<std::string, unsigned> occurences(const z3::expr &expr);

  std::vector<z3::expr> atoms(const z3::expr &expr, const std::string &what);

  z3::expr generate_forall(const z3::expr &,
                           const std::map<std::string, unsigned> &);

  virtual std::pair<bool, z3::expr> deduce(z3::solver &slv);
  ;

  z3::expr run();

  z3::expr simplify(z3::expr sigma);

  template <typename T, typename Theory>
  static z3::expr inferSIC(const z3::expr &sigma, T variables,
                           const Theory &theory);
};

std::unordered_map<z3::expr, std::unordered_set<std::string>> unconstrained(
    const z3::expr &e, const std::map<std::string, unsigned> &occs);
z3::expr remove_unconstrained(const z3::expr &expr,
                              std::map<std::string, unsigned> &occurs);
class packet_theory;
z3::expr remove_packets(const z3::expr &expr, packet_theory &pt);
template <typename Fun>
z3::expr remove_unconstrained(const z3::expr &expr, Fun f) {
  cegis c(expr);
  auto occs = c.occurences(expr);
  for (auto I = occs.begin(); I != occs.end();) {
    if (!f(I->first))
      I = occs.erase(I);
    else
      ++I;
  }
  return remove_unconstrained(expr, occs);
}

z3::expr chunkify(const z3::expr &expr);

bool any_occurence(const z3::func_decl &ct, const z3::expr &target);
template <typename T>
bool any_occurence(T variables, const z3::expr &target) {
  if (target.is_app()) {
    if (target.decl().decl_kind() == Z3_OP_TRUE ||
        target.decl().decl_kind() == Z3_OP_FALSE ||
        target.decl().decl_kind() == Z3_OP_BNUM ||
        target.decl().decl_kind() == Z3_OP_DT_CONSTRUCTOR)
      return false;
    if (target.is_const()) return variables(target.decl().name().str());
    for (unsigned i = 0; i != target.num_args(); ++i)
      if (any_occurence(variables, target.arg(i))) return true;
  }
  return false;
}

template <typename T>
std::vector<unsigned> candidates(const z3::expr &and_e, T variables) {
  std::vector<unsigned> cand;
  for (unsigned i = 0; i != and_e.num_args(); ++i) {
    const auto &arg = and_e.arg(i);
    if (arg.is_app() && arg.decl().decl_kind() == Z3_OP_EQ) {
      if (arg.arg(0).is_const() || arg.arg(1).is_const()) {
        if (arg.arg(0).is_const() &&
            arg.arg(0).decl().decl_kind() == Z3_OP_UNINTERPRETED &&
            variables(arg.arg(0).decl().name().str()) &&
            !any_occurence(arg.arg(0).decl(), arg.arg(1))) {
          cand.emplace_back(i);
        } else if (arg.arg(1).is_const() &&
                   arg.arg(1).decl().decl_kind() == Z3_OP_UNINTERPRETED &&
                   variables(arg.arg(1).decl().name().str()) &&
                   !any_occurence(arg.arg(1).decl(), arg.arg(0))) {
          cand.emplace_back(i);
        }
      }
    } else if (arg.is_const() &&
               arg.decl().decl_kind() == Z3_OP_UNINTERPRETED) {
      if (variables(arg.decl().name().str())) cand.emplace_back(i);
    } else if (arg.is_app() && arg.decl().decl_kind() == Z3_OP_NOT) {
      if (arg.arg(0).is_const() &&
          arg.arg(0).decl().decl_kind() == Z3_OP_UNINTERPRETED) {
        if (variables(arg.arg(0).decl().name().str())) cand.emplace_back(i);
      }
    }
  }
  return cand;
}

template <typename T>
std::pair<z3::expr, z3::expr> miniscope_ex(const z3::expr &initial,
                                           T variables) {
  if (initial.is_app() && initial.decl().decl_kind() == Z3_OP_AND) {
    z3::expr_vector remaining(initial.ctx()), withdraw(initial.ctx());
    for (unsigned i = 0; i != initial.num_args(); ++i) {
      if (!any_occurence(variables, initial.arg(i))) {
        withdraw.push_back(initial.arg(i));
      } else {
        remaining.push_back(initial.arg(i));
      }
    }
    return {z3::mk_and(withdraw), z3::mk_and(remaining)};
  }
  return {initial.ctx().bool_val(true), initial};
};

template <typename T>
void get_variables(const z3::expr &initial, T variables,
                   std::set<std::string> &what, z3::expr_vector &vec) {
  if (initial.is_const() && initial.decl().decl_kind() == Z3_OP_UNINTERPRETED) {
    if (variables(initial.decl().name().str()) &&
        what.emplace(initial.decl().name().str()).second) {
      vec.push_back(initial);
      return;
    }
  }
  if (initial.is_app()) {
    auto args = initial.num_args();
    for (unsigned i = 0; i != args; ++i) {
      get_variables(initial.arg(i), variables, what, vec);
    }
  }
}

// void find_unconstrained(
//    const z3::expr &expr,
//    std::unordered_map<z3::expr, std::pair<bool, std::set<std::string>>>
//        &unconstrained,
//    const std::map<std::string, unsigned> &occs,
//    std::vector<std::string> &bounds) {
//  if (occs.empty()) {
//    return;
//  }
//  if (expr.is_const() && expr.decl().decl_kind() == Z3_OP_UNINTERPRETED) {
//    return;
//  }
//  if (expr.is_app()) {
//    auto dec = expr.decl();
//    bool all = true;
//    bool any = false;
//    std::set<std::string> ucs;
//    for (auto e = expr.num_args(), i = 0; i != e; ++i) {
//      auto arg = expr.arg(static_cast<unsigned int>(i));
//      find_unconstrained(arg, unconstrained, occs, bounds);
//      auto &unconstrd = unconstrained[arg];
//      all = all && unconstrd.first;
//      ucs.emplace(unconstrd.second.begin(), unconstrd.second.end());
//      any = any || unconstrd.first;
//    }
//    if (all) {
//      unconstrained[expr] = {true, ucs};
//      return;
//    }
//    if (!any) {
//      return;
//    }
//    if (dec.decl_kind() == Z3_OP_BADD || dec.decl_kind() == Z3_OP_EQ ||
//        dec.decl_kind() == Z3_OP_BXOR) {
//      unconstrained[expr] = {true, ucs};
//      return;
//    }
//  } else if (expr.is_quantifier()) {
//    auto nrs = Z3_get_quantifier_num_bound(expr.ctx(), expr);
//    for (unsigned i = 0; i != nrs; ++i) {
//      z3::symbol nm(expr.ctx(),
//                    Z3_get_quantifier_bound_name(expr.ctx(), expr, i));
//      bounds.push_back(nm.str());
//    }
//    find_unconstrained(expr.body(), unconstrained, occs, bounds);
//    for (unsigned i = 0; i != nrs; ++i) bounds.pop_back();
//  } else if (expr.is_var()) {
//    auto idx = Z3_get_index_value(expr.ctx(), expr);
//    auto I = occs.find(bounds[bounds.size() - idx - 1]);
//    if (I != occs.end() && I->second == 1) {
//      unconstrained[expr] = {true, {I->first}};
//      return;
//    }
//  } else {
//    BUG("unknown kind of expression %1%", expr);
//  }
//}
//
// z3::expr remove_unconstrained(const z3::expr &expr,
//                              const std::map<std::string, unsigned> &occs) {
//  std::unordered_map<z3::expr, std::pair<bool, std::set<std::string>>>
//  uncnstrd;
//  std::vector<std::string> bounds;
//  find_unconstrained(expr, uncnstrd, occs, bounds);
//  std::vector<std::tuple<std::set<std::string>, std::string>> repls;
//  std::function<void(z3::expr &)> f;
//  f = [&](z3::expr &e) {
//    if (e.is_app()) {
//      auto I = uncnstrd.find(e);
//      if (I != uncnstrd.end()) {
//        auto ct = z3::expr(expr.ctx(),
//                           Z3_mk_fresh_const(expr.ctx(), "v", e.get_sort()));
//        repls.emplace_back(I->second.second, ct.decl().name().str());
//      } else {
//        auto f_ = e.decl();
//        z3::expr_vector evec(f_.ctx());
//        for (unsigned auto int i = 0; i != e.num_args(); ++i) {
//          auto cp = e.arg(i);
//          f(cp);
//          evec.push_back(cp);
//        }
//        e = f_(evec);
//      }
//    } else if (e.is_quantifier()) {
//      auto nrs = Z3_get_quantifier_num_bound(expr.ctx(), expr);
//      for (auto &xx : repls) {
//        for (unsigned i = 0; i != nrs; ++i) {
//          z3::symbol nm(expr.ctx(),
//                        Z3_get_quantifier_bound_name(expr.ctx(), expr, i));
//          auto J = std::get<0>(xx).find(nm.str());
//          if (J != std::get<0>(xx).end()) {
//
//          }
//          auto strr = nm.str();
//        }
//      }
//
//    }
//  };
//}

template <typename T>
z3::expr_vector get_variables(const z3::expr &initial, T variables) {
  std::set<std::string> occs;
  z3::expr_vector v(initial.ctx());
  get_variables(initial, variables, occs, v);
  return v;
}

template <typename T>
z3::expr convert_to_forall(const z3::expr &initial, T variables) {
  auto vars = get_variables(initial, variables);
  return z3::forall(vars, initial);
}

namespace std {
template <>
struct hash<z3::expr> {
  size_t operator()(const z3::expr &k) const { return k.hash(); }
};
}

template <typename ForEach>
void recurse(const z3::expr &expr, ForEach foreach) {
  if (expr.is_app()) {
    if (foreach (expr)) {
      unsigned nargs = expr.num_args();
      for (unsigned i = 0; i != nargs; ++i) {
        recurse(expr.arg(i), foreach);
      }
    }
  } else if (expr.is_var()) {
    (void)foreach (expr);
  }
}

template <typename Pre, typename Post>
void recurse(const z3::expr &expr, Pre pre, Post post) {
  if (expr.is_app()) {
    if (pre(expr)) {
      unsigned nargs = expr.num_args();
      for (unsigned i = 0; i != nargs; ++i) {
        recurse(expr.arg(i), pre, post);
      }
      post(expr);
    }
  }
}

// template <typename Controlled>
// std::unordered_set<z3::expr> compute_controlled_literals(const z3::expr
// &expr,
//                                                         Controlled
//                                                         controlled_vars) {
//    auto atoms = analysis::get_atoms(expr);
//    auto changed = true;
//    while (changed) {
//
//    }
//}

template <typename Controlled>
std::unordered_set<z3::expr> find_controlled_literals(
    const z3::expr &expr, Controlled controlled_vars) {
  std::unordered_set<z3::expr> controlled_expressions;
  std::unordered_set<z3::expr> visited;
  auto pre = [&](const z3::expr &e) {
    if (!visited.emplace(e).second) return false;
    if (e.is_app()) {
      switch (e.decl().decl_kind()) {
        case Z3_OP_UNINTERPRETED:
          if (controlled_vars(e.decl().name().str())) {
            controlled_expressions.emplace(e);
          }
          return false;
        case Z3_OP_DT_CONSTRUCTOR:
        case Z3_OP_TRUE:
        case Z3_OP_FALSE:
        case Z3_OP_BNUM:
          controlled_expressions.emplace(e);
          return false;
        default:
          break;
      }
    }
    return true;
  };
  auto post = [&](const z3::expr &e) {
    if (e.is_app()) {
      switch (e.decl().decl_kind()) {
        case Z3_OP_UNINTERPRETED:
        case Z3_OP_DT_CONSTRUCTOR:
        case Z3_OP_TRUE:
        case Z3_OP_FALSE:
        case Z3_OP_BNUM:
        case Z3_OP_AND:
        case Z3_OP_OR:
        case Z3_OP_IMPLIES:
        case Z3_OP_ITE:
        case Z3_OP_NOT:
          return;
        default:
          break;
      }
      auto nargs = e.num_args();
      bool all_controlled = true;
      for (unsigned i = 0; i != nargs; ++i) {
        const auto &arg = e.arg(i);
        if (controlled_expressions.find(arg) == controlled_expressions.end()) {
          all_controlled = false;
          break;
        }
      }
      if (all_controlled) controlled_expressions.emplace(e);
    }
  };
  recurse(expr, pre, post);
  std::unordered_set<z3::expr> filtered;
  for (auto I = controlled_expressions.begin();
       I != controlled_expressions.end(); ++I) {
    const auto &ctrld = *I;
    if (ctrld.is_bool()) {
      auto simpd = ctrld.simplify();
      if (simpd.is_app() && simpd.decl().decl_kind() != Z3_OP_TRUE &&
          simpd.decl().decl_kind() != Z3_OP_FALSE)
        filtered.emplace(simpd);
    }
  }
  return filtered;
}

inline z3::expr to_nnf(const z3::expr &expr) {
  z3::tactic nnf =
      z3::tactic(expr.ctx(), "simplify") & z3::tactic(expr.ctx(), "nnf");
  z3::goal g(expr.ctx());
  g.add(expr);
  auto tr = nnf(g);
  BUG_CHECK(tr.size() == 1,
            "nnf conversion should produce 1 result, but produced %1%",
            tr.size());
  return tr[0].as_expr();
}

namespace analysis {

class EqGraph {};

template <typename Filter>
void get_atoms(const z3::expr &flat_context,
               std::unordered_set<z3::expr> &all_living_things, Filter filter) {
  recurse(flat_context,
          [&](const z3::expr &e) {
            if (e.get_sort().is_bool()) {
              if (e.is_true() || e.is_false()) return false;
              if (e.decl().decl_kind() == Z3_OP_AND ||
                  e.decl().decl_kind() == Z3_OP_OR ||
                  e.decl().decl_kind() == Z3_OP_NOT ||
                  e.decl().decl_kind() == Z3_OP_ITE ||
                  e.decl().decl_kind() == Z3_OP_IMPLIES) {
                return true;
              }
              if (e.is_eq() && e.arg(0).get_sort().is_bool()) return true;
              if (e.decl().decl_kind() == Z3_OP_UNINTERPRETED &&
                  filter(e.decl().name().str())) {
                all_living_things.emplace(e);
              } else if (e.decl().decl_kind() == Z3_OP_EQ) {
                auto e0 = e.arg(0);
                auto e1 = e.arg(1);
                if (e0.decl().decl_kind() == Z3_OP_UNINTERPRETED &&
                    filter(e0.decl().name().str())) {
                  all_living_things.emplace(e);
                }
                if (e1.decl().decl_kind() == Z3_OP_UNINTERPRETED &&
                    filter(e1.decl().name().str())) {
                  all_living_things.emplace(e);
                }
              } else {
                all_living_things.emplace(e);
              }
              return false;
            }
            return false;
          },
          [](const z3::expr &) {});
}

std::unordered_set<z3::expr> get_atoms(const z3::expr &flat_context);
inline z3::expr control_var(z3::context &ctx, const std::string &s);
z3::expr controls_expr(const z3::expr &need_to);
z3::expr_vector get_extra_controls(
    z3::solver &context, const std::unordered_set<z3::expr> &hints,
    const std::unordered_set<std::string> &must_control);

bool get_extra_control(z3::solver &context, z3::expr &must_control,
                       const std::set<std::string> &controls,
                       const std::set<std::string> &may_control,
                       const std::unordered_set<z3::expr> &hints,
                       z3::expr_vector &do_add);
}

z3::expr_vector generate_necessary_abstraction(
    z3::solver *pslv, z3::solver *pdual_slv,
    std::unordered_set<z3::expr> &ctrld,
    const std::unordered_set<z3::expr> &may_control);

z3::expr_vector generate_necessary_abstraction_2(
    z3::expr &rho_a, z3::solver *pslv, z3::solver *pdual_slv,
    std::unordered_set<z3::expr> &ctrld,
    const std::unordered_set<z3::expr> &may_control);

z3::expr_vector generate_necessary_abstraction(
    z3::solver *pslv, z3::solver *pdual_slv,
    std::unordered_set<z3::expr> &ctrld);

z3::expr merge_or(const z3::expr &e1, const z3::expr &e2);

template <typename T>
z3::expr convert_to_exists(const z3::expr &initial, T variables) {
  auto vars = get_variables(initial, variables);
  return z3::exists(vars, initial);
}

inline z3::expr flipQuantifierAndModifyBody(const z3::expr &quantifierExpr,
                                            const z3::expr &newBody) {
  auto context = &quantifierExpr.ctx();
  Z3_ast ast = (Z3_ast)quantifierExpr;
  int numBound = Z3_get_quantifier_num_bound(*context, ast);
  Z3_sort sorts[numBound];
  Z3_symbol decl_names[numBound];
  for (int i = 0; i < numBound; i++) {
    sorts[i] = Z3_get_quantifier_bound_sort(*context, ast, i);
    decl_names[i] = Z3_get_quantifier_bound_name(*context, ast, i);
  }

  Z3_ast newAst =
      Z3_mk_quantifier(*context, !Z3_is_quantifier_forall(*context, ast),
                       Z3_get_quantifier_weight(*context, ast), 0, {}, numBound,
                       sorts, decl_names, (Z3_ast)newBody);
  return to_expr(*context, newAst);
}

inline z3::expr negate(const z3::expr &initial) {
  z3::expr_vector vec(initial.ctx());
  if (initial.is_app()) {
    switch (initial.decl().decl_kind()) {
      case Z3_OP_NOT:
        return initial.arg(0);
      case Z3_OP_AND:
        for (unsigned i = 0; i != initial.num_args(); ++i) {
          vec.push_back(negate(initial.arg(i)));
        }
        return mk_or(vec);
      case Z3_OP_OR:
        for (unsigned i = 0; i != initial.num_args(); ++i) {
          vec.push_back(negate(initial.arg(i)));
        }
        return mk_and(vec);
      case Z3_OP_IMPLIES:
        return initial.arg(0) && negate(initial.arg(1));
      case Z3_OP_ITE: {
        auto a1n = negate(initial.arg(1));
        auto a2n = negate(initial.arg(2));
        return z3::ite(initial.arg(0), a1n, a2n) || (a1n && a2n);
      }
      case Z3_OP_TRUE:
        return initial.ctx().bool_val(false);
      case Z3_OP_FALSE:
        return initial.ctx().bool_val(true);
      default:
        return !initial;
    }
  } else if (initial.is_quantifier()) {
    return flipQuantifierAndModifyBody(initial, negate(initial.body()));
  } else if (initial.is_var()) {
    return !initial;
  } else {
    BUG("can't handle this %1%", initial);
  }
}

inline z3::expr applyDer(const z3::expr &expression) {
  auto context = &expression.ctx();
  z3::goal g(expression.ctx());
  g.add(expression);

  z3::tactic derTactic = z3::tactic(*context, "simplify") &
                         z3::tactic(*context, "distribute-forall") &
                         z3::tactic(*context, "elim-and") &
                         z3::tactic(*context, "der") &
                         z3::tactic(*context, "simplify") &
                         z3::tactic(*context, "distribute-forall") &
                         z3::tactic(*context, "simplify");

  z3::apply_result result = derTactic(g);
  z3::goal simplified = result[0];
  return simplified.as_expr();
}

template <typename T>
z3::expr cer(const z3::expr &initial, T variables,
             std::vector<std::pair<z3::func_decl, z3::expr>>
                 *known_replacements = nullptr) {
  auto crt = initial;
  unsigned old_hash = 0;
  auto &ctx = initial.ctx();

  while (old_hash != crt.hash()) {
    old_hash = crt.hash();
    if (crt.get_sort().is_bool() && crt.is_app() &&
        crt.decl().decl_kind() == Z3_OP_AND) {
      auto cand = candidates(crt, variables);
      auto I = cand.begin();
      if (I != cand.end()) {
        z3::expr_vector v(ctx);
        for (unsigned i = 0; i != crt.num_args(); ++i) {
          if (i != *I) v.push_back(crt.arg(i));
        }
        auto and_ = z3::mk_and(v);
        auto arg = crt.arg(*I);
        if (arg.is_app() && arg.num_args() > 1 &&
            arg.decl().decl_kind() == Z3_OP_EQ) {
          auto is_arg0 = arg.arg(0).is_const() &&
                         !any_occurence(arg.arg(0).decl(), arg.arg(1));
          auto is_arg1 = arg.arg(1).is_const() &&
                         !any_occurence(arg.arg(1).decl(), arg.arg(0));
          z3::expr_vector sub(ctx), with(ctx);
          bool arg0var = is_arg0 &&
                         arg.arg(0).decl().decl_kind() == Z3_OP_UNINTERPRETED &&
                         variables(arg.arg(0).decl().name().str());
          bool arg1var = is_arg1 &&
                         arg.arg(1).decl().decl_kind() == Z3_OP_UNINTERPRETED &&
                         variables(arg.arg(1).decl().name().str());
          if (arg0var) {
            sub.push_back(arg.arg(0));
            with.push_back(arg.arg(1));
          } else if (arg1var) {
            sub.push_back(arg.arg(1));
            with.push_back(arg.arg(0));
          }
          crt = and_.substitute(sub, with);
        } else if (arg.is_const()) {
          z3::expr_vector sub(ctx), with(ctx);
          bool arg0var = arg.decl().decl_kind() == Z3_OP_UNINTERPRETED &&
                         variables(arg.decl().name().str());
          if (arg0var) {
            sub.push_back(arg);
            with.push_back(ctx.bool_val(true));
          }
          crt = and_.substitute(sub, with);
        } else if (arg.num_args() == 1 && arg.is_app() &&
                   arg.decl().decl_kind() == Z3_OP_NOT) {
          z3::expr_vector sub(ctx), with(ctx);
          bool arg0var = arg.arg(0).decl().decl_kind() == Z3_OP_UNINTERPRETED &&
                         variables(arg.arg(0).decl().name().str());
          if (arg0var) {
            sub.push_back(arg);
            with.push_back(ctx.bool_val(true));
          }
          crt = and_.substitute(sub, with);
        }
      }
    }
  }
  return crt.simplify();
}

template <typename T, typename Theory>
z3::expr cegis::inferSIC(const z3::expr &sigma, T variables,
                         const Theory &theory) {
  if (sigma.is_app() && (sigma.decl().decl_kind() == Z3_OP_BNUM ||
                         sigma.decl().decl_kind() == Z3_OP_FALSE ||
                         sigma.decl().decl_kind() == Z3_OP_BNUM ||
                         sigma.decl().decl_kind() == Z3_OP_DT_CONSTRUCTOR)) {
    return sigma.ctx().bool_val(true);
  } else if (sigma.is_const()) {
    return sigma.ctx().bool_val(!variables(sigma.decl().name().str()));
  } else if (sigma.is_app()) {
    auto decl = sigma.decl();
    auto num_args = sigma.num_args();
    z3::expr_vector phis(sigma.ctx());
    z3::expr_vector psis(sigma.ctx());
    for (unsigned i = 0; i != num_args; ++i) {
      const auto &arg = sigma.arg(i);
      phis.push_back(arg);
      psis.push_back(inferSIC(arg, variables, theory));
    }
    auto Psi = theory(decl, phis, psis);
    return (Psi || z3::mk_and(psis)).simplify();
  } else {
    BUG("unknown expression %1%", sigma);
  }
}

class TaintTheory {
  z3::context &ctx;

 public:
  TaintTheory(z3::context &ctx) : ctx(ctx) {}
  z3::expr operator()(const z3::func_decl &d, const z3::expr_vector &phis,
                      const z3::expr_vector &psis) const {
    if (d.decl_kind() == Z3_OP_AND) {
      z3::expr_vector tor(ctx);
      unsigned sz = phis.size();
      for (unsigned i = 0; i != sz; ++i) {
        const auto &phi = phis[i];
        const auto &psi = psis[i];
        tor.push_back(psi && !phi);
      }
      return z3::mk_or(tor);
    } else if (d.decl_kind() == Z3_OP_OR) {
      z3::expr_vector tor(ctx);
      unsigned sz = phis.size();
      for (unsigned i = 0; i != sz; ++i) {
        const auto &phi = phis[i];
        const auto &psi = psis[i];
        tor.push_back(psi && phi);
      }
      return z3::mk_or(tor);
    } else if (d.decl_kind() == Z3_OP_NOT) {
      return psis[0];
    } else if (d.decl_kind() == Z3_OP_ITE) {
      return (psis[0] && z3::ite(phis[0], psis[1], psis[2])) ||
             (psis[1] && psis[2] && phis[1] == phis[2]);
    } else if (d.decl_kind() == Z3_OP_IMPLIES) {
      return (psis[0] && !phis[0]) || (psis[1] && phis[1]);
    } else if (d.decl_kind() == Z3_OP_EQ) {
      return ctx.bool_val(false);
    } else if (d.decl_kind() == Z3_OP_BAND) {
      z3::expr_vector tor(ctx);
      unsigned sz = phis.size();
      for (unsigned i = 0; i != sz; ++i) {
        const auto &phi = phis[i];
        const auto &psi = psis[i];
        auto srt = phi.get_sort();
        if (srt.is_bool()) {
          tor.push_back(psi && !phi);
        } else if (srt.is_bv()) {
          auto zeros = ctx.num_val(0, srt);
          tor.push_back(psi && (phi == zeros));
        }
      }
      return z3::mk_or(tor);
    } else if (d.decl_kind() == Z3_OP_BOR) {
      z3::expr_vector tor(ctx);
      unsigned sz = phis.size();
      for (unsigned i = 0; i != sz; ++i) {
        const auto &phi = phis[i];
        const auto &psi = psis[i];
        auto srt = phi.get_sort();
        if (srt.is_bool()) {
          tor.push_back(psi && !phi);
        } else if (srt.is_bv()) {
          auto ones = ctx.num_val(-1, srt);
          tor.push_back(psi && (phi == ones));
        }
      }
      return z3::mk_or(tor);
    }
    return ctx.bool_val(false);
  }
};

template <typename Filter>
void variables_to_control(const z3::expr &ez, Filter filter,
                          std::set<std::string> &vars) {
  recurse(ez,
          [&](const z3::expr &e) {
            if (e.is_app() && e.decl().decl_kind() == Z3_OP_UNINTERPRETED) {
              if (filter(e.decl().name().str()))
                vars.emplace(e.decl().name().str());
            }
            return true;
          },
          [](const z3::expr &) {});
}

std::map<std::string, z3::sort> typed_occurences(const z3::expr &expr);
bool is_unconstrained(const z3::expr &src,
                      const std::map<std::string, unsigned> &occs);

struct packet_theory {
  z3::context &context;
  z3::sort packetSort;
  z3::sort bsort;
  std::unordered_map<unsigned, z3::func_decl> packetExtracts;
  std::unordered_map<unsigned, z3::func_decl> packetEmits;
  std::unordered_map<unsigned, z3::func_decl> packetAdvances;
  std::unordered_map<unsigned, z3::func_decl> rotates;
  z3::func_decl zero;
  z3::func_decl prepend;
  z3::func_decl length;
  z3::func_decl constructor;
  z3::func_decl_vector projections;

  z3::context &ctx() { return context; }

  packet_theory(z3::context &context);

  z3::expr_vector make_axioms();

  bool isPacket(const z3::expr &e) { return z3::eq(e.get_sort(), packetSort); }

  z3::func_decl &advance(unsigned n) {
    return analysis::getOrEmplace(packetAdvances, n,
                                  [&]() {
                                    std::stringstream ss;
                                    ss << "modelAdvance_" << n;
                                    return context.function(ss.str().c_str(),
                                                            packetSort,
                                                            packetSort);
                                  })
        .first;
  }

  bool isConst(const z3::expr &e) { return e.is_const() && !isZero(e); }

  bool isPrepend(const z3::expr &e) {
    return e.is_app() && z3::eq(e.decl(), prepend);
  }
  bool isZero(const z3::expr &e) {
    return e.is_const() && z3::eq(e.decl(), zero);
  }
  z3::func_decl &extract(unsigned n) {
    return analysis::getOrEmplace(packetExtracts, n,
                                  [&]() {
                                    std::stringstream ss;
                                    ss << "modelExtract_" << n;
                                    return context.function(ss.str().c_str(),
                                                            packetSort,
                                                            context.bv_sort(n));
                                  })
        .first;
  }

  z3::func_decl &emit(unsigned sz) {
    return analysis::getOrEmplace(packetEmits, sz,
                                  [&]() {
                                    std::stringstream ss;
                                    ss << "modelEmit_" << sz;
                                    z3::sort_vector sortVector(context);
                                    sortVector.push_back(context.bv_sort(sz));
                                    return context.function(ss.str().c_str(),
                                                            sortVector,
                                                            packetSort);
                                  })
        .first;
  }
  z3::func_decl &reverse(unsigned sz) {
    return analysis::getOrEmplace(rotates, sz,
                                  [&]() {
                                    std::stringstream ss;
                                    ss << "reverse_" << sz;
                                    return context.function(
                                        ss.str().c_str(), context.bv_sort(sz),
                                        context.bv_sort(sz));
                                  })
        .first;
  }

  boost::optional<unsigned> is(const z3::func_decl &f, const char *name) {
    if (f.name().str().find(name) != std::string::npos) {
      auto nr = std::atoi(f.name().str().substr(strlen(name)).c_str());
      return static_cast<unsigned>(nr);
    }
    return {};
  }

  boost::optional<unsigned> isEmit(const z3::func_decl &f) {
    return is(f, "modelEmit_");
  }
  boost::optional<unsigned> isAdvance(const z3::func_decl &f) {
    return is(f, "modelAdvance_");
  }
  boost::optional<unsigned> isExtract(const z3::func_decl &f) {
    return is(f, "modelExtract_");
  }
};

struct packet_solver_ {
  z3::solver &s;
  packet_theory &pt;
  std::unordered_set<z3::expr> theory_atoms;
  std::unordered_map<z3::expr, unsigned> theory_atoms_polarity;

  // holds string -> unsigned -- assign term to id
  std::unordered_map<z3::expr, unsigned> index;
  // holds reverse mapping -- assign id to term
  std::vector<z3::expr> revindex;
  std::unordered_set<z3::expr> constants;
  // all terms must have a variable attached
  std::set<unsigned> free_terms;
  std::map<unsigned, z3::expr> dumb_vars;

  packet_solver_(z3::solver &s, packet_theory &pt);
  z3::context &ctx() { return s.ctx(); }
private:
  unsigned termid(const z3::expr &e);

public:
  void add(z3::expr e);

  z3::check_result check();
  z3::check_result check(z3::expr_vector &evec);
  z3::expr_vector unsat_core() const;
  z3::model get_model() const;

  void push();
  void pop(unsigned n = 1);
  void makeAxioms();

  friend std::ostream &operator<<(std::ostream &os, const packet_solver_ &ps);
};

void packet_solver(z3::expr_vector &assertions, packet_theory &);

#endif  // P4C_CEGIS_H
