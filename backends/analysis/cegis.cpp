//
// Created by dragos on 31.10.2018.
//

#include "cegis.h"
#include "cfg_algos.h"
#include <algorithm>
#include <fstream>
#include <boost/functional/hash.hpp>
#include <boost/pending/disjoint_sets.hpp>

std::pair<bool, z3::expr> cegis::deduce(z3::solver &slv) {
  const auto &asserts = slv.assertions();
  return {false, sigma.ctx().bool_val(true)};
}

z3::expr cegis::run() {
  auto occs = occurences(sigma);
  auto typed = typed_occurences(sigma);
  std::set<std::string> non_consts;
  for (const auto &p : occs) {
    if (p.first.find("pre_call") == std::string::npos) {
      non_consts.emplace(p.first);
    }
  }
  z3::solver slv(sigma.ctx());
  auto nsigma = !sigma;
  auto &ctx = sigma.ctx();
  auto expand_bools = sigma;
  while (true) {
    if (slv.check() != z3::check_result::sat) {
      return sigma.ctx().bool_val(false);
    }
    slv.push();
    slv.add(nsigma);
    auto cr2 = slv.check();
    if (cr2 == z3::check_result::sat) {
      auto cex = slv.get_model();
      slv.pop();
      auto deduced = deduce(slv);
      auto res = deduced.first;
      auto C = deduced.second;
      if (res) {
        return C;
      } else {
        auto sz = cex.size();
        z3::expr_vector rep(ctx), with(ctx);
        std::set<std::string> found;
        for (unsigned i = 0; i != sz; ++i) {
          auto fd = cex.get_const_decl(i);
          auto v = cex.get_const_interp(fd);
          if (fd.name().str().find("pre_call") == std::string::npos) {
            found.emplace(fd.name().str());
            // means input variable
            rep.push_back(fd());
            with.push_back(v);
          }
        }
        std::set<std::string> unfound;
        std::set_difference(non_consts.begin(), non_consts.end(), found.begin(),
                            found.end(), std::inserter(unfound, unfound.end()));
        for (const auto &uf : unfound) {
          auto tp = typed.find(uf)->second;
          rep.push_back(ctx.constant(uf.c_str(), tp));
          if (tp.is_bool()) {
            with.push_back(ctx.bool_val(true));
          } else {
            with.push_back(ctx.num_val(0, tp));
          }
        }
        slv.add(sigma.substitute(rep, with).simplify());
      }
    } else {
      slv.pop();
      return z3::mk_and(slv.assertions());
    }
  }
}

z3::expr cegis::replace_constants(const z3::expr &old) {
  if (old.is_app()) {
    if (old.decl().decl_kind() == Z3_OP_FALSE ||
        old.decl().decl_kind() == Z3_OP_TRUE) {
      return ctx().bool_const(next().c_str());
    }
    if (old.decl().decl_kind() == Z3_OP_DT_CONSTRUCTOR) {
      return ctx().constant(next().c_str(), old.get_sort());
    }
    if (old.is_const()) {
      if (old.decl().decl_kind() == Z3_OP_UNINTERPRETED) {
        return old;
      } else if (old.decl().decl_kind() == Z3_OP_BNUM) {
        return ctx().constant(next().c_str(), old.get_sort());
      }
    }
    auto num = old.num_args();
    z3::expr_vector quoi(ctx());
    for (unsigned i = 0; i != num; ++i) {
      auto arg = old.arg(i);
      quoi.push_back(replace_constants(arg));
    }
    return old.decl()(quoi);
  } else if (old.is_numeral()) {
    return ctx().constant(next().c_str(), old.get_sort());
  }

  return old;
}

std::unordered_map<z3::expr, std::unordered_set<std::string>>
unconstrained(const z3::expr &e, const std::map<std::string, unsigned> &occs) {
  std::unordered_map<z3::expr, std::unordered_set<std::string>> ucterms;
  std::function<void(const z3::expr &, std::vector<std::string> &)> lam;
  lam = [&](const z3::expr &e, std::vector<std::string> &bounds) -> void {
    if (e.is_app()) {
      if (e.is_const() && e.decl().decl_kind() == Z3_OP_UNINTERPRETED)
        return;
      if (e.decl().decl_kind() == Z3_OP_DT_CONSTRUCTOR)
        return;
      if (e.decl().decl_kind() == Z3_OP_BNUM)
        return;
      std::vector<z3::expr> vars;
      std::vector<z3::expr> nonvars;
      for (unsigned i = 0; i != e.num_args(); ++i) {
        if ((e.arg(i).is_const() &&
             e.arg(i).decl().decl_kind() == Z3_OP_UNINTERPRETED) ||
            e.arg(i).is_var()) {
          vars.push_back(e.arg(i));
        } else {
          nonvars.push_back(e.arg(i));
        }
      }
      bool uc = true;
      std::unordered_set<std::string> involved;
      for (auto &v : vars) {
        std::string declname;
        if (v.is_const()) {
          declname = v.decl().name().str();
        } else if (v.is_var()) {
          declname = bounds[bounds.size() - 1 - Z3_get_index_value(v.ctx(), v)];
        }
        auto I = occs.find(declname);
        if (I == occs.end() || I->second != 1) {
          uc = false;
        } else {
          involved.emplace(declname);
        }
      }
      if (e.is_eq() || e.decl().decl_kind() == Z3_OP_BADD) {
        if (involved.size() == 1) {
          ucterms[e] = std::move(involved);
        } else {
          for (auto &ex : nonvars) {
            lam(ex, bounds);
          }
        }
      } else {
        if (nonvars.empty()) {
          if (uc) {
            ucterms[e] = std::move(involved);
          }
        } else {
          for (auto &ex : nonvars) {
            lam(ex, bounds);
          }
        }
      }
    } else if (e.is_quantifier()) {
      auto nrs = Z3_get_quantifier_num_bound(e.ctx(), e);
      for (unsigned i = 0; i != nrs; ++i) {
        z3::symbol nm(e.ctx(), Z3_get_quantifier_bound_name(e.ctx(), e, i));
        bounds.push_back(nm.str());
      }
      lam(e.body(), bounds);
      for (unsigned i = 0; i != nrs; ++i)
        bounds.pop_back();
    } else if (e.is_var()) {
      return;
    }
  };
  std::vector<std::string> bounds;
  lam(e, bounds);
  return ucterms;
};

z3::expr remove_unconstrained(const z3::expr &expr,
                              std::map<std::string, unsigned> &occurs) {
  if (!expr.is_quantifier())
    return expr;
  auto nr = Z3_get_quantifier_num_bound(expr.ctx(), expr);
  std::vector<z3::sort> sorts;
  std::vector<std::string> names;
  std::unordered_set<std::string> remove;
  for (unsigned i = 0; i != nr; ++i) {
    auto qname = Z3_get_quantifier_bound_name(expr.ctx(), expr, i);
    z3::symbol symbol(expr.ctx(), qname);
    names.push_back(symbol.str());
    auto qsort = Z3_get_quantifier_bound_sort(expr.ctx(), expr, i);
    z3::sort srt(expr.ctx(), qsort);
    sorts.push_back(srt);
  }
  z3::expr_vector subs(expr.ctx());
  for (unsigned i = 0; i != nr; ++i) {
    subs.push_back(
        expr.ctx().constant(names[nr - 1 - i].c_str(), sorts[nr - 1 - i]));
  }
  auto qfexpr = expr;
  qfexpr = qfexpr.body().substitute(subs);
  for (unsigned i = 0; i != nr; ++i) {
    subs[i] = expr.ctx().constant(names[i].c_str(), sorts[i]);
  }

  BUG_CHECK(!qfexpr.is_quantifier(),
            "quantifier found even though not expecting one %1%", qfexpr);

  auto crt = qfexpr;
  cegis c(expr);
  bool change = true;
  auto crtoccurences = occurs;
  std::unordered_set<std::string> interesting;
  std::transform(
      occurs.begin(), occurs.end(),
      std::inserter(interesting, interesting.begin()),
      [](const std::pair<std::string, unsigned> &x) { return x.first; });
  do {
    LOG4("step: " << crt);
    change = false;
    auto ucd = unconstrained(crt, crtoccurences);
    for (auto &uc : ucd) {
      LOG4("uc: " << uc.first << Z3_get_ast_id(uc.first.ctx(), uc.first));
      auto fresh = z3::expr(expr.ctx(), Z3_mk_fresh_const(expr.ctx(), "v__",
                                                          uc.first.get_sort()));
      auto fname = fresh.decl().name().str();
      change = true;
      z3::expr_vector src(uc.first.ctx());
      src.push_back(uc.first);
      z3::expr_vector dst(uc.first.ctx());
      dst.push_back(fresh);
      crt = crt.substitute(src, dst).simplify();
      LOG4("after substitution:" << crt << " ");
      interesting.emplace(fname);
      remove.insert(uc.second.begin(), uc.second.end());
      for (auto &rm : uc.second)
        LOG4("removing " << rm);
      names.push_back(fname);
      sorts.push_back(fresh.get_sort());
      subs.push_back(fresh);
    }
    if (change) {
      auto nocs = c.occurences(crt);
      crtoccurences.clear();
      for (auto &n : nocs) {
        if (interesting.count(n.first))
          crtoccurences.emplace(n);
      }
    }
  } while (change);

  z3::expr_vector qs(expr.ctx());
  for (unsigned i = 0; i != names.size(); ++i) {
    if (!remove.count(names[i])) {
      qs.push_back(subs[i]);
    }
  }
  return z3::forall(qs, crt);
}

std::map<std::string, unsigned> occurences(const z3::expr &expr,
                                           std::vector<std::string> &bounds) {
  if (expr.is_const()) {
    if (expr.decl().decl_kind() == Z3_OP_UNINTERPRETED) {
      return {{expr.decl().name().str(), 1}};
    }
    return {};
  } else if (expr.is_var()) {
    auto idx = Z3_get_index_value(expr.ctx(), expr);
    return {{bounds[bounds.size() - idx - 1], 1}};
  }
  std::map<std::string, unsigned> res;
  if (expr.is_app()) {
    auto num = expr.num_args();
    for (unsigned i = 0; i != num; ++i) {
      auto arg = expr.arg(i);
      auto evd = occurences(arg, bounds);
      if (res.empty()) {
        res = std::move(evd);
      } else {
        for (const auto &pr : evd) {
          auto rib = res.emplace(pr);
          if (!rib.second) {
            rib.first->second += pr.second;
          }
        }
      }
    }
  } else if (expr.is_quantifier()) {
    auto body = expr.body();
    auto nrs = Z3_get_quantifier_num_bound(expr.ctx(), expr);
    for (unsigned i = 0; i != nrs; ++i) {
      z3::symbol nm(expr.ctx(),
                    Z3_get_quantifier_bound_name(expr.ctx(), expr, i));
      bounds.push_back(nm.str());
    }
    auto occs = occurences(body, bounds);
    for (unsigned i = 0; i != nrs; ++i)
      bounds.pop_back();
    return std::move(occs);
  }
  return res;
}

std::map<std::string, unsigned> cegis::occurences(const z3::expr &expr) {
  std::vector<std::string> bounds;
  return ::occurences(expr, bounds);
}

std::map<std::string, z3::sort> typed_occurences(const z3::expr &expr) {
  if (expr.is_const()) {
    if (expr.decl().decl_kind() == Z3_OP_UNINTERPRETED) {
      return {{expr.decl().name().str(), expr.get_sort()}};
    }
    return {};
  }
  std::map<std::string, z3::sort> res;
  if (expr.is_app()) {
    auto num = expr.num_args();
    for (unsigned i = 0; i != num; ++i) {
      auto arg = expr.arg(i);
      auto evd = typed_occurences(arg);
      if (res.empty()) {
        res = std::move(evd);
      } else {
        for (const auto &pr : evd) {
          auto rib = res.emplace(pr);
          if (!rib.second) {
            rib.first->second = pr.second;
          }
        }
      }
    }
  }
  return res;
}

std::vector<z3::expr> cegis::atoms(const z3::expr &expr,
                                   const std::string &what) {
  if (expr.get_sort().is_bool() && expr.is_app()) {
    auto decl = expr.decl();
    if (decl.decl_kind() == Z3_OP_AND || decl.decl_kind() == Z3_OP_OR ||
        decl.decl_kind() == Z3_OP_NOT || decl.decl_kind() == Z3_OP_IMPLIES) {
      // nothing to do here , will be handled below
    } else {
      auto occs = occurences(expr);
      if (occs.count(what)) {
        return {expr};
      }
    }
  }
  std::vector<z3::expr> res;
  if (expr.is_app()) {
    auto num = expr.num_args();
    for (unsigned i = 0; i != num; ++i) {
      auto arg = expr.arg(i);
      auto evd = atoms(arg, what);
      if (res.empty()) {
        res = std::move(evd);
      } else {
        res.insert(res.end(), evd.begin(), evd.end());
      }
    }
  }
  return res;
}

bool is_unconstrained(const z3::expr &src,
                      const std::map<std::string, unsigned> &occs) {
  if (src.is_app()) {
    if (src.is_bool()) {
      if (src.is_app() && src.decl().decl_kind() == Z3_OP_TRUE)
        return false;
      if (src.is_app() && src.decl().decl_kind() == Z3_OP_FALSE)
        return false;
      const auto &decl = src.decl();
      if (decl.decl_kind() == Z3_OP_EQ) {
        auto arg1 = src.arg(0);
        auto arg2 = src.arg(1);
        if (is_unconstrained(arg1, occs) || is_unconstrained(arg2, occs)) {
          return true;
        } else {
          if (arg1.is_app() && arg1.decl().decl_kind() == Z3_OP_BAND &&
              arg2.is_app() && arg2.decl().decl_kind() == Z3_OP_BAND) {
            auto arg11 = arg1.arg(0);
            auto arg12 = arg1.arg(1);
            auto arg21 = arg2.arg(0);
            auto arg22 = arg2.arg(1);
            if (z3::eq(arg12, arg22) && (is_unconstrained(arg11, occs) ||
                                         is_unconstrained(arg21, occs))) {
              return true;
            }
          } else if (arg1.is_app() && arg1.decl().decl_kind() == Z3_OP_BNOT &&
                     arg2.is_app() && arg2.decl().decl_kind() == Z3_OP_BNOT) {
            // the bv rewriter does this for some yet undisclosed reasons
            auto arg11 = arg1.arg(0);
            auto arg21 = arg2.arg(0);
            if (arg11.is_app() && arg11.decl().decl_kind() == Z3_OP_BOR &&
                arg21.is_app() && arg21.decl().decl_kind() == Z3_OP_BOR) {
              if (arg11.num_args() == 2 && 2 == arg21.num_args()) {
                auto arg111 = arg11.arg(0);
                auto arg112 = arg11.arg(1);
                auto arg211 = arg21.arg(0);
                auto arg212 = arg21.arg(1);
                if (arg111.is_app() &&
                    arg111.decl().decl_kind() == Z3_OP_BNOT &&
                    arg112.is_app() &&
                    arg112.decl().decl_kind() == Z3_OP_BNOT &&
                    arg211.is_app() &&
                    arg211.decl().decl_kind() == Z3_OP_BNOT &&
                    arg212.is_app() &&
                    arg212.decl().decl_kind() == Z3_OP_BNOT) {
                  if (z3::eq(arg212.arg(0), arg112.arg(0)) &&
                      (is_unconstrained(arg111, occs) ||
                       is_unconstrained(arg211, occs))) {
                    return true;
                  }
                }
              }
            }
          }
        }
      }
    }
    if (src.is_app() && src.decl().decl_kind() == Z3_OP_BNUM)
      return false;
    if (src.is_const() && src.decl().decl_kind() == Z3_OP_UNINTERPRETED)
      return occs.find(src.decl().name().str())->second == 1;
    auto num = src.num_args();
    bool uncnstrd = true;
    for (unsigned i = 0; i != num; ++i) {
      if (!is_unconstrained(src.arg(i), occs)) {
        uncnstrd = false;
        break;
      }
    }
    if (uncnstrd)
      return true;
  }
  return false;
}

bool any_occurence(const std::string &ct, const z3::expr &target) {
  if (target.is_app()) {
    if (target.decl().decl_kind() == Z3_OP_TRUE ||
        target.decl().decl_kind() == Z3_OP_FALSE ||
        target.decl().decl_kind() == Z3_OP_BNUM ||
        target.decl().decl_kind() == Z3_OP_DT_CONSTRUCTOR)
      return false;
    if (target.is_const())
      return target.decl().name().str() == ct;
    for (unsigned i = 0; i != target.num_args(); ++i)
      if (any_occurence(ct, target.arg(i)))
        return true;
  }
  return false;
}

bool any_occurence(const z3::func_decl &ct, const z3::expr &target) {
  return any_occurence(ct.name().str(), target);
}

z3::expr_vector generate_necessary_abstraction(
    z3::solver *pslv, z3::solver *pdual_slv,
    std::unordered_set<z3::expr> &ctrld,
    const std::unordered_set<z3::expr> &may_control) {
  z3::context *context = &pslv->ctx();
  auto cr = pslv->check();
  z3::expr_vector control_blocks(*context);
  unsigned int nr_push = 0;
  while (cr == z3::check_result::sat) {
    auto model = pslv->get_model();
    z3::expr_vector assumptions(*context);
    for (const auto &e : ctrld) {
      auto ev = model.eval(e);
      switch (ev.bool_value()) {
      case Z3_L_TRUE:
        assumptions.push_back(e);
        break;
      case Z3_L_FALSE:
        assumptions.push_back(!e);
      default:
        break;
      }
    }
    std::stringstream ss;
    for (unsigned i = 0; i != assumptions.size(); ++i) {
      ss << assumptions[i] << ';';
    }
    LOG4("assumptions: " << ss.str());
    auto dual_res = pdual_slv->check(assumptions);
    switch (dual_res) {
    case z3::check_result::unsat: {
      auto uc = pdual_slv->unsat_core();
      std::stringstream ss;
      for (unsigned i = 0; i != uc.size(); ++i) {
        ss << uc[i] << ';';
      }
      LOG4("core: " << ss.str());
      control_blocks.push_back(!z3::mk_and(uc));
      nr_push++;
      pslv->push();
      pslv->add(!z3::mk_and(uc));
      break;
    }
    case z3::check_result::sat: {
      LOG4("can't do with current abstraction, need to refine");
      bool changed = false;
      pdual_slv->push();
      for (unsigned i = 0; i != assumptions.size(); ++i) {
        pdual_slv->add(assumptions[i]);
      }
      z3::expr_vector old_assumptions(pdual_slv->ctx());
      for (unsigned i = 0; i != assumptions.size(); ++i) {
        old_assumptions.push_back(assumptions[i]);
      }
      assumptions.resize(0);
      for (auto &m : may_control) {
        if (ctrld.find(m) == ctrld.end()) {
          changed = true;
          auto ev = model.eval(m);
          switch (ev.bool_value()) {
          case Z3_L_TRUE:
            assumptions.push_back(m);
            break;
          case Z3_L_FALSE:
            assumptions.push_back(!m);
          default:
            break;
          }
        }
      }
      z3::expr_vector core(pdual_slv->ctx());
      if (!changed) {
        LOG3("can't control this behavior");
      } else {
        auto cr = pdual_slv->check(assumptions);
        if (cr == z3::check_result::sat) {
          core = assumptions;
          LOG3("can't control this behavior");
        } else {
          core = pdual_slv->unsat_core();
          for (unsigned i = 0, e = core.size(); i != e; ++i) {
            auto a = core[i];
            if (a.decl().decl_kind() == Z3_OP_NOT) {
              ctrld.emplace(a.arg(0));
            } else {
              ctrld.emplace(a);
            }
          }
          for (unsigned i = 0, e = old_assumptions.size(); i != e; ++i) {
            core.push_back(old_assumptions[i]);
          }
          control_blocks.push_back(!z3::mk_and(core));
        }
      }
      pdual_slv->pop();
      nr_push++;
      pslv->push();
      pslv->add(!z3::mk_and(core));
      break;
    }
    default:
      BUG("???");
    }
    cr = pslv->check();
  }
  if (nr_push)
    pslv->pop(nr_push);
  return control_blocks;
}

z3::expr_vector generate_necessary_abstraction_2(
    z3::expr &rho_a, z3::solver *pslv, z3::solver *pdual_slv,
    std::unordered_set<z3::expr> &ctrld,
    const std::unordered_set<z3::expr> &may_control) {
  z3::context *context = &pslv->ctx();
  z3::solver rho_solver(*context);
  rho_solver.add(rho_a);
  auto cr = pslv->check();
  z3::expr_vector control_blocks(*context);
  unsigned int nr_push = 0;
  while (cr == z3::check_result::sat) {
    auto model = pslv->get_model();
    auto rhoeval = model.eval(rho_a).bool_value();
    if (rhoeval == Z3_L_FALSE) {
      auto ct_sz = model.num_consts();
      z3::expr_vector kill_this(*context);
      for (unsigned i = 0; i != ct_sz; ++i) {
        auto cd = model.get_const_decl(i);
        auto ci = model.get_const_interp(cd);
        kill_this.push_back(cd() == ci);
      }
      BUG_CHECK(rho_solver.check(kill_this) == z3::check_result::unsat,
                "rho solver should be unsat in this model");
      nr_push++;
      pslv->push();
      pslv->add(!z3::mk_and(rho_solver.unsat_core()));
    } else {
      z3::expr_vector assumptions(*context);
      for (const auto &e : ctrld) {
        auto ev = model.eval(e);
        switch (ev.bool_value()) {
        case Z3_L_TRUE:
          assumptions.push_back(e);
          break;
        case Z3_L_FALSE:
          assumptions.push_back(!e);
        default:
          break;
        }
      }
      std::stringstream ss;
      for (unsigned i = 0; i != assumptions.size(); ++i) {
        ss << assumptions[i] << ';';
      }
      LOG4("assumptions: " << ss.str());
      auto dual_res = pdual_slv->check(assumptions);
      switch (dual_res) {
      case z3::check_result::unsat: {
        auto uc = pdual_slv->unsat_core();
        std::stringstream ss;
        for (unsigned i = 0; i != uc.size(); ++i) {
          ss << uc[i] << ';';
        }
        LOG4("core: " << ss.str());
        control_blocks.push_back(!z3::mk_and(uc));
        nr_push++;
        pslv->push();
        pslv->add(!z3::mk_and(uc));
        break;
      }
      case z3::check_result::sat: {
        LOG4("can't do with current abstraction, need to refine");
        bool changed = false;
        pdual_slv->push();
        for (unsigned i = 0; i != assumptions.size(); ++i) {
          pdual_slv->add(assumptions[i]);
        }
        z3::expr_vector old_assumptions(pdual_slv->ctx());
        for (unsigned i = 0; i != assumptions.size(); ++i) {
          old_assumptions.push_back(assumptions[i]);
        }
        assumptions.resize(0);
        for (auto &m : may_control) {
          if (ctrld.find(m) == ctrld.end()) {
            changed = true;
            auto ev = model.eval(m);
            switch (ev.bool_value()) {
            case Z3_L_TRUE:
              assumptions.push_back(m);
              break;
            case Z3_L_FALSE:
              assumptions.push_back(!m);
            default:
              break;
            }
          }
        }
        z3::expr_vector core(pdual_slv->ctx());
        if (!changed) {
          LOG3("can't control this behavior");
        } else {
          auto cr = pdual_slv->check(assumptions);
          if (cr == z3::check_result::sat) {
            core = assumptions;
            LOG3("can't control this behavior");
          } else {
            core = pdual_slv->unsat_core();
            for (unsigned i = 0, e = core.size(); i != e; ++i) {
              auto a = core[i];
              if (a.decl().decl_kind() == Z3_OP_NOT) {
                ctrld.emplace(a.arg(0));
              } else {
                ctrld.emplace(a);
              }
            }
            for (unsigned i = 0, e = old_assumptions.size(); i != e; ++i) {
              core.push_back(old_assumptions[i]);
            }
            control_blocks.push_back(!z3::mk_and(core));
          }
        }
        pdual_slv->pop();
        nr_push++;
        pslv->push();
        pslv->add(!z3::mk_and(core));
      } break;
      default:
        BUG("???");
      }
    }
    cr = pslv->check();
  }
  if (nr_push)
    pslv->pop(nr_push);
  return control_blocks;
}

z3::expr_vector
generate_necessary_abstraction(z3::solver *pslv, z3::solver *pdual_slv,
                               std::unordered_set<z3::expr> &ctrld) {
  std::unordered_set<z3::expr> may_control;
  return generate_necessary_abstraction(pslv, pdual_slv, ctrld, may_control);
}

z3::expr merge_or(const z3::expr &e1, const z3::expr &e2) {
  if (e1.is_app() && e1.decl().decl_kind() == Z3_OP_AND && e2.is_app() &&
      e2.decl().decl_kind() == Z3_OP_AND) {
    auto nargs1 = e1.num_args();
    auto nargs2 = e2.num_args();
    unsigned int idx = 0;
    z3::expr_vector evec(e1.ctx());
    while (idx < nargs1 && idx < nargs2) {
      auto arg1 = e1.arg(idx);
      auto arg2 = e2.arg(idx);
      if (!z3::eq(arg1, arg2)) {
        break;
      }
      evec.push_back(arg1);
      ++idx;
    }
    z3::expr conj1 = e1.ctx().bool_val(true);
    for (unsigned i = idx; i < nargs1; ++i)
      conj1 = conj1 && e1.arg(i);
    z3::expr conj2 = e2.ctx().bool_val(true);
    for (unsigned i = idx; i < nargs2; ++i)
      conj2 = conj2 && e2.arg(i);
    evec.push_back(conj1 || conj2);
    return z3::mk_and(evec);
  }
  return e1 || e2;
}

template <typename T, typename Fun> void toFixPoint(T &obj, Fun f) {
  bool change = true;
  while (change) {
    change = f(obj);
  }
};

void packet_solver(z3::expr_vector &assertions, packet_theory &pt) {
  z3::solver slv(assertions.ctx());
  auto dumpAssertions = [](std::ostream &os, const z3::expr_vector &assertions,
                           std::string n) {
    os << n << ":===============\n";
    for (unsigned i = 0, nr = assertions.size(); i != nr; ++i) {
      os << assertions[i] << '\n';
    }
    os << "===============";
  };
  auto assertionString = [&dumpAssertions](const z3::expr_vector &assertions,
                                           std::string n) {
    std::stringstream ss;
    dumpAssertions(ss, assertions, n);
    return ss.str();
  };

  auto replacefun = [&](z3::expr_vector &src, z3::expr_vector &dst,
                        z3::expr_vector &cp) -> bool {
    bool change = false;
    for (unsigned i = 0, nr = assertions.size(); i != nr; ++i) {
      auto e = assertions[i];
      auto newe = e.substitute(src, dst).simplify();
      if (!z3::eq(e, newe)) {
        change = true;
        LOG4("replace: " << e << " -> " << newe);
      }
      cp.push_back(newe);
    }
    return change;
  };

  auto replaceEqualities = [&](z3::expr_vector &assertions) {
    std::unordered_map<z3::expr, z3::expr> replace;
    z3::expr_vector cp(assertions.ctx());
    z3::expr_vector src(assertions.ctx());
    z3::expr_vector dst(assertions.ctx());
    auto nr = assertions.size();
    for (unsigned i = 0; i != nr; ++i) {
      auto e = assertions[i];
      if (e.is_eq()) {
        auto e1 = e.arg(0);
        auto e2 = e.arg(1);
        if (z3::eq(e1.get_sort(), pt.packetSort)) {
          if (pt.isConst(e1) && pt.isConst(e2)) {
            auto replace1 = replace.count(e1) != 0;
            auto replace2 = replace.count(e2) != 0;
            z3::expr what(assertions.ctx());
            z3::expr with(assertions.ctx());
            if (!replace1 || !replace2) {
              if (!replace1) {
                what = e1;
                with = e2;
              } else if (!replace2) {
                what = e2;
                with = e1;
              }
              auto I = replace.find(with);
              src.push_back(what);
              if (I != replace.end()) {
                replace.emplace(what, I->second);
                dst.push_back(I->second);
              } else {
                replace.emplace(what, with);
                dst.push_back(with);
              }
            }
          }
        }
      }
    }
    auto c = replacefun(src, dst, cp);
    assertions = cp;
    return c;
  };
  toFixPoint(assertions, replaceEqualities);
  LOG4(assertionString(assertions, "fold equalities"));
  // push equalities inwards
  auto pushEqualities = [&](z3::expr_vector &assertions) {
    bool change = false;
    auto nr = assertions.size();
    z3::expr_vector cp(assertions.ctx());
    z3::expr_vector src(assertions.ctx());
    z3::expr_vector dst(assertions.ctx());
    std::unordered_map<z3::expr, z3::expr> replace;
    for (unsigned i = 0; i != nr; ++i) {
      auto e = assertions[i];
      if (e.is_eq()) {
        auto e1 = e.arg(0);
        auto e2 = e.arg(1);
        if (pt.isPacket(e1)) {
          auto e1const = pt.isConst(e1);
          auto e2const = pt.isConst(e2);
          z3::expr rep(e1.ctx());
          z3::expr with(e1.ctx());
          if (e1const != e2const) {
            if (e1const) {
              rep = e1;
              with = e2;
            } else {
              rep = e2;
              with = e1;
            }
            replace.emplace(rep, with);
          } else if (e1const) {
            BUG("expecting (= p constructor), got %1%", e);
          }
        }
      }
    }
    for (auto &rep : replace) {
      src.push_back(rep.first);
      dst.push_back(rep.second);
    }
    for (unsigned i = 0; i != nr; ++i) {
      auto e = assertions[i];
      auto newe = e.substitute(src, dst).simplify();
      if (!z3::eq(newe, e)) {
        change = true;
      }
      cp.push_back(newe);
    }
    assertions = cp;
    return change;
  };
  toFixPoint(assertions, pushEqualities);
  LOG4(assertionString(assertions, "push equalities"));
  auto eliminatePrependPrepend = [&](z3::expr_vector &assertions) {
    z3::expr_vector src(assertions.ctx());
    z3::expr_vector dst(assertions.ctx());
    auto nr = assertions.size();
    for (unsigned i = 0; i != nr; ++i) {
      auto e = assertions[i];
      recurse(e,
              [&](const z3::expr &ex) {
                if (pt.isPacket(ex) && pt.isPrepend(ex)) {
                  auto e1 = ex.arg(1);
                  if (pt.isPrepend(e1)) {
                    auto p = ex.arg(0);
                    auto c = e1.arg(0);
                    auto d = e1.arg(1);
                    src.push_back(ex);
                    dst.push_back(pt.prepend(pt.prepend(p, c), d));
                  }
                }
                return true;
              },
              [](const z3::expr &) {});
    }
    z3::expr_vector cp(assertions.ctx());
    auto c = replacefun(src, dst, cp);
    assertions = cp;
    return c;
  };
  toFixPoint(assertions, eliminatePrependPrepend);
  LOG4(assertionString(assertions, "trans"));
  // post re-write checks:
  auto emitHandling = [&](z3::expr_vector &assertions) {
    bool change = false;
    std::unordered_map<z3::expr, z3::expr> replace;
    for (unsigned i = 0, e = assertions.size(); i != e; ++i) {
      if (assertions[i].is_eq()) {
        auto e1 = assertions[i].arg(0);
        auto e2 = assertions[i].arg(1);
        if (pt.isPacket(e1)) {
          if (pt.isPrepend(e1) && pt.isPrepend(e2)) {
            auto e12 = e1.arg(1);
            auto e22 = e2.arg(1);
            auto ex12 = pt.isEmit(e12.decl());
            auto ex22 = pt.isEmit(e22.decl());
            if (ex12 && ex22) {
              if (*ex12 == *ex22) {
                replace.emplace(assertions[i], e12.arg(0) == e22.arg(0) &&
                                                   e1.arg(0) == e2.arg(0));
                assertions.push_back(e12.arg(0) == e22.arg(0));
                assertions.push_back(e1.arg(0) == e2.arg(0));
              } else {
                unsigned N = 0;
                unsigned M = 0;
                z3::expr x(assertions.ctx());
                z3::expr y(assertions.ctx());
                z3::expr p1(assertions.ctx());
                z3::expr p2(assertions.ctx());
                if (*ex12 < *ex22) {
                  N = *ex22;
                  M = *ex12;
                  p1 = e2.arg(0);
                  p2 = e1.arg(0);
                  x = e22.arg(0);
                  y = e12.arg(0);
                } else {
                  N = *ex12;
                  M = *ex22;
                  p1 = e1.arg(0);
                  p2 = e2.arg(0);
                  x = e12.arg(0);
                  y = e22.arg(0);
                }
                auto p2_ = z3::to_expr(
                    assertions.ctx(),
                    Z3_mk_fresh_const(assertions.ctx(), "pack", pt.packetSort));
                auto x2_ = z3::to_expr(
                    assertions.ctx(),
                    Z3_mk_fresh_const(assertions.ctx(), "x",
                                      assertions.ctx().bv_sort(N - M)));
                assertions.push_back(y == x.extract(N - 1, N - M));
                assertions.push_back(p2 ==
                                     pt.prepend(p2_, pt.emit(N - M)(x2_)));
                assertions.push_back(x2_ == x.extract(N - M - 1, 0));
                assertions.push_back(p2_ == p1);
              }
              change = true;
              Z3_ast_vector_set(assertions.ctx(), assertions, i,
                                assertions.ctx().bool_val(true));
            }
          }
        }
      }
    }
    return change;
  };
  toFixPoint(assertions, emitHandling);
  LOG4(assertionString(assertions, "emitHandling"));
}

z3::expr cegis::generate_forall(const z3::expr &src,
                                const std::map<std::string, unsigned> &occs) {
  auto &ctx = src.ctx();
  if (is_unconstrained(src, occs)) {
    std::cerr << "yup, unconstrained statement... " << src << '\n';
    return ctx.bool_val(true);
  } else {
    std::cerr << "not unconstrained statement... " << src << '\n';
    return ctx.bool_val(false);
  }
  z3::expr_vector rep(ctx), with(ctx);
  auto typed = typed_occurences(src);
  for (auto &occ : occs) {
    if (occ.second == 1) {
      with.push_back(ctx.constant((occ.first + "__").c_str(),
                                  typed.find(occ.first)->second));
      rep.push_back(
          ctx.constant(occ.first.c_str(), typed.find(occ.first)->second));
    }
  }
  auto ebody = z3::expr(src).substitute(rep, with);
  auto existvars = with;
  rep = z3::expr_vector(ctx);
  with = z3::expr_vector(ctx);
  for (auto &occ : occs) {
    if (occ.second > 1) {
      with.push_back(ctx.constant((occ.first + "__").c_str(),
                                  typed.find(occ.first)->second));
      rep.push_back(
          ctx.constant(occ.first.c_str(), typed.find(occ.first)->second));
    }
  }
  auto body = ebody.substitute(rep, with);
  with.push_back(ctx.constant("value____", src.get_sort()));
  return z3::forall(with, z3::exists(existvars, with.back() == body));
}

z3::expr cegis::simplify(z3::expr sigma) {
  z3::context &ctx = sigma.ctx();
  auto m = occurences(sigma);
  std::map<std::string, unsigned> level_1_unconstrained;
  std::copy_if(
      m.begin(), m.end(),
      std::inserter(level_1_unconstrained, level_1_unconstrained.end()),
      [&](const std::pair<std::string, unsigned> &pr) {
        // level of quantification == 2 && number of occurences == 1 =>
        // need to just check if I can simply slash all formulas
        return pr.first.find("pre_call") == std::string::npos && pr.second == 1;
      });
  z3::expr_vector rep(ctx), with(ctx);
  auto tmp_nr = 0;
  for (const auto &p : level_1_unconstrained) {
    auto exprs = atoms(sigma, p.first);
    if (!exprs.empty()) {
      for (const auto &e : exprs) {
        auto eoccs = occurences(e);
        try {
          std::map<std::string, unsigned> all_occs;
          for (const auto &p : m) {
            if (p.first.find("pre_call") != std::string::npos &&
                eoccs.count(p.first)) {
              all_occs.emplace(p.first, 2);
            } else {
              if (eoccs.count(p.first)) {
                all_occs.emplace(p);
              }
            }
          }
          auto fall = is_unconstrained(e, all_occs);
          if (fall) {
            rep.push_back(e);
            std::string tmp = "tmp";
            tmp += std::to_string(tmp_nr++);
            with.push_back(ctx.constant(tmp.c_str(), e.get_sort()));
          }
        } catch (z3::exception &e) {
          std::cerr << e << '\n';
          throw e;
        }
      }
    }
  }
  return sigma.substitute(rep, with).simplify();
}

namespace analysis {
void get_extra_controls(z3::solver &context,
                        const std::unordered_set<z3::expr> &hints,
                        const std::string &check_against,
                        z3::expr_vector &evec) {
  LOG4("starting inference loop for " << check_against);
  std::unordered_set<z3::expr> all_living_things, known;
  auto nr_assertions = context.assertions().size();
  auto assertions = context.assertions();
  for (unsigned i = 0; i != nr_assertions; ++i) {
    auto flat_context = assertions[i];
    get_atoms(flat_context, all_living_things,
              [&](const std::string &nm) { return check_against == nm; });
  }
  for (auto &hint : hints) {
    get_atoms(hint, all_living_things,
              [&](const std::string &nm) { return check_against == nm; });
  }
  for (auto &e : all_living_things) {
    context.push();
    context.add(!e);
    if (context.check() == z3::check_result::unsat) {
      // nothing
      if (e.decl().decl_kind() != Z3_OP_EQ) {
        known.emplace(e.ctx().bool_val(true));
      } else {
        auto e0 = e.arg(0);
        auto e1 = e.arg(1);
        if (e0.decl().decl_kind() == Z3_OP_UNINTERPRETED &&
            check_against == e0.decl().name().str()) {
          known.emplace(e1);
        } else if (e1.decl().decl_kind() == Z3_OP_UNINTERPRETED &&
                   check_against == e1.decl().name().str()) {
          known.emplace(e0);
        }
      }
    } else {
      context.pop();
      context.push();
      context.add(e);
      if (context.check() == z3::check_result::unsat) {
        if (e.decl().decl_kind() == Z3_OP_EQ) {
          auto e0 = e.arg(0);
          auto e1 = e.arg(1);
          if (e0.is_bool()) {
            known.emplace(!e1);
          }
        } else {
          known.emplace(e.ctx().bool_val(false));
        }
      }
    }
    context.pop();
  }
  for (const auto &exp : known) {
    auto e = controls_expr(exp);
    LOG4("inference computed " << e);
    evec.push_back(e);
  }
}

bool get_extra_control_bt(
    z3::solver &context, z3::solver &ctx2,
    const std::set<std::string> &may_control,
    const std::unordered_set<z3::expr> &hints, std::set<std::string> &processed,
    std::map<std::string, z3::expr_vector> &known_inferences,
    z3::expr_vector &do_add) {
  z3::context &ctx = context.ctx();
  bool is_changed = true;
  unsigned int nr_pushes = 0;
  while (ctx2.check() == z3::check_result::sat) {
    is_changed = false;
    auto model = ctx2.get_model();
    auto model_size = model.num_consts();
    std::unordered_set<std::string> uncontrolled;
    z3::expr_vector block(ctx);
    z3::expr_vector exprs(ctx);
    for (unsigned i = 0; i != model_size; ++i) {
      auto ct = model.get_const_decl(i);
      if (ct.name().str().find("controls_") != std::string::npos &&
          ct.range().is_bool()) {
        auto in = model.get_const_interp(ct);
        switch (in.bool_value()) {
        case Z3_L_FALSE:
          block.push_back(!ct());
          if (processed.find(ct.name().str().substr(9)) == processed.end()) {
            uncontrolled.emplace(ct.name().str().substr(9));
            auto I = known_inferences.find(ct.name().str().substr(9));
            if (I != known_inferences.end()) {
              for (unsigned idx = 0, e = I->second.size(); idx != e; ++idx) {
                exprs.push_back(I->second[idx]);
              }
            } else {
              z3::expr_vector new_vec(ctx);
              get_extra_controls(context, hints, ct.name().str().substr(9),
                                 new_vec);
              known_inferences.emplace(ct.name().str().substr(9), new_vec)
                  .first;
              for (unsigned idx = 0, e = new_vec.size(); idx != e; ++idx) {
                exprs.push_back(new_vec[idx]);
              }
            }
          }
          break;
        case Z3_L_TRUE:
          block.push_back(ct());
        case Z3_L_UNDEF:
          break;
        }
      }
    }
    unsigned sz = exprs.size();
    // add consequences
    for (unsigned i = 0; i != sz; ++i) {
      auto e = exprs[i];
      ctx2.push();
      ctx2.add(e);
      auto cr = ctx2.check();
      ctx2.pop();
      if (cr == z3::check_result::sat) {
        is_changed = true;
        ctx2.push();
        ++nr_pushes;
        ctx2.add(!e);
      }
    }
    if (!is_changed) {
      z3::expr_vector assumptions(ctx);
      for (const auto &mc : may_control) {
        assumptions.push_back(control_var(ctx, mc));
      }
      auto cr = ctx2.check(assumptions);
      if (cr != z3::check_result::unsat) {
        LOG4("oh, snap...");
        return false;
      } else {
        for (unsigned i = 0; i != model_size; ++i) {
          auto ct = model.get_const_decl(i);
          if (ct.name().str().find("controls_") != std::string::npos &&
              ct.range().is_bool() &&
              may_control.count(ct.name().str().substr(9))) {
            auto v = model.get_const_interp(ct).bool_value();
            if (v == Z3_L_FALSE) {
              do_add.push_back(ct());
            }
          }
        }
      }
    } else {
      auto old_size = do_add.size();
      processed.insert(uncontrolled.begin(), uncontrolled.end());
      if (!get_extra_control_bt(context, ctx2, may_control, hints, processed,
                                known_inferences, do_add))
        return false;
      for (auto n : uncontrolled) {
        processed.erase(n);
      }
      if (nr_pushes) {
        ctx2.pop(nr_pushes);
        nr_pushes = 0;
      }
      if (do_add.size() != old_size) {
        for (auto i = old_size; i != do_add.size(); ++i)
          ctx2.add(do_add[i]);
      }
    }
    ctx2.add(!z3::mk_and(block));
    block.resize(0);
  }
  return true;
}

z3::expr controls_expr(const z3::expr &need_to) {
  std::set<std::string> must_control;
  recurse(need_to,
          [&](const z3::expr &e) {
            if (e.is_app() && e.num_args() == 0 &&
                e.decl().decl_kind() == Z3_OP_UNINTERPRETED) {
              must_control.emplace(e.decl().name().str());
              return false;
            } else {
              return true;
            }
          },
          [](const z3::expr &) {});
  z3::expr_vector evec(need_to.ctx());
  for (const auto &s : must_control) {
    evec.push_back(control_var(need_to.ctx(), s));
  }
  return z3::mk_and(evec);
}

z3::expr control_var(z3::context &ctx, const std::string &s) {
  std::stringstream ss;
  ss << "controls_" << s;
  return ctx.bool_const(ss.str().c_str());
}

bool get_extra_control(z3::solver &context, z3::expr &must_control,
                       const std::set<std::string> &controls,
                       const std::set<std::string> &may_control,
                       const std::unordered_set<z3::expr> &hints,
                       z3::expr_vector &do_add) {
  z3::solver ctx2(context.ctx());
  for (const auto &ctrl : controls) {
    ctx2.add(control_var(ctx2.ctx(), ctrl));
  }
  for (unsigned i = 0, e = do_add.size(); i != e; ++i) {
    ctx2.add(do_add[i]);
  }
  auto old_sz = do_add.size();
  LOG4("must control " << must_control);
  ctx2.add(!controls_expr(must_control));
  std::set<std::string> visited;
  std::map<std::string, z3::expr_vector> known_inferences;
  auto rest = get_extra_control_bt(context, ctx2, may_control, hints, visited,
                                   known_inferences, do_add);
  LOG4("result " << must_control);
  for (unsigned i = old_sz; i != do_add.size(); ++i) {
    LOG4("means " << do_add[i]);
  }
  return rest;
}

std::unordered_set<z3::expr> get_atoms(const z3::expr &flat_context) {
  std::unordered_set<z3::expr> atoms;
  get_atoms(flat_context, atoms, [](const std::string &) { return true; });
  return atoms;
}
}

unsigned packet_solver_::termid(const z3::expr &e) {
  auto EMI = index.emplace(e, index.size());
  if (EMI.second)
    revindex.emplace_back(e);
  return EMI.first->second;
}

void packet_solver_::add(z3::expr e) {
  // auto nnfe = to_nnf(e);
  // auto atoms = analysis::get_atoms(nnfe);
  // for (auto &at : atoms) {
  //   bool isth = false;
  //   recurse(at, [&](const z3::expr &ex) {
  //     if (pt.isPacket(ex)) {
  //       auto before = revindex.size();
  //       auto nr = termid(ex);
  //       if (nr == before) {
  //         // new term found
  //         if (!pt.isConst(ex))
  //           free_terms.emplace(nr);
  //       }
  //       isth = true;
  //     }
  //     return true;
  //   });
  //   if (isth) {
  //     theory_atoms.emplace(at);
  //     if (at.is_eq()) {
  //       auto e0 = at.arg(0);
  //       auto e1 = at.arg(1);
  //       if (!pt.isConst(e0)) {
  //         if (pt.isConst(e1)) {
  //           std::swap(e0, e1);
  //         } else {
  //           BUG("can't handle arbitrary equations, only between var to term "
  //               "%1%",
  //               at);
  //         }
  //       }
  //       free_terms.erase(termid(e1));
  //     }
  //   }
  // }
  // for (auto tid : free_terms) {
  //   // make up new variables for terms which have no variables
  //   // implicitly attached. i.e. modelEmit_XXX
  //   auto oldterm = revindex[tid];
  //   if (pt.isZero(oldterm)) continue;
  //   BUG_CHECK(pt.isEmit(oldterm.decl()), "new terms must be emits, but %1% found", oldterm);
  //   auto tdumb = z3::to_expr(ctx(), Z3_mk_fresh_const(ctx(), "pack", pt.packetSort));
  //   dumb_vars.emplace(tid, tdumb);
  // }
  // unsigned int crt_polarity = 0;
  // recurse(nnfe, [&crt_polarity](const z3::expr &e) {
  //   if (e.is_not()) crt_polarity++;
  //   return true;
  // }, [this, &crt_polarity](const z3::expr &e) {
  //   if (e.is_not()) {
  //     crt_polarity--;
  //     return;
  //   }
  //   if (theory_atoms.count(e)) {
  //     auto EMI = theory_atoms_polarity.emplace(e, 1 << (crt_polarity % 2));
  //     if (!EMI.second) {
  //       EMI.first->second |= (1 << (crt_polarity % 2));
  //     }
  //   }
  // });
  // for (const auto &pol : theory_atoms_polarity) {
  //   if (pol.second != 1) {
  //     BUG("bipolar atom %1% %2%", pol.first, pol.second);
  //   }
  // }
  //  s.add(e.substitute(src, dst));
  s.add(e);
}

analysis::node_t node_from_exp(const z3::expr &e) {
  analysis::node_t n;
  return n.clone(e.hash());
}

z3::check_result packet_solver_::check() {
  START(solve);
  auto cr = s.check();
  END(solve);
  auto d = DURATION(solve);

  std::cerr << "check result:" << cr << " #assertions:" << s.assertions().size()
            << " time:" << d << "ms\n";
  return cr;
}

z3::check_result packet_solver_::check(z3::expr_vector &evec) {
  START(solve);
  auto cr = s.check(evec);
  END(solve);
  auto d = DURATION(solve);
  std::cerr << "check assumptions result:" << cr
            << " #assertions:" << s.assertions().size()
            << " #assumptions:" << evec.size() << " time:" << d << "ms\n";
  return cr;
}

z3::expr_vector packet_solver_::unsat_core() const {
  START(unsatCore);
  auto r = s.unsat_core();
  END(unsatCore);
  auto d = DURATION(unsatCore);
  std::cerr << "unsat core result:" << r.size() << " time:" << d << " ms\n";
  return r;
}

z3::model packet_solver_::get_model() const {
  START(getModel);
  auto m = s.get_model();
  END(getModel);
  auto d = DURATION(getModel);
  std::cerr << "get model time:" << d << "ms\n";
  return m;
}

void packet_solver_::pop(unsigned int n) { s.pop(n); }

void packet_solver_::push() { s.push(); }

std::ostream &operator<<(std::ostream &os, const packet_solver_ &ps) {
  return os << ps.s;
}

z3::expr remove_packets(const z3::expr &expr, packet_theory &pt) {
  if (!expr.is_quantifier()) {
    return expr;
  }
  auto &ctx = expr.ctx();
  std::vector<std::pair<std::string, z3::sort>> sorted;

  std::vector<unsigned> occurences;
  auto numbounds = Z3_get_quantifier_num_bound(expr.ctx(), expr);
  Z3_symbol syms[numbounds];
  Z3_sort sorts[numbounds];
  for (unsigned i = 0; i != numbounds; ++i) {
    auto sm = Z3_get_quantifier_bound_name(ctx, expr, i);
    auto str = Z3_get_symbol_string(ctx, sm);
    auto srt = z3::to_sort(ctx, Z3_get_quantifier_bound_sort(ctx, expr, i));
    sorted.emplace_back(str, srt);
    syms[i] = sm;
    sorts[i] = srt;
  }
  auto body = expr.body();
  z3::expr_vector src(ctx);
  z3::expr_vector dst(ctx);
  recurse(body, [&](const z3::expr &e) {
    if (e.is_and() || e.is_or() || e.is_implies() || e.is_ite() || e.is_not())
      return true;
    if (e.is_eq()) {
      if (pt.isPacket(e.arg(0))) {
        src.push_back(e);
        dst.push_back(ctx.bool_val(true));
      }
      return false;
    }
    return true;
  });
  body = body.substitute(src, dst);
  return z3::to_expr(ctx,
                     Z3_mk_quantifier(ctx, Z3_is_quantifier_forall(ctx, expr),
                                      Z3_get_quantifier_weight(ctx, expr), 0,
                                      nullptr, numbounds, sorts, syms, body));
}

z3::expr chunkify(const z3::expr &expr) {
  if (!expr.is_quantifier()) {
    return expr;
  }
  auto &ctx = expr.ctx();
  std::vector<std::pair<std::string, z3::sort>> sorted;
  std::vector<unsigned> occurences;
  auto numbounds = Z3_get_quantifier_num_bound(expr.ctx(), expr);
  for (unsigned i = 0; i != numbounds; ++i) {
    auto sm = Z3_get_quantifier_bound_name(ctx, expr, i);
    auto str = Z3_get_symbol_string(ctx, sm);
    auto srt = z3::to_sort(ctx, Z3_get_quantifier_bound_sort(ctx, expr, i));
    sorted.emplace_back(str, srt);
  }
  occurences.resize(numbounds, 0);
  auto body = expr.body();
  recurse(body, [](const z3::expr &e) {
    if (e.is_quantifier())
      BUG("no nested quantifiers allowed %1%", e);
    return true;
  });
  recurse(body, [&](const z3::expr &e) {
    if (e.is_var()) {
      auto idx = Z3_get_index_value(e.ctx(), e);
      occurences[numbounds - idx - 1]++;
    }
    return true;
  });
  auto body_ = body;
  std::vector<unsigned> remove;
  std::vector<z3::expr> add;
  for (unsigned j = 0; j != numbounds; ++j) {
    auto occs = occurences[j];
    if (occs > 1 && sorted[j].second.is_bv()) {
      std::unordered_set<z3::expr> terms;
      LOG4(sorted[j].first << " occurs #" << occs);
      recurse(body, [&](const z3::expr &e) {
        if (e.is_app()) {
          for (unsigned i = 0; i != e.num_args(); ++i) {
            if (e.arg(i).is_var()) {
              auto idx = numbounds - Z3_get_index_value(e.ctx(), e.arg(i)) - 1;
              if (idx == j) {
                LOG4("in term:" << e);
                terms.emplace(e);
              }
            }
          }
        }
        return true;
      });
      std::set<unsigned> intervals({0, sorted[j].second.bv_size()});
      std::map<std::pair<unsigned, unsigned>, z3::expr> extracts;
      for (auto &term : terms) {
        if (term.decl().decl_kind() == Z3_OP_EXTRACT) {
          auto lo = Z3_get_decl_int_parameter(ctx, term.decl(), 1);
          auto hi = Z3_get_decl_int_parameter(ctx, term.decl(), 0);
          intervals.emplace(lo);
          intervals.emplace(hi + 1);
          extracts.emplace(std::make_pair(lo, hi + 1), term);
        }
      }
      if (intervals.size() <= 2)
        continue;
      auto I = intervals.begin();
      auto crt = *I;
      ++I;
      std::map<unsigned, std::pair<unsigned, z3::expr>> cover;
      for (; I != intervals.end(); ++I) {
        auto Zi = z3::to_expr(
            ctx, Z3_mk_fresh_const(ctx, "x", ctx.bv_sort(*I - crt)));
        cover.emplace(crt, std::make_pair(*I, Zi));
        crt = *I;
      }
      if (cover.size() == 1)
        continue;
      z3::expr_vector src(ctx);
      z3::expr_vector dst(ctx);
      for (auto &ex : extracts) {
        auto c = cover.find(ex.first.first)->second;
        z3::expr_vector evec(ctx);
        while (c.first <= ex.first.second) {
          evec.push_back(c.second);
          c = cover.find(c.first)->second;
        }
        z3::expr pleaserep(ctx);
        if (evec.size() == 1)
          pleaserep = evec.back();
        else
          pleaserep = z3::concat(evec);
        src.push_back(ex.second);
        dst.push_back(pleaserep);
      }
      body_ = body_.substitute(src, dst);
      z3::expr_vector cov(ctx);
      for (auto &x : cover) {
        cov.push_back(x.second.second);
        add.push_back(x.second.second);
      }
      z3::expr cove = z3::concat(cov);
      recurse(body, [&](const z3::expr &e) {
        if (e.is_var()) {
          auto idx = numbounds - Z3_get_index_value(e.ctx(), e) - 1;
          if (idx == j) {
            src.push_back(e);
            dst.push_back(cove);
          }
        }
        return true;
      });
      body_ = body_.substitute(src, dst);
      remove.push_back(j);
    }
  }

  std::vector<z3::expr> freshes;
  z3::expr_vector src(ctx);
  z3::expr_vector dst(ctx);

  for (auto &p : sorted) {
    freshes.push_back(
        z3::to_expr(ctx, Z3_mk_fresh_const(ctx, p.first.c_str(), p.second)));
  }
  recurse(body, [&](const z3::expr &ex) {
    if (ex.is_var()) {
      auto idx = numbounds - Z3_get_index_value(ex.ctx(), ex) - 1;
      src.push_back(ex);
      dst.push_back(freshes[idx]);
    }
    return true;
  });
  body_ = body_.substitute(src, dst);
  z3::expr_vector newbounds(ctx);
  for (unsigned i = 0; i != numbounds; ++i) {
    if (!std::binary_search(remove.begin(), remove.end(), i)) {
      newbounds.push_back(freshes[i]);
    }
  }
  for (const auto &ex : add) {
    newbounds.push_back(ex);
  }
  return z3::forall(newbounds, body_);
}

packet_solver_::packet_solver_(z3::solver &s, packet_theory &pt)
    : s(s), pt(pt) {
  s.set("macro_finder", true);
  termid(pt.zero());
}

void packet_solver_::makeAxioms() {
  // saturate extracts
  auto made = pt.make_axioms();
  for (unsigned i = 0, e = made.size(); i != e; ++i) {
    s.add(made[i]);
  }
  //  bool saturated = false;
  //  while (!saturated) {
  //    auto oldsize = pt.packetExtracts.size();
  //    std::set<unsigned> alsoadd;
  //    for (auto &pex : pt.packetExtracts) {
  //      for (auto &pem : pt.packetEmits) {
  //        auto N = pex.first;
  //        auto M = pem.first;
  //        while (N > M) {
  //          (void)alsoadd.emplace(N - M);
  //          N -= M;
  //        }
  //      }
  //    }
  //    for (auto als : alsoadd) {
  //      pt.extract(als);
  //    }
  //    saturated = oldsize == pt.packetExtracts.size();
  //  }
  //  LOG4("#packetExtracts:" << pt.packetExtracts.size());
  //  {
  //    auto observation = [](const z3::expr &e) { return e; };
  //    auto pack = ctx().constant("p", pt.packetSort);
  //    auto c = ctx().constant("c", pt.packetSort);
  //    auto d = ctx().constant("d", pt.packetSort);
  //    auto ast = new Z3_ast[1];
  //    ast[0] = observation(pt.prepend(pack, pt.zero()));
  //    auto ppat = new Z3_pattern[1];
  //    ppat[0] = Z3_mk_pattern(ctx(), 1, ast);
  //    Z3_inc_ref(ctx(), Z3_pattern_to_ast(ctx(), ppat[0]));
  //    BUG_CHECK(ctx().check_error() == Z3_OK, "not ok ");
  //
  //    auto ppack = new Z3_app[1];
  //    ppack[0] = pack;
  //    //    s.add(z3::to_expr(
  //    //        ctx(), Z3_mk_forall_const(ctx(), 0, 1, ppack, 1, ppat,
  //    //                                  observation(pt.prepend(pack,
  //    pt.zero()))
  //    //                                  ==
  //    //                                      observation(pack))));
  //    LOG4("made forall");
  //    ast[0] = observation(pt.prepend(pt.zero(), pack));
  //    ppat[0] = Z3_mk_pattern(ctx(), 1, ast);
  //    Z3_inc_ref(ctx(), Z3_pattern_to_ast(ctx(), ppat[0]));
  //    BUG_CHECK(ctx().check_error() == Z3_OK, "not ok ");
  //    //    s.add(z3::to_expr(
  //    //        ctx(), Z3_mk_forall_const(ctx(), 0, 1, ppack, 1, ppat,
  //    //                                  observation(pt.prepend(pt.zero(),
  //    pack))
  //    //                                  ==
  //    //                                      observation(pack))));
  //    LOG4("made forall 2");
  //    ast[0] = observation(pt.prepend(pack, pt.prepend(c, d)));
  //    ppat[0] = Z3_mk_pattern(ctx(), 1, ast);
  //    Z3_inc_ref(ctx(), Z3_pattern_to_ast(ctx(), ppat[0]));
  //
  //    auto apps = new Z3_app[3];
  //    apps[0] = pack;
  //    apps[1] = c;
  //    apps[2] = d;
  //    //    s.add(z3::to_expr(
  //    //        ctx(), Z3_mk_forall_const(
  //    //                   ctx(), 0, 3, apps, 1, ppat,
  //    //                   observation(pt.prepend(pack, pt.prepend(c, d))) ==
  //    //                       observation(pt.prepend(pt.prepend(pack, c),
  //    d)))));
  //
  //    for (auto &pem : pt.packetEmits) {
  //      auto X = ctx().bv_const("x", pem.first);
  //      s.add(z3::forall(X, pt.length(pt.emit(pem.first)(X)) ==
  //                              ctx().num_val(pem.first, ctx().int_sort())));
  //    }
  //    s.add(z3::forall(pack, pt.length(pack) >= 0));
  //    s.add(z3::forall(
  //        pack, z3::implies(pt.length(pack) == ctx().num_val(0,
  //        ctx().int_sort()),
  //                          pack == pt.zero())));
  //    s.add(pt.length(pt.zero()) == ctx().num_val(0, ctx().int_sort()));
  //
  //    //    for (auto &pem : pt.packetEmits) {
  //    //      auto X = ctx().bv_const("x", pem.first);
  //    //      s.add(z3::forall(X, pt.emit(pem.first)(X) != pt.zero()));
  //    //    }
  //    //    {
  //    //      auto c = ctx().constant("c", pt.packetSort);
  //    //      auto d = ctx().constant("d", pt.packetSort);
  //    //      z3::expr_vector expr_vector(ctx());
  //    //      expr_vector.push_back(c);
  //    //      expr_vector.push_back(d);
  //    //      s.add(z3::forall(expr_vector,
  //    //                       lenfun(pt.prepend(c, d)) == lenfun(c) +
  //    //                       lenfun(d)));
  //    //    }
  //  }
}
packet_theory::packet_theory(z3::context &context)
    : context(context), packetSort(context), bsort(context.bv_sort(1)),
      zero(context), prepend(context), length(context), constructor(context),
      projections(context) {
  //  packetSort = ctx().seq_sort(bsort);
  packetSort = ctx().uninterpreted_sort("packet");
  zero = ctx().function("modelZero", 0, nullptr, packetSort);
  length = ctx().function("length", packetSort, ctx().int_sort());
  //  const char *names[2] = {"length", "arr"};
  //  z3::sort sorts[2] = {ctx().int_sort(), ctx().bv_sort(4096)};
  //  constructor = ctx().tuple_sort("packet", 2, names, sorts, projections);
  //  packetSort = constructor.range();
  //  z3::sort_vector emp(context);
  //  zero = ctx().function("modelZero", emp, packetSort);
  prepend = ctx().function("modelPrepend", packetSort, packetSort, packetSort);
  //  length = projections[0];
}

namespace z3 {
z3::expr forall(z3::expr_vector &xs, const z3::expr &b,
                z3::expr_vector &patterns) {
  array<Z3_app> vars(xs);
  array<Z3_pattern> pats(patterns.size());
  for (unsigned i = 0; i != patterns.size(); ++i) {
    array<Z3_ast> asts(1);
    asts[0] = patterns[i];
    pats[i] = Z3_mk_pattern(b.ctx(), 1, asts.ptr());
    Z3_inc_ref(b.ctx(), Z3_pattern_to_ast(b.ctx(), pats[i]));
  }
  Z3_ast r = Z3_mk_forall_const(b.ctx(), 0, vars.size(), vars.ptr(),
                                pats.size(), pats.ptr(), b);
  b.check_error();
  return expr(b.ctx(), r);
}
z3::expr forall(const z3::expr &x1, const z3::expr &b,
                z3::expr_vector &patterns) {
  z3::expr_vector evec(b.ctx());
  evec.push_back(x1);
  return forall(evec, b, patterns);
}
}

z3::expr_vector packet_theory::make_axioms() {
  z3::expr_vector axes(ctx());
  //  for (auto &pem : packetEmits) {
  //    auto x = ctx().bv_const("x", pem.first);
  //    auto p = ctx().constant("p", packetSort);
  //    z3::expr_vector bounds(ctx());
  //    bounds.push_back(x);
  //    bounds.push_back(p);
  //    axes.push_back(
  //        z3::forall(bounds,
  //                   pem.second(p, x) ==
  //                       z3::concat(p, reverse(pem.first)(x)).extract(4095,
  //                       0)));
  //  }
  for (auto &padv : packetAdvances) {
    auto p = ctx().constant("p", packetSort);
    axes.push_back(
        z3::forall(p, padv.second(p) ==
                          z3::zext(p.extract(4095, padv.first), padv.first)));
  }

  for (auto &pex : packetExtracts) {
    auto p = ctx().constant("p", packetSort);
    axes.push_back(z3::forall(p, pex.second(p) == p.extract(pex.first - 1, 0)));
  }
  for (auto &r : rotates) {
    auto x = ctx().bv_const("x", r.first);

    z3::expr_vector concd(ctx());
    for (unsigned i = 0; i != r.first; ++i) {
      concd.push_back(x.extract(i, i));
    }
    axes.push_back(z3::forall(x, r.second(x) == z3::concat(concd)));
    //    z3::expr_vector patterns(ctx());
    //    patterns.push_back(r.second(r.second(x)));
    //    axes.push_back(z3::forall(x, r.second(r.second(x)) == x, patterns));
  }
  axes.push_back(zero() == ctx().bv_val(0, 4096));
  return axes;
}
