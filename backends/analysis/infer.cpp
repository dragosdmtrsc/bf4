//
// Created by dragos on 20.01.2019.
//

#include "infer.h"
#include <p4/toP4/toP4.h>

namespace analysis {
class ResolutionContext {
  z3::solver &direct, &dual;
  Analyzer &ctx;
  const std::pair<node_t const, std::vector<node_t>> &control_bugs;
  std::map<node_t, std::vector<const IR::Expression *>> *fixes;

public:
  std::chrono::milliseconds elapsed;

  ResolutionContext(
      z3::solver &direct, z3::solver &dual, Analyzer &ctx,
      const std::pair<node_t const, std::vector<node_t>> &control_bugs,
      std::map<node_t, std::vector<const IR::Expression *>> *fixes)
      : direct(direct), dual(dual), ctx(ctx), control_bugs(control_bugs),
        fixes(fixes) {
    direct.push();
    dual.push();
  }
  ~ResolutionContext() {
    direct.pop();
    dual.pop();
  }
  MemPath get_post_path(analysis::VersionMemory_t *&version) {
    auto flow = control_bugs.first->to<IR::AssignmentStatement>()
                    ->left->to<IR::PathExpression>();
    auto post_reach = ctx.forward_cfg()
                          .find(ctx.forward_cfg()
                                    .find(control_bugs.first)
                                    ->second.front()
                                    .first)
                          ->first;
    version = ctx.mem().find(post_reach)->second;
    auto mp = get_path(flow, version);
    return mp;
  }
  MemPath get_post_path() {
    analysis::VersionMemory_t *version;
    return get_post_path(version);
  }
  z3::expr get_reach_lit() {
    analysis::VersionMemory_t *version;
    auto mp = get_post_path(version);
    mp.append(cstring("reach"));
    return get_z3_expr(mp, version, &ctx.typeWrapper());
  }
  cstring flow_name() {
    return control_bugs.first->to<IR::AssignmentStatement>()
        ->left->to<IR::PathExpression>()
        ->path->name.name;
  }

  void compute_block(z3::expr_vector &block) {
    dual.add(get_reach_lit());
    auto mp = get_post_path();
    auto nxt =
        ctx.forward_cfg().find(control_bugs.first)->second.begin()->first;
    auto post_version = ctx.mem().find(nxt)->second;
    auto mps = get_basic_versions(mp, post_version);

    std::set<std::string> allowable;
    for (auto &new_mp : mps) {
      if (new_mp.path.back().is_str() && new_mp.path.back().str == "reach") {
        continue;
      } else {
        allowable.emplace(get_qualified_name(new_mp, post_version));
      }
    }
    auto ctrld = [&](const std::string &var) { return allowable.count(var); };

    z3::expr bug_condition = ctx.ctx().bool_val(false);
    bool first = true;
    for (auto trouble : control_bugs.second) {
      auto bug_label = ctx.labels().find(trouble)->second.simplify();
      if (first)
        bug_condition = bug_label;
      else
        bug_condition = merge_or(bug_condition, bug_label);
      first = false;
    }
    direct.add(bug_condition);
    auto lits = find_controlled_literals(bug_condition, ctrld);
    std::unordered_set<z3::expr> mclits;
    std::set<std::string> may_control;
    auto mc = [&](const std::string &var) { return may_control.count(var); };
    if (fixes) {
      auto bv = get_basic_versions(post_version);
      for (auto &path : bv) {
        if (!path.path.empty() && path.path.back().is_str() &&
            path.path.back().str == "reach")
          continue;
        auto qpath = get_qualified_name(path, post_version);
        may_control.emplace(qpath);
      }
      mclits = find_controlled_literals(bug_condition, mc);
    }
    auto start_infer = std::chrono::system_clock::now();
    LOG4("starting abstraction generation at " << control_bugs.first);
    LOG4("direct");
    LOG4(direct);
    LOG4("dual");
    LOG4(dual);
    LOG4("lits");
    for (const auto &l : lits) {
      LOG4(l);
    }
    LOG4("may control");
    for (const auto &m : mclits)
      LOG4(m);
    auto copy = lits;
    block = generate_necessary_abstraction(&direct, &dual, lits, mclits);

    if (fixes) {
      std::set<std::string> extra_control;
      for (auto &x : lits) {
        if (!copy.count(x)) {
          variables_to_control(x, mc, extra_control);
        }
      }
      for (const auto &s : extra_control) {
        LOG3("need to also control: " << s);
        (*fixes)[control_bugs.first].emplace_back(
            DoComputeFixes::str_to_expr(s));
      }
    }

    auto end_infer = std::chrono::system_clock::now();
    LOG3("inference time "
         << std::chrono::duration_cast<std::chrono::milliseconds>(end_infer -
                                                                  start_infer)
                .count()
         << "ms");
    elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(
        end_infer - start_infer);
  }
  void compute_block_optimized(z3::expr_vector &block) {
    dual.add(get_reach_lit());
    auto mp = get_post_path();
    auto nxt =
        ctx.forward_cfg().find(control_bugs.first)->second.begin()->first;
    auto post_version = ctx.mem().find(nxt)->second;
    auto mps = get_basic_versions(mp, post_version);

    std::set<std::string> allowable;
    for (auto &new_mp : mps) {
      if (new_mp.path.back().is_str() && new_mp.path.back().str == "reach") {
        continue;
      } else {
        allowable.emplace(get_qualified_name(new_mp, post_version));
      }
    }
    auto ctrld = [&](const std::string &var) { return allowable.count(var); };

    z3::expr bug_condition = ctx.ctx().bool_val(false);
    bool first = true;
    std::map<node_t, z3::expr> small_labels;
    analysis::reachability_conditions_compute(
        &ctx.forward_cfg(), ctx.sorted(), control_bugs.first,
        ctx.transformers(), ctx.ctx(), &small_labels);
    auto rho_a = ctx.labels().find(control_bugs.first)->second;
    for (auto trouble : control_bugs.second) {
      auto bug_label = small_labels.find(trouble)->second.simplify();
      if (first)
        bug_condition = bug_label;
      else
        bug_condition = merge_or(bug_condition, bug_label);
      first = false;
    }
    direct.add(bug_condition);
    auto lits = find_controlled_literals(bug_condition, ctrld);
    std::unordered_set<z3::expr> mclits;
    std::set<std::string> may_control;
    auto mc = [&](const std::string &var) { return may_control.count(var); };
    if (fixes) {
      auto bv = get_basic_versions(post_version);
      for (auto &path : bv) {
        if (!path.path.empty() && path.path.back().is_str() &&
            path.path.back().str == "reach")
          continue;
        auto qpath = get_qualified_name(path, post_version);
        may_control.emplace(qpath);
      }
      mclits = find_controlled_literals(bug_condition, mc);
    }
    auto start_infer = std::chrono::system_clock::now();
    LOG4("starting abstraction generation at " << control_bugs.first);
    LOG4("direct");
    LOG4(direct);
    LOG4("dual");
    LOG4(dual);
    LOG4("lits");
    for (const auto &l : lits) {
      LOG4(l);
    }
    LOG4("may control");
    for (const auto &m : mclits)
      LOG4(m);
    auto copy = lits;
    block =
        generate_necessary_abstraction_2(rho_a, &direct, &dual, lits, mclits);

    if (fixes) {
      std::set<std::string> extra_control;
      for (auto &x : lits) {
        if (!copy.count(x)) {
          variables_to_control(x, mc, extra_control);
        }
      }
      for (const auto &s : extra_control) {
        LOG3("need to also control: " << s);
        (*fixes)[control_bugs.first].emplace_back(
            DoComputeFixes::str_to_expr(s));
      }
    }

    auto end_infer = std::chrono::system_clock::now();
    LOG3("inference time "
         << std::chrono::duration_cast<std::chrono::milliseconds>(end_infer -
                                                                  start_infer)
                .count()
         << "ms");
    elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(
        end_infer - start_infer);
  }
};
}

bool analysis::DoInfer::preorder(const IR::P4Parser *parser) {
  auto prog = findContext<IR::P4Program>();
  Analyzer ctx(refMap, typeMap, parser, prog);
  std::chrono::milliseconds elapsed(0);
  std::vector<const IR::Node *> level_1_uncontrolled;
  START(full);
  START(prepare);
  LOG3("#accepts:" << ctx.ok_points().size());
  LOG3("#bugs:" << ctx.bug_points().size());
  auto &c2b = ctx.control_to_bugs();
  END(prepare);
  LOG3("prepare time " << DURATION(prepare) << "ms");
  z3::solver dual(ctx.ctx());
  dual.set("core.minimize", true);
  BUG_CHECK(ctx.ok_points().size() == 1, "exactly one ok point");
  auto &ok = *ctx.ok_points().begin();
  dual.add(ctx.labels().find(ok)->second);
  z3::solver direct(ctx.ctx());
  for (const auto &control_bugs : c2b) {
    z3::expr_vector block(ctx.ctx());
    {
      ResolutionContext resolutionContext(direct, dual, ctx, control_bugs,
                                          fixes);
      if (!optimize)
        resolutionContext.compute_block(block);
      else
        resolutionContext.compute_block_optimized(block);
      elapsed += resolutionContext.elapsed;
      if (!block.empty()) {
        output_ofs << "assert:" << resolutionContext.flow_name() << '\n';
        auto ande = z3::mk_and(block);
        output_ofs << ande << '\n';
        output_ofs.flush();
      }
    }
    if (!block.empty()) {
      for (unsigned i = 0; i != block.size(); ++i) {
        direct.add(block[i]);
      }
    }
    START(bug_unreach);
    for (auto trouble : control_bugs.second) {
      auto bug_label = ctx.labels().find(trouble)->second.simplify();
      direct.push();
      direct.add(bug_label);
      if (direct.check() == z3::check_result::sat) {
        level_1_uncontrolled.emplace_back(trouble);
        LOG3("no control over: " << control_bugs.first);
        auto crt = ctx.get_problem_root(trouble);
        if (!crt)
          crt = trouble;
        LOG3("at statement: " << crt);
      } else {
        LOG3("controlled: " << control_bugs.first);
      }
      direct.pop();
    }
    END(bug_unreach);
    LOG3("uncontrolled count time " << DURATION(bug_unreach));
  }
  END(full);
  LOG3("total time inference " << elapsed.count() << "ms");
  LOG3("total time " << DURATION(full) << "ms");
  return false;
}

analysis::Infer::Infer(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                       cstring out_file, const IR::P4Program *&old_program,
                       cstring fixed_file, bool optimize)
    : refMap(refMap), typeMap(typeMap), old_program(old_program),
      fix_gen(new DoFixOldProgram(&fixes)) {
  passes.push_back(new DoInfer(
      refMap, typeMap, out_file,
      (fixed_file.isNullOrEmpty()) ? nullptr : &simple_fixes, optimize));
  if (!fixed_file.isNullOrEmpty()) {
    passes.push_back(new Node2StateAndTable(&simple_fixes, &fixes));
    passes.push_back(
        new VisitFunctor([this](const IR::Node *) -> const IR::Node * {
          for (auto &f : fixes) {
            for (auto e : f.second) {
              LOG3("fix in " << f.first.first << " table " << f.first.second
                             << " extra key " << e);
            }
          }
          return this->old_program->apply(*fix_gen);
        }));
    passes.push_back(new P4::ToP4(new std::ofstream(fixed_file), false));
  }
}

bool analysis::PrintTableStats::preorder(const IR::P4Table *tab) {
  auto k = tab->getKey();
  auto control = findContext<IR::P4Control>();
  size_t nr_k = 0;
  if (k) {
    nr_k = k->keyElements.size();
  }
  auto sz = tab->getSizeProperty();
  unsigned nr_entries = 4096;
  if (sz)
    nr_entries = sz->asUnsigned();
  LOG3("table_stats," << control->name.name << ',' << tab->name.name << ','
                      << nr_k << ',' << nr_entries);
  return false;
}

bool analysis::Verify::preorder(const IR::P4Parser *parser) {
  auto prog = findContext<IR::P4Program>();
  START(reach);
  Analyzer ctx(refMap, typeMap, parser, prog);
  z3::expr bug = ctx.ctx().bool_val(false);
  std::map<const IR::Node *, z3::expr> mapping;
  for (auto &b : ctx.bug_points()) {
    auto label = ctx.labels().find(b)->second;
    if (vera_style) {
      z3::solver s(ctx.ctx());
      s.add(label);
      if (s.check() == z3::check_result::sat) {
        auto crt = ctx.get_problem_root(b);
        if (!crt)
          crt = b;
        LOG3("yup, bug reachable at statement " << crt);
      }
    }
    if (p4v_style) {
      bug = merge_or(bug, label);
      mapping.emplace(b, label);
    }
  }
  if (p4v_style) {
    z3::solver slv(ctx.ctx());
    slv.add(bug);
    int nr = 0;
    int LIMIT = 5;
    while (nr < LIMIT && slv.check() == z3::check_result::sat) {
      auto model = slv.get_model();
      LOG3("yup, bugs reachable");
      bool found = false;
      for (auto &f : mapping) {
        auto v = model.eval(f.second);
        switch (v.bool_value()) {
        case Z3_lbool::Z3_L_TRUE:
          found = true;
        default:
          break;
        }
        if (found) {
          slv.add(!f.second);
          auto crt = ctx.get_problem_root(f.first);
          if (!crt)
            crt = f.first;
          LOG3("for instance, at statement " << crt);
          break;
        }
      }
      ++nr;
    }
    if (nr == 0) {
      LOG3("nope, bugs unreachable");
    }
  }
  END(reach);
  LOG3("reach duration " << DURATION(reach) << "ms");
  return false;
}
