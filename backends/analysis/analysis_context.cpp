//
// Created by dragos on 20.01.2019.
//

#include "analysis_context.h"
#include <z3++.h>

void analysis::Analyzer::init() {
  smttypewrapper = new SmtTypeWrapper(context);
  auto computeTypes =
      new IRToSmtTypeMap(refMap, typeMap, context, smttypewrapper);
  prog->apply(*computeTypes);
  if (parser)
    fw = cg.get_forward(parser);
  else
    fw = cg.get_forward(control);
  bw = analysis::reverse(fw);
  propagate_constants();
  analysis::findVersions(apply(), locals(), fw, p_mem, p_sorted, refMap,
                         typeMap);
}

void analysis::Analyzer::propagate_constants() {
  analysis::constant_propagate(apply(), locals(), fw, p_vals, p_sorted, refMap,
                               typeMap);
  for (auto I = fw->begin(); I != fw->end();) {
    auto crt = I->first;
    bool eraseI = false;
    if (!p_vals->count(crt)) {
      eraseI = true;
    }
    if (!eraseI) {
      for (auto J = I->second.begin(); J != I->second.end();) {
        if (!p_vals->count(J->first)) {
          LOG5("erasing " << J->first << ',' << J->second << " from "
                          << I->first);
          J = I->second.erase(J);
        } else {
          ++J;
        }
      }
      ++I;
    } else {
      LOG5("erasing " << I->first << " for good");
      I = fw->erase(I);
    }
  }
}

void analysis::Analyzer::compute_transformers() {
  std::map<std::pair<node_t, int>, Adjustment> adjustments;
  std::map<std::pair<node_t, int>, analysis::VersionMemory_t *> outs;
  compute_outs(fw, sorted(), mem(), outs);
  compute_phis(fw, sorted(), mem(), adjustments);
  traverse_df(
      fw, sorted().back(), [&](node_t crt, const std::pair<node_t, int> &edge) {
        auto val = edge.second;
        auto expr = analysis::node_to_smt(crt, val, &mem(), refMap, typeMap,
                                          smttypewrapper);
        auto out_version = mem().find(edge.first)->second;
        auto myout_version = outs.find(std::make_pair(crt, val))->second;
        auto I = p_transformers->emplace(std::make_pair(crt, val), expr);
        auto phi = adjustments.find(std::make_pair(crt, val));
        if (phi != adjustments.end()) {
          for (auto &adj : phi->second) {
            auto v0 = get_qualified_name(adj, myout_version);
            auto v1 = get_qualified_name(adj, out_version);
            auto z3type = smttypewrapper->get_type(get_type(adj, typeMap));
            I.first->second =
                I.first->second && (context->constant(v0.c_str(), *z3type) ==
                                    context->constant(v1.c_str(), *z3type));
          }
        }
      });
}

void analysis::Analyzer::compute_assertion_points() {
  for (auto crt : sorted()) {
    if (auto asg = crt->to<IR::AssignmentStatement>()) {
      if (auto lpe = asg->left->to<IR::PathExpression>()) {
        if (lpe->path->name.name.startsWith("pre_call")) {
          if (auto rmce = asg->right->to<IR::MethodCallExpression>()) {
            if (is_havoc(rmce, refMap, typeMap)) {
              p_assertion_points->emplace(crt);
            }
          }
        }
      }
    }
  };
}

void analysis::Analyzer::compute_reachability() {
  analysis::reachability_conditions_compute(fw, sorted(), transformers(),
                                            *context, p_labels);
}

void analysis::Analyzer::compute_finals() {
  traverse_df_pernode(fw, sorted().back(), [&](node_t crt) {
    auto furtherIT = fw->find(crt);
    bool is_terminal = false;
    if (furtherIT == fw->end()) {
      is_terminal = true;
    } else {
      if (furtherIT->second.empty()) is_terminal = true;
    }
    if (is_terminal) {
      bool is_bug = false;
      if (auto mcs = crt->to<IR::MethodCallStatement>())
        if (analysis::is_bug(mcs)) {
          is_bug = true;
          p_bug_points->emplace(crt);
        }
      if (!is_bug) {
        if (auto eok = crt->to<IR::Expression>()) {
          if (auto pe = eok->to<IR::PathExpression>()) {
            if (pe->path->name == IR::ParserState::accept) {
              p_ok_points->emplace(crt);
            }
          }
        }
      }
    }
  });
}

void analysis::Analyzer::compute_control_to_bugs() {
  std::map<node_t, std::vector<node_t>> controlling;
  for (auto bp : bug_points()) {
    auto &v = controlling[bp];
    traverse_df_pernode(bw, bp, [&](node_t crt) {
      auto found = assertion_points().find(crt);
      if (found != assertion_points().end()) {
        v.emplace_back(crt);
      }
    });
    if (!v.empty()) {
      LOG4("bug in context " << bw->find(bp)->second.front().first);
      LOG4("controlled by " << v.front());
      (*p_control_to_bugs)[v.front()].emplace_back(bp);
    }
  }
}

void analysis::Analyzer::print_cfg(std::ostream &os, bool orig,
                                   analysis::node_t start_from) {
  os << "digraph {\n";
  auto srted = &sorted();
  EdgeHolder *fw = &forward_cfg();
  std::vector<node_t> vsrted;
  if (orig) {
    if (parser)
      fw = cg.get_forward(parser);
    else
      fw = cg.get_forward(control);
    vsrted = analysis::topo_sort(fw);
    srted = &vsrted;
  }

  if (!start_from) {
    start_from = srted->back();
  }
  traverse_df_pernode(fw, start_from, [&](node_t n) { print_node(os, n); });
  traverse_df(fw, start_from,
              [&](node_t crt, const std::pair<node_t, int> &nxt) {
                os << id(crt) << "->" << id(nxt.first);
                os << "[label=\"";
                if (auto selex = crt->to<IR::SelectExpression>()) {
                  os << selex->selectCases[nxt.second]->keyset;
                } else {
                  os << nxt.second;
                }
                os << "\"];";
                os << '\n';
              });

  os << "}\n";
}

void analysis::Analyzer::print_node(std::ostream &os, analysis::node_t n) {
  if (auto selex = n->to<IR::SelectExpression>()) {
    os << id(n) << "[label=\"" << selex->select << "\"];";
    return;
  }
  os << id(n) << "[label=\"" << n << "\"];";
}

const IR::IndexedVector<IR::Declaration> &analysis::Analyzer::locals() {
  if (parser != nullptr)
    return parser->parserLocals;
  else
    return control->controlLocals;
}

const IR::IApply *analysis::Analyzer::apply() {
  if (parser != nullptr) return parser;
  return control;
}

analysis::Analyzer::Analyzer(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                             const IR::P4Control *control,
                             const IR::P4Program *prog,
                             bool do_full_constant_propagation)
    : refMap(refMap),
      typeMap(typeMap),
      control(control),
      prog(prog),
      cg(refMap),
      context(new z3::context()),
      do_full_constant_propagation(do_full_constant_propagation) {
  context->set("unsat_core", true);
  context->set("sat.core.minimize", true);
  context->set("smt.core.minimize", true);
  context->set("core.minimize", true);
}

analysis::Analyzer::Analyzer(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                             const IR::P4Parser *parser,
                             const IR::P4Program *prog, z3::context *context,
                             bool do_full_constant_propagation)
    : refMap(refMap),
      typeMap(typeMap),
      parser(parser),
      prog(prog),
      cg(refMap),
      context(context),
      do_full_constant_propagation(do_full_constant_propagation) {}

analysis::Analyzer::Analyzer(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                             const IR::P4Control *control,
                             const IR::P4Program *prog, z3::context *context,
                             bool do_full_constant_propagation)
    : refMap(refMap),
      typeMap(typeMap),
      control(control),
      prog(prog),
      cg(refMap),
      context(context),
      do_full_constant_propagation(do_full_constant_propagation) {}

analysis::Analyzer::Analyzer(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                             const IR::P4Parser *parser,
                             const IR::P4Program *prog, bool cprop)
    : refMap(refMap),
      typeMap(typeMap),
      parser(parser),
      prog(prog),
      cg(refMap),
      context(new z3::context()),
      do_full_constant_propagation(cprop) {
  context->set("unsat_core", true);
  context->set("sat.core.minimize", true);
  context->set("smt.core.minimize", true);
  context->set("core.minimize", true);
}

std::set<analysis::node_t> &analysis::Analyzer::bug_points() {
  if (!p_bug_points) {
    p_bug_points = new std::set<node_t>();
    p_ok_points = new std::set<node_t>();
    compute_finals();
  }
  return *p_bug_points;
}

z3::expr analysis::Analyzer::bug() {
  z3::expr res = ctx().bool_val(false);
  for (auto b : bug_points()) {
    auto label = labels().find(b);
    if (label != labels().end()) res = res || label->second;
  }
  return res;
}

std::map<std::pair<analysis::node_t, int>, z3::expr>
    &analysis::Analyzer::transformers() {
  if (!p_transformers) {
    p_transformers = new std::map<std::pair<node_t, int>, z3::expr>();
    compute_transformers();
  }
  return *p_transformers;
}

std::map<analysis::node_t, z3::expr> &analysis::Analyzer::labels() {
  if (!p_labels) {
    p_labels = new std::map<node_t, z3::expr>();
    compute_reachability();
  }
  return *p_labels;
}

std::map<analysis::node_t, std::vector<analysis::node_t>>
    &analysis::Analyzer::control_to_bugs() {
  if (!p_control_to_bugs) {
    p_control_to_bugs = new std::map<node_t, std::vector<node_t>>();
    compute_control_to_bugs();
  }
  return *p_control_to_bugs;
}

std::map<analysis::node_t, P4::ValueMap *> &analysis::Analyzer::vals() {
  if (!p_vals) pre_init();
  return *p_vals;
}

std::map<analysis::node_t, analysis::VersionMemory_t *>
    &analysis::Analyzer::mem() {
  if (!p_mem) pre_init();
  return *p_mem;
}

std::vector<analysis::node_t> &analysis::Analyzer::sorted() {
  if (!p_sorted) {
    pre_init();
  }
  return *p_sorted;
}

std::set<analysis::node_t> &analysis::Analyzer::assertion_points() {
  if (!p_assertion_points) {
    p_assertion_points = new std::set<node_t>();
    compute_assertion_points();
  }
  return *p_assertion_points;
}

std::set<analysis::node_t> &analysis::Analyzer::ok_points() {
  if (!p_ok_points) {
    p_bug_points = new std::set<node_t>();
    p_ok_points = new std::set<node_t>();
    compute_finals();
  }
  return *p_ok_points;
}

analysis::SmtTypeWrapper &analysis::Analyzer::typeWrapper() {
  if (!smttypewrapper) {
    pre_init();
  }
  return *smttypewrapper;
}

analysis::node_t analysis::Analyzer::get_problem_root(analysis::node_t bug) {
  auto BNeI = backward_cfg().find(bug);
  if (BNeI != backward_cfg().end()) {
    // here is the condition body
    auto isValidCondition = BNeI->second.begin()->first;
    auto fg = forward_cfg().find(isValidCondition)->second;
    for (auto &p : fg) {
      if (p.first != bug) {
        return p.first;
      }
    }
    return isValidCondition;
  } else {
    return nullptr;
  }
}

analysis::EdgeHolder &analysis::Analyzer::forward_cfg() {
  if (!fw) {
    pre_init();
  }
  return *fw;
}

analysis::EdgeHolder &analysis::Analyzer::backward_cfg() {
  if (!bw) {
    pre_init();
  }
  return *bw;
}

void analysis::Analyzer::pre_init() {
  p_sorted = new std::vector<node_t>();
  p_vals = new std::map<node_t, P4::ValueMap *>();
  p_mem = new std::map<node_t, analysis::VersionMemory_t *>();
  init();
}
