//
// Created by dragos on 28.11.2019.
//

#include "BugReport.h"
#include "AnalysisContext.h"
#include "PropagateFormulas.h"
#include <boost/pending/disjoint_sets.hpp>
#include <boost/property_map/property_map.hpp>
#include <fstream>

namespace analysis {

BugReport::BugReport(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                     bug_report_options brp)
    : refMap(refMap), typeMap(typeMap), bugReportOptions(std::move(brp)) {
  passes.push_back(new VisitFunctor([this](const IR::Node *n) {
    analyzeProgram(n->to<IR::P4Program>());
    return n;
  }));
}

void BugReport::analyzeProgram(const IR::P4Program *program) {
  Analysis analyzer(refMap, typeMap, program, "run");
  auto main = analyzer.getMain();
  analysis::node_t basicBlockStart;
  analysis::EdgeHolder basicBlocks, rBasicBlocks;
  *main = push_ifs(*main, refMap, typeMap);
  basic_blocks(main->holder, main->start_node, basicBlocks, rBasicBlocks,
               basicBlockStart);
  make_ssa(basicBlocks, rBasicBlocks, basicBlockStart, refMap, typeMap,
           analyzer.getFunMap());
  auto sorted = analysis::topo_sort(&basicBlocks, basicBlockStart);
  auto p_ctx = new z3::context();
  EdgeFormulas edgeFormulas(typeMap, refMap, p_ctx);
  z3::solver direct_(*p_ctx);
  z3::solver dual_(*p_ctx);
  packet_solver_ direct(direct_, edgeFormulas.packetTheory);
  packet_solver_ dual(direct_, edgeFormulas.packetTheory);
  z3::expr_vector bugs(*p_ctx);
  // ensure reverse postorder holds, will help a lot in debugging
  for (auto I = sorted.rbegin(); I != sorted.rend(); ++I)
    (void)edgeFormulas.nodeLabel(*I);
  std::unordered_set<node_t> dead, buggy;
  std::vector<node_t> sortedBuggy;
  for (auto &n : sorted) {
    auto lst = last(n);
    if (lst) {
      if (auto mcs = is_extern_method_call(lst)) {
        if (is_bug(mcs->methodCallStatement)) {
          buggy.emplace(n);
          sortedBuggy.emplace_back(n);
        } else if (is_terminal(mcs->methodCallStatement)) {
          // replace basic block ending in send/drop with assume false and
          // simply continue
          dead.emplace(n);
          continue;
        }
      }
    }
  }

  for (auto &n : sorted) {
    auto Cl = edgeFormulas.node(n);
    auto nl = edgeFormulas.nodeLabel(n);
    z3::expr_vector succv(*p_ctx);
    auto lst = last(n);
    if (lst) {
      if (auto mcs = is_extern_method_call(lst)) {
        if (is_bug(mcs->methodCallStatement)) {
          bugs.push_back(edgeFormulas.nodeLabel(n));
        } else if (is_terminal(mcs->methodCallStatement)) {
          // replace basic block ending in send/drop with assume false and
          // simply continue
          direct.add(!edgeFormulas.nodeLabel(n));
          continue;
        }
      }
    }
    auto Isuccs = basicBlocks.find(n);
    bool empty = true;
    if (Isuccs != basicBlocks.end()) {
      for (auto &succ : Isuccs->second) {
        empty = false;
        if (!dead.count(succ.first)) {
          succv.push_back(edgeFormulas.nodeLabel(succ.first));
        }
      }
    }
    if (!succv.empty()) {
      direct.add(z3::implies(edgeFormulas.nodeLabel(n),
                             (Cl && z3::mk_or(succv)).simplify()));
    } else {
      if (empty) {
        direct.add(z3::implies(edgeFormulas.nodeLabel(n), Cl));
      } else {
        direct.add(!edgeFormulas.nodeLabel(n));
      }
    }
  }
  // direct now encodes reachability of bug (see reachability modulo theories
  // paper - aka Corral). If direct is unsat => no bug there
  // if direct is sat => need to model check the path. see code below
  direct.add(edgeFormulas.nodeLabel(basicBlockStart));

  auto get_path = [&](z3::model &model) {
    std::unordered_set<node_t> active;
    for (auto &n : sorted) {
      switch (model.eval(edgeFormulas.nodeLabel(n)).bool_value()) {
      case Z3_L_TRUE:
        active.emplace(n);
      default:
        break;
      }
    }
    std::function<void(std::vector<node_t> &, bool &)> rec;
    rec = [&](std::vector<node_t> &crt, bool &ret) {
      if (auto lst = last(crt.back())) {
        if (auto mcs = is_extern_method_call(lst)) {
          if (is_bug(mcs->methodCallStatement)) {
            ret = true;
            return;
          }
        }
      }
      auto Isuccs = basicBlocks.find(crt.back());
      for (auto &n : Isuccs->second) {
        if (!active.count(n.first))
          continue;
        crt.push_back(n.first);
        rec(crt, ret);
        if (ret)
          return;
        crt.pop_back();
      }
      ret = false;
    };
    std::vector<node_t> pth({basicBlockStart});
    bool found = false;
    rec(pth, found);
    BUG_CHECK(found, "model says path found, but none there");
    return pth;
  };
  NodeValues<std::unordered_set<z3::expr>> packetAtoms;
  for (auto &node : sorted) {
    auto Cl = edgeFormulas.node(node);
    if (Cl.is_and()) {
      for (unsigned i = 0, e = Cl.num_args(); i != e; ++i) {
        auto exp = Cl.arg(i);
        if (exp.is_eq()) {
          auto arg0 = exp.arg(0);
          auto arg1 = exp.arg(1);
          if (edgeFormulas.packetTheory.isPacket(arg0)) {
            packetAtoms[node].emplace(exp);
          }
        }
      }
    }
  }
  while (direct.check() == z3::check_result::sat) {
    auto model = direct.get_model();
    std::unordered_set<node_t> active;
    auto pth = get_path(model);
    std::copy(pth.begin(), pth.end(), std::inserter(active, active.begin()));

    auto smtPrint = [&](std::ostream &os, const node_t &n) {
      if (dead.count(n)) {
        os << n.nodeId()
           << "[style=filled,label=\"dead\",filledcolor=gray47];\n";
        return;
      }
      os << n.nodeId() << "[shape=box,label=\"";
      auto Cl = edgeFormulas.node(n);
      if (Cl.is_and()) {
        for (unsigned i = 0, e = Cl.num_args(); i != e; ++i) {
          os << Cl.arg(i) << "\n";
        }
      } else {
        os << Cl;
      }
      os << "\"";
      if (active.count(n)) {
        os << ",style=filled,color=forestgreen";
      }
      os << "]\n";
    };
    std::unordered_map<z3::expr, unsigned> termindex;
    std::vector<z3::expr> revtermindex;
    std::unordered_map<unsigned, std::set<unsigned>> deps;
    typedef std::map<unsigned, std::size_t> rank_t; // => order on Element
    typedef std::map<unsigned, unsigned> parent_t;
    rank_t rank_map;
    parent_t parent_map;
    boost::associative_property_map<rank_t> rank_pmap(rank_map);
    boost::associative_property_map<parent_t> parent_pmap(parent_map);
    boost::disjoint_sets<boost::associative_property_map<rank_t>,
                         boost::associative_property_map<parent_t>>
        djsets(rank_pmap, parent_pmap);
    auto mkSet = [&](const z3::expr &e0) -> unsigned {
      auto EMI0 = termindex.emplace(e0, termindex.size());
      if (EMI0.second) {
        revtermindex.push_back(e0);
        djsets.make_set(EMI0.first->second);
      }
      return EMI0.first->second;
    };
    auto split = [&](const z3::expr &e) {
      if (edgeFormulas.packetTheory.isPrepend(e)) {
        auto e0 = e.arg(0);
        auto e1 = e.arg(1);
        deps[mkSet(e)].emplace(mkSet(e0));
        deps[mkSet(e)].emplace(mkSet(e1));
      }
    };
    z3::expr_vector allConstraints(*p_ctx);
    auto isPrepend = [&](const z3::expr &e) {
      return edgeFormulas.packetTheory.isPrepend(e);
    };
    auto tmpPack = [&]() {
      return z3::to_expr(
          *p_ctx, Z3_mk_fresh_const(*p_ctx, "pack",
                                    edgeFormulas.packetTheory.packetSort));
    };
    auto normalizePrepend = [&](const z3::expr &e0,
                                std::vector<z3::expr> &extra_equalities) {
      if (isPrepend(e0)) {
        auto e01 = e0.arg(1);
        auto rep = djsets.find_set(termindex[e01]);
        auto &repe = revtermindex[rep];
        if (isPrepend(repe)) {
          auto tmp = tmpPack();
          extra_equalities.push_back(
              tmp == edgeFormulas.packetTheory.prepend(e0.arg(0), repe.arg(0)));
          return edgeFormulas.packetTheory.prepend(tmp, repe.arg(1));
        }
      }
      return e0;
    };

    std::function<void(const z3::expr &)> handleEquality;
    handleEquality = [&](const z3::expr &eq) {
      std::vector<z3::expr> extra_equalities;
      auto e0 = eq.arg(0);
      auto e1 = eq.arg(1);
      split(e0);
      split(e1);
      // normalize prepends into right normal form:
      // prepend(a, prepend(b, c)) == prepend(prepend(a, b), c)
      // add tmp == prepend(a, b) && e0 <- prepend(tmp, c)
      e0 = normalizePrepend(e0, extra_equalities);
      e1 = normalizePrepend(e1, extra_equalities);
      for (auto &xx : extra_equalities) {
        handleEquality(xx);
      }
      auto ei0 = djsets.find_set(mkSet(e0));
      auto ei1 = djsets.find_set(mkSet(e1));
      // this is equality is redundant, move on
      if (ei0 == ei1)
        return;
      auto &ax0 = revtermindex[ei0];
      auto &ax1 = revtermindex[ei1];
      if (isPrepend(ax0) && isPrepend(ax1)) {
        // two prepends are trying to get into the same class
        // xy = ut. Given property of right known length, we know
        // that y = emit_N (X1) && t = emit_M (X2)
        // case split on N vs M
        auto x = ax0.arg(0);
        auto y = ax0.arg(1);
        auto u = ax1.arg(0);
        auto t = ax1.arg(1);
        auto emN = edgeFormulas.packetTheory.isEmit(y.decl());
        auto emM = edgeFormulas.packetTheory.isEmit(t.decl());
        BUG_CHECK(emN && emM,
                  "can't handle prepend with unknown rights %1% vs %2%", ax0,
                  ax1);
        if (*emN == *emM) {
          auto X1 = y.arg(0);
          auto X2 = t.arg(0);
          auto propagate = X1 == X2;
          LOG4("propagating " << propagate);
          allConstraints.push_back(propagate);
          handleEquality(x == u);
        } else {
          if (*emN > *emM) {
            std::swap(x, u);
            std::swap(y, t);
            emN.swap(emM);
          }
          auto X1 = y.arg(0);
          auto X2 = t.arg(0);
          auto propagate = X1 == X2.extract(*emM - 1, *emM - *emN);
          LOG4("propagating " << propagate);
          allConstraints.push_back(propagate);
          handleEquality(x ==
                         edgeFormulas.packetTheory.prepend(
                             u,
                             edgeFormulas.packetTheory.emit(*emM - *emN)(
                                 X2.extract(*emM - *emN - 1, 0))));
        }
      } else {
        // link classes
        djsets.link(ei0, ei1);
        auto rep = djsets.find_set(ei0);
        // if either one of the equated (x, y) are
        // in the same eq class with eps then ensure
        // that the representative of the newly formed
        // set corresponds to eps
        if (edgeFormulas.packetTheory.isZero(ax0) ||
            edgeFormulas.packetTheory.isZero(ax1)) {
          if (!edgeFormulas.packetTheory.isZero(revtermindex[rep])) {
            auto zerorep =
                djsets.find_set(mkSet(edgeFormulas.packetTheory.zero()));
            std::swap(termindex[revtermindex[rep]],
                      termindex[revtermindex[zerorep]]);
            std::swap(revtermindex[rep], revtermindex[zerorep]);
          }
        }
      }
    };

    for (auto &n : pth) {
      allConstraints.push_back(edgeFormulas.nodeLabel(n));
      auto &patoms = packetAtoms[n];
      for (auto &eq : patoms) {
        handleEquality(eq);
      }
    }
    auto cr = direct.check(allConstraints);
    if (cr == z3::check_result::sat) {
      z3::expr_vector block(*p_ctx);
      for (auto &n : pth) {
        block.push_back(!edgeFormulas.nodeLabel(n));
      }
      {
        std::ofstream path(refMap->newName("path") + ".dot");
        CFG cfg(nullptr, std::move(basicBlocks));
        cfg.start_node = basicBlockStart;
        cfg.toDot(path, smtPrint);
        basicBlocks = std::move(cfg.holder);
      }
      auto mdl = direct.get_model();
      // TODO: find initial packet from program and solve for it
      // TODO: magic with mdl to get the packet + djsets and friends
      // TODO: dump packet to options.packet_file
      // TODO: uncomment if need more examples
      std::ofstream report(bugReportOptions.packet_file);
      //      direct.add(z3::mk_or(block));
      LOG4("bug reachable!");
      break;
    } else {
      LOG4("spurious path detected");
      auto uc = direct.unsat_core();
      direct.add(!z3::mk_and(uc));
    }
  }
}
}