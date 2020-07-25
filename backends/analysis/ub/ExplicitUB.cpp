//
// Created by dragos on 04.07.2019.
//

#include "ExplicitUB.h"
#include <analysis/DataDependencies.h>
#include <analysis/HandleHeaders.h>
#include <analysis/VersionedExpression.h>
#include <analysis/bvset/bvset.h>
#include <analysis/cfg_algos.h>
#include <analysis/context/Context.h>
#include <analysis/context/InterproceduralCFGs.h>
#include <analysis/lattice/Lattice.h>
#include <p4/def_use.h>
#include <p4/parserCallGraph.h>
#include <p4/toP4/toP4.h>
#include <boost/functional/hash.hpp>
#include <boost/optional/optional.hpp>
#include <boost/pending/disjoint_sets.hpp>
#include <boost/range/irange.hpp>
#include <boost/variant/detail/apply_visitor_delayed.hpp>
#include <boost/variant/detail/hash_variant.hpp>
#include <boost/variant/static_visitor.hpp>
#include <fstream>
#include <utility>
#include "../analysis.h"
#include "AnalysisContext.h"
#include "ControlLattice.h"
#include "ExpressionCanonicalizer.h"
#include "IOLattice.h"
#include "KeyAdder.h"
#include "PropagateFormulas.h"
#include "ReachingDefinitions.h"
#include "RemovePacketLookahead.h"
#include "StorageLattice.h"
#include "UBLattice.h"
#include "analysis/dj_set_expl.h"
#include "ssa.h"
#include "symbex.h"

using namespace std::placeholders;

namespace analysis {

std::string tableName(const IR::Node *nd) {
  if (auto mcs = nd->to<IR::MethodCallStatement>()) {
    if (auto pe = mcs->methodCall->method->to<IR::PathExpression>())
      return pe->path->name.name.c_str();
  }
  return "";
}

EdgeHolder fullClone(const EdgeHolder &eh, node_t &newstart) {
  NodeValues<node_t> transform;
  auto fun = [&](const node_t &nd) {
    return getOrEmplace(transform, nd,
                        [&]() {
                          auto v = nd->clone();
                          return node_t(v);
                        })
        .first;
  };
  EdgeHolder newg = eh;
  newg = gmap(std::move(newg), std::ref(fun)).first;
  newstart = fun(newstart);
  return newg;
}

struct packet_method_t {
  // stands for term emit<size>(v)
  struct rotate_t {
    unsigned size;
    MemPath v;
    rotate_t(unsigned int size, MemPath v) : size(size), v(std::move(v)) {}
    bool operator<(const rotate_t &r) const {
      if (size != r.size) return size < r.size;
      return v < r.v;
    }
    bool operator==(const rotate_t &r) const {
      return size == r.size && v == r.v;
    }
    friend std::ostream &operator<<(std::ostream &os, const rotate_t &r) {
      return os << r.size << "w(" << r.v << ")";
    }
  };
  // stands for eqn x_ = prepend(x, y)
  struct prepend_var_var_t {
    MemPath x_, x, y;
    prepend_var_var_t(MemPath x_, MemPath x, MemPath y)
        : x_(std::move(x_)), x(std::move(x)), y(std::move(y)) {}
  };
  // stands for x_ = prepend(x, emit<y.size>(y.v)) if headerFirst is false
  // stands for x_ = prepend(emit<y.size>(y.v), x) if headerFirst is true
  struct prepend_var_emit_t {
    bool headerFirst;
    MemPath x_, x;
    rotate_t y;
    prepend_var_emit_t(bool headerFirst, MemPath x_, MemPath x, rotate_t y)
        : headerFirst(headerFirst),
          x_(std::move(x_)),
          x(std::move(x)),
          y(std::move(y)) {}
  };
  // will eventually translate to prepend_var_emit_t,
  // but treatment will be more involved - i.e. need
  // to create another variable
  // stands for y = extract<size>(x)
  struct extract_t {
    MemPath x;
    unsigned size;
    MemPath y;
    extract_t(MemPath x, unsigned int size, MemPath y)
        : x(std::move(x)), size(size), y(std::move(y)) {}
  };
  // same as above need to create another var
  // stands for x_ = advance<size>(x)
  struct advance_t {
    MemPath x_, x;
    unsigned size;
    advance_t(MemPath x_, MemPath x, unsigned int size)
        : x_(std::move(x_)), x(std::move(x)), size(size) {}
  };

  // stands for x = y
  struct assign_t {
    MemPath x, y;
    assign_t(MemPath x, MemPath y) : x(std::move(x)), y(std::move(y)) {}
  };
  // stands for x = zero()
  struct zero_t {
    MemPath x;
    zero_t(MemPath x) : x(std::move(x)) {}
  };
  typedef boost::variant<prepend_var_var_t, prepend_var_emit_t, extract_t,
                         advance_t, assign_t, zero_t>
      data_t;
  data_t data;
  packet_method_t(data_t data) : data(std::move(data)) {}

  struct print_visitor_t : public boost::static_visitor<std::ostream &> {
    std::ostream &os;
    print_visitor_t(std::ostream &os) : os(os) {}
    std::ostream &operator()(const prepend_var_var_t &pvv) {
      return os << pvv.x_ << " = " << pvv.x << " ++ " << pvv.y;
    }
    std::ostream &operator()(const prepend_var_emit_t &pve) {
      if (!pve.headerFirst)
        return os << pve.x_ << " = " << pve.x << " ++ " << pve.y;
      else
        return os << pve.x_ << " = " << pve.y << " ++ " << pve.x;
    }
    std::ostream &operator()(const extract_t &e) {
      return os << e.y << "=extract(" << e.size << "," << e.x << ")";
    }
    std::ostream &operator()(const advance_t &a) {
      return os << a.x_ << "=advance(" << a.size << "," << a.x << ")";
    }
    std::ostream &operator()(const assign_t &a) {
      return os << a.x << "=" << a.y;
    }
    std::ostream &operator()(const zero_t &z) {
      return os << z.x << "=zero()";
    }
  };

  friend std::ostream &operator<<(std::ostream &os, const packet_method_t &pm) {
    print_visitor_t pvt(os);
    return boost::apply_visitor(pvt, pm.data);
  }

  static boost::optional<packet_method_t> resolve(const IR::Node *instr,
                                 P4::ReferenceMap *refMap,
                                 P4::TypeMap *typeMap) {
    auto &packModel = AnalysisLibrary::instance.packetModel;
    PathGetter rds(refMap, typeMap);
    IsLv isLv(refMap, typeMap);
    if (auto asg = is_assign(instr)) {
      auto tp = typeMap->getType(asg->lv);
      if (auto tnt = tp->to<IR::Type_Newtype>()) {
        if (tnt->getName() == AnalysisLibrary::instance.packetModel.name) {
          auto l1 = rds(asg->lv);
          auto l2 = rds(asg->rv);
          CHECK_NULL(l1);
          CHECK_NULL(l2);
          return boost::make_optional<packet_method_t>({assign_t(*l1, *l2)});
        }
      }
    } else {
      if (auto mcs = instr->to<IR::MethodCallStatement>()) {
        auto mi = P4::MethodInstance::resolve(mcs, refMap, typeMap);
        if (auto ef = mi->to<P4::ExternFunction>()) {
          if (ef->method->name == packModel.prepend.name) {
            auto a0 = ef->expr->arguments->at(0)->expression;
            auto a1 = ef->expr->arguments->at(1)->expression;
            auto a2 = ef->expr->arguments->at(2)->expression;
            auto l0 = rds(a0);
            auto l1 = rds(a1);
            auto l2 = rds(a2);
            CHECK_NULL(l0);
            CHECK_NULL(l1);
            CHECK_NULL(l2);
            return boost::make_optional<packet_method_t>(
                {prepend_var_var_t(*l1, *l0, *l2)});
          } else if (ef->method->name == packModel.emit.name) {
            auto a0 = ef->expr->arguments->at(0)->expression;
            auto a1 = ef->expr->arguments->at(1)->expression;
            auto a2 = ef->expr->arguments->at(2)->expression;
            // stands for emit<emitSize>(a0 (x), a1 (x'), a2 (h))
            // <=> x' == h ++ x
            auto emitSize = typeMap->getType(a2)->to<IR::Type_Bits>();
            CHECK_NULL(emitSize);
            auto l0 = rds(a0);
            auto l1 = rds(a1);
            auto l2 = rds(a2);
            CHECK_NULL(l0);
            CHECK_NULL(l1);
            CHECK_NULL(l2);
            return boost::make_optional<packet_method_t>({prepend_var_emit_t(
                true, *l1, *l0, {static_cast<unsigned>(emitSize->size), *l2})});
          } else if (ef->method->name == packModel.peek.name) {
            auto a0 = ef->expr->arguments->at(0)->expression;
            auto a1 = ef->expr->arguments->at(1)->expression;
            auto l0 = rds(a0);
            auto l1 = rds(a1);
            CHECK_NULL(l0);
            CHECK_NULL(l1);
            auto emitSize = typeMap->getType(a1)->to<IR::Type_Bits>();
            CHECK_NULL(emitSize);
            return boost::make_optional<packet_method_t>({extract_t(
                *l0, static_cast<unsigned int>(emitSize->size), *l1)});
          } else if (ef->method->name == packModel.pop.name) {
            auto a0 = ef->expr->arguments->at(0)->expression;
            auto a1 = ef->expr->arguments->at(1)->expression;
            auto a2 = ef->expr->arguments->at(2)->expression;
            auto emitSize = typeMap->getType(a2)->to<IR::Type_Bits>();
            CHECK_NULL(emitSize);
            auto l0 = rds(a0);
            auto l1 = rds(a1);
            auto l2 = rds(a2);
            CHECK_NULL(l0);
            CHECK_NULL(l1);
            CHECK_NULL(l2);
            // stands for extract<emitSize->size>(a0 (x), a1 (x'), a2 (h))
            // <=> x == x' ++ h
            return boost::make_optional<packet_method_t>({prepend_var_emit_t(
                false, *l0, *l1,
                {static_cast<unsigned>(emitSize->size), *l2})});
          } else if (ef->method->name == packModel.zero.name) {
            auto a0 = ef->expr->arguments->at(0)->expression;
            auto l = rds(a0);
            CHECK_NULL(l);
            return boost::make_optional<packet_method_t>({zero_t(*l)});
          } else if (ef->method->name == packModel.advance.name) {
            BUG("advance not implemented");
          }
        }
      }
    }
    return {};
  }
};

class GraphPrinter {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  NodeValues<int> color;

  WriteSet writeSet;
  ReadSet readSet;

 public:
  static const int GREEN = 0;
  static const int RED = 1;
  static const int LGREEN = 2;
  static const int DORANGE = 3;
  static const int LGREY = 4;
  static const int BLUE = 5;

  GraphPrinter(ReferenceMap *refMap, TypeMap *typeMap,
               NodeToFunctionMap *funMap, NodeValues<int> color)
      : refMap(refMap),
        typeMap(typeMap),
        color(std::move(color)),
        writeSet(refMap, typeMap, funMap),
        readSet(refMap, typeMap, funMap) {}

 public:
  std::string prettyInstr(const IR::Node *nd, unsigned lim) {
    std::stringstream ss;
    auto act = actual_node(nd);
    ss << act;
    auto rep = ss.str();
    if (rep.size() > lim) {
      ss.str("");
      auto &ws = writeSet[nd];
      auto &rs = readSet[nd];
      if (!ws.empty()) {
        ss << "[";
        std::ostream_iterator<MemPath> paths(ss, ",");
        std::copy(ws.begin(), ws.end(), paths);
        ss << "] = ";
      }
      ss << "f_" << id(nd) << "(";
      std::ostream_iterator<MemPath> paths(ss, ",");
      std::copy(rs.begin(), rs.end(), paths);
      ss << ")";
      if (ss.str().size() >= rep.size()) return rep;
    }
    return ss.str();
  }

  void operator()(std::ostream &os, node_t node) {
    std::string shape = "box";
    os << node.nodeId() << "[shape=" << shape << ",label=\"";
    if (node.node->is<IR::Vector<IR::Node>>()) {
      // basic block
      auto vec = node.node->to<IR::Vector<IR::Node>>();
      auto sz = vec->size();
      std::string noderepr;
      std::stringstream nodestream;
      for (unsigned i = 0; i != sz; ++i) {
        auto v = vec->at(i);
        if (!v->is<IR::EmptyStatement>()) {
          nodestream << prettyInstr(v, 501);
          if (i != sz - 1) nodestream << "\n";
        }
      }
      noderepr = nodestream.str();
      std::string target("\"");
      unsigned long pos;
      while ((pos = noderepr.find(target)) != std::string::npos)
        target.replace(pos, target.length(), "\\\"");
      size_t lim = 5000;
      if (noderepr.size() > lim + 1) {
        size_t strip = (lim + 1 - 5) / 2;
        auto substr = noderepr.substr(0, strip);
        auto substr2 = noderepr.substr(noderepr.size() - strip);
        noderepr = substr + "\n...\n" + substr2;
      }
      os << noderepr << "\"";
    } else {
      os << prettyInstr(node.node, 501) << "\"";
    }
    auto Icolor = color.find(node);
    if (Icolor != color.end()) {
      std::string col;
      switch (Icolor->second) {
        case LGREY:
          col = "lightgrey";
          break;
        case RED:
          col = "red";
          break;
        case GREEN:
          col = "green";
          break;
        case BLUE:
          col = "blue";
          break;
        case DORANGE:
          col = "darkorange1";
          break;
        case LGREEN:
          col = "chartreuse1";
        default:
          break;
      }
      if (!col.empty()) {
        os << ",fillcolor=" << col << ",style=filled";
      }
    }
    os << "];\n";
  }
};

EdgeHolder make_decision_tree(const EdgeHolder &sg, node_t bstart,
                              const NodeSet &targets, EdgeHolder &pdomf,
                              const NodeValues<node_t> &pdomtree, node_t &start,
                              std::vector<const IR::Expression *> &edgeLabels) {
  NodeSet frontier = targets;
  auto srt = topo_sort(&sg, bstart);
  unsigned rank = 0;
  NodeValues<unsigned> ranks;
  for (auto n : srt) {
    ranks[n] = rank;
    ++rank;
  }
  EdgeHolder decisionTree;
  size_t edgeId = 0;
  NodeSet solved;
  for (auto J = frontier.begin(); J != frontier.end();) {
    if (pdomf[*J].empty())
      J = frontier.erase(J);
    else
      ++J;
  }
  while (true) {
    node_t expandthis;
    node_t nextstop;
    unsigned rankmin = rank;
    for (auto &n : frontier) {
      for (const auto &fe : pdomf[n]) {
        auto &f = fe.first;
        if (frontier.count(f) || solved.count(f)) continue;
        auto rankf = ranks[f];
        if (rankmin > rankf) {
          expandthis = n;
          nextstop = f;
          rankmin = rankf;
        }
      }
    }
    if (rankmin == rank) break;
    if (solved.count(nextstop)) {
      BUG("invariant: no solved node shall ever return to the frontier, "
          "violated");
    }
    BUG_CHECK(
        rankmin > ranks[expandthis],
        "invariant: rank[nextstop] (%1%) <= rank[expandthis] (%2%), violated",
        rankmin, ranks[expandthis]);
    NodeValues<NodeVector> partition_by_pdom;
    if (auto neighs = neighbors_or_null(sg, nextstop)) {
      size_t nr_partitioned = 0;
      BUG_CHECK(neighs->size() > 1,
                "can't have e in pdomf(n) s.t. |neighs| <= 1, but (%1%)",
                neighs->size());
      for (const auto &neigh : *neighs) {
        auto x = neigh.first;
        bool partitioned = false;
        for (auto &n : frontier) {
          if (dominates(pdomtree, n, x)) {
            partition_by_pdom[n].emplace_back(x);
            ++nr_partitioned;
            partitioned = true;
            break;
          }
        }
        if (!partitioned) {
          BUG("found unpartitioned node");
        }
      }
      BUG_CHECK(neighs->size() == nr_partitioned,
                "invariant: all neighbors "
                "of nextstop must be in "
                "the frontier %1% <> %2%",
                neighs->size(), nr_partitioned);
      BUG_CHECK(partition_by_pdom.size() > 1,
                "invariant: there MUST be at least 2 partitions, but %1%",
                partition_by_pdom.size());
    }
    for (const auto &part : partition_by_pdom) {
      auto &n = part.first;
      auto &outgoing = part.second;
      const IR::Expression *e = nullptr;
      for (const auto &neigh : outgoing) {
        const IR::Expression *neighFormula = nullptr;
        for (auto instr : instructions(neigh)) {
          if (auto ifs = instr->to<IR::IfStatement>()) {
            if (!neighFormula)
              neighFormula = ifs->condition;
            else
              neighFormula = new IR::LAnd(ifs->condition, neighFormula);
          }
        }
        if (!e)
          e = neighFormula;
        else
          e = new IR::LOr(neighFormula, e);
      }
      decisionTree[nextstop].emplace_back(n, edgeId++);
      BUG_CHECK(e != nullptr, "%1% (%2%) has no formula for %3% (%4%)",
                nextstop, nextstop.nodeId(), n, n.nodeId());
      edgeLabels.push_back(e);
    }
    frontier.emplace(nextstop);
    NodeSet erase;
    for (const auto &n : frontier) {
      if (n != nextstop) {
        bool anyalive = false;
        for (const auto &fe : pdomf[n]) {
          auto &f = fe.first;
          if (!frontier.count(f) && !solved.count(f)) {
            anyalive = true;
            break;
          }
        }
        if (!anyalive) {
          erase.emplace(n);
        }
      }
    }
    for (const auto e : erase) {
      solved.emplace(e);
      frontier.erase(e);
    }
  }
  if (frontier.size() > 1) {
    start = new IR::EmptyStatement();
    for (const auto &f : frontier) {
      decisionTree[start].emplace_back(f, edgeId);
      LOG5("still standing: " << f);
    }
    edgeLabels.emplace_back(new IR::BoolLiteral(true));
    ++edgeId;
  } else if (frontier.size() == 1) {
    start = *frontier.begin();
  } else {
    BUG("frontier must not be empty");
  }
  return decisionTree;
}

ExplicitUB::dec_tree_holder ExplicitUB::computeDT(
    const EdgeHolder &basicBlocks, const EdgeHolder &rBasicBlocks,
    node_t basicBlockStart, std::unordered_map<MemPath, NodeVector> &writes) {
  dec_tree_holder hld;
  auto &depends = hld.depends;
  NodeValues<std::vector<node_t>> children;
  EdgeHolder domf;
  dom_frontier(basicBlocks, rBasicBlocks, basicBlockStart, children, domf);
  NodeValues<node_t> domtree = get_parents(children);
  NodeValues<std::pair<node_t, unsigned>> instr2bb =
      getInstr2bb(basicBlocks, basicBlockStart);
  NodeValues<PathSet> mergepoints;
  for (auto &write : writes) {
    if (write.second.size() > 1) {
      node_t common_next = node_t::before();
      for (auto instr : write.second) {
        auto bb = instr2bb[instr].first;
        if (auto ns = neighbors_or_null(basicBlocks, bb)) {
          BUG_CHECK(!ns->empty(), "no neighbor, but write happens %1%", instr);
          if (common_next == node_t::before()) {
            common_next = ns->begin()->first;
          } else {
            BUG_CHECK(common_next == ns->begin()->first,
                      "multi-writes should have a common neighbor, but %1% "
                      "doesn't",
                      instr);
          }
        } else {
          BUG("no neighbor, but write happens %1%", instr);
        }
      }
      BUG_CHECK(common_next != node_t::before(),
                "multi-writes for %1% should have a common neighbor, but don't",
                write.first);
      mergepoints[common_next].emplace(write.first);
    }
  }
  LOG4("# merge points: " << mergepoints.size());

  std::map<MemPath, std::tuple<EdgeHolder *, node_t, NodeSet *>> mp2dt;
  std::map<MemPath, std::tuple<EdgeHolder *, node_t, NodeSet *>> mp2refineddt;
  ExpressionCanonicalizer canon(refMap, typeMap);
  for (const auto &mp : mergepoints) {
    auto common_next = mp.first;
    auto previous = *neighbors_or_null(rBasicBlocks, common_next);
    NodeSet targets;
    for (const auto &d : previous) {
      auto bb = d.first;
      targets.emplace(bb);
    }
    auto wdom = domtree.at(common_next);
    EdgeHolder sg;
    NodeSet alldead;
    traverse_df_with_check(
        &basicBlocks, wdom,
        [&](const node_t &n) {
          auto eds = neighbors_or_empty(basicBlocks, n);
          if (!eds.empty()) {
            sg[n] = std::move(eds);
          } else {
            alldead.emplace(n);
          }
        },
        [&](const node_t &, const std::pair<node_t, int> &ed) {
          return ed.first != common_next;
        });
    removeDeadNodes(&sg, wdom,
                    [&](const node_t &nd) { return nd == common_next; });
    auto srt = analysis::topo_sort(&sg, wdom);
    for (auto &s : srt) {
      if (s == common_next) BUG("common next must have been slashed already");
      if (targets.count(s)) continue;
      if (auto neighs = neighbors_or_null(sg, s)) {
        if (std::all_of(neighs->begin(), neighs->end(),
                        [&](const std::pair<node_t, int> &ed) {
                          return alldead.count(ed.first);
                        })) {
          alldead.emplace(s);
        }
      } else {
        alldead.emplace(s);
      }
    }
    removeDeadNodes(&sg, wdom,
                    [&](const node_t &nd) { return alldead.count(nd); });
    auto rsg = std::move(*reverse(&sg));
    NodeValues<NodeVector> ipdoms;
    EdgeHolder pdomf;
    pdom_frontier(sg, rsg, wdom, ipdoms, pdomf);
    auto pdomtree = get_parents(ipdoms);
    std::vector<const IR::Expression *> edgeLabels;
    node_t start;
    START(decisiontree);
    auto decisionTree = make_decision_tree(sg, wdom, targets, pdomf, pdomtree,
                                           start, edgeLabels);
    auto p_decisionTree = new EdgeHolder(std::move(decisionTree));
    auto p_targets = new NodeSet(std::move(targets));
    END(decisiontree);
    std::cerr << "building parent decision tree " << DURATION(decisiontree)
              << "ms\n";
    for (const auto &t : mp.second) {
      // mp2dt[t] = std::make_tuple(p_decisionTree, start, p_targets);
      auto instrs = writes[t];
      NodeValues<const IR::Expression *> instr2partition;
      std::unordered_map<const IR::Expression *, NodeSet> part2instr;
      START(partition);
      for (auto instr : instrs) {
        BUG_CHECK(instr->is<IR::AssignmentStatement>(), "multi-write non asg");
        auto can = canon(instr->to<IR::AssignmentStatement>()->right);
        instr2partition[instr] = can;
        part2instr[can].emplace(instr);
      }
      END(partition);
      std::cerr << "partitioning " << t << " took " << DURATION(partition)
                << "ms\n";
      if (part2instr.size() == instrs.size()) {
        LOG4("no room for partition " << t);
        mp2refineddt[t] = std::make_tuple(p_decisionTree, start, p_targets);
        continue;
      }
      if (part2instr.size() == 1) {
        LOG4("singleton partition for " << t << " = "
                                        << part2instr.begin()->first);
        auto nd = *part2instr.begin()->second.begin();
        EdgeHolder eh;
        (void)eh[instr2bb[nd].first];
        mp2refineddt[t] =
            std::make_tuple(new EdgeHolder(std::move(eh)), nd, p_targets);
        continue;
      }
      LOG4("partitioning " << t << " " << instrs.size() << " vs "
                           << part2instr.size());
      START(decisiontree);
      NodeSet targets;
      for (auto &x : part2instr) {
        auto ex = x.first;
        for (auto &nd : x.second) {
          auto bb = instr2bb[nd].first;
          sg[bb].emplace_back(ex, 0);
          rsg[ex].emplace_back(bb, 0);
        }
        targets.emplace(ex);
      }
      NodeValues<NodeVector> ipdoms;
      EdgeHolder pdomf;
      pdom_frontier(sg, rsg, start, ipdoms, pdomf);
      auto pdomtree = get_parents(ipdoms);
      if (LOGGING(5)) {
        auto nm = refMap->newName("refine") + cstring(".dot");
        std::cerr << t << "," << nm << '\n';
        std::ofstream f(nm);
        toDot(sg, f,
              std::bind(&ExplicitUB::bbNodePrintWStart, this, _1, _2, start));
      }
      node_t mpstart;
      std::vector<const IR::Expression *> edgeLabels;
      auto mpDecisionTree = make_decision_tree(sg, start, targets, pdomf,
                                               pdomtree, mpstart, edgeLabels);
      hld.decision_trees.emplace(
          std::pair<MemPath, dec_tree>(t, {sg, mpstart, edgeLabels}));
      if (LOGGING(5)) {
        NodeSet init, final;
        traverse_df_pernode(&sg, start,
                            [&](const node_t &nd) { init.emplace(nd); });
        traverse_df_pernode(&mpDecisionTree, mpstart, [&](const node_t &nd) {
          if (!init.count(nd)) {
            BUG("node found %1% in decision tree but not in initial", nd);
          }
        });
      }
      auto newtarget = new NodeSet(*p_targets);
      for (auto &x : part2instr) {
        newtarget->emplace(x.first);
        for (auto &nd : x.second) {
          sg.erase(instr2bb[nd].first);
        }
        rsg.erase(x.first);
      }
      mp2refineddt[t] = std::make_tuple(
          new EdgeHolder(std::move(mpDecisionTree)), mpstart, newtarget);
      END(decisiontree);
      std::cerr << "refined decision tree " << t << " in "
                << DURATION(decisiontree) << "ms\n";
    }
  }
  for (auto &mpdt : mp2refineddt) {
    auto g = std::get<0>(mpdt.second);
    auto gs = std::get<1>(mpdt.second);
    auto targets = std::get<2>(mpdt.second);
    auto &dep = depends[mpdt.first];
    traverse_df_pernode(g, gs, [&](const node_t &nd) {
      if (!targets->count(nd)) {
        dep.emplace(nd);
      }
    });
    if (LOGGING(5)) {
      auto nm = refMap->newName("decision_tree") + cstring(".dot");
      std::cerr << mpdt.first << "," << nm << '\n';
      std::ofstream f(nm);
      NodeValues<int> colors;
      for (auto &d : dep) {
        colors[d] = GraphPrinter::BLUE;
      }
      colors[gs] = GraphPrinter::GREEN;
      GraphPrinter gp(refMap, typeMap, nullptr, std::move(colors));
      toDot(*g, f, gp);
    }
  }
  return hld;
}

NodeSet ExplicitUB::dec_tree_holder::operator()(const MemPath &mp) const {
  return depends[mp];
}

ExplicitUB::dec_tree::dec_tree(EdgeHolder h, node_t start,
                               std::vector<const IR::Expression *> edgeLabels)
    : h(std::move(h)), start(start), edgeLabels(std::move(edgeLabels)) {}
}

typedef ProgramPoint call_string_t;
analysis::ExplicitUB::ExplicitUB(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap) {
  passes.push_back(new VisitFunctor([this](const IR::Node *n) {
    analyzeProgram(n->to<IR::P4Program>());
    return n;
  }));
}

void analysis::ExplicitUB::analyzeProgram(const IR::P4Program *program) {
  Analysis analyzer(refMap, typeMap, program, "run");
  auto main = analyzer.getMain();
  auto funMap = analyzer.getFunMap();
  if (LOGGING(5)) {
    std::ofstream out("post_unroll.dot");
    main->toDot(out, ExplicitUB::deadnodeprint);
  }
  p_writeSet = new WriteSet(refMap, typeMap, funMap);
  p_readSet = new ReadSet(refMap, typeMap, funMap);
  std::vector<node_t> nodes =
      analysis::topo_sort(&main->holder, main->start_node);
  auto &readSet = rss();
  auto &writeSet = wss();
  // remove if statements and select statements to assume statements
  *main = push_ifs(*main, refMap, typeMap);
  if (LOGGING(5)) {
    std::ofstream out("ifs_pushed.dot");
    main->toDot(out, ExplicitUB::deadnodeprint);
  }
  analysis::node_t basicBlockStart;
  analysis::EdgeHolder basicBlocks, rBasicBlocks;
  basic_blocks(main->holder, main->start_node, basicBlocks, rBasicBlocks,
               basicBlockStart);
  {
    NodeSet already;
    TypeInference tc(refMap, typeMap, false);
    traverse_df_pernode(&basicBlocks, basicBlockStart, [&](const node_t &nd) {
      auto mut = mutate(nd);
      for (auto &instr : *mut) {
        if (!already.emplace(instr).second) {
          instr = instr->clone();
          instr->apply(tc);
          already.emplace(instr);
        }
      }
    });
  }
  auto sorted = analysis::topo_sort(&basicBlocks, basicBlockStart);
  if (LOGGING(5)) {
    std::ofstream bbstream("basic_blocks_init.dot");
    toDot(basicBlocks, bbstream,
          std::bind(&ExplicitUB::bbNodePrint, this, _1, _2));
    bbstream.close();
  }
  auto ispackMethod = std::bind(&ExplicitUB::ispackMethod_, this, _1, false);
  if (!AnalysisContext::get().options().usePacket) {
    solve_lookaheads(basicBlocks, &rBasicBlocks, basicBlockStart, refMap,
                     typeMap);
    if (LOGGING(5)) {
      std::ofstream bbstream("basic_blocks_0.dot");
      toDot(basicBlocks, bbstream,
            std::bind(&ExplicitUB::bbNodePrint, this, _1, _2));
      bbstream.close();
    }
    rminstrIf(basicBlocks, basicBlockStart, ispackMethod);
    ensure_basic_blocks(basicBlocks, rBasicBlocks, basicBlockStart);
    rBasicBlocks = std::move(*reverse(&basicBlocks));
  }
  make_ssa(basicBlocks, rBasicBlocks, basicBlockStart, refMap, typeMap,
           analyzer.getFunMap());
  if (LOGGING(5)) {
    std::ofstream bbstream("basic_blocks_1.dot");
    toDot(basicBlocks, bbstream,
          std::bind(&ExplicitUB::bbNodePrint, this, _1, _2));
    bbstream.close();
  }
  intra_basic_block_simplifications(basicBlocks, basicBlockStart, refMap,
                                    typeMap, funMap);
  domtree_simplifications(basicBlocks, basicBlockStart, refMap, typeMap,
                          funMap);
  if (LOGGING(5)) {
    std::ofstream bbprint("post_domtree.dot");
    toDot(basicBlocks, bbprint,
          std::bind(&ExplicitUB::bbNodePrint, this, _1, _2));
  }
  simplify_ifs(basicBlocks, basicBlockStart, refMap, typeMap);
  ifs_to_nnf(basicBlocks, basicBlockStart, refMap, typeMap);
  sorted = analysis::topo_sort(&basicBlocks, basicBlockStart);
  rBasicBlocks = std::move(*reverse(&basicBlocks));
  std::ofstream bbstream("basic_blocks.dot");
  toDot(basicBlocks, bbstream,
        std::bind(&ExplicitUB::bbNodePrint, this, _1, _2));
  bbstream.close();
  // done initial simplifications
  {
    EdgeHolder packetProjection;
    NodeValues<node_t> clones;
    traverse_df_pernode(&basicBlocks, basicBlockStart, [&](const node_t &nd) {
      getOrEmplace(clones, nd, [&]() -> node_t {
        auto vec = new IR::Vector<IR::Node>();
        std::copy_if(instructions(nd).begin(), instructions(nd).end(),
                     std::back_inserter(*vec),
                     std::bind(&ExplicitUB::ispackMethod_, this, _1, true));
        return vec;
      });
    });
    for (const auto &np : clones) {
      auto I = basicBlocks.find(np.first);
      if (I != basicBlocks.end()) {
        auto &v = packetProjection[np.second];
        std::transform(I->second.begin(), I->second.end(),
                       std::back_inserter(v), [&](const Edge &ed) -> Edge {
                         return {clones[ed.first], ed.second};
                       });
      }
    }
    std::ofstream bbprint("packets.dot");
    toDot(packetProjection, bbprint,
          std::bind(&ExplicitUB::bbNodePrint, this, _1, _2));
  }

  // computing writes
  auto writes = getWrites(basicBlocks, basicBlockStart);

  NodeValues<std::vector<node_t>> fwchildren;
  EdgeHolder fwdomf;
  dom_frontier(basicBlocks, rBasicBlocks, basicBlockStart, fwchildren, fwdomf);
  std::unordered_set<node_t> dead, buggy;
  std::vector<node_t> sortedBuggy;
  // control boundary computation
  START(boundary);
  NodeValues<NodeSet> control_boundary;
  {
    NodeValues<node_t> node_to_table;
    // compute control boundaries
    for (auto &nd : sorted) {
      if (anycontrol(nd)) {
        auto &boundary = control_boundary[nd];
        boundary.emplace(nd);
        auto dominees = dominees_of(fwchildren, nd);
        for (auto &d : dominees) {
          if (!node_to_table.count(d)) {
            boundary.emplace(d);
          }
        }
        traverse_df_pernode(&basicBlocks, nd, [&](const node_t &n) {
          if (n != nd) node_to_table.emplace(n, nd);
        });
      }
    }
  }
  END(boundary);

  std::cerr << "boundaries computed: " << control_boundary.size() << " in "
            << DURATION(boundary) << "ms\n";
  NodeValues<tab_summary> functionals;
  NodeValues<std::map<MemPath, NodeSet>> tabmaywrite;
  NodeValues<PathSet> tabsurewrite;
  NodeValues<std::vector<state_t>> c2oks;
  NodeValues<std::vector<state_t>> c2bugs;
  std::vector<std::pair<NodeVector, const IR::Expression *>> specs;
  // starting simple spec
  auto instr2bb = getInstr2bb(basicBlocks, basicBlockStart);
  START(simple_spec);
  auto writequery = [&](const IR::Node *at, const MemPath &mp) {
    auto &otherwr = c2oks[at];
    const IR::Expression *mux = nullptr;
    for (const auto &otherpath : otherwr) {
      if (!mux)
        mux = otherpath.store.at(mp);
      else
        mux = new IR::Mux(otherpath.condition(), otherpath.store.at(mp), mux);
    }
    return mux;
  };
  auto printspc = [&](NodeVector &at, const IR::Expression *e) {
    std::stringstream ss;
    for (auto &t : at) {
      auto tabcall = *controlInstr(t);
      auto tabcalltype =
          P4::MethodInstance::resolve(tabcall->to<IR::MethodCallStatement>(),
                                      refMap, typeMap)
              ->to<P4::ExternFunction>();
      ss << "(" << tabcalltype->method << ")\n";
    }
    for (auto &t : at) {
      auto tabcall = *controlInstr(t);
      ss << "WHEN " << tabcall << "\n";
    }
    ss << "AND (" << e << ")";
    return ss.str();
  };
  auto spc = [&](NodeVector &at, const IR::Expression *e) {
    auto cdrs = readSet(e);
    std::unordered_map<MemPath, const IR::Expression *> repls;
    for (const auto &mp : cdrs) {
      for (auto &t : at) {
        auto ci = *controlInstr(t);
        auto &sum = functionals.at(ci);
        auto dw = sum.directWrites.count(mp);
        auto w = sum.written.count(mp);
        if (dw || w) {
          if (!dw) {
            repls[mp] = writequery(ci, mp);
          }
          break;
        }
      }
    }
    Replace replace(refMap, typeMap, repls);
    return replace(e)->to<IR::Expression>();
  };
  NodeValues<EdgeHolder> table_sugraphs;
  for (auto &n : control_boundary) {
    auto nd = n.first;
    auto &bounds = n.second;
    EdgeHolder sub;
    traverse_df_with_check(
        &basicBlocks, nd,
        [&](const node_t &x) {
          if (auto neighs = neighbors_or_null(basicBlocks, x)) {
            EdgeEnumerator eds;
            std::copy_if(neighs->begin(), neighs->end(),
                         std::back_inserter(eds),
                         [&](const std::pair<node_t, int> &ed) {
                           return bounds.count(ed.first);
                         });
            if (!eds.empty()) sub[x] = std::move(eds);
          }
        },
        [&](const node_t &, const std::pair<node_t, int> &ed) {
          return bounds.count(ed.first);
        });
    table_sugraphs[nd] = std::move(sub);
  }
  LiveVariables liveVariables(refMap, typeMap, &basicBlocks, basicBlockStart,
                              funMap);
  NodeSet possiblyIncomplete;
  for (auto I = sorted.rbegin(); I != sorted.rend(); ++I) {
    auto cbI = control_boundary.find(*I);
    if (cbI == control_boundary.end()) continue;
    auto &bounds = *cbI;
    auto &sub = table_sugraphs[*I];
    if (sub.empty()) continue;
    auto tabcall =
        (*std::find_if(instructions(bounds.first).begin(),
                       instructions(bounds.first).end(),
                       [&](const IR::Node *instr) { return isControl(instr); }))
            ->to<IR::MethodCallStatement>();
    auto &tabws = writeSet[tabcall];
    auto &tabrs = readSet[tabcall];
    auto &tabsum = functionals.emplace(tabcall, tabrs).first->second;
    auto tabname =
        tabcall->methodCall->method->to<IR::PathExpression>()->path->name.name;
    tabsum.name = tabname;
    tabsum.directWrites = PathSet(tabws.begin(), tabws.end());
    LOG4("@" << tabname << " " << tabcall);
    if (LOGGING(4)) {
      std::stringstream nm;
      nm << "control_" << tabname;
      std::ofstream sgfile(refMap->newName(nm.str()) + ".dot");
      toDot(sub, sgfile,
            std::bind(&ExplicitUB::bbNodePrintWStart, this, _1, _2, *I));
    }
    auto &tabwrites = tabmaywrite[tabcall];
    NodeSet bugs;
    traverse_df_pernode(&sub, bounds.first, [&](const node_t &nd) {
      if (!bounds.second.count(nd)) return;
      for (const auto &instr : instructions(nd)) {
        auto ws = writeSet[instr];
        if (auto mcs = is_extern_method_call(instr)) {
          if (is_bug(mcs->methodCallStatement)) bugs.emplace(nd);
        }
        if (!ws.empty()) {
          for (const auto &w : ws) {
            tabwrites[w].emplace(instr);
          }
        }
      }
    });
    std::unordered_set<MemPath> erase;
    for (const auto &wr : tabwrites) {
      auto &mp = wr.first;
      auto &allws = writes[mp];
      for (const auto i : allws) {
        if (!wr.second.count(i)) {
          erase.emplace(mp);
          break;
        }
      }
    }
    for (const auto &e : erase) {
      tabwrites.erase(e);
    }
    std::unordered_set<const IR::Node *> assumes;
    for (const auto &x : sub) {
      if (x.second.size() == 2) {
        auto Ibug = std::find_if(
            x.second.begin(), x.second.end(),
            [&](const std::pair<node_t, int> &ed) {
              auto &nd = ed.first;
              if (auto mcs = is_extern_method_call(analysis::last(nd))) {
                if (is_bug(mcs->methodCallStatement)) {
                  return true;
                }
              }
              return false;
            });
        if (Ibug != x.second.end()) {
          auto idx = Ibug - x.second.begin();
          auto other = (idx == 0) ? 1 : 0;
          auto otherNode = x.second[other];
          auto guard = first(otherNode.first);
          BUG_CHECK(guard->is<IR::IfStatement>(), "expecting if guard, got %1%",
                    guard);
          auto ifs = guard->to<IR::IfStatement>();
          assumes.emplace(ifs);
          LOG4("assume statement " << actual_node(ifs));
        }
      }
    }
    pc_t start(bounds.first, -1);
    START(symbex);
    std::vector<state_t> done;
    bool maybeIncomplete = false;
    {
      std::vector<state_t> in_progress({start});
      std::set<std::pair<node_t, int>> seen;
      unsigned iters = 0;
      while (!in_progress.empty()) {
        ++iters;
        if (iters > 50000) {
          std::cerr << "WARNING: very long loop @" << tabname << '\n';
          maybeIncomplete = true;
          break;
        }
        auto last = std::move(in_progress.back());
        in_progress.pop_back();
        auto children = neighbors(sub, last.location);
        if (children.empty()) {
          done.push_back(std::move(last));
          continue;
        }
        for (const auto &child : children) {
          if (!last.location.is_end() && assumes.count(*last.location)) {
            auto cpy = last;
            cpy.location = child;
            in_progress.push_back(std::move(cpy));
          } else {
            auto execd = execute(child, last, refMap, typeMap, funMap);
            in_progress.insert(in_progress.end(),
                               std::make_move_iterator(execd.begin()),
                               std::make_move_iterator(execd.end()));
          }
        }
      }
      if (maybeIncomplete) possiblyIncomplete.emplace(tabcall);
    }
    END(symbex);
    std::vector<state_t> &bugpaths = c2bugs[tabcall];
    std::vector<state_t> &okpaths = c2oks[tabcall];
    for (auto &st : done) {
      if (bugs.count(st.location.nd))
        bugpaths.push_back(std::move(st));
      else
        okpaths.push_back(std::move(st));
    }
    if (!maybeIncomplete) {
      for (auto &ok : okpaths) {
        auto cdrs = readSet(ok.condition());
        auto &condwritten = tabsum.newConditional(ok.path_condition);
        for (const auto &mpw : tabwrites) {
          auto &mp = mpw.first;
          if (!ok.store.count(mp)) {
            continue;
          }
          auto st = ok.store[mp];
          auto rwrs = readSet(st);
          bool allwritten, readwrite;
          allwritten =
              std::all_of(rwrs.begin(), rwrs.end(),
                          [&](const MemPath &mp) { return tabws.count(mp); });
          if (!allwritten) {
            readwrite =
                std::all_of(rwrs.begin(), rwrs.end(),
                            [&](const MemPath &mp) { return tabrs.count(mp); });
          }
          if (allwritten || readwrite) {
            condwritten.emplace(mp);
          }
        }
      }
      tabsum.summarize();
      tabsurewrite[tabcall] = tabsum.written;
    }
    LOG4("done symbex @" << tabname << " in " << DURATION(symbex) << "ms");
    LOG4("bug paths: " << bugpaths.size());
    LOG4("ok paths: " << okpaths.size());
    LOG4("tab summary: " << tabsum);
    if (!bugpaths.empty()) {
      size_t actualid = 0;
      for (auto &bg : bugpaths) {
        auto cdrs = readSet(bg.condition());
        std::vector<MemPath> notthere;
        std::copy_if(cdrs.begin(), cdrs.end(), std::back_inserter(notthere),
                     [&](const MemPath &mp) {
                       return !tabsum.written.count(mp) &&
                              !tabsum.read.count(mp);
                     });
        if (notthere.empty()) {
          NodeVector at_nodes({*I});
          auto cd = new IR::LNot(bg.condition());
          TypeInference typeInference(refMap, typeMap, true);
          cd->apply(typeInference);
          specs.emplace_back(at_nodes, cd);
          std::stringstream ss;
          auto spst = printspc(at_nodes, spc(at_nodes, bg.condition()));
          std::cout << spst << '\n';
        } else {
          std::stringstream ss;
          std::ostream_iterator<MemPath> osi(ss, ",");
          std::copy(notthere.begin(), notthere.end(), osi);
          LOG4("@" << tabname << " bug: ? target (" << ss.str() << ")");
          bugpaths[actualid++] = bg;
          auto Imp = std::find_if(notthere.begin(), notthere.end(),
                                  [&](const MemPath &mp) {
                                    return !liveVariables.live(cbI->first, mp);
                                  });
          if (Imp != notthere.end()) {
            std::cerr << "WARNING: " << *Imp << " is not live at " << tabname
                      << '\n';
          }
        }
      }
      bugpaths.resize(actualid, start);
    }
    for (auto &otherts : functionals) {
      if (otherts.first.node == tabcall) continue;
      auto &othersum = otherts.second;
      if (!tabsum.read.empty() &&
          std::all_of(tabsum.read.begin(), tabsum.read.end(),
                      [&](const MemPath &mp) {
                        return othersum.written.count(mp) != 0;
                      })) {
        LOG4("@" << tabname << " may write-join with "
                 << tableName(otherts.first));
      }

      if (std::all_of(
              othersum.read.begin(), othersum.read.end(),
              [&](const MemPath &rd) { return tabsum.read.count(rd) != 0; })) {
        LOG4("@" << tabname << " may read-join with "
                 << tableName(otherts.first));
        LOG4("@" << tabname << " extra write because of " << otherts.first);
        if (!bugpaths.empty()) {
          size_t actualid = 0;
          for (auto &bg : bugpaths) {
            auto cdrs = readSet(bg.condition());
            std::vector<MemPath> notthere;
            std::copy_if(cdrs.begin(), cdrs.end(), std::back_inserter(notthere),
                         [&](const MemPath &mp) {
                           return !tabws.count(mp) && !tabrs.count(mp) &&
                                  !othersum.written.count(mp);
                         });
            if (notthere.empty()) {
              NodeVector at_nodes({*I});
              at_nodes.push_back(instr2bb[otherts.first].first);
              auto cd = new IR::LNot(bg.condition());
              TypeInference typeInference(refMap, typeMap, true);
              cd->apply(typeInference);
              specs.emplace_back(at_nodes, cd);
              auto spst = printspc(at_nodes, spc(at_nodes, bg.condition()));
              std::cout << spst << '\n';
              LOG4("@" << tabname << " rescued by " << otherts.first);
            } else {
              bugpaths[actualid++] = bg;
            }
          }
          bugpaths.resize(actualid, start);
        }
      }
    }
  }
  END(simple_spec);
  std::cerr << "obtained specs: " << specs.size() << " in "
            << DURATION(simple_spec) << "ms\n";
  std::function<bool(const analysis::node_t &)> oks =
      std::bind(&ExplicitUB::endsInTerminal, this, _1, basicBlocks);
  std::function<bool(const analysis::node_t &)> isbug =
      std::bind(&ExplicitUB::endsInBug, this, _1);
  std::function<bool(const analysis::node_t &)> isdontcare =
      std::bind(&ExplicitUB::isDontCare, this, _1, basicBlocks);

  {
    START(dontcare);
    z3::context ctx;
    ctx.set("sat.core.minimize", true);
    ctx.set("smt.core.minimize", true);
    ctx.set("core.minimize", true);
    EdgeFormulas edgeFormulas(typeMap, refMap, &ctx);
    EdgeFormulas edgeFormulasPrime(typeMap, refMap, &ctx, "prime");
    TypeInference typeInference(refMap, typeMap, true);
    for (auto &np : table_sugraphs) {
      auto &sub = np.second;
      auto n = np.first;
      bool isIncomplete = possiblyIncomplete.count(*controlInstr(n)) != 0;
      auto &bnd = control_boundary[n];
      auto I = std::find_if(bnd.begin(), bnd.end(), [&](const node_t &nd) {
        return std::any_of(
            instructions(nd).begin(), instructions(nd).end(),
            [&](const IR::Node *nd) {
              if (auto mcs = nd->to<IR::MethodCallStatement>()) {
                if (is_extern(mcs, AnalysisLibrary::instance.dontCare.name)) {
                  return true;
                }
              }
              return false;
            });
      });
      if (!isIncomplete && I == bnd.end()) {
        continue;
      }
      z3::solver direct_(ctx);
      packet_solver_ direct(direct_, edgeFormulas.packetTheory);
      LOG4("don't care found for table " << *controlInstr(n)
                                         << ": try reasoning about it");
      auto i2bb = getInstr2bb(sub, np.first);
      auto sorted = topo_sort(&sub, np.first);
      // build direct formula
      buildSolver(direct, sub, np.first, sorted, edgeFormulas);
      avoidAll(direct, sub, np.first, oks, edgeFormulas);
      // build dual formula
      direct.push();
      buildSolver(direct, sub, np.first, sorted, edgeFormulasPrime);
      avoidAll(direct, sub, np.first, isbug, edgeFormulasPrime);
      avoidAll(direct, sub, np.first, isdontcare, edgeFormulasPrime);
      auto tabcall = (*controlInstr(np.first))->to<IR::MethodCallStatement>();
      auto tabname = tabcall->methodCall->method->to<IR::PathExpression>()
                         ->path->name.name;
      for (auto &r : readSet[tabcall]) {
        direct.add(edgeFormulas.toSMT(r) == edgeFormulasPrime.toSMT(r));
      }
      for (auto &r : writeSet[tabcall]) {
        direct.add(edgeFormulas.toSMT(r) == edgeFormulasPrime.toSMT(r));
      }
      auto allbugs = allBugs(sub, np.first);
      NodeSet blockBugs;
      auto init = allbugs.size();
      auto nrpush = 0u;
      while (direct.check() == z3::check_result::sat) {
        auto model = direct.get_model();
        auto path = getPath(model, sub, np.first, edgeFormulas);
        auto bg = path.back();
        LOG4("still reaching " << bg);
        direct.push();
        avoid(direct, bg, edgeFormulas);
        allbugs.erase(bg);
        blockBugs.emplace(bg);
        ++nrpush;
      }
      if (allbugs.empty()) {
        LOG4("no dice for don't care reasoning @" << tabname);
      } else {
        LOG4("dice for don't care reasoning @"
             << tabname << ": controls " << allbugs.size() << "/" << init);
        direct.pop(nrpush + 1);
        for (auto &blk : blockBugs) {
          avoid(direct, blk, edgeFormulas);
        }
        addSpecs(direct, specs, edgeFormulas, i2bb);
        z3::solver dual_(ctx);
        dual_.set("core.minimize", true);
        packet_solver_ dual(dual_, edgeFormulas.packetTheory);
        buildSolver(dual, sub, np.first, sorted, edgeFormulas);
        avoidAll(dual, sub, np.first, isbug, edgeFormulas);
        avoidAll(dual, sub, np.first, isdontcare, edgeFormulas);

        while (direct.check() == z3::check_result::sat) {
          auto model = direct.get_model();
          auto path = getPath(model, sub, np.first, edgeFormulas);
          auto bg = path.back();
          z3::expr_vector assumptions(ctx);
          for (auto &r : readSet[tabcall]) {
            assumptions.push_back(
                (edgeFormulas.toSMT(r) == model.eval(edgeFormulas.toSMT(r)))
                    .simplify());
          }
          for (auto &r : writeSet[tabcall]) {
            assumptions.push_back(
                (edgeFormulas.toSMT(r) == model.eval(edgeFormulas.toSMT(r)))
                    .simplify());
          }
          auto dres = dual.check(assumptions);
          if (dres == z3::check_result::sat) {
            std::ofstream dualf("dual.smt");
            dualf << dual.s;
            std::ofstream directf("direct.smt");
            directf << direct.s;
            std::stringstream ss;
            for (unsigned i = 0; i != assumptions.size(); ++i) {
              LOG4("assumption: " << assumptions[i]);
            }
            BUG("should be unsat, but %1% reachable", bg.nodeId());
          } else {
            auto uc = dual.unsat_core();
            auto theSpec = !z3::mk_and(uc);
            auto p4spec = edgeFormulas.translate(theSpec);
            p4spec->apply(typeInference);
            direct.add(theSpec);
            LOG4("@" << tabname << " don't care spec found: " << p4spec);
            NodeVector nv({np.first});
            specs.emplace_back(std::move(nv), p4spec->to<IR::Expression>());
          }
        }
      }
    }
    END(dontcare);
    std::cerr << "don't care reasoning done in " << DURATION(dontcare)
              << " ms\n";
  }

  auto et = computeDT(basicBlocks, rBasicBlocks, basicBlockStart, writes);
  std::function<NodeSet(const MemPath &)> mpdep = std::bind(et, _1);
  // holds mapping between old_bug -> new_bug (to be used by key inference)
  NodeValues<node_t> bug_transforms;
  if (!AnalysisContext::get().options().noslice) {  // start slicing
    node_t artificialBug = new IR::Vector<IR::Node>();
    auto mutArti = mutate(artificialBug);
    bool anybugs = false;
    for (auto n : sorted) {
      if (auto lst = last(n)) {
        if (auto mcs = lst->to<IR::MethodCallStatement>()) {
          if (is_bug(mcs)) {
            anybugs = true;
            if (mutArti->empty()) {
              mutArti->push_back(lst);
            }
            mutate(n)->resize(nr_instructions(n) - 1);
            basicBlocks[n].emplace_back(artificialBug, 0);
            rBasicBlocks[artificialBug].emplace_back(n, 0);
          }
        }
      }
    }
    if (anybugs) {
      bugids[artificialBug] = 0;
      NodeValues<node_t> transforms;
      for (const auto &x : rBasicBlocks[artificialBug]) {
        transforms[x.first] = node_t::before();
      }
      auto allSlice = mkslice(basicBlocks, basicBlockStart, artificialBug, true,
                              writes, mpdep, &transforms);
      for (const auto &t : transforms) {
        if (t.second != node_t::before()) {
          bug_transforms[t.second] = t.first;
        }
      }
      auto &fullsliceGraph = std::get<0>(allSlice);
      auto fullsliceStart = std::get<1>(allSlice);
      auto newbg = std::get<2>(allSlice);
      auto rfullsliceGraph = std::move(*reverse(&fullsliceGraph));
      if (auto newbgneighs = neighbors_or_null(rfullsliceGraph, newbg)) {
        for (auto &bg : *newbgneighs) {
          mutate(bg.first)->push_back(last(newbg)->clone());
          fullsliceGraph.erase(bg.first);
        }
      }
      rfullsliceGraph.erase(newbg);
      fullsliceGraph.erase(newbg);
      basicBlocks = std::move(fullsliceGraph);
      rBasicBlocks = std::move(rfullsliceGraph);
      basicBlockStart = fullsliceStart;
      if (LOGGING(4)) {
        std::ofstream pslice("basic_blocks_postslice_0.dot");
        toDot(basicBlocks, pslice, std::bind(&ExplicitUB::bbNodePrintWStart,
                                             this, _1, _2, basicBlockStart));
      }
      ensure_basic_blocks(basicBlocks, rBasicBlocks, basicBlockStart);
      if (LOGGING(4)) {
        std::ofstream pslice("basic_blocks_postslice.dot");
        toDot(basicBlocks, pslice, std::bind(&ExplicitUB::bbNodePrintWStart,
                                             this, _1, _2, basicBlockStart));
      }
      traverse_df_pernode(&basicBlocks, basicBlockStart, [&](const node_t &nd) {
        if (endsInBug(nd)) {
          if (auto neighs = neighbors_or_null(basicBlocks, nd)) {
            BUG_CHECK(neighs->empty(), "bug must not have a successor");
          }
        }
      });
      sorted = topo_sort(&basicBlocks, basicBlockStart);
      writes = getWrites(basicBlocks, basicBlockStart);
      et = computeDT(basicBlocks, rBasicBlocks, basicBlockStart, writes);
      mpdep = std::bind(et, _1);
    }
  }  // end slicing

  NodeValues<std::tuple<EdgeHolder, node_t, node_t>> slices;
  NodeValues<std::tuple<EdgeHolder, node_t, node_t>> relaxed_slices;
  auto p_ctx = new z3::context();
  EdgeFormulas edgeFormulas(typeMap, refMap, p_ctx);
  z3::solver direct_(*p_ctx);
  // direct_.set("core.minimize", true);
  // direct_.set("model.completion", false);
  packet_solver_ direct(direct_, edgeFormulas.packetTheory);
  auto i2bb = getInstr2bb(basicBlocks, basicBlockStart);
  sortedBuggy.clear();
  for (auto &nd : sorted) {
    if (auto lst = last(nd)) {
      if (auto mcs = lst->to<IR::MethodCallStatement>()) {
        if (is_bug(mcs)) {
          sortedBuggy.emplace_back(nd);
        }
      }
    }
  }
  for (auto &bg : make_reverse(sortedBuggy)) {
    bugids[bg] = static_cast<unsigned int>(bugids.size());
  }
  buildSolver(direct, basicBlocks, basicBlockStart, sorted, edgeFormulas);
  oks = std::bind(&ExplicitUB::endsInTerminal, this, _1, basicBlocks);
  avoidAll(direct, basicBlocks, basicBlockStart, oks, edgeFormulas);
  if (LOGGING(5)) {
    std::ofstream directf("direct.smt");
    directf << direct;
  }
  auto simplify = z3::tactic(*p_ctx, "solve-eqs") &
                  z3::tactic(*p_ctx, "elim-uncnstr") &
                  z3::tactic(*p_ctx, "simplify");
  goal g(*p_ctx, false, false, false);
  auto assrts = direct.s.assertions();
  for (unsigned i = 0; i != assrts.size(); ++i) {
    g.add(assrts[i]);
  }
  auto ar = simplify(g);
  z3::solver news(*p_ctx);
  for (unsigned i = 0; i != ar.size(); ++i) {
    news.add(ar[i].as_expr());
  }
  {
    std::ofstream simplef("simple.smt");
    simplef << news;
  }

  std::unordered_set<z3::expr> rhos;
  unsigned bugid = 0;

  std::unordered_map<z3::expr, std::pair<node_t, MemPath>> var2tabkey;
  NodeValues<std::unordered_map<MemPath, z3::expr>> tab2key2var;
  size_t ndid = 0;
  for (const auto &nd : make_reverse(sorted)) {
    if (anycontrol(nd)) {
      auto ci = *controlInstr(nd);
      auto keys = readSet[ci];
      size_t keyid = 0;
      for (const auto &k : keys) {
        std::stringstream ss;
        ss << "tab_" << ndid << "_key_" << keyid;
        auto ct =
            p_ctx->constant(ss.str().c_str(), edgeFormulas.toSMT(k).get_sort());
        var2tabkey[ct] = {ci, k};
        tab2key2var[ci].emplace(k, ct);
        ++keyid;
      }
    }
    ++ndid;
  }
  NodeValues<PathSet> patches;
  auto check = [&](bool withSpecs) {
    unsigned iter = 0;
    if (withSpecs) {
      addSpecs(direct, specs, edgeFormulas, i2bb);
    }
    START(modelcheck);
    while (direct.check() == z3::check_result::sat) {
      auto model = direct.get_model();
      if (!solve_for_packet(model, direct.s, basicBlocks, basicBlockStart,
                       edgeFormulas)) {
        LOG3("packet says no");
        break;
      }
      //        auto cr = direct.check(allConstraints);
      auto path = getPath(model, basicBlocks, basicBlockStart, edgeFormulas);
      auto lastbg = path.back();
      bugid = bugids[lastbg];
      LOG3("bug " << bugid << " reachable");
      for (auto instr : instructions(lastbg)) {
        LOG4("bug " << bugid << ",instr:" << prettyInstr(instr, 2000));
      }
      if (withSpecs) {
        auto slzg =
            mkslice(basicBlocks, basicBlockStart, lastbg, true, writes, mpdep);
        auto &slg = std::get<0>(slzg);
        auto sls = std::get<1>(slzg);
        auto newbg = std::get<2>(slzg);
        auto rslg = std::move(*reverse(&slg));
        NodeSet controls;
        traverse_df_with_check(
            &rslg, newbg,
            [&](const node_t &nd) {
              if (anycontrol(nd) || nd == sls) {
                controls.emplace(nd);
              }
            },
            [&](const node_t &nd, const std::pair<node_t, int> &) {
              return !anycontrol(nd);
            });
        if (controls.count(sls)) {
          std::cerr << "bug " << bugid << ",WARNING: uncontrolled bug\n";
        } else {
          LOG4("bug " << bugid << ",found " << controls.size() << " controls");
          for (const auto &control : controls) {
            LOG4("bug " << bugid << ",controlled by " << control);
            typedef std::pair<PathSet, PathSet> fixset;
            auto propagate = [&](const IR::Node *const *startat,
                                 const IR::Node *const *end, fixset init) {
              for (; startat != end; ++startat) {
                auto outinit = init;
                auto instr = *startat;
                auto &irs = readSet[instr];
                for (const auto &mp : irs) {
                  if (!init.first.count(mp) && !init.second.count(mp)) {
                    outinit.first.emplace(mp);
                  }
                }
                auto &iws = writeSet[instr];
                for (const auto &mp : iws) {
                  outinit.second.emplace(mp);
                }
                init = std::move(outinit);
              }
              return init;
            };
            auto startat = controlInstr(control);
            ++startat;
            auto init = propagate(startat, instructions(control).end(), {});
            NodeValues<fixset> ins;
            DefaultDiscipline discipline(&slg, sls);
            std::set<node_t, DefaultDiscipline> q(std::move(discipline));
            if (auto neighs = neighbors_or_null(slg, control)) {
              for (const auto &ng : *neighs) {
                ins[ng.first] = init;
                q.emplace(ng.first);
              }
            }
            fixset fixes;
            bool bugfound = false;
            while (!q.empty()) {
              auto ext = *q.begin();
              q.erase(q.begin());
              auto nxt =
                  propagate(instructions(ext).begin(), instructions(ext).end(),
                            std::move(ins[ext]));
              if (ext == newbg) {
                bugfound = true;
                fixes = std::move(nxt);
                break;
              }
              if (auto neighs = neighbors_or_null(slg, ext)) {
                for (const auto &ng : *neighs) {
                  ins[ng.first] = nxt;
                  q.emplace(ng.first);
                }
              }
            }
            auto tabcall = *controlInstr(control);
            auto &rst = readSet[tabcall];
            auto &wst = writeSet[tabcall];
            for (const auto &mp : rst) fixes.first.erase(mp);
            for (const auto &mp : wst) fixes.first.erase(mp);
            BUG_CHECK(bugfound, "bug %1% not found from control %2%", bugid,
                      tabcall);
            std::stringstream ss;
            std::ostream_iterator<MemPath> osi(ss, ",");
            std::copy(fixes.first.begin(), fixes.first.end(), osi);
            for (const auto &fix : fixes.first) {
              std::cerr << "bug " << bugid << ",missing fixes at table "
                        << tableName(tabcall) << ": " << fix << '\n';
            }
          }
        }
      }
      direct.push();
      direct.add(!edgeFormulas.nodeLabel(lastbg));
      ++iter;
    }
    END(modelcheck);
    direct.pop(iter);
    std::cerr << (withSpecs ? "with" : "without") << " specs " << iter
              << " bugs in " << DURATION(modelcheck) << "ms\n";
  };
  check(false);
  check(true);
  if (patches.empty()) {
    LOG3("no patches to add");
  } else {
    LOG4("adding patches");
    std::ofstream fix("fixed.p4");
    PassManager pm({new KeyAdder(refMap, typeMap, std::move(patches)),
                    new ToP4(&fix, false)});
    program->apply(pm);
  }
}

bool analysis::ExplicitUB::isControl(const IR::Node *nd) {
  if (auto mcs = is_extern_method_call(nd)) {
    return is_controlled(mcs->methodCallStatement, refMap, typeMap);
  }
  return false;
}

const IR::Node *const *analysis::ExplicitUB::controlInstr(
    const analysis::node_t &nd) {
  return std::find_if(instructions(nd).begin(), instructions(nd).end(),
                      [&](const IR::Node *instr) { return isControl(instr); });
}

std::tuple<analysis::EdgeHolder, analysis::node_t, analysis::node_t>
analysis::ExplicitUB::mkslice(const analysis::EdgeHolder &basicBlocks,
                              const analysis::node_t &basicBlockStart,
                              const analysis::node_t &bg, bool relax,
                              std::unordered_map<MemPath, NodeVector> &writes,
                              std::function<NodeSet(const MemPath &)> &depends,
                              NodeValues<node_t> *transforms) {
  auto sorted = topo_sort(&basicBlocks, basicBlockStart);
  auto instr2bb = getInstr2bb(basicBlocks, basicBlockStart);
  auto bugid = bugids[bg];
  auto hcopy = basicBlocks;
  NodeSet bugs;
  for (auto &n : sorted) {
    if (n != bg) {
      auto lst = last(n);
      if (auto mcs = is_extern_method_call(lst)) {
        if (is_bug(mcs->methodCallStatement)) {
          bugs.emplace(n);
          continue;
        }
      }
      if (auto neighs = neighbors_or_null(basicBlocks, n)) {
        if (!neighs->empty()) {
          if (std::all_of(neighs->begin(), neighs->end(),
                          [&](const std::pair<node_t, int> &ed) {
                            return bugs.count(ed.first);
                          })) {
            bugs.emplace(n);
          }
        }
      }
    }
  }
  removeDeadNodes(&hcopy, basicBlockStart,
                  [&](const node_t &n) { return bugs.count(n); });
  START(slice);
  NodeSet alldead;
  NodeValues<NodeVector> boundary;
  auto sted = topo_sort(&hcopy, basicBlockStart);
  for (auto x : sted) {
    bool isDead = false;
    if (x == bg) continue;
    auto neighs = neighbors_or_null(hcopy, x);
    if (neighs) {
      if (neighs->empty()) {
        isDead = true;
        alldead.emplace(x);
      } else {
        if (std::all_of(neighs->begin(), neighs->end(),
                        [&](const std::pair<node_t, int> &ed) {
                          return alldead.count(ed.first);
                        })) {
          isDead = true;
          alldead.emplace(x);
        }
      }
    } else {
      isDead = true;
      alldead.emplace(x);
    }
    if (!isDead) {
      auto I = std::find_if(neighs->begin(), neighs->end(),
                            [&](const std::pair<node_t, int> &ed) {
                              return alldead.count(ed.first);
                            });
      while (I != neighs->end()) {
        auto nd = new IR::Vector<IR::Node>();
        std::copy_if(instructions(I->first).begin(),
                     instructions(I->first).end(), std::back_inserter(*nd),
                     [&](const IR::Node *n) {
                       if (auto mcs = is_extern_method_call(n)) {
                         if (is_terminal(mcs->methodCallStatement)) return true;
                       }
                       return n->is<IR::IfStatement>();
                     });
        boundary[x].emplace_back(nd);
        ++I;
        I = std::find_if(I, neighs->end(),
                         [&](const std::pair<node_t, int> &ed) {
                           return alldead.count(ed.first);
                         });
      }
    }
  }
  removeDeadNodes(&hcopy, basicBlockStart,
                  [&](const node_t &nd) { return alldead.count(nd); });
  for (const auto &b : boundary) {
    std::transform(b.second.begin(), b.second.end(),
                   std::back_inserter(hcopy[b.first]),
                   [](const node_t &nd) -> std::pair<node_t, int> {
                     return {nd, 0};
                   });
  }
  EdgeHolder pdomf;
  NodeValues<NodeVector> pdoms;
  auto rev = std::move(*reverse(&hcopy));
  pdom_frontier(hcopy, rev, basicBlockStart, pdoms, pdomf);
  auto &readSet = rss();
  auto reqInstrs = [&](const std::unordered_set<MemPath> &rs,
                       NodeSet &needassigns) {
    for (const auto &r : rs) {
      auto instrs = writes[r];
      for (auto instr : instrs) {
        needassigns.emplace(instr);
      }
    }
  };
  auto dustar_ = [&](std::unordered_set<MemPath> &rs, bool relax) {
    std::vector<MemPath> explore(rs.begin(), rs.end());
    while (!explore.empty()) {
      auto rd = explore.back();
      explore.pop_back();
      auto instrs = writes[rd];
      for (auto instr : instrs) {
        if (!isControl(instr) || !relax) {
          auto &rds = rss()[instr];
          for (auto &neighr : rds) {
            if (rs.emplace(neighr).second) {
              explore.push_back(neighr);
            }
          }
        }
      }
    }
  };
  auto dustar = std::bind(dustar_, _1, relax);
  auto pdomfstar = [&](const node_t &from, const EdgeHolder &pdomf) {
    NodeSet ns;
    traverse_df_pernode(&pdomf, from,
                        [&](const node_t &nd) { ns.emplace(nd); });
    return ns;
  };
  auto ifs = [&](const NodeSet &nodes) {
    NodeSet iffs;
    for (auto &b : nodes) {
      if (auto neighs = neighbors_or_null(hcopy, b)) {
        for (const auto &ed : *neighs) {
          for (auto instr : instructions(ed.first)) {
            if (instr->is<IR::IfStatement>()) {
              iffs.emplace(instr);
            }
          }
        }
      }
    }
    return iffs;
  };
  auto allReads = [&](const NodeSet &nodes) {
    std::unordered_set<MemPath> rds;
    for (auto nd : nodes) {
      auto &rs = readSet[nd];
      rds.insert(rs.begin(), rs.end());
    }
    return rds;
  };

  auto B = pdomfstar(bg, pdomf);
  NodeSet needassigns;
  NodeSet needifs;
  while (!B.empty()) {
    auto needifs_ = ifs(B);
    auto R1 = allReads(needifs_);
    needifs.insert(needifs_.begin(), needifs_.end());
    dustar(R1);
    reqInstrs(R1, needassigns);
    B.clear();
    for (auto &m : R1) {
      auto deps = depends(m);
      B.insert(deps.begin(), deps.end());
    }
  }
  needassigns.emplace(last(bg));
  NodeValues<node_t> done;
  auto fun = [&](node_t n) {
    return getOrEmplace(
               done, n,
               [&]() {
                 auto cp = n;
                 auto cl = n.node->to<IR::Vector<IR::Node>>()->clone();
                 unsigned crt = 0;
                 for (auto instr : instructions(n)) {
                   if (needassigns.count(instr) || needifs.count(instr)) {
                     cl->at(crt++) = instr;
                   } else {
                     if (auto mcs = is_extern_method_call(instr)) {
                       if (is_terminal(mcs->methodCallStatement)) {
                         cl->at(crt++) = instr;
                       }
                     }
                   }
                 }
                 cl->resize(crt);
                 cp.node = cl;
                 return cp;
               })
        .first;
  };
  size_t initial_instrs = 0;
  traverse_df_pernode(&hcopy, basicBlockStart, [&](const node_t &nd) {
    initial_instrs += nr_instructions(nd);
  });
  hcopy = gmap(std::move(hcopy), std::ref(fun)).first;
  auto newstart = fun(basicBlockStart);
  NodeSet removeThis;
  traverse_df_pernode(&hcopy, newstart, [&](const node_t &nd) {
    if (auto neighs = neighbors_or_null(hcopy, nd)) {
      if (neighs->size() > 1) {
        auto anyif = [&](const std::pair<node_t, int> &ed) {
          return std::any_of(
              instructions(ed.first).begin(), instructions(ed.first).end(),
              [](const IR::Node *nd) { return nd->is<IR::IfStatement>(); });
        };
        auto allifs = std::all_of(neighs->begin(), neighs->end(), anyif);
        if (!allifs) {
          auto anycdneigh = std::any_of(neighs->begin(), neighs->end(), anyif);
          BUG_CHECK(!anycdneigh, "some neighs have ifs some don't");
          auto Ib = neighs->begin();
          ++Ib;
          std::transform(
              Ib, neighs->end(), std::inserter(removeThis, removeThis.end()),
              [&](const std::pair<node_t, int> &ed) { return ed.first; });
        }
      }
    }
  });
  removeDeadNodes(&hcopy, newstart,
                  [&](const node_t &nd) { return removeThis.count(nd); });

  auto newsort = topo_sort(&hcopy, newstart);
  NodeValues<node_t> compressed;
  trans_remove_empty(hcopy, newstart, newsort, &compressed);
  {
    auto J = compressed.find(newstart);
    if (J != compressed.end()) {
      newstart = J->second;
    }
  }
  size_t final_instrs = 0;
  traverse_df_pernode(&hcopy, newstart, [&](const node_t &nd) {
    final_instrs += nr_instructions(nd);
  });
  if (transforms) {
    auto &ts = *transforms;
    for (auto &x : ts) {
      x.second = fun(x.first);
      auto Icompressed = compressed.find(x.second);
      if (Icompressed != compressed.end()) {
        x.second = Icompressed->second;
      }
    }
  }
  if (LOGGING(4)) {
    std::stringstream ss;
    ss << "bug_" << bugid << ".dot";
    std::ofstream ofs(ss.str());
    START(printbug);
    toDot(hcopy, ofs,
          std::bind(&ExplicitUB::bbNodePrintWStart, this, _1, _2, newstart));
    END(printbug);
    std::cerr << "printing bug " << bugid << " took " << DURATION(printbug)
              << "ms\n";
  }
  END(slice);
  std::cerr << "slicing bug " << bugid << ' ' << final_instrs << '/'
            << initial_instrs << " took " << DURATION(slice) << "ms\n";
  return std::make_tuple(hcopy, newstart, fun(bg));
}

void analysis::ExplicitUB::deadnodeprint(std::ostream &os,
                                         analysis::node_t node) {
  const IR::Node *printthis = node.node;
  if (node.node->is<IR::IfStatement>()) {
    printthis = node.node->to<IR::IfStatement>()->condition;
  }
  os << node.nodeId() << "[label=\"" << printthis << "\"";
  if (auto f = is_extern_method_call(node)) {
    if (is_bug(f->methodCallStatement)) os << ",fillcolor=red,style=filled";
  }
  os << "];\n";
}

std::string analysis::ExplicitUB::prettyInstr(const IR::Node *nd,
                                              unsigned lim) {
  std::stringstream ss;
  auto act = actual_node(nd);
  ss << act;
  auto rep = ss.str();
  if (rep.size() > lim) {
    ss.str("");
    auto &ws = wss()[nd];
    auto &rs = rss()[nd];
    if (!ws.empty()) {
      ss << "[";
      std::ostream_iterator<MemPath> paths(ss, ",");
      std::copy(ws.begin(), ws.end(), paths);
      ss << "] = ";
    }
    ss << "f_" << id(nd) << "(";
    std::ostream_iterator<MemPath> paths(ss, ",");
    std::copy(rs.begin(), rs.end(), paths);
    ss << ")";
    if (ss.str().size() >= rep.size()) return rep;
  }
  return ss.str();
}

void analysis::ExplicitUB::bbNodePrint(std::ostream &os,
                                       analysis::node_t node) {
  bbNodePrintWStart(os, node, node_t::before());
}

analysis::NodeValues<std::pair<analysis::node_t, unsigned>>
analysis::ExplicitUB::getInstr2bb(const analysis::EdgeHolder &h,
                                  analysis::node_t start) {
  NodeValues<std::pair<node_t, unsigned>> instr2bb;
  traverse_df_pernode(&h, start, [&](const node_t &s) {
    unsigned idx = 0;
    for (auto instr : instructions(s)) {
      BUG_CHECK(instr2bb.emplace(instr, std::make_pair(s, idx++)).second,
                "instruction %1% occurs in two basic blocks", instr);
    }
  });
  return instr2bb;
}

bool analysis::ExplicitUB::anycontrol(const analysis::node_t &nd) {
  return std::any_of(instructions(nd).begin(), instructions(nd).end(),
                     std::bind(&ExplicitUB::isControl, this, _1));
}

void analysis::ExplicitUB::bbNodePrintWStart(std::ostream &os,
                                             analysis::node_t node,
                                             const analysis::node_t &start) {
  if (node.node->is<IR::Vector<IR::Node>>()) {
    // basic block
    auto vec = node.node->to<IR::Vector<IR::Node>>();
    auto sz = vec->size();
    std::string shape = "box";
    std::string color = "";
    if (std::any_of(instructions(node).begin(), instructions(node).end(),
                    [&](const IR::Node *instr) {
                      if (auto mcs = is_extern_method_call(instr))
                        return is_bug(mcs->methodCallStatement);
                      return false;
                    })) {
    }
    os << node.nodeId() << "[shape=" << shape << ",label=\"";
    std::string noderepr;
    std::stringstream nodestream;
    for (unsigned i = 0; i != sz; ++i) {
      auto v = vec->at(i);
      if (!v->is<IR::EmptyStatement>()) {
        nodestream << prettyInstr(v, 501);
        if (i != sz - 1) nodestream << "\n";
      }
    }
    noderepr = nodestream.str();
    std::string target("\"");
    unsigned long pos = 0;
    while ((pos = noderepr.find(target, pos)) != std::string::npos) {
      noderepr.replace(pos, target.length(), "\\\"");
      pos += 2;
    }
    size_t lim = 5000;
    if (noderepr.size() > lim + 1) {
      size_t strip = (lim + 1 - 5) / 2;
      auto substr = noderepr.substr(0, strip);
      auto substr2 = noderepr.substr(noderepr.size() - strip);
      noderepr = substr + "\n...\n" + substr2;
    }
    os << noderepr << "\"";
  } else {
    deadnodeprint(os, node);
    return;
  }
  if (node == start) {
    os << ",style=filled,color=green";
  }
  os << "];\n";
}

std::unordered_map<analysis::MemPath, analysis::NodeVector>
analysis::ExplicitUB::getWrites(const analysis::EdgeHolder &basicBlocks,
                                analysis::node_t basicBlockStart) {
  std::unordered_map<MemPath, NodeVector> writes;
  traverse_df_pernode(&basicBlocks, basicBlockStart, [&](const node_t &n) {
    for (auto instr : instructions(n)) {
      auto &ws = wss()[instr];
      for (const auto &mp : ws) {
        writes[mp].push_back(instr);
      }
    }
  });
  return writes;
}

bool analysis::ExplicitUB::endsInBug(const analysis::node_t &nd) {
  if (auto lst = last(nd)) {
    if (auto mcs = lst->to<IR::MethodCallStatement>()) {
      if (is_bug(mcs)) return true;
    }
  }
  return false;
}

void analysis::ExplicitUB::buildSolver(packet_solver_ &direct,
                                       const analysis::EdgeHolder &basicBlocks,
                                       analysis::node_t basicBlockStart,
                                       const analysis::NodeVector &sorted,
                                       analysis::EdgeFormulas &edgeFormulas) {
  for (auto &n : make_reverse(sorted)) {
    auto Cl = edgeFormulas.node(n);
    direct.add(z3::implies(edgeFormulas.nodeLabel(n), Cl));
    if (auto neighs = neighbors_or_null(basicBlocks, n)) {
      if (!neighs->empty()) {
        z3::expr_vector succv(direct.ctx());
        for (auto &succ : *neighs) {
          succv.push_back(edgeFormulas.nodeLabel(succ.first));
        }
        direct.add(z3::implies(edgeFormulas.nodeLabel(n), z3::mk_or(succv))
                       .simplify());
      }
    }
  }
  direct.add(edgeFormulas.nodeLabel(basicBlockStart));
}

void analysis::ExplicitUB::avoid(packet_solver_ &direct,
                                 const analysis::node_t &nd,
                                 analysis::EdgeFormulas &edgeFormulas) {
  direct.add(!edgeFormulas.nodeLabel(nd));
}

void analysis::ExplicitUB::avoidAll(
    packet_solver_ &direct, const analysis::EdgeHolder &basicBlocks,
    analysis::node_t basicBlockStart,
    std::function<bool(const analysis::node_t &)> &filter,
    analysis::EdgeFormulas &edgeFormulas) {
  traverse_df_pernode(&basicBlocks, basicBlockStart, [&](const node_t &nd) {
    if (filter(nd)) {
      avoid(direct, nd, edgeFormulas);
    }
  });
}

bool analysis::ExplicitUB::endsInTerminal(
    const analysis::node_t &nd, const analysis::EdgeHolder &basicBlocks) {
  if (!endsInBug(nd)) {
    return neighbors_empty(basicBlocks, nd);
  }
  return false;
}

bool analysis::ExplicitUB::isDontCare(const analysis::node_t &nd,
                                      const analysis::EdgeHolder &) {
  return std::any_of(instructions(nd).begin(), instructions(nd).end(),
                     [](const IR::Node *lst) {
                       if (auto mcs = lst->to<IR::MethodCallStatement>()) {
                         return is_extern(
                             mcs, AnalysisLibrary::instance.dontCare.name);
                       }
                       return false;
                     });
}

std::vector<analysis::node_t> analysis::ExplicitUB::getPath(
    z3::model model, const analysis::EdgeHolder &basicBlocks,
    const analysis::node_t &basicBlockStart,
    analysis::EdgeFormulas &edgeFormulas) {
  std::vector<node_t> path({basicBlockStart});
  while (true) {
    auto lst = path.back();
    if (auto neighs = neighbors_or_null(basicBlocks, lst)) {
      if (neighs->empty()) break;
      bool neighfound = false;
      for (auto &neigh : *neighs) {
        if (model.eval(edgeFormulas.nodeLabel(neigh.first)).bool_value() ==
            Z3_L_TRUE) {
          path.push_back(neigh.first);
          neighfound = true;
          break;
        }
      }
      if (!neighfound) {
        BUG("at (%1%) no neighbor found", lst.nodeId());
      }
    } else {
      break;
    }
  }
  return path;
}

analysis::NodeSet analysis::ExplicitUB::allBugs(
    const analysis::EdgeHolder &basicBlocks, const analysis::node_t &start) {
  NodeSet bugs;
  traverse_df_pernode(&basicBlocks, start, [&](const node_t &nd) {
    if (endsInBug(nd)) bugs.emplace(nd);
  });
  return bugs;
}

void analysis::ExplicitUB::addSpecs(
    packet_solver_ &direct,
    const std::vector<std::pair<analysis::NodeVector, const IR::Expression *>>
        &specs,
    analysis::EdgeFormulas &edgeFormulas,
    analysis::NodeValues<std::pair<analysis::node_t, unsigned int>> &i2bb) {
  for (const auto &spec : specs) {
    z3::expr_vector guard(direct.ctx());
    for (const auto &nd : spec.first) {
      auto instr = *controlInstr(nd);
      auto I2 = i2bb.find(instr);
      if (I2 != i2bb.end()) {
        auto actual = I2->second.first;
        guard.push_back(edgeFormulas.nodeLabel(actual));
      }
    }
    auto spc = edgeFormulas.toSMT(spec.second);
    if (!guard.empty()) {
      auto z3sp = z3::implies(z3::mk_and(guard), spc).simplify();
      direct.add(z3sp);
      LOG5("created spec " << z3sp);
    }
  }
}
namespace analysis {
// equations are of the form x == y or
// x == y ++ z
// x, y, z are terminals. A terminal is either
// a variable x or an expression: emit<N>(y)
// discover all terminals
struct terminal_t {
  struct the_zero_t {
    bool operator==(the_zero_t) const { return true; }
  };
  static unsigned ID;

  boost::variant<MemPath, packet_method_t::rotate_t, the_zero_t> data;
  bool operator<(const terminal_t &other) const {
    if (data.which() != other.data.which())
      return data.which() < other.data.which();
    if (auto d = boost::get<MemPath>(&data)) {
      return *d < boost::get<MemPath>(other.data);
    } else if (auto dr = boost::get<packet_method_t::rotate_t>(&data)) {
      return *dr < boost::get<packet_method_t::rotate_t>(other.data);
    } else {
      // zero is always equal to zero
      return false;
    }
  }
  bool is_zero() const { return boost::get<the_zero_t>(&data) != nullptr; }
  const MemPath *packet_variable() const { return boost::get<MemPath>(&data); }
  const packet_method_t::rotate_t *bv_variable() const {
    return boost::get<packet_method_t::rotate_t>(&data);
  }
  terminal_t(MemPath m) : data(std::move(m)) {}
  terminal_t(packet_method_t::rotate_t m) : data(std::move(m)) {}
  terminal_t(MemPath m, unsigned sz)
      : data(packet_method_t::rotate_t(sz, std::move(m))) {}

  terminal_t() : data(the_zero_t()) {}

  static MemPath fresh_mp() {
    MemPath m;
    m.decl = nullptr;
    m.version = ID++;
    return m;
  }
  static terminal_t mk_fresh_terminal() { return fresh_mp(); }
  static terminal_t mk_fresh_terminal(unsigned sz) {
    return packet_method_t::rotate_t(sz, fresh_mp());
  }
  boost::optional<unsigned> len() const {
    if (auto bv = bv_variable()) return bv->size;
    if (is_zero()) return 0;
    return {};
  }
  bool operator==(const terminal_t &t) const {
    return data == t.data;
  }

  friend std::ostream &operator<<(std::ostream &os, const terminal_t &t) {
    if (t.is_zero()) return os << "''";
    if (auto bv = t.bv_variable()) {
      return os << bv->size << "w(" << bv->v << ")";
    }
    return os << *t.packet_variable();
  }
};

unsigned terminal_t::ID = 0;

#define SAME_METHOD(a) \
  packet_method_t operator()(const a &x) { return same(x); }
struct PackVisitor : public boost::static_visitor<packet_method_t> {

  template <typename T>
  packet_method_t same(const T &v) {
    packet_method_t::data_t d(v);
    return {d};
  }
  SAME_METHOD(packet_method_t::assign_t);
  SAME_METHOD(packet_method_t::zero_t);
  SAME_METHOD(packet_method_t::advance_t);
  SAME_METHOD(packet_method_t::prepend_var_var_t);
  SAME_METHOD(packet_method_t::prepend_var_emit_t);

  packet_method_t operator()(const packet_method_t::extract_t &ext) {
    // h = extract<sz>(x)
    // means: there exists x' = pop<sz>(x, h)
    // <=> x == prepend(x', h)
    return same(packet_method_t::prepend_var_emit_t(
        false, ext.x, terminal_t::fresh_mp(), {ext.size, ext.y}));
  }
  packet_method_t shred(packet_method_t &&pm) {
    return boost::apply_visitor(*this, std::move(pm.data));
  }
};
#undef SAME_METHOD

#define SAME_METHOD(a) \
  void operator()(const a &) {}
struct make_terminals : public boost::static_visitor<void> {
  variable_context_t<terminal_t> &vc;
  std::map<congruence_closure_t::var_t,
           std::vector<std::pair<congruence_closure_t::var_t,
                                 congruence_closure_t::var_t>>>
      lv_to_equations;

  make_terminals(variable_context_t<terminal_t> &vc) : vc(vc) {}

  void operator()(const packet_method_t::assign_t &asg) {
    vc.cc.add_equality(congruence_closure_t::var_eq_t(
        vc.var(terminal_t(asg.x)), vc.var(terminal_t(asg.y))));
  }
  void operator()(const packet_method_t::zero_t &z) {
    vc.cc.add_equality(congruence_closure_t::var_eq_t(vc.var(terminal_t(z.x)),
                                                      vc.var(terminal_t())));
  }
  void operator()(const packet_method_t::advance_t &) {
    BUG("advance should not occur");
  }
  void operator()(const packet_method_t::prepend_var_emit_t &ppeq) {
    terminal_t x_(ppeq.x_);
    terminal_t x(ppeq.x);
    terminal_t y(ppeq.y);
    auto vx_ = vc.var(x_);
    auto vx = vc.var(x);
    auto vy = vc.var(y);
    lv_to_equations[vx_].emplace_back(
      ppeq.headerFirst ? vy : vx, ppeq.headerFirst ? vx : vy);
    vc.cc.add_equality(congruence_closure_t::var_fun_eq_t(
        ppeq.headerFirst ? vy : vx, ppeq.headerFirst ? vx : vy, vx_));
  }
  void operator()(const packet_method_t::prepend_var_var_t &ppeq) {
    terminal_t x_(ppeq.x_);
    terminal_t x(ppeq.x);
    terminal_t y(ppeq.y);
    auto vx_ = vc.var(x_);
    auto vx = vc.var(x);
    auto vy = vc.var(y);
    lv_to_equations[vx_].emplace_back(vx, vy);
    vc.cc.add_equality(congruence_closure_t::var_fun_eq_t(vx, vy, vx_));
  }

  void operator()(const packet_method_t::extract_t &) {
    BUG("extract should not occur");
  }
  void operator()(const packet_method_t &pm) {
    boost::apply_visitor(*this, pm.data);
  }
};

#undef SAME_METHOD

struct prepend_t {
  terminal_t left, right;
  prepend_t(terminal_t left, terminal_t right)
      : left(std::move(left)), right(std::move(right)) {}

  bool operator<(const prepend_t &p) const {
    if (left == p.left) return right < p.right;
    return left < p.left;
  }
};

}  // namespace analysis
bool analysis::ExplicitUB::solve_for_packet(
    z3::model &model, z3::solver &slv, const analysis::EdgeHolder &basicBlocks,
    const analysis::node_t &basicBlockStart,
    analysis::EdgeFormulas &edgeFormulas) {
  unsigned nriters = 0;
  START(solving);
  while (true) {
    nriters++;
    auto path = getPath(model, basicBlocks, basicBlockStart, edgeFormulas);
    PackVisitor pv;
    std::vector<packet_method_t> packet_methods;
    slv.push();
    for (const auto &nd : path) {
      for (auto instr : instructions(nd)) {
        if (auto pinstr = packet_method_t::resolve(instr, refMap, typeMap)) {
          if (LOGGING(5)) {
            std::cerr << "packet instruction " << instr << " ==> " << *pinstr
                      << " ==> ";
          }
          auto shreded = pv.shred(std::move(*pinstr));
          if (LOGGING(5)) {
            std::cerr << shreded << "\n";
          }
          packet_methods.emplace_back(std::move(shreded));
        }
      }
      slv.add(edgeFormulas.nodeLabel(nd));
    }
    variable_context_t<terminal_t> pack_context;
    make_terminals mt(pack_context);
    for (const auto &pm : packet_methods) {
      mt(pm);
    }
    std::map<congruence_closure_t::representative_t,
             std::set<std::pair<congruence_closure_t::var_t,
                                congruence_closure_t::var_t>>>
        distinct_prepends;
    auto &cc = pack_context.cc;
    for (const auto &leq : mt.lv_to_equations) {
      auto rep = cc.representatives[leq.first];
      auto &dp = distinct_prepends[rep];
      for (const auto &p : leq.second) {
        auto r1 = cc.representatives[p.first];
        auto r2 = cc.representatives[p.second];
        dp.emplace(r1, r2);
      }
    }

    EdgeHolder var_order;
    auto eqc_node = [](congruence_closure_t::representative_t r) -> node_t {
      return node_t().clone(r);
    };
    auto node_to_eqc =
        [&](const node_t &nd) -> congruence_closure_t::representative_t {
      return nd.label;
    };
    for (const auto &dp : distinct_prepends) {
      for (const auto &nxt : dp.second) {
        var_order[eqc_node(nxt.first)].emplace_back(eqc_node(dp.first), 0);
        var_order[eqc_node(nxt.second)].emplace_back(eqc_node(dp.first), 0);
      }
    }

    terminal_t zr;
    auto zrvar = pack_context.var(zr);
    auto zero_rep = cc.get_representative(zrvar);
    typedef std::vector<congruence_closure_t::var_t> normal_form_t;
    std::map<congruence_closure_t::representative_t, normal_form_t> nfs;

    auto nf_to_terminals = [&](const normal_form_t &nf) {
      std::vector<terminal_t> terminals;
      std::transform(nf.begin(), nf.end(), std::back_inserter(terminals),
                     [&](congruence_closure_t::var_t v) {
                       return pack_context.for_variable(v);
                     });
      return terminals;
    };

    auto terminal_to_string = [&](const terminal_t &term,
                                  std::ostream &os) -> std::ostream & {
      if (term.is_zero()) {
        return os << "''";
      } else if (auto bvar = term.bv_variable()) {
        return os << bvar->size << "w(" << bvar->v << ")";
      } else {
        auto pvar = term.packet_variable();
        return os << *pvar;
      }
    };
    auto terminals_to_string = [&](const std::vector<terminal_t> &terminals,
                                   std::ostream &os) {
      bool first = true;
      for (const auto &term : terminals) {
        if (first) {
          first = false;
        } else {
          os << " ++ ";
        }
        terminal_to_string(term, os);
      }
    };

    auto interval_heads = [](unsigned lx, unsigned offl,
                             unsigned ll) -> std::pair<unsigned, unsigned> {
      return {lx - offl - 1, lx - offl - ll};
    };

    auto ensure = [&](const terminal_t &l,
                      const std::pair<unsigned, unsigned> &linterval,
                      const terminal_t &r,
                      const std::pair<unsigned, unsigned> &rinterval) {
      auto bl = l.bv_variable();
      auto br = r.bv_variable();
      CHECK_NULL(bl);
      CHECK_NULL(br);
      auto el = edgeFormulas.toSMT(bl->v);
      auto er = edgeFormulas.toSMT(br->v);
      auto assertion = el.extract(linterval.first, linterval.second) ==
                       er.extract(rinterval.first, rinterval.second);
      auto checkres = model.eval(assertion).bool_value();
      if (LOGGING(5)) {
        std::cerr << "adjustment equation: " << assertion << " evaluates to "
                  << checkres << '\n';
      }
      if (checkres != Z3_L_FALSE) {
        return true;
      } else {
        // time to adjust
        if (LOGGING(5)) {
          std::cerr << "adjusting: " << l << "[" << linterval.first << ':'
                    << linterval.second << "] == " << r << "["
                    << rinterval.first << ':' << rinterval.second << "]\n";
          slv.add(assertion);
          if (slv.check() == z3::check_result::sat) {
            LOG5("adjustment ok");
            model = slv.get_model();
          } else {
            LOG5("real conflict encountered");
            return false;
          }
        }
      }
      return true;
    };

    auto resolution = [&](const std::vector<terminal_t> &left,
                          const std::vector<terminal_t> &right) {
      // left variable id, right variable id
      // left offset (in the current left variable)
      // right offset (in the current right variable)
      unsigned vl = 0, vr = 0, offl = 0, offr = 0;
      auto lenL = left.size();
      auto lenR = right.size();
      while (vl < lenL && vr < lenR) {
        auto &term_l = left[lenL - 1 - vl];
        auto &term_r = right[lenR - 1 - vr];
        // reached a variable terminal, end of story
        auto maybeLL = term_l.len();
        auto maybeRL = term_r.len();
        if (!maybeLL || !maybeRL) break;
        // remaining length (l(eft) and r(ight))
        auto ll = *maybeLL - offl;
        auto lr = *maybeRL - offr;
        // create constraint
        auto left_interval = interval_heads(*maybeLL, offl, std::min(ll, lr));
        auto right_interval = interval_heads(*maybeRL, offr, std::min(ll, lr));
        // model check if left
        if (!ensure(term_l, left_interval, term_r, right_interval))
          return false;
        if (ll < lr) {
          // eatup the left
          vl++;
          offl = 0;
          // offset in right
          offr += ll;
        } else if (ll > lr) {
          // eatup the right
          vr++;
          offr = 0;
          // offset in left
          offl += lr;
        } else {
          // eatup both
          vl++;
          vr++;
          offl = offr = 0;
        }
      }
      return true;
    };
    bool is_conflicted = false;
    auto sorted_vars = topo_sort(&var_order);
    for (auto nd : make_reverse(sorted_vars)) {
      auto eqc = node_to_eqc(nd);
      bool iszero = (eqc == zero_rep);
      auto &nf = nfs[eqc];
      std::vector<normal_form_t> candidates;
      auto &mydps = distinct_prepends[eqc];
      if (mydps.empty()) {
        if (iszero) {
          candidates = {{}};
        } else {
          candidates = {{eqc}};
        }
      } else {
        for (const auto &dp : mydps) {
          auto nf1 = nfs[dp.first];
          std::copy(nfs[dp.second].begin(), nfs[dp.second].end(),
                    std::back_inserter(nf1));
          if (!candidates.empty()) {
            // possible conflict goes here
            auto &first = candidates[0];
            std::vector<terminal_t> nf1_terminals, first_terminals;
            nf1_terminals = nf_to_terminals(nf1);
            first_terminals = nf_to_terminals(first);

            if (LOGGING(5)) {
              std::cerr << "conflict: ";
              terminals_to_string(nf1_terminals, std::cerr);
              std::cerr << " vs ";
              terminals_to_string(first_terminals, std::cerr);
              std::cerr << '\n';
            }
            if (resolution(nf1_terminals, first_terminals)) {
              continue;
            } else {
              is_conflicted = true;
              break;
            }
          } else {
            candidates.emplace_back(std::move(nf1));
          }
        }
        if (is_conflicted) break;
      }
      if (candidates.size() == 1) {
        if (LOGGING(5)) {
          auto term = pack_context.for_variable(eqc);
          terminal_to_string(term, std::cerr);
          std::cerr << " {";
          bool first = true;
          for (auto v : pack_context.cc.class_list[eqc]) {
            if (v != eqc) {
              if (!first) {
                std::cerr << ',';
              }
              first = false;
              terminal_to_string(pack_context.for_variable(v), std::cerr);
            }
          }
          std::cerr << "} <- ";
          auto terms = nf_to_terminals(candidates[0]);
          terminals_to_string(terms, std::cerr);
          std::cerr << '\n';
        }
        nf = std::move(candidates[0]);
      }
    }
    if (is_conflicted) {
      if (LOGGING(5)) {
        std::cerr << "conflict encountered because of: ";
        bool first = true;
        for (const auto &pm : packet_methods) {
          if (!first) std::cerr << ',';
          first = false;
          std::cerr << pm;
        }
        std::cerr << ", blocking\n";
      }
      slv.pop();

      z3::expr_vector all(slv.ctx());
      for (const auto &nd : path) {
        all.push_back(edgeFormulas.nodeLabel(nd));
      }
      slv.add(!z3::mk_and(all));
      if (slv.check() == z3::check_result::unsat) {
        LOG5("answer is now unsat");
        END(solving);
        std::cerr << "unsat in " << nriters << " iters, " << DURATION(solving)
                  << "ms\n";
        return false;
      }
      model = slv.get_model();
    } else {
      slv.pop();
      END(solving);
      std::cerr << "sat in " << nriters << " iters, " << DURATION(solving)
                << "ms\n";
      LOG5("answer remains sat");
      // means: last model which was adjusted is ok
      return true;
    }
  }
}
bool analysis::ExplicitUB::ispackMethod_(const IR::Node *instr, bool all) {
  if (auto mcs = instr->to<IR::MethodCallStatement>()) {
    if (auto ef = P4::MethodInstance::resolve(mcs, refMap, typeMap)
                      ->to<P4::ExternFunction>()) {
      if (isPacketMethod(ef->method->name.name, all)) {
        return true;
      }
    }
  } else if (auto asg = instr->to<IR::AssignmentStatement>()) {
    auto rt = typeMap->getType(asg->right);
    if (auto te = rt->to<IR::Type_Newtype>()) {
      if (te->name.name == AnalysisLibrary::instance.packetModel.name) {
        return true;
      }
    }
  }
  return false;
}
bool analysis::ExplicitUB::isPacketMethod(cstring nm, bool all) {
  return nm == AnalysisLibrary::instance.packetModel.peek.name ||
         nm == AnalysisLibrary::instance.packetModel.pop.name ||
         nm == AnalysisLibrary::instance.packetModel.copy.name ||
         nm == AnalysisLibrary::instance.packetModel.zero.name ||
         nm == AnalysisLibrary::instance.packetModel.emit.name ||
         nm == AnalysisLibrary::instance.packetModel.advance.name ||
         (all && nm == AnalysisLibrary::instance.packetModel.prepend.name);
}
