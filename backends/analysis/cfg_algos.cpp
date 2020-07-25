//
// Created by dragos on 17.12.2018.
//
#include <common/resolveReferences/referenceMap.h>
#include <p4/callGraph.h>
#include <p4/evaluator/evaluator.h>
#include <p4/typeChecking/typeConstraints.h>
#include <p4/typeChecking/typeUnification.h>

#include <analysis/ub/AnalysisContext.h>
#include <analysis/ub/loop.h>
#include <boost/pending/disjoint_sets.hpp>
#include <boost/property_map/property_map.hpp>
#include <utility>

#include "MakeImplementations.h"
#include "analysis_helpers.h"
#include "cfg_algos.h"

size_t analysis::node_t::LABEL = 1;

analysis::node_t analysis::ComputeGraph::create(const IR::Node *thisnode,
                                                NodeType type) {
  node_t n(thisnode, type);
  for (auto &o : outstanding) {
    o.first->second.emplace_back(n, o.second);
  }
  return n;
}

analysis::EdgeHolder *
analysis::ComputeGraph::mk_cfg(const IR::P4Control *ctrl) {
  auto eh = get_forward(ctrl->body);
  return eh;
}

void analysis::ComputeGraph::makeOutstanding() {
  if (!this->outstanding.empty()) {
    // there are still hanging nodes (aka return statements,
    // maybe last statements) - need to connect them to an
    // artificial empty statement
    auto artificial = new IR::EmptyStatement();

    for (auto &out : this->outstanding) {
      LOG4("[terminal]:" << out.first->first);
    }
    create(artificial, NodeType::END);
    this->outstanding.clear();
  }
}

analysis::EdgeHolder *
analysis::ComputeGraph::get_forward(const IR::P4Control *ctrl) {
  auto cfg = mk_cfg(ctrl);
  setLabel(cfg);
  return cfg;
}

analysis::EdgeHolder *
analysis::ComputeGraph::get_backward(const IR::P4Control *ctrl) {
  auto it = reverse_graphs.emplace(ctrl, EdgeHolder());
  if (it.second) {
    auto fw = get_forward(ctrl);
    auto bw = &it.first->second;
    for (auto &fwedges : *fw) {
      for (auto &ed : fwedges.second) {
        (*bw)[ed.first].emplace_back(fwedges.first, ed.second);
      }
    }
  }
  return &(it.first->second);
}

namespace analysis {
bool node_t::operator<(const node_t &other) const {
  if (node != other.node)
    return node < other.node;
  if (type != other.type)
    return type < other.type;
  return label < other.label;
}

const IR::Node *node_t::operator->() const { return node; }

std::ostream &operator<<(std::ostream &os, const node_t &n) {
  switch (n.type) {
  case NodeType::NORMAL:
    break;
  case NodeType::START:
    os << "start:";
    break;
  case NodeType::END:
    os << "end:";
    break;
  case NodeType::CALL:
    os << "call:";
    break;
  case NodeType::RETURN:
    os << "return:";
    break;
  case NodeType::UNKNOWN:
    os << "unknown";
    break;
  }
  if (n.node) {
    if (n.node->is<IR::IfStatement>()) {
      return os << n.node->to<IR::IfStatement>()->condition;
    } else if (n.node->is<IR::SelectExpression>()) {
      return os << n.node->to<IR::SelectExpression>()->select;
    } else if (n.node->is<IR::Vector<IR::Node>>()) {
      auto vec = n.node->to<IR::Vector<IR::Node>>();
      bool first = true;
      for (const auto instr : *vec) {
        if (!first)
          os << '\n';
        first = false;
        os << node_t(instr);
      }
      return os;
    }
    return os << n.node;
  }
  return os;
}
#define NORMAL_NODE(n)                                                         \
  ((n.type == NodeType::NORMAL || n.type == NodeType::START))
boost::optional<assign_t> is_assign(node_t n) {
  if (!NORMAL_NODE(n))
    return {};
  if (n.node->is<IR::AssignmentStatement>())
    return assign_t(n.node->to<IR::AssignmentStatement>());
  return {};
}

boost::optional<assign_ret_t> is_assign_ret(node_t n) {
  if (n.type != NodeType::CALL && n.type != NodeType::RETURN)
    return {};
  if (n.node->is<IR::AssignmentStatement>()) {
    auto asg = n.node->to<IR::AssignmentStatement>();
    auto mem = asg->right->to<IR::MethodCallExpression>();
    if (mem) {
      return assign_ret_t(asg->left, mem, n.type);
    }
  }
  return {};
}

boost::optional<return_t> is_return(node_t n) {
  if (!NORMAL_NODE(n) || !n.node->is<IR::ReturnStatement>())
    return {};
  return return_t(n.node->to<IR::ReturnStatement>()->expression);
}

boost::optional<method_call_t> is_method_call(node_t n) {
  if (n.type != NodeType::CALL)
    return {};
  if (n.node->is<IR::MethodCallStatement>()) {
    auto asg = n.node->to<IR::MethodCallStatement>();
    return method_call_t(asg, n.type);
  }
  return {};
}

boost::optional<method_call_t> is_extern_method_call(node_t n) {
  if (NORMAL_NODE(n) && n.node->is<IR::MethodCallStatement>()) {
    return method_call_t(n.node->to<IR::MethodCallStatement>(), n.type);
  }
  return {};
}

boost::optional<var_decl_t> is_var_decl(node_t n) {
  if (!NORMAL_NODE(n) || !n.node->is<IR::Declaration>())
    return {};
  return var_decl_t(n.node->to<IR::Declaration>());
}

boost::optional<assign_ret_t> is_extern_assign_ret(node_t n) {
  if (!NORMAL_NODE(n))
    return {};
  if (n.node->is<IR::AssignmentStatement>()) {
    auto asg = n.node->to<IR::AssignmentStatement>();
    auto mem = asg->right->to<IR::MethodCallExpression>();
    if (mem) {
      return assign_ret_t(asg->left, mem, n.type);
    }
  }
  return {};
}

const IR::Vector<IR::Node> *is_basic_block(node_t n) {
  return n.node->to<IR::Vector<IR::Node>>();
}

node_iterator instructions(node_t n) {
  if (n.node->is<IR::Vector<IR::Node>>()) {
    return n.node->to<IR::Vector<IR::Node>>();
  }
  return n.node;
}

const IR::Node *instruction_at(node_t n, unsigned i) {
  if (n.node->is<IR::Vector<IR::Node>>()) {
    return n.node->to<IR::Vector<IR::Node>>()->at(i);
  }
  if (i == 0)
    return n.node;
  return nullptr;
}

std::string node_t::nodeId() const {
  auto id_ = id(node);
  char str[100];
  snprintf(str, 99, "%ld%d%016ld", label, (int)type, id_);
  return std::string(str);
}
std::vector<const IR::Expression *> getMatch(const IR::SelectCase *selcase) {
  auto ks = selcase->keyset;
  const IR::ListExpression *lexp = nullptr;
  if (!ks->is<IR::ListExpression>()) {
    lexp = new IR::ListExpression({ks});
  } else {
    lexp = ks->to<IR::ListExpression>();
  }
  std::vector<const IR::Expression *> mat;
  for (auto exp : lexp->components)
    mat.push_back(exp);
  return mat;
}

node_iterator::node_iterator(const IR::Vector<IR::Node> *nodes)
    : nodes(nodes) {}

node_iterator::node_iterator(const IR::Node *singleton)
    : singleton(singleton) {}
}

void analysis::ComputeGraph::compute_cfg(
    const IR::P4Parser *ctrl, const IR::ParserState *state,
    std::map<const IR::ParserState *, node_t> &visited,
    std::vector<node_t> &finals) {
  BUG_CHECK(outstanding.size() <= 1, "can't have more than one outstanding");
  auto EMI = visited.emplace(state, nullptr);
  if (EMI.second) {
    bool any_good_instructions = false;
    if (!outstanding.empty()) {
      auto lastPtr = outstanding.back();
      auto eenum = outstanding.back().first->second.size();
      if (!state->components.empty())
        state->components.apply(*this);
      if (lastPtr.first->second.size() != eenum) {
        // means that a CFG node was added as a result
        // of call to apply
        any_good_instructions = true;
        auto myfirst = lastPtr.first->second[eenum];
        EMI.first->second = myfirst.first;
      } else {
        // add artificial empty statement when
        // selex is null and there are no "useful"
        // instructions in the parserState (e.g. accept and reject)
        if (state->selectExpression) {
          EMI.first->second = state->selectExpression;
        } else {
          EMI.first->second = new IR::EmptyStatement();
        }
        create(EMI.first->second);
      }
    } else {
      // outstanding is empty iff this is the first call to
      // get_cfg => automatically set start node to NodeType::START
      if (!state->components.empty())
        state->components.apply(*this);
      if (!forward.empty()) {
        // means that something useful got for this state,
        // good to be the first
        any_good_instructions = true;
        EMI.first->second = find_start_node(&forward);
      } else {
        if (state->selectExpression) {
          EMI.first->second = state->selectExpression;
        } else {
          EMI.first->second = new IR::EmptyStatement();
        }
        create(EMI.first->second);
      }
    }
    if (!state->selectExpression) {
      // if no selex exists => return and add to finals
      if (any_good_instructions) {
        // there are some instructions here
        for (auto &o : outstanding) {
          finals.emplace_back(o.first->first);
        }
      } else {
        // there are no instructions, nor returns
        finals.emplace_back(EMI.first->second);
      }
      return;
    }
    EdgeHolder::iterator I;
    if (!any_good_instructions) {
      // at this point, we have that state->selectExpression != nullptr
      // no useful instructions => state->selectExpression was created
      // and added to the graph
      I = addNode(EMI.first->second);
    } else {
      I = addNode(create(state->selectExpression));
    }
    outstanding.clear();
    if (auto pe = state->selectExpression->to<IR::PathExpression>()) {
      auto foreign =
          ctrl->getDeclByName(pe->path->name.name)->to<IR::ParserState>();
      outstanding.emplace_back(I, 0);
      compute_cfg(ctrl, foreign, visited, finals);
    } else if (auto se = state->selectExpression->to<IR::SelectExpression>()) {
      bool has_default = false;
      unsigned i = 0;
      for (; i != se->selectCases.size(); ++i) {
        outstanding.clear();
        outstanding.emplace_back(I, i);
        auto sc = se->selectCases[i];
        if (sc->keyset->is<IR::DefaultExpression>())
          has_default = true;
        auto sname = sc->state->path->name.name;
        auto foreign = ctrl->getDeclByName(sname)->to<IR::ParserState>();
        compute_cfg(ctrl, foreign, visited, finals);
      }
      if (!has_default) {
        outstanding.clear();
        outstanding.emplace_back(I, i);
        auto sname = IR::ParserState::reject;
        auto foreign = ctrl->getDeclByName(sname)->to<IR::ParserState>();
        compute_cfg(ctrl, foreign, visited, finals);
      }
    }
  } else {
    create(EMI.first->second);
  }
}

analysis::EdgeHolder *
analysis::ComputeGraph::get_forward(const IR::P4Parser *p4Parser) {
  auto eh = new analysis::EdgeHolder();
  std::map<const IR::ParserState *, EdgeHolder> holder;
  std::map<const IR::ParserState *, node_t> starting_points;
  std::vector<node_t> finals;
  auto startstate =
      p4Parser->getDeclByName(IR::ParserState::start)->to<IR::ParserState>();
  forward.clear();
  outstanding.clear();
  compute_cfg(p4Parser, startstate, starting_points, finals);
  node_t artificial(new IR::EmptyStatement(), NodeType::END);
  for (auto final : finals) {
    forward[final].emplace_back(artificial, toNumber(EdgeType::NORMAL));
  }
  outstanding.clear();
  *eh = std::move(forward);
  setLabel(eh);
  auto start_nodes = find_start_nodes(eh);
  if (start_nodes.size() > 1) {
    auto ISt = std::find_if(
        start_nodes.begin(), start_nodes.end(),
        [](const node_t &nd) { return nd.type == NodeType::START; });
    if (ISt != start_nodes.end()) {
      removeDeadNodes(eh, *ISt);
    } else {
      BUG("no start node found in %1%", p4Parser);
    }
  }
  //  return analysis::unroll(eh, starting_points[startstate], 2);
  return eh;
}

bool analysis::ComputeGraph::preorder(const IR::IfStatement *stat) {
  auto I = addNode(create(stat));
  outstanding.clear();
  outstanding.emplace_back(I, 1);
  visit(stat->ifTrue);
  auto last_outstanding = std::move(outstanding);
  outstanding.clear();
  outstanding.emplace_back(I, 0);
  if (stat->ifFalse)
    visit(stat->ifFalse);
  outstanding.insert(outstanding.end(), last_outstanding.begin(),
                     last_outstanding.end());
  return false;
}

analysis::EdgeHolder::iterator
analysis::ComputeGraph::addNode(analysis::node_t n) {
  if (forward.empty()) {
    n.type = NodeType::START;
  }
  auto I = forward.emplace(n, analysis::EdgeEnumerator()).first;
  return I;
}

bool analysis::ComputeGraph::preorder(const IR::StatOrDecl *n) {
  auto I = addNode(create(n));
  outstanding.clear();
  outstanding.emplace_back(I, 0);
  return false;
}

bool analysis::ComputeGraph::preorder(const IR::MethodCallStatement *mcs) {
  auto n = create(mcs);
  outstanding.clear();
  if (!is_bug(mcs) && !is_send(mcs) && !is_drop(mcs) && !is_oob(mcs)) {
    outstanding.emplace_back(addNode(n), 0);
  }
  return false;
}

bool analysis::ComputeGraph::preorder(const IR::ParserState *n) {
  visit(n->components);
  return false;
}

analysis::EdgeHolder *
analysis::ComputeGraph::get_forward(const IR::Function *fun) {
  auto cfg = get_forward(fun->body);
  setLabel(cfg);
  return cfg;
}

analysis::EdgeHolder *
analysis::ComputeGraph::get_forward(const IR::Statement *stat) {
  forward.clear();
  outstanding.clear();
  stat->apply(*this);
  makeOutstanding();
  auto eh = new analysis::EdgeHolder();
  *eh = std::move(forward);
  if (eh->empty()) {
    // statement is empty
    node_t dumbStart(new IR::EmptyStatement(), NodeType::START);
    node_t dumbEnd(new IR::EmptyStatement(), NodeType::END);
    (*eh)[dumbStart].emplace_back(dumbEnd, 0);
  }
  return eh;
}

void topo_sort_util(const analysis::EdgeHolder *fwgraph, analysis::node_t v,
                    std::unordered_set<analysis::node_t> &visited,
                    std::vector<analysis::node_t> &sorted) {
  visited.emplace(v);
  auto neighsIT = fwgraph->find(v);
  if (neighsIT != fwgraph->end()) {
    const auto &neighs = neighsIT->second;
    for (const auto &n : neighs) {
      if (!visited.count(n.first))
        topo_sort_util(fwgraph, n.first, visited, sorted);
    }
  }
  sorted.emplace_back(v);
}

std::vector<analysis::node_t>
analysis::topo_sort(const analysis::EdgeHolder *fwgraph) {
  std::vector<analysis::node_t> sorted;
  std::unordered_set<analysis::node_t> visited;
  // Mark the current node as visited.
  for (const auto &p : *fwgraph) {
    if (!visited.count(p.first)) {
      topo_sort_util(fwgraph, p.first, visited, sorted);
    }
  }
  return sorted;
}
std::vector<analysis::node_t>
analysis::topo_sort(const analysis::EdgeHolder *fwgraph, node_t start) {
  std::vector<analysis::node_t> sorted;
  std::unordered_set<analysis::node_t> visited;
  // Mark the current node as visited.
  topo_sort_util(fwgraph, start, visited, sorted);
  return sorted;
}

void classify(const analysis::EdgeHolder *graph, analysis::node_t start,
              std::map<analysis::node_t, int> &start_times,
              std::map<analysis::node_t, int> &end_times,
              std::set<analysis::node_t> &visited, int &clock) {
  //    start[u] = clock; clock = clock + 1
  //    visited[u] = true
  //    for each successor v of u:
  //      if not visited[v]:
  //        AnnotatedDFS(v, u)
  //    end[u] = clock; clock = clock + 1
  start_times[start] = clock;
  ++clock;
  visited.emplace(start);
  auto I = graph->find(start);
  if (I != graph->end()) {
    for (auto &neigh : I->second) {
      if (!visited.count(neigh.first)) {
        classify(graph, neigh.first, start_times, end_times, visited, clock);
      }
    }
  }
  end_times[start] = clock;
  ++clock;
}

void analysis::classify(const analysis::EdgeHolder *graph,
                        analysis::node_t start,
                        std::map<analysis::node_t, int> &start_times,
                        std::map<analysis::node_t, int> &end_times) {
  std::set<node_t> visited;
  int clock = 0;
  ::classify(graph, start, start_times, end_times, visited, clock);
}

void analysis::find_back_edges(const analysis::EdgeHolder *graph,
                               analysis::node_t start,
                               std::vector<FullEdge_t> &back,
                               std::vector<FullEdge_t> &tree,
                               std::vector<FullEdge_t> &cross) {
  std::map<analysis::node_t, int> start_times, end_times;
  classify(graph, start, start_times, end_times);
  for (auto &p : *graph) {
    for (auto &neigh : p.second) {
      /*  start[u] > start[v] && end[u] > end[v] */
      if (start_times[p.first] > start_times[neigh.first] &&
          end_times[p.first] > end_times[neigh.first])
        cross.emplace_back(p.first, neigh.first, neigh.second);
      /*start[u] > start[v]; end[u] < end[v]*/
      if (start_times[p.first] > start_times[neigh.first] &&
          end_times[p.first] < end_times[neigh.first])
        back.emplace_back(p.first, neigh.first, neigh.second);
      /*start[u] < start[v]; end[u] > end[v]*/
      if (start_times[p.first] < start_times[neigh.first] &&
          end_times[p.first] > end_times[neigh.first])
        tree.emplace_back(p.first, neigh.first, neigh.second);
    }
  }
}
std::set<analysis::node_t>
analysis::find_start_nodes(const analysis::EdgeHolder *graph) {
  std::set<analysis::node_t> encountered;
  std::set<analysis::node_t> with_neighs;
  for (auto &p : *graph) {
    if (!with_neighs.count(p.first))
      encountered.emplace(p.first);
    for (auto &target : p.second) {
      encountered.erase(target.first);
      with_neighs.emplace(target.first);
    }
  }
  return encountered;
}
analysis::node_t analysis::find_start_node(const analysis::EdgeHolder *graph) {
  auto encountered = find_start_nodes(graph);
  return *encountered.begin();
}

void compute_idominators(
    const analysis::EdgeHolder *graph, const analysis::EdgeHolder *bw,
    analysis::node_t start,
    std::map<analysis::node_t, std::set<analysis::node_t>> &dominators) {
  analysis::compute_dominators(graph, bw, start, dominators);
  // x \in rev_dominators[n] <=> n dom x
  // x \in dominators[n] <=> x dom n
  std::map<analysis::node_t, std::set<analysis::node_t>> idoms;
  for (auto &d : dominators) {
    auto N = d.first;
    for (auto M : d.second) {
      if (M != N) {
        // M sdom N
        bool isidom = true;
        for (auto P : d.second) {
          if (P != N) {
            // P sdom N
            auto Mdominators = dominators.find(M);
            if (Mdominators == dominators.end()) {
              isidom = false;
              break;
            } else {
              if (!Mdominators->second.count(P)) {
                isidom = false;
                break;
              }
              // else means that P dom M
            }
          }
        }
        if (isidom) {
          // \forall P s.t. P sdom N => P sdom M
          idoms[M].emplace(N);
        }
      }
    }
  }
  dominators = std::move(idoms);
}

void analysis::compute_dominators(
    const analysis::EdgeHolder *graph, const analysis::EdgeHolder *bw,
    analysis::node_t start,
    std::map<analysis::node_t, std::set<analysis::node_t>> &dominators) {
  std::vector<analysis::node_t> worklist;
  worklist.emplace_back(start);
  while (!worklist.empty()) {
    auto last = worklist.back();
    worklist.pop_back();
    std::set<analysis::node_t> new_set;
    bool all = true;
    auto IBW = bw->find(last);
    if (IBW == bw->end() || IBW->second.empty()) {
      all = false;
    } else {
      for (const auto &pred : bw->find(last)->second) {
        if (!all && new_set.empty())
          break;
        std::set<analysis::node_t> tmp;
        auto preddomI = dominators.find(pred.first);
        if (preddomI != dominators.end()) {
          if (all) {
            tmp = preddomI->second;
          } else {
            std::set_intersection(preddomI->second.begin(),
                                  preddomI->second.end(), new_set.begin(),
                                  new_set.end(),
                                  std::inserter(tmp, tmp.begin()));
          }
          all = false;
        }
        new_set = std::move(tmp);
      }
    }
    if (!all) {
      new_set.emplace(last);
    }
    auto mylastI = dominators.find(last);
    bool trigger = false;
    if (mylastI != dominators.end()) {
      if (all) {
        // unreachable in principle
        dominators.erase(mylastI);
        trigger = true;
      } else {
        if (new_set != mylastI->second) {
          mylastI->second = std::move(new_set);
          trigger = true;
        }
      }
    } else {
      if (!all) {
        trigger = true;
        dominators.emplace(last, std::move(new_set));
      }
    }
    if (trigger) {
      auto I = graph->find(last);
      if (I != graph->end()) {
        for (auto &neigh : graph->find(last)->second) {
          worklist.emplace_back(neigh.first);
        }
      }
    }
  }
}

std::vector<analysis::node_t>
compute_ancestors(std::map<analysis::node_t, analysis::node_t> &tree_parents,
                  analysis::node_t A) {
  auto crt = A;
  std::vector<analysis::node_t> nodes;
  while (true) {
    auto I = tree_parents.find(crt);
    if (I != tree_parents.end()) {
      nodes.push_back(crt);
      crt = I->second;
    } else {
      break;
    }
  }
  return nodes;
}

void analysis::compute_cdg(
    analysis::EdgeHolder *graph, analysis::EdgeHolder *bw,
    NodeValues<std::unordered_set<analysis::node_t>> &dependency) {
  std::map<analysis::node_t, std::set<analysis::node_t>> postdoms;
  auto start = find_start_node(bw);
  compute_idominators(bw, graph, start, postdoms);
  std::map<analysis::node_t, analysis::node_t> tree_parents;
  LOG4("immediate postdominators:");
  for (auto &d : postdoms) {
    for (auto n : d.second) {
      // d.first ipdom n
      tree_parents[n] = d.first;
      LOG4(d.first << " ipdom " << n);
    }
  }
  std::set<std::tuple<analysis::node_t, analysis::node_t, int>> S;
  for (auto &p : *graph) {
    auto A = p.first;
    for (auto &nxt : p.second) {
      auto B = nxt.first;
      bool bAncestor = false;
      node_t crt = A;
      // walk ipdom up starting from A.
      // if B is found in the tree => B postdominates A
      // if not => need to add this edge to CDG
      while (!bAncestor) {
        if (crt == B) {
          bAncestor = true;
        } else {
          auto I = tree_parents.find(crt);
          if (I != tree_parents.end())
            crt = I->second;
          else
            break;
        }
      }
      if (!bAncestor)
        S.emplace(A, B, nxt.second);
    }
  }
  for (auto &edge : S) {
    auto A = std::get<0>(edge);
    auto B = std::get<1>(edge);
    std::vector<analysis::node_t> AAncestors =
        compute_ancestors(tree_parents, A);
    std::vector<analysis::node_t> BAncestors =
        compute_ancestors(tree_parents, B);
    auto IA = AAncestors.rbegin();
    auto IB = BAncestors.rbegin();
    // invariant: all nodes share common ancestor in ipdom tree
    while (*IA == *IB) {
      ++IA;
      ++IB;
    }
    auto L = *IB;
    bool includesA = (L == A);
    auto &depa = dependency[A];
    while (IB != BAncestors.rend()) {
      if (*IB != A || includesA)
        depa.emplace(*IB);
      ++IB;
    }
  }
}

void analysis::print_graph(const analysis::EdgeHolder *graph, bool withHeader,
                           std::ostream &os) {
  if (withHeader)
    os << "digraph G {\n";
  std::set<node_t> nodes;
  for (auto &n : *graph) {
    if (nodes.emplace(n.first).second) {
      os << n.first.nodeId() << " [label=\"" << n.first << "\"];\n";
    }
    for (auto neigh : n.second) {
      if (nodes.emplace(neigh.first).second) {
        os << neigh.first.nodeId() << " [label=\"" << neigh.first << "\"];\n";
      }
      os << n.first.nodeId() << " -> " << neigh.first.nodeId() << ";\n";
    }
  }
  if (withHeader)
    os << "}";
}

analysis::CFG::CFG(const IR::Node *maps_to, analysis::EdgeHolder holder, bool)
    : maps_to(maps_to) {
  this->holder = std::move(holder);
  if (!this->holder.empty())
    start_node = analysis::find_start_node(&this->holder);
  else
    start_node = node_t::before();
  auto ends = analysis::findEndNodes(&this->holder, start_node);
  bool found = false;
  if (maps_to) {
    if (this->holder.empty())
      return;
    for (auto &n : ends) {
      if (n.type == NodeType::END) {
        if (found)
          BUG("CFG for %1% wrong, has 2x end nodes", maps_to);
        found = true;
        end_node = n;
      }
    }
    if (!found)
      end_node = node_t::before();
    //    BUG_CHECK(found, "CFG for %1% wrong, has no end node", maps_to);
  }
}
namespace analysis {
std::ostream &operator<<(std::ostream &os, const analysis::CFG &cfg) {
  os << "cfg: ";
  if (cfg.maps_to)
    cfg.maps_to->dbprint(os);
  os << "\n";
  analysis::print_graph(&cfg.holder, true, os);
  os << "\n";

  if (cfg.start_node) {
    os << "start:";
    cfg.start_node->dbprint(os);
  }
  if (cfg.end_node) {
    os << "\nend:";
    cfg.end_node->dbprint(os);
  }
  return os;
}

bool is_a_dag(EdgeHolder *holder, analysis::node_t start,
              std::vector<analysis::node_t> &sorted) {
  P4::CallGraph<analysis::node_t> callGraph("");
  for (auto &p : *holder) {
    callGraph.add(p.first);
    for (auto &n : p.second) {
      callGraph.add(n.first);
      callGraph.calls(p.first, n.first);
    }
  }
  return !callGraph.sccSort(start, sorted);
}

EdgeType edgeType(const Edge &e) {
  auto et = e.second;
  return edgeType(et);
}

EdgeType edgeType(int et) {
  if (et >= 0)
    return EdgeType::NORMAL;
  else if (et < 0) {
    if (et == -1)
      return EdgeType::CALL;
    else if (et == -2)
      return EdgeType::RETURN;
    else if (et == -3)
      return EdgeType::CALL_TO_RETURN;
    else if (et == -4)
      return EdgeType::GOTO;
    else
      return EdgeType::UNKNOWN;
  }
  return EdgeType::UNKNOWN;
}

class IsACall : public Inspector {
  bool isACall;
  static IsACall *instance;
  IsACall() {}
  static IsACall *getInstance() {
    if (!instance) {
      instance = new IsACall();
    }
    return instance;
  }
  bool preorder(const IR::MethodCallExpression *) override {
    isACall = true;
    return false;
  }
  bool preorder(const IR::Node *) override { return !isACall; }
  bool nodeHasCalls(const IR::Node *n) {
    isACall = false;
    n->apply(*this);
    return isACall;
  }

public:
  static bool hasCalls(const IR::Node *node) {
    return getInstance()->nodeHasCalls(node);
  }
};
IsACall *IsACall::instance = nullptr;
bool isCall(const IR::Node *node) { return IsACall::hasCalls(node); }

EdgeHolder clone(EdgeHolder *holder, node_t &newstart) {
  auto L = node_t::LABEL;
  ++node_t::LABEL;
  newstart.label = L;
  EdgeHolder ret;
  for (auto &n : *holder) {
    auto newnode = n.first;
    newnode.label = L;
    auto &crt = (ret[newnode] = n.second);
    for (auto &c : crt) {
      c.first.label = L;
    }
  }
  return ret;
}

P4::CallGraph<node_t> mkCallGraph(const EdgeHolder *holder) {
  P4::CallGraph<node_t> thisgraph("");
  for (auto n : *holder) {
    thisgraph.add(n.first);
    for (auto &neigh : n.second) {
      thisgraph.calls(n.first, neigh.first);
    }
  }
  return std::move(thisgraph);
}
std::unordered_map<node_t, unsigned>
sccIndices(std::vector<std::unordered_set<node_t>> &sccs) {
  unsigned idx = 0;
  std::unordered_map<node_t, unsigned> ret;
  for (; idx != sccs.size(); ++idx) {
    auto &scc = sccs[idx];
    for (auto n : scc)
      ret[n] = idx;
  }
  return std::move(ret);
}

void setLabel(EdgeHolder *holder, std::size_t L) {
  EdgeHolder nxt;
  for (auto &n : *holder) {
    auto cp = n.first;
    cp.label = L;
    auto &crt = (nxt[cp] = std::move(n.second));
    for (auto &c : crt) {
      c.first.label = L;
    }
  }
  *holder = std::move(nxt);
}

std::unordered_set<node_t> findEndNodes(EdgeHolder *holder, node_t start) {
  std::unordered_set<node_t> end;
  traverse_df_pernode(holder, start, [&end, holder](node_t n) {
    auto I = holder->find(n);
    if (I != holder->end()) {
      if (I->second.empty())
        end.emplace(n);
    } else {
      end.emplace(n);
    }
  });
  return end;
}
std::unordered_set<node_t> terminals(const EdgeHolder &holder) {
  std::unordered_set<node_t> end;
  for (auto &n : holder) {
    if (n.second.empty())
      end.emplace(n.first);
    for (auto &x : n.second) {
      auto NIt = holder.find(x.first);
      if (NIt == holder.end())
        end.emplace(x.first);
    }
  }
  return end;
}

void basic_blocks(const EdgeHolder &graph, const EdgeHolder &rgraph,
                  const node_t &start, EdgeHolder &basicBlockGraph,
                  EdgeHolder &rBasicBlockGraph, node_t &basicBlockStart) {
  std::unordered_map<node_t, size_t> resolved;
  std::vector<BasicBlock> blocks;
  std::vector<BasicBlock> stack({{start}});
  while (!stack.empty()) {
    auto crt = std::move(stack.back());
    stack.pop_back();
    while (true) {
      auto last = crt.back();
      BUG_CHECK(resolved.emplace(last, blocks.size()).second,
                "processing twice the same node %1% (%2%)", last,
                last.nodeId());
      auto Is = graph.find(last);
      if (Is != graph.end() && Is->second.size() == 1) {
        auto succ = Is->second.begin()->first;
        auto Iprds = rgraph.find(succ);
        if (Iprds == rgraph.end() || Iprds->second.size() <= 1) {
          crt.push_back(succ);
        } else {
          if (!resolved.count(succ)) {
            stack.emplace_back(BasicBlock({succ}));
          }
          break;
        }
      } else {
        if (Is != graph.end()) {
          for (auto &succP : Is->second) {
            auto &succ = succP.first;
            if (!resolved.count(succ))
              stack.emplace_back(BasicBlock({succ}));
          }
        }
        break;
      }
    }
    blocks.push_back(std::move(crt));
  }
  std::vector<node_t> nodes;
  for (auto &blk : blocks) {
    auto nodevector = new IR::Vector<IR::Node>();
    for (auto &instr : blk) {
      nodevector->push_back(instr.node);
    }
    nodes.emplace_back(nodevector);
  }
  auto J = nodes.begin();
  for (auto &blk : blocks) {
    auto &last = blk.back();
    auto &first = blk.front();
    auto Isuccs = graph.find(last);
    if (Isuccs != graph.end()) {
      for (auto &succ : Isuccs->second) {
        auto idx = resolved[succ.first];
        auto &nd = nodes[idx];
        basicBlockGraph[*J].emplace_back(nd, succ.second);
      }
    }
    auto IPreds = rgraph.find(first);
    if (IPreds != rgraph.end()) {
      for (auto &pred : IPreds->second) {
        auto idx = resolved[pred.first];
        auto &nd = nodes[idx];
        rBasicBlockGraph[*J].emplace_back(nd, pred.second);
      }
    }
    ++J;
  }
  basicBlockStart = nodes[resolved[start]];
}

void basic_blocks(const EdgeHolder &graph, const node_t &start,
                  EdgeHolder &basicBlockGraph, EdgeHolder &rBasicBlockGraph,
                  node_t &basicBlockStart) {
  auto rgraph = std::move(*reverse(&graph));
  basic_blocks(graph, rgraph, start, basicBlockGraph, rBasicBlockGraph,
               basicBlockStart);
}

void dom_frontier(const EdgeHolder &graph, const EdgeHolder &rgraph,
                  const node_t &start,
                  std::unordered_map<node_t, std::vector<node_t>> &children,
                  EdgeHolder &domf) {
  auto sorted = analysis::topo_sort(&graph);
  std::unordered_map<node_t, unsigned> reverseSorted;
  BUG_CHECK(sorted.back() == start, "clean up graph from dead nodes");
  {
    unsigned idx = 0;
    for (auto &n : sorted) {
      reverseSorted[n] = idx;
      ++idx;
    }
  }
  std::vector<unsigned> ddoms;
  ddoms.resize(sorted.size(), static_cast<const unsigned int &>(sorted.size()));
  ddoms.back() = static_cast<unsigned int>(sorted.size() - 1);
  auto intersect = [&](unsigned n1, unsigned n2) {
    auto finger1 = n1;
    auto finger2 = n2;
    while (finger1 != finger2) {
      while (finger1 < finger2) {
        finger1 = ddoms[finger1];
      }
      while (finger2 < finger1) {
        finger2 = ddoms[finger2];
      }
    }
    return finger1;
  };
  bool changed = true;
  while (changed) {
    changed = false;
    for (int i = static_cast<int>(sorted.size() - 2); i >= 0; --i) {
      auto &b = sorted[i];
      auto Ipreds = rgraph.find(b);
      if (Ipreds != rgraph.end() && !Ipreds->second.empty()) {
        auto J = Ipreds->second.begin();
        auto newidom = reverseSorted[J->first];
        ++J;
        for (; J != Ipreds->second.end(); ++J) {
          auto p = reverseSorted[J->first];
          if (ddoms[p] != sorted.size()) {
            newidom = intersect(p, newidom);
          }
        }
        if (ddoms[i] != newidom) {
          ddoms[i] = newidom;
          changed = true;
        }
      }
    }
  }
  std::vector<std::set<std::pair<unsigned, int>>> df(sorted.size());
  for (unsigned i = 0; i != sorted.size(); ++i) {
    auto &b = sorted[i];
    auto Ipreds = rgraph.find(b);
    if (Ipreds != rgraph.end() && Ipreds->second.size() > 1) {
      for (auto &pp : Ipreds->second) {
        auto &p = pp.first;
        auto runner = reverseSorted[p];
        while (runner != ddoms[i]) {
          df[runner].emplace(i, pp.second);
          runner = ddoms[runner];
        }
      }
    }
  }
  for (unsigned i = 0; i != sorted.size(); ++i) {
    auto &b = sorted[i];
    auto &xx = domf[b];
    auto &bdf = df[i];
    for (auto idx : bdf) {
      xx.emplace_back(sorted[idx.first], idx.second);
    }
  }
  for (int i = static_cast<int>(sorted.size()) - 2; i >= 0; --i) {
    auto parent = ddoms[i];
    children[sorted[parent]].emplace_back(sorted[i]);
  }
}

EdgeHolder freshClone(EdgeHolder h, node_t &start, node_t &end,
                      NodeValues<analysis::node_t> *parents) {
  NodeValues<node_t> mappings;
  auto fun = [&](const node_t &nd) {
    return getOrEmplace(mappings, nd,
                        [&]() {
                          auto cl = nd.clone(++node_t::LABEL);
                          if (parents)
                            (*parents)[cl] = nd;
                          return cl;
                        })
        .first;
  };
  start = fun(start);
  end = fun(end);
  return gmap(h, std::ref(fun)).first;
}

EdgeHolder take_starting_from(const EdgeHolder &h, node_t last,
                              unsigned limit) {
  EdgeHolder subgraph;
  std::list<node_t> q({last});
  NodeSet total;
  while (!q.empty()) {
    auto last = q.back();
    q.pop_back();
    if (total.emplace(last).second) {
      if (total.size() > limit)
        break;
      auto Ineigh = h.find(last);
      if (Ineigh != h.end()) {
        for (const auto &nxt : Ineigh->second) {
          subgraph[last].push_back(nxt);
          q.push_front(nxt.first);
        }
      }
    }
  }
  return subgraph;
}

EdgeEnumerator neighbors_or_empty(const EdgeHolder &hld, node_t nd) {
  auto I = hld.find(nd);
  if (I != hld.end())
    return I->second;
  return {};
}

const EdgeEnumerator *neighbors_or_null(const EdgeHolder &hld, node_t nd) {
  auto I = hld.find(nd);
  if (I != hld.end())
    return &I->second;
  return nullptr;
}

void ensure_basic_blocks(EdgeHolder &basicBlockGraph,
                         EdgeHolder &rBasicBlockGraph,
                         node_t &basicBlockStart) {
  auto sorted = topo_sort(&basicBlockGraph, basicBlockStart);
  for (const auto &n : sorted) {
    if (auto rneighs = neighbors_or_null(rBasicBlockGraph, n)) {
      if (rneighs->size() == 1) {
        auto neigh = (*rneighs)[0].first;
        if (auto nneighs = neighbors_or_null(basicBlockGraph, neigh)) {
          if (nneighs->size() == 1) {
            BUG_CHECK((*nneighs)[0].first == n,
                      "invariant: x in fw[n] <=> n in bw[x]");
            // merge nodes
            auto mut = mutate(neigh);
            for (auto instr : instructions(n)) {
              mut->push_back(instr);
            }
            auto mn = mutate(n);
            mn->clear();
          }
        } else {
          BUG("invariant: x in fw[n] <=> n in bw[x]");
        }
      }
    }
  }
  trans_remove_empty(basicBlockGraph, basicBlockStart, sorted);
  NodeSet singleOutEmpty, zeroOutEmpty;
  traverse_df_pernode(&basicBlockGraph, basicBlockStart, [&](const node_t &nd) {
    if (isEmpty(nd)) {
      auto emp = true;
      if (auto neighs = neighbors_or_null(basicBlockGraph, nd)) {
        emp = neighs->empty();
      }
      if (emp)
        zeroOutEmpty.emplace(nd);
    }
  });
  removeDeadNodes(&basicBlockGraph, basicBlockStart,
                  [&](const node_t &nd) { return zeroOutEmpty.count(nd); });
  for (auto &blk : basicBlockGraph) {
    if (isEmpty(blk.first)) {
      if (blk.second.size() == 1) {
        singleOutEmpty.emplace(blk.first);
      }
    }
  }
  for (auto &blk : basicBlockGraph) {
    if (blk.second.size() == 1) {
      auto emp = blk.second[0].first;
      if (isEmpty(emp) && singleOutEmpty.count(emp)) {
        blk.second.clear();
        if (auto emptyneighs = neighbors_or_null(basicBlockGraph, emp)) {
          for (auto &e : *emptyneighs) {
            blk.second.emplace_back(e);
          }
        }
      }
    }
  }
  removeDeadNodes(&basicBlockGraph, basicBlockStart);
  rBasicBlockGraph = std::move(*reverse(&basicBlockGraph));
}

void trans_remove_empty(EdgeHolder &hcopy, const node_t &,
                        const std::vector<node_t> &newsort,
                        NodeValues<node_t> *transforms) {
  NodeValues<size_t> sizes;
  NodeValues<node_t> classes;
  boost::associative_property_map<NodeValues<size_t>> rank_pmap(sizes);
  boost::associative_property_map<NodeValues<node_t>> parent_pmap(classes);
  boost::disjoint_sets<boost::associative_property_map<NodeValues<size_t>>,
                       boost::associative_property_map<NodeValues<node_t>>>
      dsets(rank_pmap, parent_pmap);
  std::vector<std::pair<node_t, node_t>> outgoing; // empty -> non
  for (auto nd : make_reverse(newsort)) {
    if (isEmpty(nd) && !sizes.count(nd)) {
      dsets.make_set(nd);
      traverse_df(&hcopy, nd,
                  [&](const node_t &src, const std::pair<node_t, int> &ed) {
                    if (!isEmpty(ed.first))
                      return false;
                    if (!sizes.count(ed.first)) {
                      dsets.make_set(ed.first);
                    }
                    if (!sizes.count(src)) {
                      dsets.make_set(src);
                    }
                    dsets.union_set(src, ed.first);
                    return true;
                  });
    }
    if (isEmpty(nd)) {
      for (auto &ed : hcopy[nd])
        if (!isEmpty(ed.first))
          outgoing.emplace_back(nd, ed.first);
    } else {
      for (auto &ed : hcopy[nd])
        if (isEmpty(ed.first))
          outgoing.emplace_back(nd, ed.first);
    }
  }
  for (auto I = hcopy.begin(); I != hcopy.end();) {
    auto &x = *I;
    if (isEmpty(x.first)) {
      I = hcopy.erase(I);
    } else {
      auto J = std::remove_if(
          x.second.begin(), x.second.end(),
          [&](const std::pair<node_t, int> &ed) { return isEmpty(ed.first); });
      x.second.resize(static_cast<unsigned long>(J - x.second.begin()));
      ++I;
    }
  }
  auto addUnq = [&](EdgeEnumerator &en, const node_t &n, int nr) {
    if (!std::any_of(en.begin(), en.end(),
                     [&](const std::pair<node_t, int> &p) {
                       return p.first == n && p.second == nr;
                     }))
      en.emplace_back(n, nr);
  };
  if (transforms) {
    for (const auto &o : sizes) {
      auto eqc = dsets.find_set(o.first);
      if (eqc != o.first) {
        (*transforms)[o.first] = eqc;
      }
    }
  }
  // invariant: y \in outgoing[x] iff (!isEmpty(x) && isEmpty(y)) ||
  // (!isEmpty(y) && isEmpty(x))
  for (auto &o : outgoing) {
    if (isEmpty(o.first)) {
      auto eqc = dsets.find_set(o.first);
      addUnq(hcopy[eqc], o.second, 0);
    } else {
      auto eqc = dsets.find_set(o.second);
      addUnq(hcopy[o.first], eqc, 0);
    }
  }
}

size_t nr_neighbors(const EdgeHolder &hld, node_t nd) {
  if (auto neighs = neighbors_or_null(hld, nd)) {
    return neighs->size();
  }
  return 0;
}

bool neighbors_empty(const EdgeHolder &hld, node_t nd) {
  return nr_neighbors(hld, nd) == 0;
}

boost::optional<selex_t> is_selex(node_t n, const Edge &e) {
  if (!selex_node(n))
    return {};
  auto selex = n.node->to<IR::SelectExpression>();
  std::vector<const IR::Expression *> exprs;
  for (auto ex : selex->select->components)
    exprs.push_back(ex);
  auto selcase = selex->selectCases.at(static_cast<size_t>(e.second));
  if (selcase->keyset->is<IR::DefaultExpression>()) {
    std::vector<selex_case> neg;
    for (auto selc : selex->selectCases) {
      if (selc != selcase) {
        neg.emplace_back(exprs, getMatch(selc));
      }
    }
    return selex_t(selex_default(neg));
  } else {
    auto mat = getMatch(selcase);
    return selex_t(selex_case(exprs, mat));
  }
}

std::size_t hash_value(const FullEdge_t &e) {
  size_t seed = 0;
  boost::hash_combine(seed, e.source);
  boost::hash_combine(seed, e.dst);
  boost::hash_combine(seed, e.label);
  return seed;
}

boost::optional<condition_t> is_if(node_t n, const Edge &e,
                                   P4::TypeMap *typeMap) {
  return is_if(FullEdge_t(n, e), typeMap);
}

boost::optional<condition_t> is_if(const FullEdge_t &fe, P4::TypeMap *typeMap) {
  if (!NORMAL_NODE(fe.source))
    return {};
  if (fe.source.node->is<IR::IfStatement>()) {
    return condition_t(fe.source.node->to<IR::IfStatement>()->condition,
                       fe.label == 1);
  } else if (fe.source.node->is<IR::Expression>() &&
             !fe.source.node->is<IR::SelectExpression>()) {
    auto tt = typeMap->getType(fe.source.node);
    if (tt->is<IR::Type_Boolean>()) {
      return condition_t(fe.source.node->to<IR::Expression>(), fe.label == 1);
    }
  }
  return {};
}

boost::optional<method_call_t> is_method_return(const FullEdge_t &fe) {
  if (fe.type() == EdgeType::RETURN && fe.source.type == NodeType::END &&
      fe.dst.type == NodeType::RETURN) {
    return method_call_t(fe.dst.node->to<IR::MethodCallStatement>(),
                         NodeType::RETURN);
  }
  return {};
}
}

analysis::CFG::CFG(const IR::Node *maps_to) : maps_to(maps_to) {}

void analysis::CFG::add(analysis::EdgeHolder *other) {
  for (auto &h : *other) {
    auto &crt = holder[h.first];
    for (auto &edge : h.second) {
      crt.emplace_back(edge);
    }
  }
}

void analysis::CFG::write_node(
    const analysis::node_t &nd,
    const std::unordered_map<analysis::node_t, bool> *dead,
    std::unordered_set<analysis::node_t> &nodes, analysis::node_t first,
    std::ostream &post_cprop) const {
  if (nodes.emplace(nd).second) {
    post_cprop << nd.nodeId() << " [label=\"" << nd << "\"";
    auto dd = false;
    if (dead) {
      auto I = dead->find(nd);
      if (I != dead->end())
        dd = I->second;
    }
    if (first == nd) {
      post_cprop << ",style=filled,fillcolor=green";
    } else if (dd) {
      post_cprop << ",style=filled,fillcolor=lightgrey";
    }
    post_cprop << "];\n";
  }
}

#define GET_FW(type)                                                           \
  if (node->is<type>()) {                                                      \
    auto f = node->to<type>();                                                 \
    holder = graphs.get_forward(f);                                            \
  }
analysis::CFG *analysis::CFGs::get(const IR::Node *node, bool nullIfCantbuild) {
  auto I = cfgs.find(node);
  if (!hasCFG(node)) {
    if (nullIfCantbuild) {
      return nullptr;
    } else {
      BUG("can't build a CFG for node %1%", node);
    }
  }
  if (I != cfgs.end()) {
    return &I->second;
  } else {
    EdgeHolder *holder = nullptr;
    GET_FW(IR::Function);
    GET_FW(IR::Statement);
    GET_FW(IR::P4Control);
    GET_FW(IR::P4Parser);
    if (!holder) {
      BUG("can't build CFG for node %1%", node);
    } else {
      auto cfg =
          &cfgs.emplace(std::make_pair<const IR::Node *, CFG>(
                            std::move(node), CFG(node, std::move(*holder))))
               .first->second;
      startToGraph[cfg->start_node] = cfg;
      return cfg;
    }
  }
}

bool analysis::CFGs::hasCFG(const IR::Node *node) const {
  return node->is<IR::Function>() || node->is<IR::P4Control>() ||
         node->is<IR::P4Parser>();
}

bool analysis::CFGs::built(const IR::Node *node) const {
  return cfgs.count(node) != 0;
}

void analysis::CFGs::interproceduralEdge(analysis::node_t n,
                                         analysis::Edge new_edge) {
  main.holder[n].push_back(std::move(new_edge));
}

void analysis::CFGs::commit() {
  main.holder.clear();
  for (auto &ntocfg : cfgs) {
    for (auto &nd : ntocfg.second.holder) {
      auto &mn = main.holder[nd.first];
      mn.insert(mn.end(), nd.second.begin(), nd.second.end());
    }
  }
  main.start_node = find_start_node(&main.holder);
}
