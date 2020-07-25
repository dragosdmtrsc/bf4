//
// Created by dragos on 02.01.2020.
//

#include "symbex.h"
#include "AnalysisContext.h"

bool analysis::pc_t::operator==(const analysis::pc_t &other) const {
  return nd == other.nd && at == other.at;
}

analysis::pc_t analysis::pc_t::next() const {
  BUG_CHECK(!is_end(), "calling next on end of block");
  return {nd, at + 1};
}

const IR::Node *analysis::pc_t::operator*() const {
  BUG_CHECK(!is_end(), "end of block");
  return instruction_at(nd, static_cast<unsigned int>(at));
}

bool analysis::pc_t::is_end() const {
  return at == -1 || static_cast<size_t>(at) == nr_instructions(nd);
}

analysis::pc_t::pc_t(const analysis::node_t &nd, int at) : nd(nd), at(at) {
  if (static_cast<size_t>(at) == nr_instructions(nd))
    this->at = -1;
}
namespace analysis {

std::vector<pc_t> neighbors(const EdgeHolder &hld, const pc_t &loc) {
  if (loc.is_end()) {
    auto I = hld.find(loc.nd);
    std::vector<pc_t> nexts;
    if (I != hld.end()) {
      std::transform(
          I->second.begin(), I->second.end(), std::back_inserter(nexts),
          [](const std::pair<node_t, int> &ed) { return pc_t(ed.first, 0); });
    }
    return nexts;
  }
  return {loc.next()};
}

std::vector<state_t> execute(pc_t next, state_t st, P4::ReferenceMap *refMap,
                             P4::TypeMap *typeMap, NodeToFunctionMap *funMap) {
  if (st.location.is_end()) {
    st.location = next;
    return {st};
  }
  auto instr = *st.location;
  std::vector<state_t> final;
  if (auto ifs = instr->to<IR::IfStatement>()) {
    auto dnfif = if_to_dnf(ifs, refMap, typeMap)->to<IR::IfStatement>();
    auto bors = cubes::break_ors(dnfif->condition);
    for (auto exp : bors) {
      auto bands = cubes::break_ands(exp);
      auto cp = st;
      cp.path_condition.insert(cp.path_condition.end(), bands.begin(),
                               bands.end());
      final.push_back(std::move(cp));
    }
  } else if (auto asg = instr->to<IR::AssignmentStatement>()) {
    WriteSet writeSet(refMap, typeMap, funMap);
    auto &ws = writeSet[instr];
    for (const auto &mp : ws) {
      st.store[mp] = asg->right;
    }
    final.push_back(std::move(st));
  } else if (auto mcs = is_extern_method_call(instr)) {
    st.called.push_back(mcs->methodCallStatement);
    final.push_back(std::move(st));
  } else {
    final.push_back(std::move(st));
  }
  for (auto &f : final) {
    f.location = next;
  }
  BUG_CHECK(!final.empty(), "can't go empty at %1%", instr);
  return final;
}

const IR::Expression *state_t::condition() const {
  const auto &pc = path_condition;
  return getExpression(pc);
}

const IR::Expression *getExpression(const path_condition_t &pc) {
  if (pc.empty())
    return new IR::BoolLiteral(true);
  if (pc.size() == 1)
    return *pc.begin();
  auto first = pc[0];
  for (unsigned i = 1; i != pc.size(); ++i) {
    first = new IR::LAnd(first, pc[i]);
  }
  return first;
}

void tab_summary::summarize() {
  written.clear();
  if (!conditionals.empty()) {
    auto &first = conditionals.begin()->second;
    written = first;
    bool isfirst = true;
    for (const auto &x : conditionals) {
      if (!isfirst) {
        const auto &ps = x.second;
        PathSet intersect;
        std::set_intersection(ps.begin(), ps.end(), written.begin(),
                              written.end(),
                              std::inserter(intersect, intersect.end()));
        written = std::move(intersect);
      }
      isfirst = false;
    }
  }
  written.insert(directWrites.begin(), directWrites.end());
}

std::ostream &operator<<(std::ostream &os, const tab_summary &ts) {
  std::ostream_iterator<analysis::MemPath> out_itw(os, ",");
  os << "[";
  std::copy(ts.written.begin(), ts.written.end(), out_itw);
  os << "]";
  os << " = ";
  os << ts.name << "(";
  std::ostream_iterator<analysis::MemPath> out_it(os, ",");
  std::copy(ts.read.begin(), ts.read.end(), out_it);
  os << ")";
  return os;
}

const IR::Expression *
expressPathConditions(const std::vector<path_condition_t> &pcs) {
  if (pcs.empty())
    return new IR::BoolLiteral(false);
  if (pcs.size() == 1)
    return getExpression(pcs[0]);
  auto crt = getExpression(pcs[0]);
  for (unsigned i = 1; i != pcs.size(); ++i) {
    crt = new IR::LOr(crt, getExpression(pcs[i]));
  }
  return crt;
}

PathSet &tab_summary::newConditional(path_condition_t pc) {
  conditionals.push_back(
      std::make_pair<path_condition_t, PathSet>(std::move(pc), {}));
  return conditionals.back().second;
}

std::map<PathSet, std::vector<path_condition_t>> tab_summary::shard_writes() {
  std::map<PathSet, std::vector<path_condition_t>> ret;
  for (const auto &cdwrt : conditionals) {
    auto EM = ret.emplace(cdwrt.second, std::vector<path_condition_t>()).first;
    EM->second.push_back(cdwrt.first);
  }
  return ret;
}
}