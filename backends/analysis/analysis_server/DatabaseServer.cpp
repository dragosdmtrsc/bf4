//
// Created by dragos on 09.12.2019.
//

#include "DatabaseServer.h"

namespace p4_thrift {
bool method::operator<(const method &o) const {
  return method_id < o.method_id;
}
bool edge::operator<(const edge &o) const {
  return std::make_tuple(sourceMethod, source, targetMethod, target) <
         std::make_tuple(o.sourceMethod, o.source, o.targetMethod, o.target);
}
bool basic_instruction::operator<(const basic_instruction &o) const {
  return std::make_pair(method_id, instruction_id) <
         std::make_pair(o.method_id, o.instruction_id);
}

bool method_info::operator<(const method_info &o) const {
  return method_id < o.method_id;
}
}

namespace analysis {

DatabaseServer::DatabaseServer(ProgramDatabase *database)
    : database(database) {}

void DatabaseServer::get_method(p4_thrift::method &ret,
                                const p4_thrift::id_t &id) {
  auto I = id_to_node.find(id);
  if (I != id_to_node.end()) {
    auto nd = I->second;
    auto blocks = database->method(nd);
    std::set<p4_thrift::edge> edges;
    std::set<p4_thrift::basic_instruction> bblocks;
    traverse_df_pernode(
        &blocks->holder, blocks->start_node,
        [&](const node_t &blk) { bblocks.emplace(translate(blk)); });
    for (const auto &x : blocks->holder) {
      const auto &nd = x.first;
      for (const auto &neigh : x.second) {
        p4_thrift::edge ed = translate(nd, neigh);
        edges.emplace(ed);
      }
    }
    ret.method_id = id;
    ret.instructions = std::move(bblocks);
    ret.edges = std::move(edges);
  } else {
    p4_thrift::NoSuchMethod noSuchMethod;
    noSuchMethod.method = id;
    throw std::move(noSuchMethod);
  }
}

p4_thrift::edge DatabaseServer::translate(const node_t &src,
                                          const Edge &neigh) const {
  auto &target = neigh.first;
  p4_thrift::edge ed;
  ed.source = src.nodeId();
  ed.sourceMethod = idof(database->method(src));
  ed.target = target.nodeId();
  ed.targetMethod = idof(database->method(neigh.first));
  if (neigh.second == toNumber(EdgeType::CALL)) {
    ed.kind = p4_thrift::edge_kind::call;
  } else if (neigh.second == toNumber(EdgeType::RETURN)) {
    ed.kind = p4_thrift::edge_kind::ret;
  } else if (neigh.second == toNumber(EdgeType::GOTO)) {
    ed.kind = p4_thrift::edge_kind::go_to;
  } else {
    ed.kind = p4_thrift::edge_kind::normal;
  }
  ed.__set_kind(ed.kind);
  return ed;
}

void DatabaseServer::exit() {
  std::cerr << "exiting\n";
  std::exit(0);
}

void DatabaseServer::get_graph(p4_thrift::method &_return) {
  auto main = database->graph();
  std::set<p4_thrift::edge> edges;
  std::set<p4_thrift::basic_instruction> instrs;
  for (const auto &xy : main->holder) {
    auto &x = xy.first;
    instrs.emplace(translate(x));
    for (const auto &ed : xy.second) {
      auto &y = ed.first;
      instrs.emplace(translate(y));
      edges.emplace(translate(x, ed));
    }
  }
  _return.method_id = "";
  _return.instructions = std::move(instrs);
  _return.edges = std::move(edges);
}

p4_thrift::basic_instruction DatabaseServer::translate(const node_t &blk) {
  // basic block maps to an API basic block
  auto bbid = blk.nodeId();
  BUG_CHECK(!blk.node->is<IR::Vector<IR::Node>>(), "not expecting basic block");
  auto instrid = bbid;
  p4_thrift::basic_instruction basic_instruction;
  basic_instruction.instruction_id = instrid;
  basic_instruction.method_id = idof(database->method(blk));
  basic_instruction.representation = node_repr(blk);
  bool is__terminal = false;
  bool is_controlled = false;
  bool is__bug = false;
  if (auto mcs = is_extern_method_call(blk)) {
    if (is_bug(mcs->methodCallStatement))
      is__bug = true;
    else if (is_terminal(mcs->methodCallStatement))
      is__terminal = true;
    else if (database->isControlled(blk))
      is_controlled = true;
  }
  switch (blk.type) {
  case NodeType::CALL:
    basic_instruction.instr_type = p4_thrift::instruction_type::type::call;
    break;
  default:
    if (is__bug) {
      basic_instruction.instr_type = p4_thrift::instruction_type::type::bug;
    } else if (is__terminal) {
      basic_instruction.instr_type = p4_thrift::instruction_type::type::good;
    } else if (is_controlled) {
      basic_instruction.instr_type =
          p4_thrift::instruction_type::type::controlled;
    } else {
      basic_instruction.instr_type = p4_thrift::instruction_type::type::normal;
    }
    break;
  }
  return basic_instruction;
}

void DatabaseServer::methods_by_names(std::set<p4_thrift::method_info> &_return,
                                      const std::set<std::string> &names) {
  for (const auto &nm : names) {
    auto I = id_to_node.find(nm);
    std::stringstream ss;
    if (I != id_to_node.end()) {
      if (auto ctrl = I->second->to<IR::P4Control>()) {
        ss << "control " << ctrl->name.name;
      } else if (auto parser = I->second->to<IR::P4Parser>()) {
        ss << "parser " << parser->name.name;
      } else if (auto meth = I->second->to<IR::Method>()) {
        meth->dbprint(ss);
      } else if (auto fun = I->second->to<IR::Function>()) {
        ss << "function ";
        ss << fun->name.name;
      } else {
        ss << "UNKNOWN";
      }
    } else {
      ss << "N/A";
    }
    p4_thrift::method_info method_info;
    method_info.method_id = nm;
    method_info.repr = ss.str();
    _return.emplace(method_info);
  }
}
}