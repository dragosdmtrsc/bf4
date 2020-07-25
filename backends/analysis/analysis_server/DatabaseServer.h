//
// Created by dragos on 09.12.2019.
//

#ifndef P4C_DATABASESERVER_H
#define P4C_DATABASESERVER_H

#include "../gen-cpp/p4_service.h"
#include "ProgramDatabase.h"

namespace analysis {
class DatabaseServer : virtual public p4_thrift::p4_serviceIf {
  ProgramDatabase *database;
  mutable std::unordered_map<p4_thrift::id_t, const IR::Node *> id_to_node;
  mutable std::unordered_map<const IR::Node *, p4_thrift::id_t> node_to_id;

  static p4_thrift::id_t id(const void *n) {
    std::stringstream ss;
    ss << n;
    return ss.str();
  }
  p4_thrift::id_t idof(const IR::Node *nd) const {
    auto EMI = getOrEmplace(node_to_id, nd, [&]() { return id(nd); });
    if (EMI.second) {
      id_to_node[EMI.first] = nd;
    }
    return EMI.first;
  }

  p4_thrift::basic_instruction translate(const node_t &blk);
  p4_thrift::edge translate(const node_t &src, const Edge &neigh) const;

public:
  DatabaseServer(ProgramDatabase *database);

  void get_main(p4_thrift::id_t &_return) override {
    _return = idof(database->mainFunction());
  }
  void get_method(p4_thrift::method &ret, const p4_thrift::id_t &id) override;

  void get_graph(p4_thrift::method &_return) override;

  void methods_by_names(std::set<p4_thrift::method_info> &_return, const std::set<std::string> &names) override;

  void exit() override;
};
}

#endif // P4C_DATABASESERVER_H
