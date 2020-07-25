//
// Created by dragos on 09.12.2019.
//

#include "ProgramDatabase.h"

namespace analysis {
CFG *ProgramDatabase::method(const IR::Node *method_id) {
  EdgeHolder hld;
  traverse_df(&main->holder, main->start_node, [&](const node_t &src, const Edge &ed) {
    FullEdge_t fe(src, ed);
    auto innersrc = builder.getMethod(fe.source) == method_id;
    auto innerdst = builder.getMethod(fe.dst) == method_id;
    if (innersrc || innerdst) {
      node_t asrc = fe.source;
      node_t adst = fe.dst;
      if (!innersrc) {
        asrc = builder.getMethod(fe.source);
        asrc.type = NodeType::CALL;
      }
      if (!innerdst) {
        adst = builder.getMethod(fe.dst);
        adst.type = NodeType::CALL;
      }
      auto elabel = fe.label;
      if (innersrc && !innerdst) {
        elabel = toNumber(EdgeType::CALL);
      }
      if (!innersrc && innerdst) {
        elabel = toNumber(EdgeType::RETURN);
      }
      hld[asrc].emplace_back(adst, elabel);
    }
  });
  return new CFG(method_id, std::move(hld));
}
const IR::Node *ProgramDatabase::mainFunction() {
  auto fun =
      (*program->getDeclsByName(startFunction)->begin())->to<IR::Function>();
  return fun;
}

ProgramDatabase::ProgramDatabase(ReferenceMap *refMap, TypeMap *typeMap,
                                 const IR::P4Program *program,
                                 const cstring &startFunction)
    : refMap(refMap), typeMap(typeMap), program(program),
      startFunction(startFunction), contextFactory(program, refMap, typeMap),
      builder(refMap, typeMap, program, &contextFactory, &cfgs, &funMap) {
  auto fun = program->getDeclsByName(startFunction)
                 ->begin()
                 .
                 operator*()
                 ->to<IR::Function>();
  auto fungraph = cfgs.get(fun, false);
  main = builder.build(fungraph);
}
}