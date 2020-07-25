//
// Created by dragos on 24.01.2020.
//

#ifndef P4C_EXPRESSIONCANONICALIZER_H
#define P4C_EXPRESSIONCANONICALIZER_H

#include <analysis/context/InterproceduralCFGs.h>
#include <analysis/versions.h>
#include <common/resolveReferences/referenceMap.h>
#include <p4/typeMap.h>

namespace analysis {
class ExpressionCanonicalizer {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  NodeToFunctionMap *funMap;

  PathGetter pathGetter;

  std::unordered_map<std::string, const IR::Expression *> canon2e;

public:
  ExpressionCanonicalizer(ReferenceMap *refMap, TypeMap *typeMap,
                          NodeToFunctionMap *funMap = nullptr);
  const IR::Expression *operator()(const IR::Expression *e) {
    std::stringstream ss;
    ss << e;
    auto strep = ss.str();
    return canon2e.emplace(strep, e).first->second;
  }
};
}

#endif // P4C_EXPRESSIONCANONICALIZER_H
