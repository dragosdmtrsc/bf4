//
// Created by dragos on 06.05.2019.
//

#ifndef P4C_HANDLEHEADERS_H
#define P4C_HANDLEHEADERS_H

#include <analysis/ub/AnalysisContext.h>
#include <common/resolveReferences/referenceMap.h>
#include <p4/typeMap.h>

namespace analysis {
class HandleHeaders : public PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

 public:
  HandleHeaders(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};

class MakeMultiAssign : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  MultiAssignment muas;

  const IR::Node *postorder(IR::AssignmentStatement *stat) override {
    auto t = typeMap->getType(stat->left);
    if (t->is<IR::Type_StructLike>()) {
      auto vec = muas(stat->left, stat->right);
      IR::IndexedVector<IR::StatOrDecl> asg;
      asg.append(*vec);
      return new IR::BlockStatement(std::move(asg));
    }
    return stat;
  }
 public:
  MakeMultiAssign(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap), muas(refMap, typeMap) {}
};

class HandleArrayIndices : public PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

 public:
  HandleArrayIndices(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};
}

#endif  // P4C_HANDLEHEADERS_H
