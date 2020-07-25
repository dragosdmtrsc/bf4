//
// Created by dragos on 24.10.2019.
//

#ifndef P4C_VERSIONEDEXPRESSION_H
#define P4C_VERSIONEDEXPRESSION_H

#include <ir/ir.h>
#include <p4/typeMap.h>
namespace IR {
class VersionedExpression : public Expression {
public:
  const Expression *leftValue;
  unsigned int version;
  cstring node_type_name() const override { return "VersionedExpression"; }
  static cstring static_type_name() { return "VersionedExpression"; }
  VersionedExpression(const Expression *leftValue, unsigned int version);

  void dbprint(std::ostream &out) const override;

  VersionedExpression *clone() const override;

  bool operator==(IR::Expression const &a) const override;
};
const IR::VersionedExpression *fixType(const IR::VersionedExpression *ve,
                                       P4::TypeMap *typeMap);
}

#endif // P4C_VERSIONEDEXPRESSION_H
