//
// Created by dragos on 24.10.2019.
//

#include "VersionedExpression.h"

namespace IR {

VersionedExpression::VersionedExpression(const Expression *leftValue,
                                         unsigned int version)
    : leftValue(leftValue), version(version) {}

VersionedExpression *VersionedExpression::clone() const {
  return new VersionedExpression(leftValue->clone(), version);
}

const IR::VersionedExpression *fixType(const IR::VersionedExpression *ve,
                                       P4::TypeMap *typeMap) {
  typeMap->setType(ve, typeMap->getType(ve->leftValue));
  typeMap->setLeftValue(ve);
  return ve;
}

void VersionedExpression::dbprint(std::ostream &out) const {
  auto prec = DBPrint::getprec(out);
  DBPrint::setprec setprec(DBPrint::Prec_Low);
  setprec.set(out);
  out << leftValue << ":" << version;
  setprec = DBPrint::setprec(prec);
  setprec.set(out);
}

bool VersionedExpression::operator==(IR::Expression const &a) const {
  if (a.is<IR::VersionedExpression>()) {
    return a.to<IR::VersionedExpression>()->leftValue->operator==(*leftValue) &&
           a.to<IR::VersionedExpression>()->version == version;
  }
  return false;
}
}