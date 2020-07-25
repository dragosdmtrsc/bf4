//
// Created by dragos on 07.05.2019.
//

#include <ir/dbprint.h>
#include <ir/ir.h>
#include <lib/indent.h>

using namespace DBPrint;
using namespace IndentCtl;

const IR::Type_Method *IR::P4PackageModel::getConstructorMethodType() const {
  return new Type_Method(getTypeParameters(), type, constructorParams);
}
void IR::P4PackageModel::dbprint(std::ostream &out) const {
  out << "package_model " << name;
  if (type->typeParameters && !type->typeParameters->empty())
    out << type->typeParameters;
  if (type->applyParams)
    out << '(' << type->applyParams << ')';
  if (constructorParams)
    out << '(' << constructorParams << ')';
  out << " " << type->annotations << "{" << IndentCtl::indent;
  for (auto d : controlLocals)
    out << IndentCtl::endl << d;
  for (auto s : body->components)
    out << IndentCtl::endl << s;
  out << " }" << IndentCtl::unindent;
}

void IR::CodeEvent::dbprint(std::ostream &out) const {
  switch (eventType) {
  case 0:
    out << "#start ";
    break;
  case 1:
    out << "#end ";
  }
  out << original;
}
const unsigned IR::CodeEvent::START = 0;
const unsigned IR::CodeEvent::END = 1;