//
// Created by dragos on 29.07.2019.
//

#include "UBLattice.h"

bool analysis::UBLattice::operator==(const analysis::UBLattice &other) const {
  if (other.isBottom())
    return isBottom();
  if (isBottom())
    return false;
  return *definitions == *other.definitions;
}

analysis::UBLattice analysis::UBLattice::
operator+(const analysis::UBLattice &other) const {
  if (other.isBottom())
    return definitions->cloneDefinitions();
  if (isBottom())
    return other.definitions->cloneDefinitions();
  return definitions->joinDefinitions(other.definitions);
}

bool analysis::UBLattice::isBottom() const {
  return !definitions || definitions->empty();
}

analysis::UBLattice::UBLattice(P4::Definitions *definitions)
    : definitions(definitions) {}

analysis::UBLattice::UBLattice() : definitions(nullptr) {}
