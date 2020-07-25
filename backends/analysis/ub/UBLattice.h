//
// Created by dragos on 29.07.2019.
//

#ifndef P4C_UBLATTICE_H
#define P4C_UBLATTICE_H

#include <analysis/lattice/Lattice.h>
#include <p4/def_use.h>

namespace analysis {
struct UBLattice : public LatticeElement<UBLattice> {
  P4::Definitions *definitions;
  UBLattice();
  UBLattice(P4::Definitions *definitions);
  bool operator==(const UBLattice &other) const override;
  UBLattice operator+(const UBLattice &other) const override;

  bool isBottom() const override;
};
}

#endif // P4C_UBLATTICE_H
