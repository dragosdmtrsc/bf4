//
// Created by dragos on 03.09.2019.
//

#ifndef P4C_VARIABLES_H
#define P4C_VARIABLES_H

#include <analysis/cfg_algos.h>
#include <analysis/lattice/Lattice.h>
#include <ir/ir.h>
#include <unordered_map>
#include <utility>

namespace analysis {
struct Variables {
  std::unordered_map<const IR::Declaration *, node_t> declarations;
  Variables(std::unordered_map<const IR::Declaration *, node_t> declarations)
      : declarations(std::move(declarations)) {}
  Variables() = default;

  void declare(const IR::Declaration *d, node_t n) {
    auto crt = declarations.find(d);
    if (crt != declarations.end()) {
      if (crt->second != n)
        BUG("can't have same declaration mapped to the same thing %1% @ %2%", d,
            n.node);
      else
        return;
    }
    declarations[d] = n;
  }
  void undeclare(const IR::Declaration *d) { declarations.erase(d); }
};
}

#endif  // P4C_VARIABLES_H
