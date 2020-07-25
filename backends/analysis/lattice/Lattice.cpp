//
// Created by dragos on 29.07.2019.
//

#include "Lattice.h"

void analysis::DefaultDiscipline::buildDiscipline(node_t start) {
  sorted = analysis::topo_sort(&graph->holder, start);
  unsigned i = 0;
  for (auto s : sorted) {
    priorities[s] = static_cast<unsigned int>(sorted.size() - i);
    ++i;
  }
}

analysis::DefaultDiscipline::DefaultDiscipline(const analysis::CFG *graph,
                                               node_t start)
    : graph(graph) {
  buildDiscipline(start);
}

bool analysis::DefaultDiscipline::operator()(analysis::node_t l,
                                             analysis::node_t r) {
  return priorities[l] < priorities[r];
}

analysis::DefaultDiscipline::DefaultDiscipline(
    const analysis::EdgeHolder *holder, analysis::node_t start) {
  sorted = analysis::topo_sort(holder, start);
  unsigned i = 0;
  for (auto s : sorted) {
    priorities[s] = static_cast<unsigned int>(sorted.size() - i);
    ++i;
  }
}
