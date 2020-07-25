//
// Created by dragos on 25.01.2020.
//

#ifndef P4C_REMOVEPACKETLOOKAHEAD_H
#define P4C_REMOVEPACKETLOOKAHEAD_H

#include "AnalysisContext.h"
#include <analysis/bvset/bvset.h>
#include <analysis/cfg_algos.h>
#include <analysis/context/InterproceduralCFGs.h>
#include <analysis/versions.h>

namespace analysis {

void solve_lookaheads(EdgeHolder &h, node_t start, P4::ReferenceMap *refMap,
                      P4::TypeMap *typeMap);
void solve_lookaheads(EdgeHolder &h, EdgeHolder *, node_t start, P4::ReferenceMap *refMap,
                      P4::TypeMap *typeMap);
}

#endif // P4C_REMOVEPACKETLOOKAHEAD_H
