//
// Created by dragos on 24.01.2020.
//

#include "ExpressionCanonicalizer.h"

namespace analysis {

ExpressionCanonicalizer::ExpressionCanonicalizer(ReferenceMap *refMap,
                                                 TypeMap *typeMap,
                                                 NodeToFunctionMap *funMap)
    : refMap(refMap), typeMap(typeMap), funMap(funMap),
      pathGetter(refMap, typeMap) {}
}