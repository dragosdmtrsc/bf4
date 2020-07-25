//
// Created by dragos on 07.05.2019.
//

#ifndef P4C_INSTANTIATEPACKAGEMODELS_H
#define P4C_INSTANTIATEPACKAGEMODELS_H


#include <common/resolveReferences/referenceMap.h>
#include <p4/typeMap.h>
#include <p4/evaluator/evaluator.h>

namespace analysis {
class InstantiatePackageModels : public PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  P4::EvaluatorPass *evaluator;
public:
  InstantiatePackageModels(P4::ReferenceMap *refMap, P4::TypeMap *typeMap, P4::EvaluatorPass *evaluator);
};
}



#endif //P4C_INSTANTIATEPACKAGEMODELS_H
