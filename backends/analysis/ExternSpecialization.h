//
// Created by dragos on 18.04.2019.
//

#ifndef P4C_EXTERNSPECIALIZATION_H
#define P4C_EXTERNSPECIALIZATION_H


#include <p4/typeMap.h>
#include <common/resolveReferences/referenceMap.h>


namespace analysis {
    class ExternSpecialization {
    public:
        const IR::Type *of;
        const IR::Type_SpecializedCanonical *actual;
        const IR::Declaration_Instance *instance = nullptr;
        const IR::ConstructorCallExpression *constructor = nullptr;
        // need to store insertion point info
        const IR::Node *justBefore = nullptr;

        ExternSpecialization(const IR::Type *of, const IR::Type_SpecializedCanonical *actual,
                             const IR::Declaration_Instance *decl) :
                of(of), actual(actual), instance(decl) {}
        ExternSpecialization(const IR::Type *of, const IR::Type_SpecializedCanonical *actual,
                             const IR::ConstructorCallExpression *constructor) :
                of(of), actual(actual), constructor(constructor) {}
    };

    class ExternSpecializations {
    public:
        P4::ReferenceMap *refMap;
        P4::TypeMap *typeMap;
        std::vector<ExternSpecialization> specializations;
    public:
        ExternSpecializations(P4::ReferenceMap *refMap, P4::TypeMap *typeMap) : refMap(refMap), typeMap(typeMap) {}

    };

    class FindExternSpecializations : public Inspector {
        ExternSpecializations *specializations;
    public:
        explicit FindExternSpecializations(ExternSpecializations *specializations) :
                specializations(specializations) {}

        void findContext(ExternSpecialization &spec);
        void postorder(const IR::ConstructorCallExpression *cce) override;
        void postorder(const IR::Declaration_Instance *decl) override;
    };

    class SpecializeExterns : public PassManager {
        P4::ReferenceMap *refMap;
        P4::TypeMap *typeMap;
        ExternSpecializations specs;
    public:
        SpecializeExterns(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
    };

}


#endif //P4C_EXTERNSPECIALIZATION_H
