//
// Created by dragos on 16.04.2019.
//

#ifndef P4C_INSTRUMENTATION_HELPER_H
#define P4C_INSTRUMENTATION_HELPER_H


#include <ir/visitor.h>
#include <common/resolveReferences/referenceMap.h>
#include <p4/typeMap.h>
#include <p4/typeChecking/typeChecker.h>
#include <p4/evaluator/evaluator.h>

#include <utility>


namespace analysis {

    class find_generics : public Inspector {
        P4::ReferenceMap *refMap;
        P4::TypeMap *typeMap;
    public:
        find_generics(P4::ReferenceMap *refMap, P4::TypeMap *typeMap) : refMap(refMap), typeMap(typeMap) {}

        void postorder(const IR::Type *type_method) override;
        void postorder(const IR::Declaration_Instance *instance) override;
        void postorder(const IR::ConstructorCallExpression *expression) override;
        void postorder(const IR::MethodCallExpression *expression) override;

    };

    class find_blocks : public Inspector {
        P4::ReferenceMap *refMap;
        P4::TypeMap *typeMap;
        std::map<const IR::Type *, std::vector<const IR::Type *>> typeMappings;
        std::map<const IR::Type *, std::vector<IR::Type *>> &newTypeDeclarations;
    public:
        find_blocks(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                    std::map<const IR::Type *, std::vector<IR::Type *>> &newTypeDeclarations) :
                refMap(refMap), typeMap(typeMap), newTypeDeclarations(newTypeDeclarations) {}

        bool preorder(const IR::Block *block) override;
        void postorder(const IR::InstantiatedBlock *instantiatedBlock) override;
    };


    class rewrite_methods : public Inspector {
        P4::ReferenceMap *refMap;
        P4::TypeMap *typeMap;
        cstring instrument_name;
        const IR::Type *type;
        std::map<const IR::Method *, const IR::Method *> *changed_methods;
        std::map<const IR::Function *, const IR::Function *> *changed_funs;
        std::map<const IR::IApply *, const IR::IApply *> *changed_applies;
        std::map<const IR::P4Action *, const IR::P4Action *> *changed_actions;
        std::function<bool(const IR::Declaration *)> filter;
    public:
        rewrite_methods(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                        cstring instrument_name, const IR::Type *type,
                        std::map<const IR::Method *, const IR::Method *> *changed_methods,
                        std::map<const IR::Function *, const IR::Function *> *changed_funs,
                        std::map<const IR::IApply *, const IR::IApply *> *changed_applies,
                        std::map<const IR::P4Action *, const IR::P4Action *> *changed_actions,
                        std::function<bool(const IR::Declaration *)> filter) :
                refMap(refMap), typeMap(typeMap), instrument_name(instrument_name),
                type(type), changed_methods(changed_methods),
                changed_funs(changed_funs),
                changed_applies(changed_applies),
                changed_actions(changed_actions),
                filter(std::move(filter)) {}
        const IR::Declaration *mkInstrument(const IR::Declaration *against);
        void postorder(const IR::P4Parser *app) override;
        void postorder(const IR::Method *method) override;
        void postorder(const IR::P4Control *method) override;
        void postorder(const IR::Function *fun) override;
        void postorder(const IR::P4Action *act) override;
        void analyze(const IR::IApply *app);
    };

    class change_methods : public Transform {
        P4::ReferenceMap *refMap;
        P4::TypeMap *typeMap;
        cstring instrument_name;
        const IR::Type *type;
        std::map<const IR::Method *, const IR::Method *> *changed_methods;
        std::map<const IR::Function *, const IR::Function *> *changed_funs;
        std::map<const IR::IApply *, const IR::IApply *> *changed_applies;
        std::map<const IR::P4Action *, const IR::P4Action *> *changed_actions;
    public:
        change_methods(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                cstring instrument_name, const IR::Type *type,
                std::map<const IR::Method *, const IR::Method *> *changed_methods,
                std::map<const IR::Function *, const IR::Function *> *changed_funs,
                std::map<const IR::IApply *, const IR::IApply *> *changed_applies,
                std::map<const IR::P4Action *, const IR::P4Action *> *changed_actions) :
                refMap(refMap), typeMap(typeMap), instrument_name(instrument_name),
                type(type), changed_methods(changed_methods), changed_funs(changed_funs),
                changed_applies(changed_applies), changed_actions(changed_actions) {}

        const IR::Node *postorder(IR::Method *method) override;
        const IR::Node *postorder(IR::MethodCallExpression *mce) override;

    };

    class instrument : public PassManager {
        std::map<const IR::Declaration *, const IR::Declaration *> instruments;
        std::map<const IR::Method *, const IR::Method *> method_mapping;
        std::map<const IR::Function *, const IR::Function *> changed_funs;
        std::map<const IR::IApply *, const IR::IApply *> changed_applies;
        std::map<const IR::P4Action *, const IR::P4Action *> changed_actions;
    public:
        instrument(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                   cstring instrument_name, const IR::Type *type) {
            passes.push_back(new rewrite_methods(refMap, typeMap,
                             instrument_name, type,
                                                 &method_mapping, &changed_funs,
                                                 &changed_applies, &changed_actions,
                                                 [refMap, typeMap](const IR::Declaration *decl) {
                        if (decl->getAnnotation("instrument")) return false;
                        if (decl->is<IR::Declaration_Variable>() || decl->is<IR::Parameter>() ||
                            decl->is<IR::StructField>()) {
                            auto tp = typeMap->getType(decl);
                            return tp->is<IR::Type_Bits>() || tp->is<IR::Type_InfInt>() ||
                                   tp->is<IR::Type_Enum>() ||
                                   tp->is<IR::Type_Error>();
                        }
                        return false;
                    }));
            passes.push_back(new change_methods(refMap, typeMap,
                                                 instrument_name, type,
                                                 &method_mapping,
                                                 &changed_funs,
                                                 &changed_applies,
                                                 &changed_actions));
            passes.push_back(new P4::ClearTypeMap(typeMap));
            passes.push_back(new P4::EvaluatorPass(refMap, typeMap));
        }
    };
}




#endif //P4C_INSTRUMENTATION_HELPER_H
