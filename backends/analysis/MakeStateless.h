//
// Created by dragos on 18.04.2019.
//

#ifndef P4C_MAKESTATELESS_H
#define P4C_MAKESTATELESS_H


#include <p4/typeMap.h>
#include <common/resolveReferences/referenceMap.h>

namespace analysis {

    class Behaviors {
    public:
        P4::ReferenceMap *refMap;
        P4::TypeMap *typeMap;
        std::map<const IR::Type_Extern *, std::map<const IR::Method *, const IR::Method *>> externBehaviors;
        std::map<const IR::IApply *, const IR::IApply *> otherBehaviors;
        Behaviors(P4::ReferenceMap *refMap,
                  P4::TypeMap *typeMap) : refMap(refMap), typeMap(typeMap) {}

        void put(const IR::Type_Extern *ext, const IR::Method *method, const IR::Method *newmethod) {
            externBehaviors[ext][method] = newmethod;
        }
        void put(const IR::P4Control *control, const IR::P4Control *copy) {
            otherBehaviors[control] = copy;
        }
        void put(const IR::P4Parser *control, const IR::P4Parser *copy) {
            otherBehaviors[control] = copy;
        }
    };

    class StateInfo {
    public:
        const IR::Type *of;
        std::map<const IR::Declaration *, const IR::Type *> declToTypes;
        IR::Type_Struct *mkStruct(cstring name);
    };

    class StateInfos {
    public:
        P4::ReferenceMap *refMap;
        P4::TypeMap *typeMap;
        std::map<const IR::Type *, StateInfo> info;
        StateInfos(P4::ReferenceMap *refMap, P4::TypeMap *typeMap) : refMap(refMap), typeMap(typeMap) {}

        void put(const IR::Type_Declaration *decl, StateInfo elem) {
            CHECK_NULL(decl);
            info.emplace(decl, elem);
        }

        bool any(const IR::Type *tp, const IR::Declaration *decl) {
            for (auto &p : info) {
                auto I = p.second.declToTypes.find(decl);
                if (I != p.second.declToTypes.end()) {
                    if (I->second == tp)
                        return true;
                }
            }
            return false;
        }

        const IR::Type *getType(const IR::Type *other);

    };
    class MakeStateless : public PassManager {
        P4::ReferenceMap *refMap;
        P4::TypeMap *typeMap;
        StateInfos info;
        Behaviors behaviors;
    public:
        MakeStateless(P4::ReferenceMap *refMap,
                      P4::TypeMap *typeMap);
    };
}

#endif //P4C_MAKESTATELESS_H
