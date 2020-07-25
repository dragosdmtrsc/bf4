//
// Created by dragos on 11.01.2019.
//

#ifndef P4C_V1_INTEGRATOR_H
#define P4C_V1_INTEGRATOR_H


#include <common/resolveReferences/referenceMap.h>
#include <p4/typeMap.h>
#include <bmv2/simple_switch/simpleSwitch.h>
#include <p4/moveDeclarations.h>
#include <midend/local_copyprop.h>
#include "analysis_helpers.h"

namespace analysis {

    class AddEgressToParser : public Transform {
        BMV2::V1ProgramStructure *v1ProgramStructure;
    public:
        AddEgressToParser(BMV2::V1ProgramStructure *v1ProgramStructure) : v1ProgramStructure(v1ProgramStructure) {}
        const IR::P4Parser *postorder(IR::P4Parser *parser) override {
            auto iniparser = getOriginal<IR::P4Parser>();
            if (v1ProgramStructure->parser->name.name == iniparser->name.name) {
                // ok, now add a new state for ingress
                auto control = v1ProgramStructure->egress;
                auto new_parser_state = new IR::ParserState(control->name,
                                                            new IR::PathExpression(IR::ParserState::accept));
                parser->states.push_back(new_parser_state);
                parser->parserLocals.insert(parser->parserLocals.end(),
                                            control->controlLocals.begin(),
                                            control->controlLocals.end());
                new_parser_state->components.insert(new_parser_state->components.end(),
                                                    control->body->components.begin(),
                                                    control->body->components.end()
                );
            }
            return parser;
        }
        const IR::Node *postorder(IR::PathExpression *pe) override {
            if (pe->path->name.name == IR::ParserState::accept) {
                return new IR::PathExpression(v1ProgramStructure->egress->name.name);
            }
            return pe;
        }
    };

    class AddVerifyToParser : public Transform {
        BMV2::V1ProgramStructure *v1ProgramStructure;
    public:
        AddVerifyToParser(BMV2::V1ProgramStructure *v1ProgramStructure) : v1ProgramStructure(v1ProgramStructure) {}
        const IR::P4Parser *postorder(IR::P4Parser *parser) override {
            auto iniparser = getOriginal<IR::P4Parser>();
            if (v1ProgramStructure->parser->name.name == iniparser->name.name) {
                // ok, now add a new state for ingress
                auto control = v1ProgramStructure->verify_checksum;
                auto new_parser_state = new IR::ParserState(control->name,
                                                            new IR::PathExpression(IR::ParserState::accept));
                parser->states.push_back(new_parser_state);
                parser->parserLocals.insert(parser->parserLocals.end(),
                                            control->controlLocals.begin(),
                                            control->controlLocals.end());
                new_parser_state->components.insert(new_parser_state->components.end(),
                                                    control->body->components.begin(),
                                                    control->body->components.end()
                );
            }
            return parser;
        }
        const IR::Node *postorder(IR::PathExpression *pe) override {
            if (pe->path->name.name == IR::ParserState::accept) {
                return new IR::PathExpression(v1ProgramStructure->verify_checksum->name.name);
            }
            return pe;
        }
    };

    class AddIngressToParser : public Transform {
        BMV2::V1ProgramStructure *v1ProgramStructure;
    public:
        AddIngressToParser(BMV2::V1ProgramStructure *v1ProgramStructure) : v1ProgramStructure(v1ProgramStructure) {}
        const IR::P4Parser *postorder(IR::P4Parser *parser) override {
            auto iniparser = getOriginal<IR::P4Parser>();
            if (v1ProgramStructure->parser->name.name == iniparser->name.name) {
                // ok, now add a new state for ingress
                auto control = v1ProgramStructure->ingress;
                auto new_parser_state = new IR::ParserState(control->name,
                                                            new IR::PathExpression(IR::ParserState::accept));
                parser->states.push_back(new_parser_state);
                parser->parserLocals.insert(parser->parserLocals.end(),
                                            control->controlLocals.begin(),
                                            control->controlLocals.end());
                new_parser_state->components.insert(new_parser_state->components.end(),
                                                    control->body->components.begin(),
                                                    control->body->components.end()
                );
            }
            return parser;
        }
        const IR::Node *postorder(IR::PathExpression *pe) override {
            if (pe->path->name.name == IR::ParserState::accept) {
                return new IR::PathExpression(v1ProgramStructure->ingress->name.name);
            }
            return pe;
        }
    };

    class ZeroizeMetas : public Transform {
        P4::ReferenceMap *refMap;
        P4::TypeMap *typeMap;

        void zeroize(const IR::Expression *e, const IR::Type *t, IR::Vector<IR::StatOrDecl> &vec) {
            if (auto strt = t->to<IR::Type_StructLike>()) {
                if (!t->is<IR::Type_Header>()) {
                    for (auto sf : strt->fields) {
                        zeroize(new IR::Member(e, sf->name), typeMap->getType(sf), vec);
                    }
                }
            } else if (auto st = t->to<IR::Type_Stack>()) {
                for (unsigned i = 0; i != st->getSize(); ++i) {
                    zeroize(new IR::ArrayIndex(e, new IR::Constant(i)), typeMap->getType(st->elementType)->to<IR::Type_Type>(), vec);
                }
            } else if (t->to<IR::Type_Bits>()) {
                vec.push_back(new IR::AssignmentStatement(e, new IR::Constant(t, 0)));
            } else if (t->is<IR::Type_Boolean>()) {
                vec.push_back(new IR::AssignmentStatement(e, new IR::BoolLiteral(false)));
            } else if (auto en = t->to<IR::Type_Enum>()) {
                auto decl = *en->members.begin();
                vec.push_back(new IR::AssignmentStatement(e, new IR::Member(new IR::PathExpression(en->name), decl->name)));
            } else if (auto er = t->to<IR::Type_Error>()) {
                vec.push_back(new IR::AssignmentStatement(e, new IR::Member(new IR::PathExpression(er->name),
                                                                            P4::P4CoreLibrary::instance.noError.name)));
            }
        }

        const IR::Node *postorder(IR::ParserState *state) override {
            auto parser = findContext<IR::P4Parser>();
            if (state->name == IR::ParserState::start) {
                IR::Vector<IR::StatOrDecl> extras;
                if (parser->getApplyParameters()) {
                    for (auto parm : *parser->getApplyParameters()) {
                        if (parm->direction == IR::Direction::InOut) {
                            if (parm->name.name == P4V1::V1Model::instance.parser.metadataParam.name ||
                                    parm->name.name == P4V1::V1Model::instance.parser.standardMetadataParam.name) {
                                zeroize(new IR::PathExpression(parm->name.name), typeMap->getType(parm), extras);
                            }
                        }
                    }
                }
                state->components.insert(state->components.begin(), extras.begin(), extras.end());
            }
            return state;
        }

    public:
        ZeroizeMetas(P4::ReferenceMap *refMap, P4::TypeMap *typeMap) : refMap(refMap), typeMap(typeMap) {}
    };

    class EmptyControl : public Transform {
        BMV2::V1ProgramStructure *v1ProgramStructure;
        BMV2::block_t which;
    public:
        EmptyControl(BMV2::V1ProgramStructure *v1ProgramStructure, BMV2::block_t which) :
                v1ProgramStructure(v1ProgramStructure), which(which) {}
        const IR::Node *postorder(IR::P4Control *control) override {
            cstring name;
            switch (which) {
                case BMV2::PARSER:break;
                case BMV2::PIPELINE:break;
                case BMV2::DEPARSER:
                    name = v1ProgramStructure->deparser->name.name;
                    break;
                case BMV2::V1_PARSER:break;
                case BMV2::V1_DEPARSER:
                    name = v1ProgramStructure->deparser->name.name;
                    break;
                case BMV2::V1_INGRESS:
                    name = v1ProgramStructure->ingress->name.name;
                    break;
                case BMV2::V1_EGRESS:
                    name = v1ProgramStructure->egress->name.name;
                    break;
                case BMV2::V1_VERIFY:
                    name = v1ProgramStructure->verify_checksum->name.name;
                    break;
                case BMV2::V1_COMPUTE:
                    name = v1ProgramStructure->compute_checksum->name.name;
                    break;
            }
            if (control->name.name == name) {
                control->body = new IR::BlockStatement();
                control->controlLocals.clear();
            }
            return control;
        }
    };

    class DropSemantics : public Transform {
        P4::ReferenceMap *refMap;
        P4::TypeMap *typeMap;
    public:
        DropSemantics(P4::ReferenceMap *refMap,
                      P4::TypeMap *typeMap) : refMap(refMap), typeMap(typeMap) {}

        const IR::Node *postorder(IR::MethodCallStatement *mcs) override {
            auto orig = getOriginal<IR::MethodCallStatement>();
            if (auto mi = P4::MethodInstance::resolve(orig, refMap, typeMap)) {
                if (auto em = mi->to<P4::ExternFunction>()) {
                    if (em->method->name == P4V1::V1Model::instance.drop.name) {
                        auto id_ = IR::ID(orig->getSourceInfo(), P4V1::V1Model::instance.standardMetadata.name);
                        auto ex = new IR::Member(
                                new IR::PathExpression(id_),
                                P4V1::V1Model::instance.standardMetadataType.egress_spec.name
                        );
                        return new IR::AssignmentStatement(ex, new IR::Constant(IR::Type::Bits::get(9), 511));
                    }
                }
            }
            return mcs;
        }
    };
    class HandleRevived : public Transform {
        P4::ReferenceMap *refMap;
        P4::TypeMap *typeMap;
        const IR::Node *postorder(IR::AssignmentStatement *asg) override {
            if (auto mem = asg->left->to<IR::Member>()) {
                if (mem->member.name == P4V1::V1Model::instance.standardMetadataType.egress_spec.name) {
                    if (auto pe = mem->expr->to<IR::PathExpression>()) {
                        if (pe->path->name ==  P4V1::V1Model::instance.standardMetadata.name) {
                            auto cd = new IR::LAnd(
                                    new IR::Equ(mem, new IR::Constant(IR::Type::Bits::get(9), 511)),
                                    new IR::LNot(new IR::Equ(asg->right, new IR::Constant(IR::Type::Bits::get(9), 511)))
                            );
                            return new IR::IfStatement(cd, analysis::call_bug(), asg);
                        }
                    }
                }
            }
            return asg;
        }
    public:
        HandleRevived(P4::ReferenceMap *refMap,
                      P4::TypeMap *typeMap) : refMap(refMap), typeMap(typeMap) {}
    };

    class V1Integration : public PassManager {
        P4::ReferenceMap *refMap;
        P4::TypeMap *typeMap;
        BMV2::V1ProgramStructure v1ProgramStructure;
        P4::EvaluatorPass *evaluator;
        BMV2::ParseV1Architecture *parseV1Architecture;
    public:
        V1Integration(P4::ReferenceMap *refMap,
                      P4::TypeMap *typeMap,
                      P4::EvaluatorPass *evaluator,
                      bool handleRevived = false) : refMap(refMap), typeMap(typeMap),
                                                                        evaluator(evaluator),
        parseV1Architecture(new BMV2::ParseV1Architecture(&v1ProgramStructure)) {
            setName("MidEnd_V1Integration");
            passes.push_back(new ZeroizeMetas(refMap, typeMap));
            passes.push_back(evaluator);
            passes.push_back(new VisitFunctor([this]() {
                this->evaluator->getToplevelBlock()->getMain()->apply(*parseV1Architecture);
            }));
            passes.push_back(new BMV2::ParseV1Architecture(&v1ProgramStructure));
            passes.push_back(new AddVerifyToParser(&v1ProgramStructure));
            passes.push_back(new EmptyControl(&v1ProgramStructure, BMV2::block_t::V1_VERIFY));
            passes.push_back(new AddIngressToParser(&v1ProgramStructure));
            passes.push_back(new EmptyControl(&v1ProgramStructure, BMV2::block_t::V1_INGRESS));
            passes.push_back(new AddEgressToParser(&v1ProgramStructure));
            passes.push_back(new EmptyControl(&v1ProgramStructure, BMV2::block_t::V1_EGRESS));
            passes.push_back(new VisitFunctor([this]() {
                this->refMap->clear();
                this->typeMap->clear();
            }));
            passes.push_back(evaluator);
            passes.push_back(new DropSemantics(refMap, typeMap));
            passes.push_back(evaluator);
            if (handleRevived) {
                passes.push_back(new HandleRevived(refMap, typeMap));
            }
        }
    };
}


#endif //P4C_V1_INTEGRATOR_H
