//
// Created by dragos on 16.04.2019.
//
#include <common/resolveReferences/referenceMap.h>
#include <p4/typeMap.h>
#include <p4/methodInstance.h>
#include <p4/evaluator/substituteParameters.h>
#include "instrumentation_helper.h"

//TODO: refactor hideous code duplication
const IR::Node *analysis::change_methods::postorder(IR::MethodCallExpression *mce) {
    auto mi = P4::MethodInstance::resolve(getOriginal<IR::MethodCallExpression>(),
                                          refMap,
                                          typeMap);
    if (auto em = mi->to<P4::ExternMethod>()) {
        auto IT = changed_methods->find(em->method);
        if (IT != changed_methods->end()) {
            auto withwhat = IT->second;
            auto *args = new IR::Vector<IR::Argument>();
            for (auto p : *withwhat->getParameters()) {
                args->push_back(mi->substitution.lookupByName(p->getName()));
                if (p->getAnnotation("instrument")) {
                    args->push_back(new IR::Argument(new IR::Constant(0, 1)));
                }
            }
            auto newmce = mce->clone();
            newmce->arguments = args;
            LOG4("changed from " << mce << " to " << newmce);
            return newmce;
        }
    } else if (auto ef = mi->to<P4::ExternFunction>()) {
        auto IT = changed_methods->find(ef->method);
        if (IT != changed_methods->end()) {
            auto withwhat = IT->second;
            auto *args = new IR::Vector<IR::Argument>();
            for (auto p : *withwhat->getParameters()) {
                if (p->getAnnotation("instrument") &&
                    p->getAnnotation("instrument")->expr[0]->to<IR::StringLiteral>()->value == instrument_name) {
                    args->push_back(new IR::Argument(new IR::Constant(IR::Type_Bits::get(1, false), 1)));
                } else {
                    args->push_back(mi->substitution.lookupByName(p->getName()));
                }
            }
            auto newmce = mce->clone();
            newmce->arguments = args;
            LOG4("changed from " << mce << " to " << newmce);
            return newmce;
        }
    } else if (auto fc = mi->to<P4::FunctionCall>()) {
        auto IT = changed_funs->find(fc->function);
        if (IT != changed_funs->end()) {
            auto withwhat = IT->second;
            auto *args = new IR::Vector<IR::Argument>();
            for (auto p : *withwhat->getParameters()) {
                if (p->getAnnotation("instrument") &&
                    p->getAnnotation("instrument")->expr[0]->to<IR::StringLiteral>()->value == instrument_name) {
                    args->push_back(new IR::Argument(new IR::Constant(IR::Type_Bits::get(1, false), 1)));
                } else {
                    args->push_back(mi->substitution.lookupByName(p->getName()));
                }
            }
            auto newmce = mce->clone();
            newmce->arguments = args;
            LOG4("changed from " << mce << " to " << newmce);
            return newmce;
        }
    } else if (auto app = mi->to<P4::ApplyMethod>()) {
        auto IT = changed_applies->find(app->applyObject);
        if (IT != changed_applies->end()) {
            auto withwhat = IT->second;
            auto *args = new IR::Vector<IR::Argument>();
            for (auto p : *withwhat->getApplyParameters()) {
                if (p->getAnnotation("instrument") &&
                    p->getAnnotation("instrument")->expr[0]->to<IR::StringLiteral>()->value == instrument_name) {
                    args->push_back(new IR::Argument(new IR::Constant(IR::Type_Bits::get(1, false), 1)));
                } else {
                    args->push_back(mi->substitution.lookupByName(p->getName()));
                }
            }
            auto newmce = mce->clone();
            newmce->arguments = args;
            LOG4("changed from " << mce << " to " << newmce);
            return newmce;
        }
    } else if (auto act = mi->to<P4::ActionCall>()) {
        auto IT = changed_actions->find(act->action);
        if (IT != changed_actions->end()) {
            auto withwhat = IT->second;
            auto *args = new IR::Vector<IR::Argument>();
            for (auto p : *withwhat->getParameters()) {
                if (p->getAnnotation("instrument") &&
                    p->getAnnotation("instrument")->expr[0]->to<IR::StringLiteral>()->value == instrument_name) {
                    args->push_back(new IR::Argument(new IR::Constant(IR::Type_Bits::get(1, false), 1)));
                } else {
                    auto byname = mi->substitution.lookupByName(p->getName());
                    if (byname)
                        args->push_back(byname);
                    else break;
                }
            }
            auto newmce = mce->clone();
            newmce->arguments = args;
            LOG4("changed from " << mce << " to " << newmce);
            return newmce;
        }
    }
    return mce;
}

const IR::Node *analysis::change_methods::postorder(IR::Method *method) {
    auto I = changed_methods->find(getOriginal<IR::Method>());
    if (I != changed_methods->end()) {
        LOG4("changed from " << method << " to " << I->second);
        return I->second;
    }
    return method;
}

const IR::Declaration *analysis::rewrite_methods::mkInstrument(const IR::Declaration *against) {
    auto annotation = new IR::Annotation("instrument",
                                         IR::Vector<IR::Expression>({
                                                                            new IR::StringLiteral(instrument_name),
                                                                            new IR::PathExpression(against->name)
                                                                    })
    );
    auto annotations = new IR::Annotations(
            IR::Vector<IR::Annotation>({
                                               annotation
                                       })
    );
    IR::Declaration *novel = nullptr;
    auto nm = cstring(against->name + "_" + instrument_name);
    if (against->is<IR::StructField>()) {
        novel = new IR::StructField(cstring(nm), annotations, type);
    } else if (against->is<IR::Parameter>()) {
        auto parm = against->to<IR::Parameter>();
        novel = new IR::Parameter(cstring(nm), annotations, parm->direction, type);
    } else if (against->is<IR::Declaration_Variable>()) {
        novel = new IR::Declaration_Variable(cstring(nm), annotations, type);
    }
    return novel;
}

void analysis::rewrite_methods::postorder(const IR::Method *method) {
    auto mt = method->type->clone();
    auto *parms = new IR::ParameterList();
    bool any_change = false;
    for (auto parm : *method->type->parameters) {
        parms->push_back(parm);
        if (filter(parm)) {
            LOG4("identified parm in  " << method << " " << parm);
            auto instrument = mkInstrument(parm);
            parms->push_back(instrument->to<IR::Parameter>());
            any_change = true;
        }
    }
    mt->parameters = parms;
    auto metclone = method->clone();
    metclone->type = mt;
    if (any_change)
        changed_methods->emplace(method, metclone);
}

void analysis::rewrite_methods::postorder(const IR::Function *fun) {
    auto mt = fun->type->clone();
    auto *parms = new IR::ParameterList();
    bool any_change = false;
    for (auto parm : *fun->type->parameters) {
        parms->push_back(parm);
        if (filter(parm)) {
            auto instrument = mkInstrument(parm);
            parms->push_back(instrument->to<IR::Parameter>());
            any_change = true;
        }
    }
    mt->parameters = parms;
    auto metclone = fun->clone();
    metclone->type = mt;
    if (any_change)
        changed_funs->emplace(fun, metclone);
}

void analysis::rewrite_methods::postorder(const IR::P4Parser *app) {
    analyze(app);
}

void analysis::rewrite_methods::postorder(const IR::P4Control *method) {
    analyze(method);
}

void analysis::rewrite_methods::analyze(const IR::IApply *app) {
    auto parms = new IR::ParameterList();
    for (auto p : *app->getApplyParameters()) {
        if (filter(p)) {
            parms->push_back(mkInstrument(p)->to<IR::Parameter>());
        }
    }
    // TODO: also look at Type_Control / Type_Parser / Type_Table -> seems
    // that they are also IApply (guess that this is valid for the constructor)
    if (auto parser = app->to<IR::P4Parser>()) {
        auto p = parser->clone();
        auto ptp = p->type->clone();
        ptp->applyParams = parms;
        p->type = ptp;
        changed_applies->emplace(app, p);
    } else if (auto control = app->to<IR::P4Control>()) {
        auto c = control->clone();
        auto ctp = c->type->clone();
        c->type = ctp;
        ctp->applyParams = parms;
        changed_applies->emplace(app, c);
    }
}

void analysis::rewrite_methods::postorder(const IR::P4Action *act) {
    auto *parms = new IR::ParameterList();
    bool any_change = false;
    for (auto parm : *act->getParameters()) {
        parms->push_back(parm);
        if (filter(parm)) {
            LOG4("identified parm in  " << act << " " << parm);
            auto instrument = mkInstrument(parm);
            parms->push_back(instrument->to<IR::Parameter>());
            any_change = true;
        }
    }
    auto metclone = act->clone();
    metclone->parameters = parms;
    if (any_change)
        changed_actions->emplace(act, metclone);
}

void analysis::find_generics::postorder(const IR::Type *type_method) {
    if (auto gen = type_method->to<IR::IMayBeGenericType>()) {
        if (gen->getTypeParameters() != nullptr) {
            for (auto p : gen->getTypeParameters()->parameters) {
                LOG4("generics: " << gen << ": " << type_method->node_type_name() << " [" << p << "]");
            }
        }
    }
}

void analysis::find_generics::postorder(const IR::Declaration_Instance *instance) {
    auto actualType = typeMap->getType(instance, false);
    if (auto canon = actualType->to<IR::Type_SpecializedCanonical>()) {
        auto bt = canon->baseType;
        BUG_CHECK(bt->is<IR::Type_Declaration>(), "need type declaration as IMayBeGeneric");
        auto decl = bt->to<IR::Type_Declaration>();
        cstring newname = refMap->newName(decl->name);
        auto subst = canon->substituted->to<IR::Type_Declaration>()->clone();
        subst->name = newname;
    } else {
//        LOG4("declared instance " << instance->name << " :" << actualType);
    }
}

void analysis::find_generics::postorder(const IR::ConstructorCallExpression *expression) {
    auto constr = typeMap->getTypeType(expression->constructedType, true);
    LOG4("constructor called to get " << constr);
}

void analysis::find_generics::postorder(const IR::MethodCallExpression *expression) {
    auto mi = P4::MethodInstance::resolve(expression, refMap, typeMap);
    if (!typeMap->equivalent(mi->actualMethodType, mi->originalMethodType)) {
        LOG4("found method instance " << mi->actualMethodType << " vs " << mi->originalMethodType);
        if (auto emethod = mi->to<P4::ExternMethod>()) {
            auto newname = refMap->newName(emethod->method->name);
            auto newdecl = emethod->method->clone();
            newdecl->type = mi->actualMethodType->to<IR::Type_Method>();
            newdecl->name = newname;
            LOG4("specializing extern method " << emethod->method->name << " " << newdecl);
        } else if (auto efun = mi->to<P4::ExternFunction>()) {
            auto newname = refMap->newName(efun->method->name);
            auto newdecl = efun->method->clone();
            newdecl->type = mi->actualMethodType->to<IR::Type_Method>();
            newdecl->name = newname;
            LOG4("specializing extern function " << efun->method->name << " " << newdecl);
        }
    }
}

bool analysis::find_blocks::preorder(const IR::Block *block) {
    LOG4("visiting " << block);
    for (auto cv : block->constantValue) {
        if (cv.second->is<IR::Block>()) {
            visit(cv.second->to<IR::Block>());
        }
    }
    return true;
}

void analysis::find_blocks::postorder(const IR::InstantiatedBlock *instantiatedBlock) {
    if (auto canon = instantiatedBlock->instanceType->to<IR::Type_SpecializedCanonical>()) {
        auto bt = canon->baseType;

        auto &base = typeMappings[bt];
        auto anyeq = std::any_of(base.begin(), base.end(), [this, canon](const IR::Type *t) {
            return typeMap->equivalent(t, canon);
        });
        if (anyeq)
            return;
        BUG_CHECK(bt->is<IR::Type_Declaration>(), "need type declaration as IMayBeGeneric");
        auto decl = bt->to<IR::Type_Declaration>();
        cstring newname = refMap->newName(decl->name);
        auto subst = canon->substituted->to<IR::Type_Declaration>()->clone();
        subst->name = newname;
        base.emplace_back(canon);
        newTypeDeclarations[bt].emplace_back(subst);
        LOG4("declared type instance" << ": " << subst);
        if (auto cb = instantiatedBlock->to<IR::ControlBlock>()) {
            auto subst = new P4::TypeVariableSubstitution(*typeMap->getSubstitutions());
            auto gen = bt->to<IR::IMayBeGenericType>();
            unsigned idx = 0;
            for (auto p : gen->getTypeParameters()->parameters) {
                subst->setBinding(p, (*canon->arguments)[idx]);
                ++idx;
            }
            visit(cb->container);
            P4::SubstituteParameters substVisitor(refMap, new P4::ParameterSubstitution, subst);
            auto ctrl = cb->container->apply(substVisitor);
            LOG4("control: " << ctrl);
        }
    }
}
