//
// Created by dragos on 19.01.2020.
//

#include "EgressSpecNotSet.h"
#include <analysis/analysis_helpers.h>
#include <bmv2/simple_switch/simpleSwitch.h>

namespace analysis {

class AssertAllInlined : public Inspector {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  BMV2::V1ProgramStructure *structure;

  bool preorder(const IR::P4Control *c) override {
    return c == structure->ingress;
  }
  bool preorder(const IR::P4Parser *) override { return false; }
  bool preorder(const IR::Function *) override { return false; }

  void postorder(const IR::MethodCallExpression *expression) override {
    if (auto mi = P4::MethodInstance::resolve(expression, refMap, typeMap)) {
      if (auto am = mi->to<P4::ApplyMethod>()) {
        if (am->object->is<IR::P4Control>()) {
          BUG("egress spec not set expecting inlined program, but %1%",
              expression);
        }
      } else if (mi->is<P4::FunctionCall>()) {
        BUG("egress spec not set expecting inlined program, but %1%",
            expression);
      }
    }
  }

public:
  AssertAllInlined(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                   BMV2::V1ProgramStructure *structure)
      : refMap(refMap), typeMap(typeMap), structure(structure) {}
};

class IsV1Model : public Inspector {};

class TrackEgressSpec : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  BMV2::V1ProgramStructure *structure;
  cstring trackVar = "__track_egress_spec";

  const IR::Node *preorder(IR::P4Parser *p) override {
    prune();
    return p;
  }
  const IR::Node *preorder(IR::Function *f) override {
    prune();
    return f;
  }
  const IR::Node *preorder(IR::P4Control *c) override {
    if (getOriginal<IR::P4Control>() != structure->ingress) {
      prune();
    }
    return c;
  }
  const IR::Parameter *standardMeta() {
    auto ctrl = findOrigCtxt<IR::P4Control>();
    CHECK_NULL(ctrl);
    BUG_CHECK(ctrl == structure->ingress, "inside another control %1%", ctrl);
    return ctrl->getApplyParameters()->parameters.at(2);
  }
  const IR::Node *postorder(IR::P4Control *c) override {
    BUG_CHECK(getOriginal<IR::P4Control>() == structure->ingress,
              "can't be here");
    c->controlLocals.insert(
        c->controlLocals.begin(),
        new IR::Declaration_Variable(trackVar, IR::Type_Boolean::get()));
    auto bcl = new IR::BlockStatement();
    bcl->push_back(setdefined(false));
    bcl->components.insert(bcl->components.end(), c->body->components.begin(),
                           c->body->components.end());
    auto finalcheck = new IR::IfStatement(isdefined(true), call_bug(), nullptr);
    bcl->push_back(finalcheck);
    c->body = bcl;
    return c;
  }
  const IR::Expression *isdefined(bool neg = false) {
    if (neg)
      return new IR::LNot(isdefined(false));
    return new IR::PathExpression(trackVar);
  }
  const IR::Statement *setdefined(bool d = true) {
    return new IR::AssignmentStatement(new IR::PathExpression(trackVar),
                                       new IR::BoolLiteral(d));
  }
  const IR::Node *postorder(IR::AssignmentStatement *stat) override {
    if (auto mem = stat->left->to<IR::Member>()) {
      if (mem->member.name ==
          P4V1::V1Model::instance.standardMetadataType.egress_spec.name) {
        if (auto pe = mem->expr->to<IR::PathExpression>()) {
          auto decl = refMap->getDeclaration(pe->path);
          if (decl == standardMeta()) {
            return new IR::BlockStatement({stat, setdefined()});
          } else {
            BUG("something is broken %1% <> %2%", decl, standardMeta());
          }
        }
      }
    }
    return stat;
  }
  const IR::Node *postorder(IR::MethodCallStatement *mce) override {
    auto mi = P4::MethodInstance::resolve(mce->methodCall, refMap, typeMap);
    if (auto ef = mi->to<P4::ExternFunction>()) {
      if (ef->method->name.name == P4V1::V1Model::instance.drop.name) {
        return new IR::BlockStatement({mce, setdefined()});
      }
    }
    return mce;
  }

public:
  TrackEgressSpec(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                  BMV2::V1ProgramStructure *structure)
      : refMap(refMap), typeMap(typeMap), structure(structure) {}
};

EgressSpecNotSet::EgressSpecNotSet(P4::ReferenceMap *refMap,
                                   P4::TypeMap *typeMap)
    : ApplyIfV1(refMap, typeMap) {
  innerPassManager.addPasses(
      {new AssertAllInlined(this->refMap, this->typeMap, &structure),
       new TrackEgressSpec(this->refMap, this->typeMap, &structure),
       new P4::ClearTypeMap(this->typeMap),
       new P4::ResolveReferences(this->refMap),
       new P4::TypeChecking(this->refMap, this->typeMap, true)});
}

ApplyIfV1::ApplyIfV1(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap), evaluator(refMap, typeMap) {
  passes.push_back(&evaluator);
  passes.push_back(new VisitFunctor([&]() {
    if (!evaluator.getToplevelBlock()->getMain()) {
      ::error("no main function found");
    } else {
      if (evaluator.getToplevelBlock()->getMain()->type->name == "V1Switch") {
        isv1 = true;
        evaluator.getToplevelBlock()->getMain()->apply(
            BMV2::ParseV1Architecture(&structure));
      }
    }
  }));
  passes.push_back(
      new VisitFunctor([&](const IR::Node *nd) -> const IR::Node * {
        if (isv1) {
          LOG4("v1 program found");
          return nd->apply(innerPassManager);
        }
        return nd;
      }));
}

class CheckForRegisters : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  BMV2::V1ProgramStructure *structure;

  const IR::Node *postorder(IR::MethodCallStatement *mcs) override {
    auto mi = P4::MethodInstance::resolve(mcs->methodCall, refMap, typeMap);
    if (auto em = mi->to<P4::ExternMethod>()) {
      auto metname = em->method->name.name;
      auto exname = em->actualExternType->name.name;
      auto &instance = P4V1::V1Model::instance;
      if (exname != instance.registers.name &&
          exname != instance.counter.name && exname != instance.meter.name) {
        return mcs;
      }
      auto obj = em->object;
      const IR::Declaration_Instance *decl = nullptr;
      if (obj->is<IR::Declaration_Instance>()) {
        decl = obj->to<IR::Declaration_Instance>();
      } else if (obj->is<IR::Parameter>()) {
        BUG("can't handle extern objects passed as constructor parameters, "
            "remove "
            "them before calling this pass");
      }
      CHECK_NULL(decl);
      auto sz = decl->arguments->at(0)->expression;
      const IR::Expression *idx = nullptr;
      if (exname == instance.registers.name) {
        if (metname == instance.registers.write.name) {
          idx = mi->expr->arguments->at(0)->expression;
        } else if (metname == instance.registers.read.name) {
          idx = mi->expr->arguments->at(1)->expression;
        }
      } else if (exname == instance.counter.name) {
        if (metname == instance.counter.increment.name) {
          idx = mi->expr->arguments->at(0)->expression;
        }
      } else if (exname == instance.meter.name) {
        if (metname == instance.meter.executeMeter.name) {
          idx = mi->expr->arguments->at(0)->expression;
        }
      }
      if (idx && sz) {
        auto idxtp = typeMap->getType(idx);
        const IR::Expression *idxgezero = new IR::Geq(idx, new IR::Constant(0));
        if (auto tb = idxtp->to<IR::Type_Bits>()) {
          if (!tb->isSigned) {
            idxgezero = nullptr;
          }
        }
        auto idxltsz = new IR::Lss(idx, sz);
        const IR::Expression *conj = nullptr;
        if (idxgezero)
          conj = new IR::LAnd(idxgezero, idxltsz);
        else
          conj = idxltsz;
        auto check =
            new IR::IfStatement(new IR::LNot(conj), call_bug(), nullptr);
        return new IR::BlockStatement({check, mcs});
      }
    }
    return mcs;
  }

public:
  CheckForRegisters(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                    BMV2::V1ProgramStructure *structure)
      : refMap(refMap), typeMap(typeMap), structure(structure) {}
};

RegistersOutOfBounds::RegistersOutOfBounds(P4::ReferenceMap *refMap,
                                           P4::TypeMap *typeMap)
    : ApplyIfV1(refMap, typeMap) {
  innerPassManager.addPasses(
      {new CheckForRegisters(this->refMap, this->typeMap, &structure),
       new P4::ClearTypeMap(this->typeMap),
       new P4::ResolveReferences(this->refMap),
       new P4::TypeInference(this->refMap, this->typeMap, false),
       new P4::ResolveReferences(this->refMap)});
}

class RemoveUpdateVerify : public Transform {
  BMV2::V1ProgramStructure *structure;

public:
  RemoveUpdateVerify(BMV2::V1ProgramStructure *structure)
      : structure(structure) {}

private:
  const IR::Node *postorder(IR::P4Control *ctrl) override {
    auto orig = getOriginal<IR::P4Control>();
    if (orig == structure->verify_checksum ||
        orig == structure->compute_checksum) {
      ctrl->body = new IR::BlockStatement();
    }
    return ctrl;
  }
};

RemoveV1Controls::RemoveV1Controls(P4::ReferenceMap *refMap,
                                   P4::TypeMap *typeMap)
    : ApplyIfV1(refMap, typeMap) {
  innerPassManager.addPasses({
    new RemoveUpdateVerify(&structure)
  });
}
}