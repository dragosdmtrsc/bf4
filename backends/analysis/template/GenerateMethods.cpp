//
// Created by dragos on 12.12.2019.
//

#include "GenerateMethods.h"
#include <build/ir/ir-generated.h>
#include <common/resolveReferences/resolveReferences.h>
#include <p4/methodInstance.h>
#include <p4/typeChecking/typeChecker.h>

namespace analysis {

class DoGenerateMethods : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

  void zero_out(const IR::Type *kind, const IR::Expression *expr,
                IR::BlockStatement *stats) {
    if (kind->is<IR::Type_Struct>()) {
      auto sl = kind->to<IR::Type_Struct>();
      for (auto fld : sl->fields) {
        zero_out(typeMap->getType(fld), new IR::Member(expr, fld->name), stats);
      }
    } else if (kind->is<IR::Type_Bits>() || kind->is<IR::Type_Boolean>() ||
               kind->is<IR::Type_Enum>()) {
      const IR::Expression *val = nullptr;
      if (kind->is<IR::Type_Bits>() || kind->is<IR::Type_InfInt>()) {
        val = new IR::Constant(kind, 0);
      } else if (kind->is<IR::Type_Boolean>()) {
        val = new IR::BoolLiteral(false);
      } else if (kind->is<IR::Type_Enum>()) {
        auto tenum = kind->to<IR::Type_Enum>();
        auto mem = tenum->members.at(0);
        auto tn = new IR::Type_Name(tenum->name);
        auto tne = new IR::TypeNameExpression(tn);
        val = new IR::Member(tne, mem->name);
      } else if (kind->is<IR::Type_Error>()) {
        auto terror = kind->to<IR::Type_Error>();
        auto mem = terror->members.at(0);
        auto tn = new IR::Type_Name(terror->name);
        auto tne = new IR::TypeNameExpression(tn);
        val = new IR::Member(tne, mem->name);
      }
      CHECK_NULL(val);
      stats->push_back(new IR::AssignmentStatement(expr, val));
    } else if (kind->is<IR::Type_Header>()) {
      auto setInvalid = new IR::Member(expr, IR::Type_Header::setInvalid);
      auto mce = new IR::MethodCallExpression(setInvalid);
      stats->push_back(new IR::MethodCallStatement(mce));
    } else if (kind->is<IR::Type_Stack>()) {
      auto stt = kind->to<IR::Type_Stack>();
      auto len = stt->getSize();
      for (unsigned i = 0; i != len; ++i) {
        zero_out(typeMap->getTypeType(stt->elementType, true),
                 new IR::ArrayIndex(expr, new IR::Constant(i)), stats);
      }
    }
  }
  const IR::Node *postorder(IR::MethodCallStatement *mcs) override {
    auto orig = getOriginal<IR::MethodCallStatement>();
    auto mi = P4::MethodInstance::resolve(orig, refMap, typeMap);
    if (auto ef = mi->to<P4::ExternFunction>()) {
      if (ef->method->name == "zero_out") {
        auto stats = new IR::BlockStatement();
        auto aex = mcs->methodCall->arguments->at(0)->expression;
        zero_out(typeMap->getType(aex), aex, stats);
        return stats;
      }
    }
    return mcs;
  }

public:
  DoGenerateMethods(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}
};

GenerateMethods::GenerateMethods(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap) {
  passes.push_back(new DoGenerateMethods(refMap, typeMap));
  addPasses({new P4::ClearTypeMap(typeMap), new P4::ResolveReferences(refMap),
             new P4::TypeInference(refMap, typeMap, false)});
}
}