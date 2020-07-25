//
// Created by dragos on 06.05.2019.
//

#include "HandleHeaders.h"
#include "analysis_helpers.h"
#include "cfg_algos.h"
#include <analysis/ub/AnalysisContext.h>
#include <common/resolveReferences/resolveReferences.h>
#include <p4/typeChecking/typeChecker.h>

namespace analysis {
class MakeBuiltins : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

public:
  MakeBuiltins(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}

  const IR::Node *preorder(IR::MethodCallExpression *mce) override {
    auto mi = P4::MethodInstance::resolve(
        getOriginal<IR::MethodCallExpression>(), refMap, typeMap);
    if (mi->is<P4::BuiltInMethod>()) {
      auto bim = mi->to<P4::BuiltInMethod>();
      if (bim->name == IR::Type_Header::isValid) {
        auto upon = mce->method->to<IR::Member>()->expr;
        prune();
        return new IR::Member(upon, "valid_");
      } else {
        BUG("got method builtin method call %1% which should have been cast "
            "away",
            mce);
      }
    }
    return mce;
  }
  const IR::Node *preorder(IR::MethodCallStatement *mcs) override {
    auto mi = P4::MethodInstance::resolve(
        getOriginal<IR::MethodCallStatement>(), refMap, typeMap);
    if (mi->is<P4::BuiltInMethod>()) {
      auto bim = mi->to<P4::BuiltInMethod>();
      if (bim->name == IR::Type_Header::setValid ||
          bim->name == IR::Type_Header::setInvalid) {
        auto upon = mcs->methodCall->method->to<IR::Member>()->expr;
        auto v = bim->name == IR::Type_Header::setValid;
        prune();
        return new IR::AssignmentStatement(new IR::Member(upon, "valid_"),
                                           new IR::BoolLiteral(v));
      }
    }
    return mcs;
  }
};

// parser p(..., out H a, ...) /
// a.x1.....xn is header =>
// state start' { a.x1.....xn.setInvalid(); start }
class MakeHeadersInvalid : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

public:
  MakeHeadersInvalid(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}

private:
  const IR::Node *postorder(IR::ParserState *pstate) override {
    auto parser = findOrigCtxt<IR::P4Parser>();
    if (pstate->name.name == IR::ParserState::start) {
      IR::IndexedVector<IR::StatOrDecl> stats;
      for (auto p : *parser->getApplyParameters()) {
        if (p->direction != IR::Direction::Out)
          continue;
        const IR::Expression *crt = new IR::PathExpression(
            pstate->srcInfo, new IR::Path(pstate->srcInfo, p->name));
        auto tp = typeMap->getType(p);
        std::function<void(const IR::Type *, const IR::Expression *)> recurs;
        recurs = [&](const IR::Type *tp, const IR::Expression *crt) {
          if (tp->is<IR::Type_Header>()) {
            auto mcs = new IR::MethodCallStatement(new IR::MethodCallExpression(
                new IR::Member(crt, IR::Type_Header::setInvalid)));
            stats.push_back(mcs);
          } else if (tp->is<IR::Type_StructLike>()) {
            for (auto sf : tp->to<IR::Type_StructLike>()->fields) {
              // recur
              recurs(typeMap->getType(sf), new IR::Member(crt, sf->name));
            }
          } else if (tp->is<IR::Type_Stack>()) {
            auto stt = tp->to<IR::Type_Stack>();
            auto elemt = typeMap->getTypeType(stt->elementType, true);
            for (unsigned i = 0; i != stt->getSize(); ++i) {
              recurs(elemt, new IR::ArrayIndex(crt, new IR::Constant(i)));
            }
          }
        };
        recurs(tp, crt);
      }
      stats.insert(stats.end(), pstate->components.begin(),
                   pstate->components.end());
      pstate->components = std::move(stats);
    }
    return pstate;
  }
};

class ReplaceAllHeaders : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

public:
  ReplaceAllHeaders(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}

  const IR::Node *postorder(IR::Type_Declaration *decl) override {
    if (auto th = decl->to<IR::Type_Header>()) {
      auto thcopy = th->fields.clone();
      thcopy->push_back(new IR::StructField("valid_", IR::Type_Boolean::get()));
      auto strt = new IR::Type_Struct(decl->srcInfo, decl->name, *thcopy);
      auto annotations = new IR::Annotations();
      annotations->addAnnotation(
          AnalysisLibrary::instance.headerAnnotation.name,
          new IR::StringLiteral(decl->name.name));
      strt->annotations = annotations;
      return strt;
    }
    return decl;
  }
};

HandleHeaders::HandleHeaders(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap) {
  passes.push_back(new MakeHeadersInvalid(refMap, typeMap));
  addPasses({new P4::ResolveReferences(refMap),
             new P4::TypeInference(refMap, typeMap, false)});
  passes.push_back(new ReplaceAllHeaders(refMap, typeMap));
  passes.push_back(new MakeBuiltins(refMap, typeMap));
  addPasses({new P4::ClearTypeMap(typeMap), new P4::ResolveReferences(refMap),
             new P4::TypeInference(refMap, typeMap, false)});
}

class FindArrayIndices : public Inspector {
  std::unordered_set<const IR::ArrayIndex *> arrays;
  void postorder(const IR::ArrayIndex *idx) override {
    if (!idx->right->is<IR::Constant>())
      arrays.emplace(idx);
  }

public:
  FindArrayIndices() {}
  std::unordered_set<const IR::ArrayIndex *> getIndices(const IR::Node *n) {
    arrays.clear();
    n->apply(*this);
    return std::move(arrays);
  }
};

class NormalizeArrayIndexAccess : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  FindArrayIndices idces;

public:
  NormalizeArrayIndexAccess(ReferenceMap *refMap, TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}

private:
  const IR::Node *preorder(IR::ParserState *pstate) override {
    prune();
    if (pstate->selectExpression->is<IR::SelectExpression>()) {
      auto idxes = idces.getIndices(pstate->selectExpression);
      if (!idxes.empty()) {
        for (auto idx : idxes) {
          auto t = refMap->newName("tmp");
          pstate->components.push_back(
              new IR::Declaration_Variable(t, typeMap->getType(idx)));
          pstate->components.push_back(
              new IR::AssignmentStatement(new IR::PathExpression(t), idx));
          pstate->selectExpression =
              ReplaceOccurence::replaceStatic(idx, new IR::PathExpression(t),
                                              pstate->selectExpression)
                  ->to<IR::Expression>();
        }
      }
    }
    return pstate;
  }
};

class DoHandleArrayIndex : public Transform {
  // INPUTS:
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

  // COMPUTED:
  FindArrayIndices findArrayIndices;
  const IR::Node *preorder(IR::Node *n) override {
    bool do_prune = false;
    const IR::Node *nn = n;
    if (auto cd = analysis::is_if(getOriginal(), typeMap)) {
      if (!findArrayIndices.getIndices(cd->cond).empty())
        BUG("if condition must not contain array index");
      do_prune = true;
    } else if (auto sel = match_selex(getOriginal())) {
      if (!findArrayIndices.getIndices(sel).empty())
        BUG("selex %1% must not contain array index", sel);
    } else if (analysis::is_assign(getOriginal()) ||
               analysis::is_extern_method_call(getOriginal())) {
      do_prune = true;
    }
    if (do_prune) {
      nn = operator()(getOriginal());
      if (nn != getOriginal())
        LOG4("in " << n << " " << nn);
      prune();
    }
    if (nn == getOriginal())
      return n;
    return nn;
  }

public:
  DoHandleArrayIndex(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}
  const IR::Node *operator()(const IR::Node *n) {
    auto indices = findArrayIndices.getIndices(n);
    if (indices.empty())
      return n;
    LOG4("indices found in " << n);
    BUG_CHECK(indices.size() == 1,
              "can't handle access to multiple arrays at once in %1%", n);
    auto idx = *indices.begin();
    auto arrt = typeMap->getType(idx->left)->to<IR::Type_Stack>();
    const IR::Statement *crt = analysis::call_bug();
    for (int i = arrt->getSize() - 1; i >= 0; --i) {
      auto infi = new IR::Constant(i);
      auto arri = idx->clone();
      arri->right = new IR::Constant(new IR::Type_InfInt(), i);
      crt = new IR::IfStatement(
          new IR::Equ(idx->right, infi),
          ReplaceOccurence::replaceStatic(idx, arri, n)->to<IR::Statement>(),
          crt);
    }
    LOG4(n << " is now " << crt);
    return crt;
  }
};

HandleArrayIndices::HandleArrayIndices(ReferenceMap *refMap, TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap) {
  addPasses({new NormalizeArrayIndexAccess(refMap, typeMap),
             new DoHandleArrayIndex(refMap, typeMap),
             new P4::ResolveReferences(refMap),
             new P4::TypeInference(refMap, typeMap, false)});
}
}
