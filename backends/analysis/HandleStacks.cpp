//
// Created by dragos on 20.04.2019.
//

#include "HandleStacks.h"
#include <common/resolveReferences/resolveReferences.h>
#include <p4/coreLibrary.h>
#include <p4/methodInstance.h>
#include <p4/typeChecking/typeChecker.h>
#include "analysis_helpers.h"
#include "version_propagator.h"

namespace analysis {
class FindStackTypes : public Inspector {
  StackRegistrar *sr;

 public:
  FindStackTypes(StackRegistrar *sr) : sr(sr) {}

  void postorder(const IR::Declaration *decl) override {
    auto crt = getChildContext();
    auto parent = crt->parent;
    while (parent && !parent->node->is<IR::P4Program>()) {
      crt = parent;
      parent = crt->parent;
    }
    if (parent) sr->put(decl, crt->node);
  }
};

class DeclareStackTypeWrappers : public Transform {
  StackRegistrar *sr;

 public:
  DeclareStackTypeWrappers(StackRegistrar *sr) : sr(sr) {}

  const IR::Node *preorder(IR::P4Program *prog) override {
    unsigned i = 0;
    std::map<std::pair<const IR::Type *, unsigned>, unsigned> already;
    for (auto o : prog->objects) {
      auto I = sr->insertPoints.find(o);
      if (I != sr->insertPoints.end()) {
        for (const auto &s : I->second) {
          already.emplace(s, i);
        }
      }
      ++i;
    }
    for (auto p : already) {
      auto I = prog->objects.begin() + p.second;
      std::stringstream nm;
      auto typeDecl = p.first.first->to<IR::Type_Declaration>();
      nm << typeDecl->getName().name << "_" << p.first.second;
      auto td = new IR::Type_Struct(cstring(nm.str()));
      td->annotations = td->annotations->addAnnotation("array", nullptr);
      auto f1 = new IR::StructField("nxt", IR::Type_Bits::get(16, false));
      td->fields.push_back(f1);
      auto sttype = new IR::Type_Stack(new IR::Type_Name(typeDecl->getName()),
                                       new IR::Constant(p.first.second));
      auto rawAnnotation = new IR::Annotation("raw", {});
      auto annots = new IR::Annotations({rawAnnotation});
      auto f2 = new IR::StructField("elements", annots, sttype);
      td->fields.push_back(f2);
      prog->objects.insert(I, td);
    }
    return prog;
  }
};

class GetPathsTo : public Inspector {
  P4::TypeMap *typeMap;
  std::vector<Path> paths;
  Path crt;

 private:
 public:
  GetPathsTo(TypeMap *typeMap) : typeMap(typeMap) {}

 private:
  bool preorder(const IR::StructField *sf) override {
    auto tp = typeMap->getType(sf);
    crt.emplace_back(sf->name.name);
    if (tp->is<IR::Type_Struct>()) {
      auto strt = tp->to<IR::Type_Struct>();
      if (strt->getAnnotation("array")) {
        paths.emplace_back(crt);
      }
    } else if (tp->is<IR::Type_Stack>()) {
      auto st = tp->to<IR::Type_Stack>();
      if (!st->getAnnotation("raw")) {
        paths.emplace_back(crt);
      }
      for (unsigned i = 0; i != st->getSize(); ++i) {
        crt.emplace_back(i);
        visit(st->elementType);
        crt.pop_back();
      }
    }
    visit(tp);
    return true;
  }
  void postorder(const IR::StructField *) override { crt.pop_back(); }

 public:
  std::vector<Path> getPaths(const IR::Node *t, Path initial) {
    crt = std::move(initial);
    t->apply(*this);
    return std::move(paths);
  }
};

class AddInitCodeToParser : public Transform {
  IR::IndexedVector<IR::StatOrDecl> what;

 public:
  AddInitCodeToParser(IR::IndexedVector<IR::StatOrDecl> what)
      : what(std::move(what)) {}

 private:
  const IR::Node *postorder(IR::ParserState *state) override {
    if (what.empty()) return state;
    if (state->name == IR::ParserState::start) {
      auto old = std::move(state->components);
      state->components = std::move(what);
      state->components.insert(state->components.end(), old.begin(), old.end());
    }
    return state;
  }
};

class ParserInitNexts : public Transform {
  P4::TypeMap *typeMap;
  std::unordered_map<const IR::P4Parser *, const IR::P4Parser *> parsers;

 public:
  ParserInitNexts(TypeMap *typeMap) : typeMap(typeMap) {}

 private:
  const IR::Node *postorder(IR::P4Parser *p) override {
    auto orig = getOriginal<IR::P4Parser>();
    auto I = parsers.find(orig);
    if (I != parsers.end() && I->second != orig) {
      return I->second;
    }
    return p;
  }

  const IR::Node *postorder(IR::Parameter *parameter) override {
    auto orig = getOriginal<IR::Parameter>();
    if (orig->direction == IR::Direction::Out) {
      auto parmList = findOrigCtxt<IR::ParameterList>();
      auto parser = findOrigCtxt<IR::P4Parser>();
      if (parser && parmList && parser->getApplyParameters() == parmList) {
        auto E = parsers.emplace(parser, parser);
        auto &impl = E.first->second;
        auto parmType = typeMap->getType(orig);
        auto vec = GetPathsTo(typeMap).getPaths(parmType,
                                                Path({parameter->name.name}));
        IR::IndexedVector<IR::StatOrDecl> stats;
        for (const auto &p : vec) {
          unsigned idx = 0;
          const IR::Expression *crt = new IR::PathExpression(p[idx++].str);
          for (; idx != p.size(); ++idx) {
            if (p[idx].is_str()) {
              crt = new IR::Member(crt, p[idx].str);
            } else {
              crt = new IR::ArrayIndex(
                  crt, new IR::Constant(new IR::Type_InfInt(), p[idx].nr));
            }
          }
          auto nxt = new IR::Member(crt, "nxt");
          stats.push_back(
              new IR::AssignmentStatement(nxt, new IR::Constant(0)));
        }
        E.first->second = impl->apply(AddInitCodeToParser(std::move(stats)));
      }
    }
    return parameter;
  }
};

class RevampExpressions : public Transform {
  StackRegistrar *sr;

 public:
  RevampExpressions(StackRegistrar *sr) : sr(sr) {}

  bool isArrayMember(const IR::Expression *expr, const IR::Type_Stack *&ts,
                     cstring &member, const IR::Expression *&stackExp) {
    if (expr->is<IR::Member>()) {
      auto mem = expr->to<IR::Member>();
      auto exptype = sr->typeMap->getType(mem->expr);
      if (exptype->is<IR::Type_Stack>()) {
        ts = exptype->to<IR::Type_Stack>();
        member = mem->member;
        stackExp = mem->expr;
        return true;
      }
    }
    return false;
  }

  const IR::Node *postorder(IR::Member *mem) override {
    auto exptype = sr->typeMap->getType(mem->expr);
    if (auto ts = exptype->to<IR::Type_Stack>()) {
      auto nxtIndex = new IR::Member(mem->expr, "nxt");
      auto elems = new IR::Member(mem->expr, "elements");
      if (mem->member == IR::Type_Stack::next) {
        return new IR::ArrayIndex(elems, nxtIndex);
      } else if (mem->member == IR::Type_Stack::last) {
        auto idx = new IR::Sub(nxtIndex, new IR::Constant(1));
        return new IR::ArrayIndex(elems, idx);
      } else if (mem->member == IR::Type_Stack::lastIndex) {
        return new IR::Sub(nxtIndex, new IR::Constant(1));
      } else if (mem->member == IR::Type_Stack::arraySize) {
        return ts->size;
      }
    }
    return mem;
  }
  const IR::Node *postorder(IR::Declaration *decl) override {
    auto orig = getOriginal<IR::Declaration>();
    auto tp = sr->typeMap->getType(orig);
    if (auto ts = tp->to<IR::Type_Stack>()) {
      auto inn = sr->typeMap->getTypeType(ts->elementType, true)
                     ->to<IR::Type_Declaration>();
      std::stringstream ss;
      ss << inn->name.name << "_"
         << ts->size->to<IR::Constant>()->value.get_ui();
      cstring nm = ss.str();
      auto tname = new IR::Type_Name(nm);
      if (auto p = decl->to<IR::Parameter>()) {
        auto pclone = p->clone();
        pclone->type = tname;
        return pclone;
      } else if (auto sm = decl->to<IR::StructField>()) {
        auto sclone = sm->clone();
        sclone->type = tname;
        return sclone;
      } else if (auto var = decl->to<IR::Declaration_Variable>()) {
        auto varclone = var->clone();
        varclone->type = tname;
        return varclone;
      }
    }
    return decl;
  }
  const IR::Node *postorder(IR::ArrayIndex *ai) override {
    auto elems = new IR::Member(ai->left, "elements");
    ai->left = elems;
    return ai;
  }

  const IR::Node *postorder(IR::Type *tp) override {
    auto orig = getOriginal<IR::Type>();
    auto tt = sr->typeMap->getType(orig);
    if (tt && tt->is<IR::Type_Type>()) {
      auto thetype = tt->to<IR::Type_Type>()->type;
      if (auto ts = thetype->to<IR::Type_Stack>()) {
        std::stringstream ss;
        ss << ts->elementType->to<IR::Type_Declaration>()->getName().name;
        ss << "_" << ts->size->to<IR::Constant>()->value.get_ui();
        auto tn = new IR::Type_Name(cstring(ss.str()));
        LOG4("type stack " << thetype << " found within " << orig
                           << " replace with " << tn);
        return tn;
      }
    }
    return tp;
  }

  const IR::Node *postorder(IR::MethodCallStatement *mce) override {
    auto orig = getOriginal<IR::MethodCallStatement>();
    auto mi = P4::MethodInstance::resolve(orig, sr->refMap, sr->typeMap);
    if (auto bim = mi->to<P4::BuiltInMethod>()) {
      auto obj = bim->appliedTo;
      auto nxtIdx = new IR::Member(obj, "nxt");
      auto elems = new IR::Member(obj, "elements");
      if (bim->name == IR::Type_Stack::push_front) {
        auto cntExp = (*mce->methodCall->arguments)[0]->expression;
        auto cnt = cntExp->to<IR::Constant>()->value.get_si();
        auto ts = sr->typeMap->getType(obj)->to<IR::Type_Stack>();
        auto sz = ts->size->to<IR::Constant>()->value.get_si();
        auto blockStatement = new IR::BlockStatement();
        for (long i = sz - 1; i >= 0; --i) {
          auto this_i = new IR::ArrayIndex(elems, new IR::Constant(i));
          if (i >= cnt) {
            auto this_i_prev =
                new IR::ArrayIndex(elems, new IR::Constant(i - cnt));
            auto asg = new IR::AssignmentStatement(this_i, this_i_prev);
            blockStatement->push_back(asg);
          } else {
            auto setinvalid =
                new IR::Member(this_i, IR::Type_Header::setInvalid);
            auto mcs = new IR::MethodCallExpression(setinvalid);
            blockStatement->push_back(new IR::MethodCallStatement(mcs));
          }
        }
        auto incdNxt = new IR::Add(cntExp, nxtIdx);
        auto guard = new IR::Grt(incdNxt, ts->size);
        auto ifguard = new IR::AssignmentStatement(nxtIdx, ts->size);
        auto elseguard = new IR::AssignmentStatement(nxtIdx, incdNxt);
        auto stat = new IR::IfStatement(guard, ifguard, elseguard);
        blockStatement->push_back(stat);
        return blockStatement;
      } else if (bim->name == IR::Type_Stack::pop_front) {
        auto cntExp = (*mce->methodCall->arguments)[0]->expression;
        auto cnt = cntExp->to<IR::Constant>()->value.get_si();
        auto ts = sr->typeMap->getType(obj)->to<IR::Type_Stack>();
        auto sz = ts->size->to<IR::Constant>()->value.get_si();
        auto blockStatement = new IR::BlockStatement();
        for (long i = 0; i != sz; ++i) {
          auto this_i = new IR::ArrayIndex(elems, new IR::Constant(i));
          if (i + cnt < sz) {
            auto this_i_prev =
                new IR::ArrayIndex(elems, new IR::Constant(i + cnt));
            auto asg = new IR::AssignmentStatement(this_i, this_i_prev);
            blockStatement->push_back(asg);
          } else {
            auto setinvalid =
                new IR::Member(this_i, IR::Type_Header::setInvalid);
            auto mcs = new IR::MethodCallExpression(setinvalid);
            blockStatement->push_back(new IR::MethodCallStatement(mcs));
          }
        }
        auto incdNxt = new IR::Sub(nxtIdx, cntExp);
        auto guard = new IR::Lss(nxtIdx, cntExp);
        auto ifguard = new IR::AssignmentStatement(nxtIdx, new IR::Constant(0));
        auto elseguard = new IR::AssignmentStatement(nxtIdx, incdNxt);
        auto stat = new IR::IfStatement(guard, ifguard, elseguard);
        blockStatement->push_back(stat);
        return blockStatement;
      }
    } else if (mi->is<P4::ExternMethod>()) {
      auto em = mi->to<P4::ExternMethod>();
      if (em->actualExternType->name ==
          P4::P4CoreLibrary::instance.packetIn.name) {
        if (em->method->name ==
            P4::P4CoreLibrary::instance.packetIn.extract.name) {
          auto arg = mi->expr->arguments->at(
              (mi->expr->arguments->size() == 1) ? 0 : 1);
          const IR::Type_Stack *ts = nullptr;
          const IR::Expression *stackexp = nullptr;
          cstring memberName;
          if (isArrayMember(arg->expression, ts, memberName, stackexp)) {
            auto nxtIndex = new IR::Member(stackexp, "nxt");
            if (memberName == IR::Type_Stack::next) {
              auto asg = new IR::AssignmentStatement(
                  nxtIndex, new IR::Add(nxtIndex, new IR::Constant(1)));
              auto call =
                  new IR::MethodCallStatement(new IR::MethodCallExpression(
                      new IR::PathExpression(IR::ParserState::verify),
                      {new IR::Lss(nxtIndex, ts->size),
                       new IR::Member(new IR::PathExpression("error"),
                                      "StackOutOfBounds")}));
              return new IR::IndexedVector<IR::StatOrDecl>({call, mce, asg});
            }
          }
        }
      }
    }
    return mce;
  }
};

void StackRegistrar::put(const IR::Declaration *decl,
                         const IR::Node *insPoint) {
  auto tp = typeMap->getType(decl);
  if (auto ts = tp->to<IR::Type_Stack>()) {
    auto inner = typeMap->getTypeType(ts->elementType, true);
    auto sz = (unsigned)(ts->size->to<IR::Constant>()->value.get_ui());
    auto pr = std::make_pair(inner, sz);
    reverseInsertionPoints[pr].emplace(insPoint);
    insertPoints[insPoint].emplace(pr);
  }
}

StackRegistrar::StackRegistrar(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap) {}

class PullOutVerify : public Transform {
  P4::ReferenceMap *refMap;
  std::unordered_map<const IR::P4Parser *, const IR::P4Parser *> replace;

 public:
  PullOutVerify(P4::ReferenceMap *refMap) : refMap(refMap) {}

 private:
  const IR::Node *postorder(IR::P4Parser *p) override {
    auto I = replace.find(getOriginal<IR::P4Parser>());
    if (I != replace.end()) return I->second;
    return p;
  }

  const IR::Node *postorder(IR::MethodCallStatement *mcs) override {
    auto e = mcs->methodCall->method;
    auto orig = getOriginal<IR::MethodCallStatement>();
    if (e->is<IR::PathExpression>()) {
      auto pe = e->to<IR::PathExpression>();
      if (pe->path->name == IR::ParserState::verify) {
        auto cd = mcs->methodCall->arguments->at(0)->expression;
        auto pstate = findOrigCtxt<IR::ParserState>();
        auto parser = findOrigCtxt<IR::P4Parser>();
        if (pstate && parser) {
          if (replace.count(parser)) {
            return mcs;
          }
          auto I = std::find(pstate->components.begin(),
                             pstate->components.end(), orig);
          BUG_CHECK(I != pstate->components.end(), "%1% doesn't contain %2%",
                    pstate, orig);
          auto nxtState = refMap->newName(pstate->name);
          IR::Vector<IR::SelectCase> cases(
              {new IR::SelectCase(new IR::BoolLiteral(true),
                                  new IR::PathExpression(nxtState)),
               new IR::SelectCase(
                   new IR::DefaultExpression(),
                   new IR::PathExpression(IR::ParserState::reject))});
          auto selex = new IR::SelectExpression(
              new IR::ListExpression(IR::Vector<IR::Expression>({cd})), cases);
          IR::IndexedVector<IR::StatOrDecl> cp1;
          cp1.insert(cp1.begin(), pstate->components.begin(), I);
          ++I;
          IR::IndexedVector<IR::StatOrDecl> cp2;
          cp2.insert(cp2.begin(), I, pstate->components.end());

          auto newstate = new IR::ParserState(pstate->name, cp1, selex);
          auto nextstate =
              new IR::ParserState(nxtState, cp2, pstate->selectExpression);
          auto parsercl = parser->clone();
          auto II = std::find(parsercl->states.begin(), parsercl->states.end(),
                              pstate);
          BUG_CHECK(II != parsercl->states.end(), "%1% should contain %2%",
                    parsercl, pstate);
          parsercl->states.replace(II, newstate);
          parsercl->states.push_back(nextstate);
          replace[parser] = parsercl;
        }
      }
    }
    return mcs;
  }
};
}

analysis::HandleStacks::HandleStacks(P4::ReferenceMap *refMap,
                                     P4::TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap), registrar(refMap, typeMap) {
  setName("MidEnd_stacks");
  passes.push_back(new FindStackTypes(&registrar));
  passes.push_back(new DeclareStackTypeWrappers(&registrar));
  passes.push_back(new RevampExpressions(&registrar));
  passes.push_back(new PassRepeated({new PullOutVerify(registrar.refMap)}));
  passes.push_back(new ParserInitNexts(registrar.typeMap));
  addPasses({new P4::ClearTypeMap(typeMap), new P4::ResolveReferences(refMap),
             new P4::TypeInference(refMap, typeMap, false),
             new P4::ApplyTypesToExpressions(typeMap),
             new P4::ResolveReferences(refMap)});
}
