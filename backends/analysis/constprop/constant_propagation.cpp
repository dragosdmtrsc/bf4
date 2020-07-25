//
// Created by dragos on 11.01.2019.
//

#include <analysis/constprop/constant_propagation.h>
#include <analysis/version_propagator.h>
#include <analysis/versions.h>
#include <common/constantFolding.h>
#include <p4/enumInstance.h>
#include <p4/fromv1.0/v1model.h>

namespace analysis {

bool is_known(P4::SymbolicValue *sv) {
  if (sv->is<P4::ScalarValue>()) {
    auto scalar = sv->to<P4::ScalarValue>();
    return scalar->isKnown();
  } else if (sv->is<P4::SymbolicHeader>()) {
    auto symhead = sv->to<P4::SymbolicHeader>();
    for (auto &p : symhead->fieldValue) {
      if (!is_known(p.second)) return false;
    }
    return is_known(symhead->valid);
  } else if (sv->is<P4::SymbolicArray>()) {
    auto symarray = sv->to<P4::SymbolicArray>();
    for (size_t idx = 0; idx != symarray->size; ++idx) {
      auto sv = symarray->get(nullptr, idx);
      if (!is_known(sv)) return false;
    }
    return true;
  } else if (sv->is<P4::SymbolicStruct>()) {
    auto symhead = sv->to<P4::SymbolicStruct>();
    for (auto &p : symhead->fieldValue) {
      if (!is_known(p.second)) return false;
    }
    return true;
  } else if (sv->is<P4::SymbolicError>()) {
    return true;
  } else {
    BUG("can't handle this sv");
  }
}

P4::SymbolicBool *ConstantPropagate::handleSelectExpression(
    const IR::SelectExpression *selectExpression, int what,
    P4::ValueMap *vmap) {
  auto lexp = selectExpression->select;
  auto crt = selectExpression->selectCases[what];
  if (crt->keyset->is<IR::DefaultExpression>()) {
    auto res = new P4::SymbolicBool(false);
    for (unsigned j = 0; j != selectExpression->selectCases.size(); ++j) {
      if (j != static_cast<unsigned>(what) &&
          !selectExpression->selectCases[j]
               ->keyset->is<IR::DefaultExpression>()) {
        res = *res || handleSelectExpression(selectExpression, j, vmap);
      }
    }
    return !(*res);
  } else {
    auto res = new P4::SymbolicBool(true);
    for (unsigned i = 0; i != lexp->size(); ++i) {
      if (lexp->size() == 1) {
        res = *res && handleSelectCase(lexp->components[0], crt->keyset, vmap);
      } else {
        res = *res &&
              handleSelectCase(
                  lexp->components[i],
                  crt->keyset->to<IR::ListExpression>()->components[i], vmap);
      }
    }
    return res;
  }
}

P4::SymbolicBool *ConstantPropagate::handleSelectCase(
    const IR::Expression *k, const IR::Expression *caselabel,
    P4::ValueMap *valueMap) {
  auto eeval = new P4::ExpressionEvaluator(refMap, typeMap, valueMap);
  auto l = eeval->evaluate(k, false);
  if (auto msk = caselabel->to<IR::Mask>()) {
    auto mskr = eeval->evaluate(msk->right, false);
    auto mskl = eeval->evaluate(msk->left, false);
    if (mskl->is<IR::Constant>() && mskr->is<IR::Constant>() &&
        l->is<IR::Constant>()) {
      return new P4::SymbolicBool(
          (mskl->to<IR::Constant>()->value & mskr->to<IR::Constant>()->value) ==
          (l->to<IR::Constant>()->value & mskr->to<IR::Constant>()->value));
    } else if (mskr->is<IR::Constant>()) {
      if (mskr->to<IR::Constant>()->asUnsigned() == 0)
        return new P4::SymbolicBool(true);
    }
  } else if (auto ct = caselabel->to<IR::Constant>()) {
    if (ct->is<IR::Constant>() && l->is<IR::Constant>()) {
      return new P4::SymbolicBool(ct->to<IR::Constant>()->value ==
                                  l->to<IR::Constant>()->value);
    }
  } else if (auto en = caselabel->to<IR::Member>()) {
    auto tp = typeMap->getType(k);
    if (tp->is<IR::Type_Enum>()) {
      auto symbenum = l->to<SymbolicEnum>();
      if (symbenum->state == ScalarValue::ValueState::Constant) {
        return new P4::SymbolicBool(symbenum->value.name == en->member.name);
      }
    }
  } else if (auto bct = caselabel->to<IR::BoolLiteral>()) {
    auto sb = l->to<SymbolicBool>();
    if (sb->isKnown()) {
      return new P4::SymbolicBool(sb->value == bct->value);
    }
  }
  return new P4::SymbolicBool(P4::ScalarValue::ValueState::NotConstant);
}

P4::ValueMap *ConstantPropagate::handleBoolExpression(const IR::Expression *crt,
                                                      int what,
                                                      P4::ValueMap *valueMap) {
  auto eeval = new P4::ExpressionEvaluator(refMap, typeMap, valueMap);
  auto sb = eeval->evaluate(crt, false)->to<P4::SymbolicBool>();
  if (sb->isKnown()) {
    if (sb->value != !what)
      return nullptr;
    else
      return valueMap;
  }
  FindInterestingAtoms fia(refMap, typeMap);
  valueMap = valueMap->clone();
  P4::ExpressionEvaluator expressionEvaluator(refMap, typeMap, valueMap);
  auto implied = fia.find_implied_equalities(crt->to<IR::Expression>(), what);
  for (auto eq : implied) {
    if (eq.second) {
      if (eq.first->is<IR::Equ>()) {
        auto e = eq.first->to<IR::Equ>();
        auto l = expressionEvaluator.evaluate(e->left, false);
        auto r = expressionEvaluator.evaluate(e->right, false);
        if (is_known(l)) {
          r->assign(l);
        } else if (is_known(r)) {
          l->assign(r);
        }
      } else {
        auto tp = typeMap->getType(eq.first);
        if (tp->is<IR::Type_Boolean>()) {
          auto l = expressionEvaluator.evaluate(eq.first, false);
          l->assign(new P4::SymbolicBool(true));
        }
      }
    } else {
      if (eq.first->is<IR::Equ>()) {
        auto e = eq.first->to<IR::Equ>();
        auto l = expressionEvaluator.evaluate(e->left, false);
        auto r = expressionEvaluator.evaluate(e->right, false);
        if (is_known(l) && l->is<P4::SymbolicBool>()) {
          auto sb = l->to<P4::SymbolicBool>();
          r->assign(!(*sb));
        } else if (is_known(r) && r->is<P4::SymbolicBool>()) {
          auto sb = r->to<P4::SymbolicBool>();
          l->assign(!(*sb));
        }
      } else {
        auto tp = typeMap->getType(eq.first);
        if (tp->is<IR::Type_Boolean>()) {
          auto l = expressionEvaluator.evaluate(eq.first, false);
          l->assign(new P4::SymbolicBool(false));
        }
      }
    }
  }
  return valueMap;
}

P4::SymbolicBool *eval_is_valid(P4::ValueMap *vmap) {
  for (auto &d : vmap->map) {
    if (d.first->getName().name == "hdr") {
      return d.second->to<P4::SymbolicStruct>()
          ->fieldValue["inner_ethernet"]
          ->to<P4::SymbolicHeader>()
          ->valid;
    }
  }
  return nullptr;
}
std::string pretty(P4::SymbolicBool *sb) {
  if (sb->isUninitialized()) {
    return "u";
  } else if (sb->isKnown()) {
    return std::to_string(sb->value);
  } else {
    return "*";
  }
}

bool ConstantPropagate::operator()(node_t crt,
                                   const std::pair<node_t, int> &neigh,
                                   P4::ValueMap *oldex, P4::ValueMap *&newex) {
  if (!oldex) {
    newex = nullptr;
    return false;
  }
  if (crt->is<IR::Declaration>()) {
    newex = oldex->clone();
    if (crt->is<IR::Declaration_Variable>()) {
      auto type = typeMap->getType(crt);
      auto symval = svf.create(type, false);
      newex->set(crt->to<IR::Declaration>(), symval);
    }
  } else if (crt->is<IR::Expression>()) {
    if (typeMap->getType(crt)->is<IR::Type_Boolean>()) {
      newex =
          handleBoolExpression(crt->to<IR::Expression>(), neigh.second, oldex);
    } else if (crt->is<IR::PathExpression>()) {
      newex = oldex->clone();
    } else if (auto selexp = crt->to<IR::SelectExpression>()) {
      auto sb = handleSelectExpression(selexp, neigh.second, oldex);
      if (sb->isKnown() && !sb->value) {
        newex = nullptr;
      } else {
        newex = oldex->clone();
      }
    } else {
      BUG("can't handle this kind of expression %1%", crt);
    }
  } else if (auto asg = crt->to<IR::AssignmentStatement>()) {
    auto methods = IdentifyMethodCalls::getMethods(asg, refMap, typeMap);
    auto next = oldex->clone();
    bool any = false;
    for (auto met : methods) {
      if (met->is<P4::BuiltInMethod>()) continue;
      any = true;
      next = handleMethodCall(next, met->expr, neigh);
    }
    auto eeval = new P4::ExpressionEvaluator(refMap, typeMap, next);
    auto lv = eeval->evaluate(asg->left, true);
    SymbolicValue *rv = nullptr;
    if (any) {
      rv = svf.create(lv->type, false);
    } else {
      rv = eeval->evaluate(asg->right, false);
    }
    lv->assign(rv);
    newex = next;
  } else if (auto mcs = crt->to<IR::MethodCallStatement>()) {
    auto mce = mcs->methodCall;
    if (crt.type != NodeType::RETURN) {
      newex = handleMethodCall(oldex, mce, neigh);
    } else {
      // this was already handled by the corresponding
      // node n with n.type == NodeType::END
      newex = oldex->clone();
    }
  } else if (crt->is<IR::IfStatement>()) {
    newex = handleBoolExpression(crt->to<IR::IfStatement>()->condition,
                                 neigh.second, oldex);
  } else if (crt->is<IR::ExitStatement>()) {
    newex = nullptr;
  } else if (crt->is<IR::EmptyStatement>()) {
    newex = oldex->clone();
  } else if (crt->is<IR::IfStatement>()) {
    newex = handleBoolExpression(crt->to<IR::IfStatement>()->condition,
                                 neigh.second, oldex);
  } else {
    BUG("can't handle this kind of instruction %1%", crt);
  }
  if (!newex && !crt->is<IR::Expression>() && !crt->is<IR::ExitStatement>() &&
      !crt->is<IR::ReturnStatement>() && !crt->is<IR::IfStatement>()) {
    BUG("why is this happening for %1%", crt);
  }
  return newex != nullptr;
}

ValueMap *ConstantPropagate::handleMethodCall(
    const ValueMap *oldex, const IR::MethodCallExpression *mce,
    const std::pair<node_t, int> &neigh) {
  auto mi = MethodInstance::resolve(mce, refMap, typeMap);
  auto nex = oldex->clone();
  auto eeval = new ExpressionEvaluator(refMap, typeMap, nex);
  if (is_set_valid(mce, refMap, typeMap) ||
      is_set_invalid(mce, refMap, typeMap)) {
    auto mem = mce->method->to<IR::Member>();
    auto lv = eeval->evaluate(mem->expr, true);
    lv->to<SymbolicHeader>()->setValid(is_set_valid(mce, refMap, typeMap) !=
                                       nullptr);
  } else if (is_assert(mce, refMap, typeMap) ||
             is_assume(mce, refMap, typeMap)) {
    auto expr = (*mce->arguments->begin())->expression;
    nex = handleBoolExpression(expr, neigh.second, nex);
  } else {
    //    if (isExtract(mi)) {
    //      size_t idx = mi->expr->arguments->size() - 1;
    //      auto arg1 = mi->expr->arguments->at(idx)->expression;
    //      auto shead = eeval->evaluate(arg1, true);
    //      shead->to<SymbolicHeader>()->setAllUnknown();
    //      shead->to<SymbolicHeader>()->setValid(true);
    //    } else
    {
      for (auto parm : *mi->getActualParameters()) {
        if (parm->direction == IR::Direction::InOut ||
            parm->direction == IR::Direction::Out) {
          auto arg = mi->substitution.lookupByName(parm->name)->expression;
          auto evald = eeval->evaluate(arg, true);
          if (evald) {
            evald->setAllUnknown();
          }
        }
      }
    }
  }
  return nex;
}

void ConstantPropagate::operator()(P4::ValueMap *&into,
                                   const P4::ValueMap *from) {
  if (into) {
    for (auto &decl : from->map) {
      auto ev = into->get(decl.first);
      if (!ev) {
        into->set(decl.first, decl.second);
      } else {
        ev->merge(decl.second);
      }
    }
  }
}

P4::SymbolicValue *ConstantPropagate::handle_havoc(const IR::Type *t) {
  return svf.create(t, false);
}

FlatLattice ConstantPropagate::operator()(node_t crt, const Edge &neigh,
                                          FlatLattice v) {
  struct GatherDecls : public Inspector {
    P4::ReferenceMap *refMap;
    P4::TypeMap *typeMap;
    SymbolicValueFactory *svf;
    P4::ValueMap *valueMap;

   public:
    GatherDecls(ReferenceMap *refMap, TypeMap *typeMap,
                SymbolicValueFactory *svf, ValueMap *valueMap)
        : refMap(refMap), typeMap(typeMap), svf(svf), valueMap(valueMap) {}

    void postorder(const IR::PathExpression *pe) override {
      auto decl = refMap->getDeclaration(pe->path);
      auto crt = valueMap->get(decl);
      if (!crt) {
        auto tp = typeMap->getType(pe);
        if (!tp->is<IR::Type_Var>() && !tp->is<IR::Type_MethodBase>() &&
            !tp->is<IR::Type_State>() && !tp->is<IR::Type_Control>() &&
            !tp->is<IR::Type_Parser>() && !tp->is<IR::P4Parser>() &&
            !tp->is<IR::P4Control>() && !tp->is<IR::Type_Package>()) {
          valueMap->set(decl, svf->create(tp, false));
        }
      }
    }
  };
  if (v.isBottom()) return LatticeOps<FlatLattice>().bottom();
  if (v.valueMap) {
    GatherDecls gatherDecls(refMap, typeMap, &svf, v.valueMap);
    // hack to create all decls, because they may appear before
    // being declared
    crt->apply(gatherDecls);
  }
  switch (crt.type) {
    case NodeType::CALL: {
      bool isCallToReturn = edgeType(neigh) == EdgeType::CALL_TO_RETURN;
      auto parms = functionMap->calleeParameters(crt);
      auto retval = new ValueMap;
      auto mi = functionMap->instance(crt);
      LOG4("calling " << dbp(functionMap->callee(crt)));
      if (isCallToReturn) {
        return nullptr;
      } else {
        for (auto parm : parms->parameters) {
          auto arge = mi->substitution.lookupByName(parm->name)->expression;
          ExpressionEvaluator expressionEvaluator(refMap, typeMap, v.valueMap);
          if (parm->direction == IR::Direction::In ||
              parm->direction == IR::Direction::InOut) {
            bool leval = parm->direction == IR::Direction::InOut;
            retval->set(parm, expressionEvaluator.evaluate(arge, leval));
          } else if (parm->direction == IR::Direction::Out ||
                     parm->direction == IR::Direction::None) {
            retval->set(parm, svf.create(typeMap->getType(parm), false));
          }
        }
      }
      auto locals = functionMap->locals(crt);
      for (auto loc : *locals) {
        auto symv = svf.create(typeMap->getType(loc), false);
        if (symv) {
          retval->set(loc, symv);
        }
      }
      return retval;
    }
    default:
      break;
  }
  P4::ValueMap *res = nullptr;

  (*this)(crt, neigh, v.valueMap, res);
  return res;
}

FlatLattice ConstantPropagate::operator()(node_t, const Edge &e,
                                          const FlatLattice &lcall,
                                          const FlatLattice &lend) {
  auto parms = functionMap->calleeParameters(e.first);
  auto retval = lcall.valueMap->clone();
  auto mi = functionMap->instance(e.first);
  ExpressionEvaluator expressionEvaluator(refMap, typeMap, retval);
  for (auto parm : parms->parameters) {
    auto arge = mi->substitution.lookupByName(parm->name)->expression;
    if (parm->direction == IR::Direction::Out ||
        parm->direction == IR::Direction::InOut) {
      auto x = expressionEvaluator.evaluate(arge, true);
      x->assign(lend.valueMap->get(parm));
    }
  }
  return retval;
}

void constant_propagate(const IR::IApply *control,
                        const IR::IndexedVector<IR::Declaration> &extra_locals,
                        const analysis::EdgeHolder *forward_graph,
                        std::map<node_t, P4::ValueMap *> *reachingVersions,
                        std::vector<node_t> *sorted, P4::ReferenceMap *refMap,
                        P4::TypeMap *typeMap) {
  if (sorted->empty() && !forward_graph->empty()) {
    *sorted = analysis::topo_sort(forward_graph);
  }
  auto factory = new P4::SymbolicValueFactory(typeMap);
  auto initial = new P4::ValueMap();
  if (control->getApplyParameters()) {
    for (auto parm : *control->getApplyParameters()) {
      auto ty = typeMap->getType(parm);
      auto p = factory->create(ty, parm->direction == IR::Direction::Out);
      if (p) initial->set(parm, p);
    }
  }
  for (auto loc : extra_locals) {
    auto ty = typeMap->getType(loc);
    auto p = factory->create(ty, true);
    if (p) initial->set(loc, p);
  }

  reachingVersions->emplace(sorted->back(), initial);
  std::unordered_map<node_t, FlatLattice> res;
  analysis::ConstantPropagate cp(refMap, typeMap, nullptr);
  analysis::label_maker(forward_graph, sorted->back(), *sorted,
                        *reachingVersions, cp, cp, cp);
}

std::map<const IR::Expression *, bool>
FindInterestingAtoms::find_implied_equalities(const IR::Expression *e,
                                              int what) {
  auto etype = typeMap->getType(e);
  if (etype->is<IR::Type_Boolean>()) {
    if (what && e->is<IR::LAnd>()) {
      auto land = e->to<IR::LAnd>();
      auto xl = find_implied_equalities(land->left, what);
      auto xr = find_implied_equalities(land->right, what);
      xl.insert(xr.begin(), xr.end());
      return xl;
    } else if (!what && e->is<IR::LOr>()) {
      auto land = e->to<IR::LOr>();
      auto xl = find_implied_equalities(land->left, what);
      auto xr = find_implied_equalities(land->right, what);
      xl.insert(xr.begin(), xr.end());
      return xl;
    } else {
      return {{e, what == 1}};
    }
  }
  return {};
}

std::set<const IR::Expression *> FindInterestingAtoms::find_interesting_atoms(
    const IR::Expression *e) {
  atoms.clear();
  e->apply(*this);
  return std::move(atoms);
}

bool FlatLattice::operator==(const FlatLattice &other) const {
  if (isBottom() != other.isBottom()) return false;
  if (isBottom()) return true;
  return valueMap->equals(other.valueMap);
}

FlatLattice FlatLattice::operator+(const FlatLattice &other) const {
  if (other.isBottom()) {
    if (!isBottom()) return valueMap->clone();
    return valueMap;
  }
  if (isBottom()) return other.valueMap->clone();
  auto cl = valueMap->clone();
  cl->merge(other.valueMap);
  return cl;
}

bool FlatLattice::isBottom() const { return !valueMap; }

FlatLattice::FlatLattice(ValueMap *valueMap) : valueMap(valueMap) {}
}