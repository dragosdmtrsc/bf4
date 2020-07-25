//
// Created by dragos on 10.09.2019.
//

#include "ConstantPropagation.h"

namespace analysis {

class EvaluateEnumConstants_ : public Inspector {
  IsLv *isLv;
  std::unordered_map<const IR::Node *, ScalarValue> *vals;

public:
  EvaluateEnumConstants_(
      IsLv *isLv, std::unordered_map<const IR::Node *, ScalarValue> *vals)
      : isLv(isLv), vals(vals) {}

private:
  bool preorder(const IR::Expression *mem) override;
};

class EvaluateLVs_ : public Inspector {
  const ConstLattice *mem;
  IsLv *isLv;
  PathGetter *pathGetter;
  // OUTPUT: evaluation of expressions and declarations to ScalarValues
  std::unordered_map<const IR::Node *, ScalarValue> *exprs;

  void Return(const IR::Node *e, ScalarValue zexp) { exprs->emplace(e, zexp); }
  bool preorder(const IR::Expression *e) override {
    if ((*isLv)(e)) {
      Return(e, (*mem)(*(*pathGetter)(e)));
      return false;
    }
    return true;
  }
  bool preorder(const IR::Declaration *decl) override {
    if ((*isLv)(decl)) {
      Return(decl, (*mem)(*(*pathGetter)(decl)));
    }
    return false;
  }

public:
  EvaluateLVs_(PathGetter *pathGetter, const ConstLattice *mem, IsLv *isLv,
               std::unordered_map<const IR::Node *, ScalarValue> *exprs)
      : mem(mem), isLv(isLv), pathGetter(pathGetter), exprs(exprs) {}
};

// assumes a pass of EvaluateLVs was performed before hand
class EvaluateRVs_ : public Inspector {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  const ConstLattice *mem;
  IsLv *isLv;
  // OUTPUT: evaluation of expressions and declarations to ScalarValues
  std::unordered_map<const IR::Node *, ScalarValue> *exprs;

  P4::DoConstantFolding doConstantFolding;

  void Return(const IR::Expression *e, ScalarValue zexp);
  ScalarValue operator[](const IR::Expression *e);
  bool preorder(const IR::Expression *e) override;
  bool preorder(const IR::MethodCallExpression *mce) override;
  bool preorder(const IR::Declaration *) override { return false; }
  void postorder(const IR::Operation_Unary *unop) override;
  void postorder(const IR::BoolLiteral *bl) override { Return(bl, bl); }
  void postorder(const IR::Constant *tb) override { Return(tb, tb); }
  void postorder(const IR::Operation_Binary *bin) override;
  void postorder(const IR::Operation_Ternary *ternop) override;

public:
  EvaluateRVs_(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
               const ConstLattice *mem, IsLv *isLv,
               std::unordered_map<const IR::Node *, ScalarValue> *exprs);
};

class EvaluateExpression_ : public PassManager {
  IsLv isLv;
  PathGetter pathGetter;
  // OUTPUT: evaluation of expressions and declarations to ScalarValues
  std::unordered_map<const IR::Node *, ScalarValue> expressions;

public:
  EvaluateExpression_(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                      const ConstLattice &vals);
  ~EvaluateExpression_() = default;
  ScalarValue &operator[](const IR::Node *n);
};

#define RETURN(a, b)                                                           \
  {                                                                            \
    {                                                                          \
      Return(a, b);                                                            \
      return;                                                                  \
    }                                                                          \
  }
class FindInterestingAtoms : public Inspector {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  std::set<const IR::Expression *> atoms;
  bool preorder(const IR::LAnd *) override { return true; }
  bool preorder(const IR::LOr *) override { return true; }
  bool preorder(const IR::LNot *) override { return true; }
  bool preorder(const IR::Expression *expression) override {
    atoms.emplace(expression);
    return false;
  }
  bool preorder(const IR::Neq *n) override {
    atoms.emplace(n);
    return false;
  }
  bool preorder(const IR::BoolLiteral *) override { return false; }
  bool preorder(const IR::Equ *e) override {
    atoms.emplace(e);
    return false;
  }
  bool preorder(const IR::Operation_Relation *) override { return false; }
  bool preorder(const IR::Operation_Ternary *) override { return false; }

public:
  FindInterestingAtoms(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}
  std::set<const IR::Expression *>
  find_interesting_atoms(const IR::Expression *e);
  std::map<const IR::Expression *, bool>
  find_implied_equalities(const IR::Expression *e, int what);
};

ConstLattice ConstantPropagation::operator()(node_t n, const Edge &e,
                                             const ConstLattice &other) {
  if (!other)
    return {};
  auto ret = other;
  EvaluateExpression_ ev(refMap, typeMap, other);
  if (auto ifs = is_if(FullEdge_t(n, e), typeMap)) {
    if (!handleCondition(ifs->cond, ifs->tt, ret, &ev))
      return {};
  } else if (auto asg = is_assign(n)) {
    MultiAssignment multiAssignment(refMap, typeMap);
    auto multiple = multiAssignment(asg->lv, asg->rv);
    for (auto as : *multiple) {
      auto pt = pathGetter(as->left);
      ret[*pt] = ev[as->right];
    }
  } else if (auto call = is_extern_method_call(n)) {
    auto mc = functionMap->calleeParameters(n);
    auto instance = functionMap->instance(n);
    bool isout = false;
    for (auto p : mc->parameters) {
      if (p->direction == IR::Direction::Out ||
          p->direction == IR::Direction::InOut) {
        isout = true;
        break;
      }
    }
    if (isout) {
      for (auto p : mc->parameters) {
        if (p->direction == IR::Direction::Out ||
            p->direction == IR::Direction::InOut) {
          auto arge =
              instance->substitution.lookupByName(p->name.name)->expression;
          auto mp = pathGetter(arge);
          auto terms = pathGetter.terminals(*mp);
          for (auto &mp : terms)
            ret[mp] = ScalarState::TOP;
        }
      }
    }
  } else if (auto decl = is_var_decl(n)) {
    auto mp = pathGetter(decl->decl);
    if (mp) {
      auto terms = pathGetter.terminals(*mp);
      for (auto &mp : terms)
        ret[mp] = ScalarState::TOP;
    }
  } else if (auto selex = match_selex(n)) {
    auto expr = selectToExpression(selex, e.second);
    LOG4("selex: " << selex->select << " -> " << expr);
    if (!handleCondition(expr, true, ret, &ev))
      return {};
  }
  return ret;
}

void ConstantPropagation::initialize() {
  idx = new std::unordered_map<MemPath, std::size_t>();
  auto add = [&](const MemPath &mp) { idx->emplace(mp, idx->size()); };
  traverse_df_pernode(&cfg->holder, cfg->start_node, [&](const node_t &n) {
    if (auto d = is_var_decl(n)) {
      auto p = pathGetter(d->decl);
      if (p) {
        auto terms = pathGetter.terminals(*p);
        std::for_each(terms.begin(), terms.end(), add);
      }
    } else {
      std::for_each(readSet[n].begin(), readSet[n].end(), add);
      std::for_each(writeSet[n].begin(), writeSet[n].end(), add);
    }
  });
}

ConstLattice ConstantPropagation::
operator()(node_t, const Edge &e, const ConstLattice &, const ConstLattice &) {
  BUG("should not reach return node %1%", e.first.node);
  return nullptr;
}

ConstantPropagation::ConstantPropagation(P4::ReferenceMap *refMap,
                                         P4::TypeMap *typeMap, const CFG &g,
                                         NodeToFunctionMap *funMap)
    : refMap(refMap), typeMap(typeMap), functionMap(funMap), cfg(&g),
      readSet(refMap, typeMap, funMap), writeSet(refMap, typeMap, funMap),
      pathGetter(refMap, typeMap), isLv(refMap, typeMap),
      selectToExpression(refMap, typeMap) {}

bool ConstantPropagation::handleCondition(const IR::Expression *cd, bool tt,
                                          ConstLattice &ret,
                                          EvaluateExpression_ *p_ev) {
  auto &ev = *p_ev;
  auto evald = ev[cd];
  if (evald.state == ScalarState::CONSTANT) {
    auto r = (evald.bconstant()->value == tt);
    return r;
  } else {
    FindInterestingAtoms fia(refMap, typeMap);
    auto implied = fia.find_implied_equalities(cd, (tt) ? 1 : 0);
    for (auto eq : implied) {
      LOG4(((tt) ? "" : "~ ")
           << cd << " |= " << ((eq.second) ? "" : "~ ") << eq.first);
      if (eq.second) {
        if (eq.first->is<IR::Equ>()) {
          auto e = eq.first->to<IR::Equ>();
          auto l = ev[e->left];
          auto r = ev[e->right];
          if (isLv(e->left) && r.state == ScalarState::CONSTANT) {
            auto p = pathGetter(e->left);
            ret[*p] = r;
          } else if (isLv(e->right) && l.state == ScalarState::CONSTANT) {
            auto p = pathGetter(e->right);
            ret[*p] = l;
          }
        } else {
          if (isLv(eq.first)) {
            auto p = pathGetter(eq.first);
            ret[*p] = new IR::BoolLiteral(true);
          } else if (eq.first->is<IR::LNot>()) {
            auto ln = eq.first->to<IR::LNot>();
            if (isLv(ln->expr)) {
              auto p = pathGetter(ln->expr);
              ret[*p] = new IR::BoolLiteral(false);
            }
          }
        }
      }
    }
  }
  return true;
}

ConstLattice ConstantPropagation::operator()(const ConstLattice &l,
                                             ConstLattice r) {
  if (!l)
    return r;
  if (!r)
    return l;
  BUG_CHECK(l.idx == r.idx, "not merging apples with apples?");
  for (unsigned i = 0, e = static_cast<unsigned int>(l.values.size()); i != e;
       ++i) {
    r.values[i] += l.values[i];
  }
  return r;
}

NodeValues<ConstLattice> ConstantPropagation::run() {
  START(const_prop);
  DefaultDiscipline dd(cfg, cfg->start_node);
  initialize();
  auto r = std::ref(*this);
  WorklistAlgo<ConstLattice, ConstantPropagation, DefaultDiscipline,
               ConstantPropagation>
      algo(*cfg, r, dd, r);
  NodeValues<ConstLattice> result;
  result[cfg->start_node] = (*this)();
  algo(cfg->start_node, result);
  END(const_prop);
  auto dr = DURATION(const_prop);
  std::cerr << "done constant propagation #nodes:" << cfg->holder.size()
            << " #vars:" << idx->size() << " in " << dr << "ms\n";
  return result;
}

NodeValues<ConstLattice> ConstantPropagation::propagate_and_simplify(
    P4::ReferenceMap *refMap, P4::TypeMap *typeMap, CFG &g,
    NodeToFunctionMap *funMap, NodeValues<node_t> *parents) {
  START(simplify);
  ConstantPropagation cp(refMap, typeMap, g, funMap);
  auto res = cp.run();
  auto inisize = g.holder.size();
  removeDeadNodes(&g.holder, g.start_node, [&](const node_t &node) {
    auto I = res.find(node);
    if (I != res.end())
      return I->second.isBottom();
    return true;
  });
  ReadSet readSet(refMap, typeMap, funMap);
  std::unordered_map<node_t, node_t> replacements;
  traverse_df_pernode(&g.holder, g.start_node, [&](const node_t &n) {
    auto &atNode = res.at(n);
    auto &rs = readSet[n];
    std::unordered_map<MemPath, const IR::Expression *> rrep;
    std::unordered_map<MemPath, const IR::Expression *> wrep;
    for (auto &rd : rs) {
      auto &sv = atNode[rd];
      if (sv.state == ScalarState::CONSTANT) {
        rrep.emplace(rd, sv.value);
      }
    }
    if (!rrep.empty()) {
      ReplaceAll replaceAll(refMap, typeMap, std::move(rrep), std::move(wrep));
      auto now = replaceAll(n.node);
      if (now != n.node) {
        node_t nn(now, n.type);
        nn = nn.clone(n.label);
        replacements.emplace(n, nn);
        LOG4("constant replace: " << n << " to " << nn);
      }
    }
  });
  traverse_df_pernode(&g.holder, g.start_node, [&](const node_t &n) {
    if (n.node->is<IR::SelectExpression>() || n.node->is<IR::IfStatement>()) {
      auto &neighs = g[n];
      if (neighs.size() == 1) {
        auto &theneigh = neighs.back();
        auto nif = new IR::IfStatement(new IR::BoolLiteral(true),
                                       new IR::EmptyStatement(), nullptr);
        typeMap->setType(nif->condition, IR::Type_Boolean::get());
        auto n2 = n;
        n2.node = nif;
        replacements[n] = n2;
        theneigh.second = 1;
      }
    }
  });
  auto fun = [&](const node_t &n) {
    auto I = replacements.find(n);
    if (I != replacements.end()) {
      if (parents && I->second != n) {
        (*parents)[I->second] = n;
      }
      return I->second;
    }
    return n;
  };
  g.holder = analysis::gmap(std::move(g.holder), fun).first;
  g.start_node = fun(g.start_node);
  END(simplify);
  auto d = DURATION(simplify);
  std::cerr << "done constant propagation and simplification #nodes:" << inisize
            << " vs " << g.holder.size() << " #foldings:" << replacements.size()
            << " in:" << d << "ms\n";
  return res;
}

NodeValues<ConstLattice>
ConstantPropagation::propagate_constants(P4::ReferenceMap *refMap,
                                         P4::TypeMap *typeMap, const CFG &g,
                                         NodeToFunctionMap *funMap) {
  ConstantPropagation cp(refMap, typeMap, g, funMap);
  return cp.run();
}

ScalarValue &EvaluateExpression_::operator[](const IR::Node *n) {
  if (n->is<IR::Declaration>() || n->is<IR::Expression>()) {
    auto I = expressions.find(n);
    if (I != expressions.end())
      return I->second;
    n->apply(*this);
    I = expressions.find(n);
    if (I != expressions.end())
      return I->second;
  }
  BUG("can't evaluate %1%", n);
}
EvaluateExpression_::EvaluateExpression_(P4::ReferenceMap *refMap,
                                         P4::TypeMap *typeMap,
                                         const ConstLattice &vals)
    : isLv(refMap, typeMap), pathGetter(refMap, typeMap) {
  passes.push_back(new EvaluateEnumConstants_(&isLv, &expressions));
  passes.push_back(new EvaluateLVs_(&pathGetter, &vals, &isLv, &expressions));
  passes.push_back(
      new EvaluateRVs_(refMap, typeMap, &vals, &isLv, &expressions));
}
EvaluateRVs_::EvaluateRVs_(
    P4::ReferenceMap *refMap, P4::TypeMap *typeMap, const ConstLattice *mem,
    IsLv *isLv, std::unordered_map<const IR::Node *, ScalarValue> *exprs)
    : refMap(refMap), typeMap(typeMap), mem(mem), isLv(isLv), exprs(exprs),
      doConstantFolding(refMap, typeMap) {}
void EvaluateRVs_::Return(const IR::Expression *e, ScalarValue zexp) {
  if (zexp.state == ScalarState::CONSTANT) {
    typeMap->setType(zexp.value, typeMap->getType(e));
  }
  exprs->emplace(e, zexp);
}
ScalarValue EvaluateRVs_::operator[](const IR::Expression *e) {
  auto I = exprs->find(e);
  if (I != exprs->end())
    return I->second;
  BUG("can't find expression %1% in map", e);
}
bool EvaluateRVs_::preorder(const IR::Expression *e) {
  return !(*isLv)(e) && !isLv->isEnumConstant(e);
}
bool EvaluateRVs_::preorder(const IR::MethodCallExpression *mce) {
  if ((*isLv)(mce))
    return false;
  BUG("can't handle a method call expression %1% outside a method call "
      "statement",
      mce);
}
void EvaluateRVs_::postorder(const IR::Operation_Unary *unop) {
  auto e = (*this)[unop->expr];
  if (e.state == ScalarState::CONSTANT) {
    auto bcl = unop->clone();
    bcl->expr = e.value;
    auto t = typeMap->getType(unop);
    typeMap->setType(bcl, t);
    auto res = bcl->apply(doConstantFolding);
    typeMap->setType(res, t);
    if (res->is<IR::Literal>() || P4::EnumInstance::resolve(res, typeMap)) {
      RETURN(unop, res);
    } else {
      RETURN(unop, ScalarState::TOP);
    }
  }
  RETURN(unop, ScalarState::TOP);
}
void EvaluateRVs_::postorder(const IR::Operation_Binary *bin) {
  auto e1 = (*this)[bin->left];
  auto e2 = (*this)[bin->right];
  if (e1.state == ScalarState::CONSTANT && e2.state == ScalarState::CONSTANT) {
    auto bcl = bin->clone();
    bcl->left = e1.value;
    bcl->right = e2.value;
    auto t = typeMap->getType(bin);
    typeMap->setType(bcl, t);
    auto res = bcl->apply(doConstantFolding);
    typeMap->setType(res, t);
    if (res->is<IR::Literal>() || P4::EnumInstance::resolve(res, typeMap)) {
      RETURN(bin, res);
    } else {
      RETURN(bin, ScalarState::TOP);
    }
  }

  if (bin->is<IR::BAnd>()) {
    if ((e1.state == ScalarState::CONSTANT && e1.constant()->value == 0) ||
        (e2.state == ScalarState::CONSTANT && e2.constant()->value == 0)) {
      RETURN(bin, new IR::Constant(0));
    }
  } else if (bin->is<IR::BOr>()) {
    auto tp = typeMap->getType(bin)->to<IR::Type_Bits>();
    mpz_class maxValue = (mpz_class(1) << static_cast<unsigned>(tp->size)) - 1;
    if ((e1.state == ScalarState::CONSTANT &&
         e1.constant()->value == maxValue) ||
        (e2.state == ScalarState::CONSTANT &&
         e2.constant()->value == maxValue)) {
      RETURN(bin, new IR::Constant(maxValue));
    }
  } else if (bin->is<IR::LAnd>()) {
    if ((e1.state == ScalarState::CONSTANT && !e1.bconstant()->value) ||
        (e2.state == ScalarState::CONSTANT && !e2.bconstant()->value)) {
      RETURN(bin, new IR::BoolLiteral(false));
    }
  } else if (bin->is<IR::LOr>()) {
    if ((e1.state == ScalarState::CONSTANT && e1.bconstant()->value) ||
        (e2.state == ScalarState::CONSTANT && e2.bconstant()->value)) {
      RETURN(bin, new IR::BoolLiteral(true));
    }
  }
  RETURN(bin, ScalarState::TOP);
}
void EvaluateRVs_::postorder(const IR::Operation_Ternary *ternop) {
  auto e1 = (*this)[ternop->e0];
  auto e2 = (*this)[ternop->e1];
  auto e3 = (*this)[ternop->e2];
  if (e1.state == ScalarState::CONSTANT && e2.state == ScalarState::CONSTANT &&
      e3.state == ScalarState::CONSTANT) {
    auto tcl = ternop->clone();
    tcl->e0 = e1.value;
    tcl->e1 = e2.value;
    tcl->e2 = e3.value;
    auto t = typeMap->getType(ternop);
    typeMap->setType(tcl, t);
    auto res = tcl->apply(doConstantFolding);
    typeMap->setType(res, t);
    if (res->is<IR::Literal>() || P4::EnumInstance::resolve(res, typeMap)) {
      RETURN(ternop, res);
    } else {
      RETURN(ternop, ScalarState::TOP);
    }
  }
  if (ternop->is<IR::Mux>()) {
    if (e1.bconstant() && e1.bconstant()->value) {
      if (e2.state == ScalarState::CONSTANT)
        RETURN(ternop, e2.value);
    } else if (e1.bconstant() && !e1.bconstant()->value) {
      if (e3.state == ScalarState::CONSTANT)
        RETURN(ternop, e3.value);
    }
  }
  RETURN(ternop, ScalarState::TOP);
}
ScalarValue ScalarValue::operator+(const ScalarValue &sv) const {
  auto cp = *this;
  cp += sv;
  return cp;
}
bool ScalarValue::operator==(const ScalarValue &sv) const {
  if (sv.state != state)
    return false;
  if (sv.state != ScalarState::CONSTANT)
    return true;
  if (constant() && sv.constant()) {
    return constant()->value == sv.constant()->value;
  } else if (bconstant() && sv.bconstant()) {
    return bconstant()->value == sv.bconstant()->value;
  } else {
    auto mem = enumMember()->to<IR::Member>();
    auto memr = sv.enumMember()->to<IR::Member>();
    return mem->member.name == memr->member.name;
  }
}
const IR::BoolLiteral *ScalarValue::bconstant() const {
  if (value)
    return value->to<IR::BoolLiteral>();
  return nullptr;
}
const IR::Constant *ScalarValue::constant() const {
  if (value)
    return value->to<IR::Constant>();
  return nullptr;
}

ScalarValue &ScalarValue::operator+=(const ScalarValue &sv) {
  if (state == ScalarState::TOP || sv.state == ScalarState::TOP)
    return (*this = ScalarState::TOP);
  if (state == ScalarState::BOTTOM)
    return (*this = sv);
  if (sv.state == ScalarState::BOTTOM)
    return *this;
  if (constant() && sv.constant()) {
    if (constant()->value == sv.constant()->value)
      return *this;
  } else if (bconstant() && sv.bconstant()) {
    if (bconstant()->value == sv.bconstant()->value)
      return *this;
  } else {
    auto mem = enumMember()->to<IR::Member>();
    auto memr = sv.enumMember()->to<IR::Member>();
    if (mem->member.name == memr->member.name)
      return *this;
  }
  return (*this = ScalarState::TOP);
}

ScalarValue ScalarValue::fromExpression(const IR::Expression *expr,
                                        P4::TypeMap *typeMap) {
  if (expr->is<IR::Literal>() || P4::EnumInstance::resolve(expr, typeMap)) {
    return expr;
  }
  return ScalarState::TOP;
}

bool EvaluateEnumConstants_::preorder(const IR::Expression *mem) {
  if (isLv->isEnumConstant(mem)) {
    vals->emplace(mem, mem);
    return false;
  }
  return true;
}

Fold::Fold(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
           ConstLattice *constants)
    : refMap(refMap), typeMap(typeMap), constants(constants),
      tc(refMap, typeMap),
      eeval(new EvaluateExpression_(refMap, typeMap, *constants)) {}

const IR::Node *Fold::preorder(IR::Expression *te) {
  auto e = getOriginal<IR::Expression>();
  auto tp = typeMap->getType(e);
  if (tp->is<IR::Type_StructLike>() || tp->is<IR::Type_Stack>()) {
    prune();
    return te;
  }
  auto sv = eeval->operator[](e);
  if (sv.state == ScalarState::CONSTANT) {
    prune();
    if (e == sv.value)
      return te;
    return sv.value;
  }
  return te;
}

const IR::Expression *Fold::operator()(const IR::Expression *e) {
  auto EMI = cache.emplace(e, e);
  if (EMI.second) {
    EMI.first->second = e->apply(*this);
    EMI.first->second->apply(tc);
  }
  return EMI.first->second;
}

const IR::Expression *EvalAt::operator()(node_t n, const IR::Expression *e) {
  auto I = constants->find(n);
  if (I != constants->end()) {
    auto EMI = getOrEmplace(
        folds, n, [&]() { return Fold(refMap, typeMap, &I->second); });
    return EMI.first(e);
  }
  return e;
}

ScalarValue &ConstLattice::operator[](const MemPath &mp) {
  auto I = idx->find(mp);
  BUG_CHECK(I != idx->end(), "%1% not found in index", mp);
  return values[I->second];
}

bool ConstLattice::operator==(const ConstLattice &o) const {
  if (o.isBottom() != isBottom())
    return false;
  if (o.isBottom())
    return true;
  BUG_CHECK(idx == o.idx, "not comparing apples with apples");
  return values == o.values;
}

const ScalarValue &ConstLattice::operator[](const MemPath &mp) const {
  auto I = idx->find(mp);
  BUG_CHECK(I != idx->end(), "%1% not found in index", mp);
  return values[I->second];
}

ScalarValue ConstLattice::operator()(const MemPath &mp) const {
  auto I = idx->find(mp);
  BUG_CHECK(I != idx->end(), "can't find %1%", mp);
  return values[I->second];
}
}