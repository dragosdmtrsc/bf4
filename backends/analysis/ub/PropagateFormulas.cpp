//
// Created by dragos on 30.08.2019.
//

#include "PropagateFormulas.h"

#include <analysis/ImplementPacket.h>
#include <analysis/Interpreter.h>
#include <analysis/VersionedExpression.h>
#include <bmv2/common/helpers.h>
#include <utility>

namespace analysis {

class EvaluateEnumConstants : public Inspector {
  TypeMapProxy &proxy;
  IsLv &isLv;
  std::unordered_map<const IR::Node *, z3::expr> &exprs;
  // HACK
  std::unordered_map<std::string,
                     std::unordered_map<std::string, const IR::Expression *>>
      z3entype2z3ct2enct;

public:
  friend class EvaluateExpression;
  EvaluateEnumConstants(TypeMapProxy &proxy, IsLv &isLv,
                        std::unordered_map<const IR::Node *, expr> &exprs)
      : proxy(proxy), isLv(isLv), exprs(exprs) {}

private:
  bool preorder(const IR::Expression *mem) override {
    if (auto dec = isLv.isEnumConstant(mem)) {
      auto z3srt = proxy.getSort(dec);
      auto tp = proxy.typeMap->getType(mem);
      auto z3ex = proxy.wrapper->enum_member(tp, dec->name.name.c_str());
      exprs.emplace(mem, z3ex);
      z3entype2z3ct2enct[z3srt->name().str()][z3ex.decl().name().str()] = mem;
      return false;
    }
    return true;
  }
};

// assumes a pass of EvaluateLVs was performed before hand
class EvaluateRVs : public Inspector {
  IsLv &isLv;
  PathTypes &pathTypes;
  TypeMapProxy &proxy;
  PathGetter &pathGetter;
  z3::context &context;
  std::unordered_map<const IR::Node *, z3::expr> &exprs;
  std::string prefix;
  z3::context &ctx() { return context; }
  void Return(const IR::Expression *e, z3::expr zexp) {
    exprs.emplace(e, zexp);
  }
  z3::expr operator[](const IR::Expression *e) {
    auto I = exprs.find(e);
    if (I != exprs.end())
      return I->second;
    BUG("can't find expression %1% in map", e);
  }
  bool preorder(const IR::Expression *e) override {
    if (e->is<IR::VersionedExpression>()) {
      auto ve = e->to<IR::VersionedExpression>();
      auto p = pathGetter(ve->leftValue);
      std::stringstream ss;
      if (!prefix.empty()) {
        ss << prefix << "_";
      }
      ss << to_string(*p) << "_" << ve->version;
      auto pt = pathTypes(*p);
      auto ct = proxy.wrapper->get_type(pt);
      Return(ve, ctx().constant(ss.str().c_str(), *ct));
      return false;
    }
    return !isLv.isEnumConstant(e);
  }
  bool preorder(const IR::MethodCallExpression *mce) override {
    if (isLv(mce))
      return false;
    BUG("can't handle a method call expression %1% outside a method call "
        "statement",
        mce);
  }

  z3::expr docast(const z3::expr &e, const IR::Type *srcType,
                  const IR::Type *dstType) {
    if (dstType->is<IR::Type_Bits>()) {
      auto dst = dstType->to<IR::Type_Bits>();
      auto width = dst->width_bits();
      auto initial = srcType->to<IR::Type_Bits>();
      if (!initial && srcType->is<IR::Type_InfInt>()) {
        initial = new IR::Type_Bits(32, false);
      }
      if (!initial && srcType->is<IR::Type_Boolean>()) {
        auto asbv = z3::ite(e, e.ctx().bv_val(1, 1), e.ctx().bv_val(1, 1));
        auto init_width = 1;
        if (init_width < width) {
          return z3::zext(asbv, static_cast<unsigned int>(width - init_width));
        } else if (init_width == width) {
          return asbv;
        } else {
          BUG("can't cast 1 bit to less");
        }
      }
      auto init_width = initial->width_bits();
      if (init_width < width) {
        return z3::zext(e, static_cast<unsigned int>(width - init_width));
      } else if (init_width == width) {
        return e;
      } else {
        return e.extract(static_cast<unsigned int>(width - 1), 0);
      }
    } else {
      BUG("can't cast %1% to %2%", srcType, dstType);
    }
  }
  bool preorder(const IR::Declaration *) override { return false; }
  void postorder(const IR::Operation_Unary *unop) override {
    auto e = (*this)[unop->expr];
    if (unop->is<IR::LNot>()) {
      Return(unop, !e);
    } else if (unop->is<IR::Cmpl>()) {
      Return(unop, ~e);
    } else if (unop->is<IR::Neg>()) {
      Return(unop, -e);
    } else if (auto cast = unop->to<IR::Cast>()) {
      auto dstType = proxy.typeMap->getType(cast);
      auto srcType = proxy.typeMap->getType(cast->expr);
      Return(cast, docast(e, srcType, dstType));
    }
  }
  void postorder(const IR::BoolLiteral *bl) override {
    Return(bl, context.bool_val(bl->value));
  }
  void postorder(const IR::Constant *tb) override {
    auto srt = proxy.getSort(tb);
    auto tp = proxy.typeMap->getType(tb);
    BUG_CHECK(srt != nullptr, "can't map %1%", tp);
    auto strrep = Util::toString(&tb->value, 10);
    Return(tb, analysis::mk_numeral(ctx(), strrep.c_str(), *srt));
  }

  z3::expr
  castAndDo(const IR::Expression *l, const IR::Expression *r,
            std::function<z3::expr(const z3::expr &, const z3::expr &)> bin_) {
    auto e1 = (*this)[l];
    auto e2 = (*this)[r];
    if (auto rconstant = r->to<IR::Constant>()) {
      auto bv_i = proxy.typeMap->getType(l);
      if (auto bt = bv_i->to<IR::Type_Bits>()) {
        return bin_(e1,
                    ctx().bv_val(rconstant->value.get_ui(),
                                 static_cast<unsigned int>(bt->width_bits())));
      } else {
        BUG("can't shl");
      }
    } else {
      auto tl = this->isLv.typeMap->getType(l);
      auto tr = this->isLv.typeMap->getType(r);
      return bin_(e1, docast(e2, tr, tl));
    }
  }

  void postorder(const IR::Operation_Binary *bin) override {
    if (bin->is<IR::Shl>() || bin->is<IR::Shr>()) {
      if (bin->is<IR::Shl>()) {
        Return(bin, castAndDo(bin->left, bin->right,
                              [](const z3::expr &e1, const z3::expr &e2) {
                                return z3::shl(e1, e2);
                              }));
      } else if (bin->is<IR::Shr>()) {
        Return(bin, castAndDo(bin->left, bin->right,
                              [](const z3::expr &e1, const z3::expr &e2) {
                                return z3::lshr(e1, e2);
                              }));
      }
    } else {
      auto e1 = (*this)[bin->left];
      auto e2 = (*this)[bin->right];
      if (bin->is<IR::BAnd>()) {
        Return(bin, e1 & e2);
      } else if (bin->is<IR::BOr>()) {
        Return(bin, e1 | e2);
      } else if (bin->is<IR::LAnd>()) {
        Return(bin, e1 && e2);
      } else if (bin->is<IR::LOr>()) {
        Return(bin, e1 || e2);
      } else if (bin->is<IR::Add>()) {
        Return(bin, e1 + e2);
      } else if (bin->is<IR::Sub>()) {
        Return(bin, e1 - e2);
      } else if (bin->is<IR::Equ>()) {
        Return(bin, e1 == e2);
      } else if (bin->is<IR::Lss>() || bin->is<IR::Grt>() ||
                 bin->is<IR::Geq>() || bin->is<IR::Leq>()) {
        auto signedCase = [&](bool sgn, const z3::expr &e1,
                              const z3::expr &e2) {
          if (bin->is<IR::Lss>()) {
            return (sgn) ? e1 < e2 : z3::ult(e1, e2);
          } else if (bin->is<IR::Grt>()) {
            return (sgn) ? e1 > e2 : z3::ugt(e1, e2);
          } else if (bin->is<IR::Geq>()) {
            return (sgn) ? e1 >= e2 : z3::uge(e1, e2);
          } else {
            return (sgn) ? e1 <= e2 : z3::ule(e1, e2);
          }
        };
        auto te1 = proxy.typeMap->getType(bin->left);
        if (auto tb = te1->to<IR::Type_Bits>()) {
          bool isSigned = tb->isSigned;
          Return(bin, signedCase(isSigned, e1, e2));
        } else {
          BUG("can't handle comparison with type %1%", te1);
        }
      } else if (bin->is<IR::Mul>()) {
        Return(bin, e1 * e2);
      } else if (bin->is<IR::Neq>()) {
        Return(bin, e1 != e2);
      } else if (bin->is<IR::BXor>()) {
        Return(bin, e1 ^ e2);
      } else if (bin->is<IR::AddSat>()) {
        z3::expr noof =
            z3::to_expr(ctx(), Z3_mk_bvadd_no_overflow(ctx(), e1, e2, false));
        BUG_CHECK(e1.get_sort().is_bv(), "can't handle non-bv addition %1%",
                  e1);
        auto bsz = e1.get_sort().bv_size();
        mpz_class maxValue = (mpz_class(1) << bsz) - 1;
        auto strrep = Util::toString(&maxValue, 10);
        Return(bin, z3::ite(noof, e1 + e2,
                            analysis::mk_numeral(ctx(), strrep.c_str(),
                                                 ctx().bv_sort(bsz))));
      } else if (bin->is<IR::SubSat>()) {
        z3::expr noof =
            z3::to_expr(ctx(), Z3_mk_bvsub_no_overflow(ctx(), e1, e2));
        BUG_CHECK(e1.get_sort().is_bv(), "can't handle non-bv addition %1%",
                  e1);
        auto bsz = e1.get_sort().bv_size();
        Return(bin,
               z3::ite(noof, e1 + e2, ctx().num_val(0, ctx().bv_sort(bsz))));
      } else if (bin->is<IR::Concat>()) {
        Return(bin, z3::concat(e1, e2));
      } else {
        BUG("can't handle this binary operation %1%", bin);
      }
    }
  }
  void postorder(const IR::Operation_Ternary *ternop) override {
    auto e1 = (*this)[ternop->e0];
    auto e2 = (*this)[ternop->e1];
    auto e3 = (*this)[ternop->e2];
    if (ternop->is<IR::Mux>()) {
      Return(ternop, z3::ite(e1, e2, e3));
    } else if (auto slice = ternop->to<IR::Slice>()) {
      auto high = slice->getH();
      auto lo = slice->getL();
      Return(ternop, e1.extract(high, lo));
    } else {
      BUG("can't handle this ternop %1%", ternop);
    }
  }

public:
  EvaluateRVs(IsLv &isLv, PathTypes &pathTypes, TypeMapProxy &proxy,
              PathGetter &pathGetter, z3::context &context,
              std::unordered_map<const IR::Node *, expr> &exprs,
              std::string prefix)
      : isLv(isLv), pathTypes(pathTypes), proxy(proxy), pathGetter(pathGetter),
        context(context), exprs(exprs), prefix(std::move(prefix)) {}
};

class EvaluateExpression : public PassManager {
  std::unordered_map<const IR::Node *, z3::expr> expressions;
  std::unordered_map<z3::expr, const IR::Node *> revexpressions;
  EvaluateEnumConstants *evaluateEnumConstants;

public:
  EvaluateExpression(PathTypes &pathTypes, TypeMapProxy &proxy, IsLv &isLv,
                     PathGetter &pathGetter, z3::context &context,
                     std::string prefix) {
    passes.push_back(evaluateEnumConstants =
                         new EvaluateEnumConstants(proxy, isLv, expressions));
    passes.push_back(new EvaluateRVs(isLv, pathTypes, proxy, pathGetter,
                                     context, expressions, std::move(prefix)));
  }
  z3::expr &operator[](const IR::Node *n) {
    if (n->is<IR::Declaration>() || n->is<IR::Expression>()) {
      auto I = expressions.find(n);
      if (I != expressions.end())
        return I->second;
      n->apply(*this);
      I = expressions.find(n);
      if (I != expressions.end()) {
        revexpressions.emplace(I->second, n);
        return I->second;
      }
    }
    BUG("can't evaluate %1%", n);
  }
  const IR::Node *operator[](const z3::expr &e) {
    auto I = revexpressions.find(e);
    if (I != revexpressions.end())
      return I->second;
    if (e.is_const() && e.decl().decl_kind() == Z3_OP_UNINTERPRETED) {
      BUG("expression %1% came out of the blue", e);
    }
    recurse(e,
            [&](const z3::expr &ex) {
              if (revexpressions.count(ex))
                return false;
              return true;
            },
            [&](const z3::expr &ex) {
              const IR::Expression *myex = nullptr;
              switch (ex.decl().decl_kind()) {
              case Z3_OP_UNINTERPRETED:
                return;
              case Z3_OP_AND:
                for (unsigned i = 0; i != ex.num_args(); ++i) {
                  auto crt = operator[](ex.arg(i))->to<IR::Expression>();
                  if (!myex)
                    myex = crt;
                  else
                    myex = new IR::LAnd(myex, crt);
                }
                revexpressions[ex] = myex;
                break;
              case Z3_OP_OR:
                for (unsigned i = 0; i != ex.num_args(); ++i) {
                  auto crt = operator[](ex.arg(i))->to<IR::Expression>();
                  if (!myex)
                    myex = crt;
                  else
                    myex = new IR::LOr(myex, crt);
                }
                revexpressions[ex] = myex;
                break;
              case Z3_OP_NOT:
                revexpressions[ex] = new IR::LNot(
                    revexpressions[ex.arg(0)]->to<IR::Expression>());
                break;
              case Z3_OP_EQ:
                revexpressions[ex] = new IR::Equ(
                    revexpressions[ex.arg(0)]->to<IR::Expression>(),
                    revexpressions[ex.arg(1)]->to<IR::Expression>());
                break;
              case Z3_OP_DT_CONSTRUCTOR: {
                auto srt = ex.get_sort();
                auto srtname = srt.name().str();
                // MASSIVE hack. Think of a cleaner way to do this
                if (!revexpressions.count(ex)) {
                  revexpressions[ex] =
                      evaluateEnumConstants
                          ->z3entype2z3ct2enct[srtname][ex.decl().name().str()];
                }
                break;
              }
              default:
                BUG("can't translate %1%: %2%", ex, ex.decl().decl_kind());
              }
            });
    auto x = revexpressions[e];
    CHECK_NULL(x);
    return x;
  }
};

class FormulaFactory;

class FormulaFactory {
  // inputs
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  z3::context *context;

  // internal state
  IsLv isLv;

  PathTypes pathTypes;
  PathGetter pathGetter;

  SmtTypeWrapper wrapper;
  TypeMapProxy proxy;
  //  FunctionToSMTMapper functionToSMTMapper;
  EvaluateExpression expreval;

public:
  friend class EdgeFormulas;
  FormulaFactory(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                 z3::context *context, std::string prefix)
      : refMap(refMap), typeMap(typeMap), context(context),
        isLv(refMap, typeMap), pathTypes(typeMap), pathGetter(refMap, typeMap),
        wrapper(context), proxy(refMap, typeMap, &wrapper),
        expreval(pathTypes, proxy, isLv, pathGetter, *context,
                 std::move(prefix)) {}

  z3::context &ctx() { return *context; }

  SmtTypeWrapper &getWrapper() { return wrapper; }
  TypeMapProxy &getTypeProxy() { return proxy; }

  IsLv &lvs() { return isLv; }
  PathTypes &getPathTypes() { return pathTypes; }
  z3::expr evaluate(const IR::Node *n) { return expreval[n]; }
  //  FunctionToSMTMapper &getFunctionMapper() { return functionToSMTMapper; }
};

void EdgeFormulas::mkFormula(const node_t &edge, z3::expr &e) {
  if (is_var_decl(edge) || edge.node->is<IR::EmptyStatement>())
    return;
  if (edge.node->is<IR::Vector<IR::Node>>()) {
    // handle basic block
    auto v = edge.node->to<IR::Vector<IR::Node>>();
    z3::expr_vector evec(*context);
    for (auto &nd : *v) {
      evec.push_back(this->node(nd));
    }
    if (evec.empty())
      e = context->bool_val(true);
    else
      e = z3::mk_and(evec).simplify();
    return;
  }
  auto &factory = *this->factory;
  auto assignment = [&](const IR::Node *lvex, const IR::Node *rvex, expr &e) {
    z3::expr_vector out(*context);
    auto multiasg = multiAssignment(lvex, rvex);
    CHECK_NULL(multiasg);
    for (auto asg : *multiasg) {
      out.push_back(factory.evaluate(asg->left) ==
                    factory.evaluate(asg->right));
    }
    if (out.empty())
      BUG("can't have zero elements");
    if (out.size() == 1)
      e = out.back();
    else
      e = z3::mk_and(out);
  };
  if (auto asg = is_assign(edge)) {
    const IR::Node *rvex = asg->rv;
    const IR::Node *lvex = asg->lv;
    assignment(lvex, rvex, e);
  } else if (auto ifs = is_if(edge, typeMap)) {
    auto cd = ifs->cond;
    e = factory.evaluate(cd);
  } else if (auto emcs = is_extern_method_call(edge)) {
    //     setMethodParameters(edge.source, true, e);
    // TODO: is there anything more involved going on here?
    // e = factory.getFunctionMapper().call(edge, emcs->methodCallStatement);
    auto mi =
        P4::MethodInstance::resolve(emcs->methodCallStatement, refMap, typeMap);
    // TODO: maybe remove this if statement
    if (mi->is<P4::ExternFunction>()) {
      auto ef = mi->to<P4::ExternFunction>();
      if (ef->method->name.name == "hash") {
        if (ef->expr->arguments->size() == 5) {
          auto base = factory.evaluate(ef->expr->arguments->at(2)->expression);
          auto max = factory.evaluate(ef->expr->arguments->at(4)->expression);
          auto out = factory.evaluate(ef->expr->arguments->at(0)->expression);
          try {
            e = z3::uge(out, base) && z3::ult(out, base + max);
          } catch (z3::exception &ex) {
            std::cerr << "caught exception " << ex << '\n';
            e = out.ctx().bool_val(true);
          }
        }
      } else {
        auto &packmodel = analysis::AnalysisLibrary::instance.packetModel;
        if (ef->method->name == packmodel.copy.name) {
          auto from = mi->expr->arguments->at(0)->expression;
          auto into = mi->expr->arguments->at(1)->expression;
          e = factory.evaluate(from) == factory.evaluate(into);
        } else if (ef->method->name == packmodel.advance.name) {
          auto pack = mi->expr->arguments->at(0)->expression;
          auto pack_ = mi->expr->arguments->at(1)->expression;
          auto by = mi->expr->arguments->at(2)->expression->to<IR::Constant>();
          CHECK_NULL(by);
          //        BUG_CHECK(packetTheory.isPacket(pack) &&
          //        packetTheory.isConst(pack), "expecting const, got
          //          % 1 % ", pack);
          auto p = factory.evaluate(pack);
          auto p_ = factory.evaluate(pack_);
          //        e = (p_ == packetTheory.advance(by->asUnsigned())(p));
          // TODO (?)
          //  pack_ == advance(N)(pack) <=> \exists X (pack ==
          //                prepend(pack_,
          //  modelEmit(N)(X)))
          auto X = z3::to_expr(
              factory.ctx(),
              Z3_mk_fresh_const(factory.ctx(), "X",
                                factory.ctx().bv_sort(by->asUnsigned())));
          e = (factory.evaluate(pack) ==
               packetTheory.prepend(factory.evaluate(pack_),
                                    packetTheory.emit(by->asUnsigned())(X)));
        } else if (ef->method->name == packmodel.peek.name) {
          auto into = mi->expr->arguments->at(1)->expression;
          auto pack = mi->expr->arguments->at(0)->expression;
          auto intotype = typeMap->getType(into);
          BUG_CHECK(intotype->is<IR::Type_Bits>(),
                    "can't peek non bits %1% %2% ", intotype, into);
          auto sz =
              static_cast<unsigned int>(intotype->to<IR::Type_Bits>()->size);
          auto pack_ = z3::to_expr(factory.ctx(),
                                   Z3_mk_fresh_const(factory.ctx(), "pack_",
                                                     packetTheory.packetSort));
          // X = extract(N)(pack) <=> \exists pack_. (pack ==
          //                prepend(pack_,
          // modelEmit(N)(X)))
          e = factory.evaluate(pack) ==
              packetTheory.prepend(
                  pack_, packetTheory.emit(sz)(factory.evaluate(into)));
        } else if (ef->method->name == packmodel.pop.name) {
          auto pack = mi->expr->arguments->at(0)->expression;
          auto pack_ = mi->expr->arguments->at(1)->expression;
          auto into = mi->expr->arguments->at(2)->expression;
          auto intotype = typeMap->getType(into);
          BUG_CHECK(intotype->is<IR::Type_Bits>(),
                    "can't peek non bits %1% %2% ", intotype, into);
          auto sz =
              static_cast<unsigned int>(intotype->to<IR::Type_Bits>()->size);
          // X = extract(N)(pack) <=> \exists pack_. (pack ==
          //                prepend(pack_,
          // modelEmit(N)(X)))
          e = factory.evaluate(pack) ==
              packetTheory.prepend(
                  factory.evaluate(pack_),
                  packetTheory.emit(sz)(factory.evaluate(into)));
        } else if (ef->method->name == packmodel.emit.name) {
          auto pack = mi->expr->arguments->at(0)->expression;
          auto pack_ = mi->expr->arguments->at(1)->expression;
          auto into = mi->expr->arguments->at(2)->expression;
          auto intotype = typeMap->getType(into);
          BUG_CHECK(intotype->is<IR::Type_Bits>(),
                    "can't peek non bits %1% %2% ", intotype, into);
          auto sz =
              static_cast<unsigned int>(intotype->to<IR::Type_Bits>()->size);
          auto p = factory.evaluate(pack);
          auto p_ = factory.evaluate(pack_);
          auto x = factory.evaluate(into);
          e = (p_ == packetTheory.prepend(packetTheory.emit(sz)(x), p));
        } else if (ef->method->name == packmodel.prepend.name) {
          auto pack = mi->expr->arguments->at(0)->expression;
          auto pack_ = mi->expr->arguments->at(1)->expression;
          auto p2 = mi->expr->arguments->at(2)->expression;
          e = (factory.evaluate(pack_) ==
               packetTheory.prepend(factory.evaluate(pack),
                                    factory.evaluate(p2)));
        } else if (ef->method->name == packmodel.zero.name) {
          e = (packetTheory.zero() ==
               factory.evaluate(mi->expr->arguments->at(0)->expression));
        }
      }
    }
  } else if (auto selex = match_selex(edge)) {
    // TODO: ensure invariant (selex(i) == default expression) <=>
    // TODO: i == selex.size() - 1
    BUG("selex should have been compiled away %1%", selex);
  } else if (auto call_node = is_method_call(edge)) {
    BUG("why is there a call node still here? %1%",
        call_node->methodCallStatement);
  } else {
    e = factory.ctx().bool_val(true);
  }
  LOG4("node " << edge << ":");
  LOG4(e);
}

EdgeFormulas::EdgeFormulas(TypeMap *typeMap, ReferenceMap *refMap,
                           z3::context *context, std::string prefix)
    : typeMap(typeMap), refMap(refMap), context(context),
      factory(new FormulaFactory(refMap, typeMap, context, prefix)),
      selectToExpression(refMap, typeMap), multiAssignment(refMap, typeMap),
      packetTheory(*context), nodeLabels(context, prefix) {
  factory->getWrapper().set_type(
      analysis::AnalysisLibrary::instance.mutablePacket.name,
      packetTheory.packetSort);
}

SmtTypeWrapper &EdgeFormulas::getWrapper() { return factory->getWrapper(); }

z3::expr EdgeFormulas::toSMT(const IR::Expression *e) {
  return factory->evaluate(e);
}

z3::expr EdgeFormulas::toSMT(const MemPath &mp) {
  return factory->evaluate(factory->pathGetter(mp));
}

const IR::Node *EdgeFormulas::translate(const z3::expr &e) {
  return factory->expreval[e];
}

z3::expr EdgeFormulas::NodeLabels::operator[](node_t n) {
  auto I = exprs.find(n);
  if (I != exprs.end())
    return I->second;
  auto sz = exprs.size();
  std::stringstream nm;
  if (!prefix.empty())
    nm << prefix << "_";
  nm << "rho_" << sz;
  return exprs.emplace(n, context->bool_const(nm.str().c_str())).first->second;
}

EdgeFormulas::NodeLabels::NodeLabels(z3::context *context, std::string prefix)
    : context(context), prefix(std::move(prefix)) {}
}
