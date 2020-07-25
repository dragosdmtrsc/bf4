//
// Created by dragos on 15.01.2019.
//

#include "analysis_helpers.h"

namespace analysis {

cstring endFunctionName(const IR::P4Table *table) {
  auto q = "end_" + table->name.name.replace(".", "__");
  return q;
}

cstring queryFunctionName(const IR::P4Table *table) {
  auto q = "query_" + table->name.name.replace(".", "__");
  return q;
}

cstring table_name_from_query(cstring name) {
  return name.substr(strlen("query_"));
}

cstring table_name_from_end(cstring name) {
  return name.substr(strlen("end_"));
}

IR::MethodCallStatement *call_bug() {
  return new IR::MethodCallStatement(
      new IR::MethodCallExpression(new IR::PathExpression("bug")));
}

IR::MethodCallStatement *call_key_match(const IR::Expression *e) {
  return new IR::MethodCallStatement(new IR::MethodCallExpression(
      new IR::PathExpression(analysis::AnalysisLibrary::instance.keyMatch.name),
      new IR::Vector<IR::Argument>({new IR::Argument(e)})));
}

IR::MethodCallStatement *
call_assert_point(const IR::Vector<IR::Expression> &args) {
  IR::Vector<IR::Type> bools;
  for (unsigned i = 0; i != args.size(); ++i) {
    bools.push_back(IR::Type_Boolean::get());
  }
  auto ntuple = new IR::Type_Tuple(bools);
  auto *actuals = new IR::Vector<IR::Argument>();
  actuals->emplace_back(new IR::ListExpression(args));
  auto mce =
      new IR::MethodCallExpression(new IR::PathExpression("assert_point"),
                                   new IR::Vector<IR::Type>({ntuple}), actuals);
  return new IR::MethodCallStatement(mce);
}

IR::MethodCallExpression *call_forall(const IR::Type *bound_type,
                                      const IR::PathExpression *bound,
                                      unsigned nr,
                                      const IR::Expression *condition) {
  IR::Vector<IR::Type> bools;
  auto mce = new IR::MethodCallExpression(
      new IR::PathExpression("forall"), new IR::Vector<IR::Type>({bound_type}),
      new IR::Vector<IR::Argument>({new IR::Argument(bound),
                                    new IR::Argument(new IR::Constant(nr)),
                                    new IR::Argument(condition)}));
  return mce;
}

const IR::Node *actual_node(const IR::Node *n) {
  if (n->is<IR::IfStatement>())
    return n->to<IR::IfStatement>()->condition;
  if (n->is<IR::SelectExpression>())
    return n->to<IR::SelectExpression>()->select;
  return n;
}

cstring node_repr(const IR::Node *n) {
  auto anode = actual_node(n);
  if (anode && !anode->is<IR::EmptyStatement>()) {
    std::stringstream ss;
    ss << anode;
    return ss.str();
  }
  return "";
}

AnalysisLibrary AnalysisLibrary::instance;

z3::ast *IRExprToSMT::get(const IR::Expression *what) {
  auto I = ast_mappings.find(what);
  if (I == ast_mappings.end())
    return nullptr;
  return &I->second;
}

z3::expr IRExprToSMT::evaluate(const IR::Expression *what) {
  what->apply(*this);
  auto got = get(what);
  if (got)
    return to_expr(*context, *get(what));
  else
    BUG("can't evaluate expression %1%", what);
}

void IRExprToSMT::postorder(const IR::LAnd *op) {
  auto lv = get(op->left);
  CHECK_NULL(lv);
  auto rv = get(op->right);
  CHECK_NULL(rv);
  auto ast = to_expr(*context, *lv) && to_expr(*context, *rv);
  set(op, ast);
}

void IRExprToSMT::postorder(const IR::Leq *op) {
  auto lv = get(op->left);
  CHECK_NULL(lv);
  auto rv = get(op->right);
  CHECK_NULL(rv);
  auto ast = to_expr(*context, *lv) <= to_expr(*context, *rv);
  set(op, ast);
}

void IRExprToSMT::postorder(const IR::Geq *op) {
  auto lv = get(op->left);
  CHECK_NULL(lv);
  auto rv = get(op->right);
  CHECK_NULL(rv);
  auto ast = to_expr(*context, *lv) >= to_expr(*context, *rv);
  set(op, ast);
}

void IRExprToSMT::postorder(const IR::Grt *op) {
  auto lv = get(op->left);
  CHECK_NULL(lv);
  auto rv = get(op->right);
  CHECK_NULL(rv);
  auto ast = to_expr(*context, *lv) > to_expr(*context, *rv);
  set(op, ast);
}

void IRExprToSMT::postorder(const IR::BoolLiteral *lit) {
  set(lit, context->bool_val(lit->value));
}

void IRExprToSMT::postorder(const IR::LOr *op) {
  auto ast =
      to_expr(*context, *get(op->left)) || to_expr(*context, *get(op->right));
  set(op, ast);
}

void IRExprToSMT::postorder(const IR::Mux *mux) {
  auto ast1 = to_expr(*context, *get(mux->e0));
  auto ast2 = to_expr(*context, *get(mux->e1));
  auto ast3 = to_expr(*context, *get(mux->e2));
  set(mux, z3::ite(ast1, ast2, ast3));
}

void IRExprToSMT::postorder(const IR::Equ *op) {
  auto lv = get(op->left);
  CHECK_NULL(lv);
  auto rv = get(op->right);
  CHECK_NULL(rv);
  try {
    auto ast = (to_expr(*context, *lv) == to_expr(*context, *rv));
    set(op, ast);
  } catch (const z3::exception &exc) {
    LOG1("caught " << exc.msg());
    throw exc;
  }
}

void IRExprToSMT::postorder(const IR::LNot *op) {
  set(op, !to_expr(*context, *get(op->expr)));
}

void IRExprToSMT::postorder(const IR::Add *op) {
  auto lv = get(op->left);
  CHECK_NULL(lv);
  auto rv = get(op->right);
  CHECK_NULL(rv);
  auto ast = to_expr(*context, *lv) + to_expr(*context, *rv);
  set(op, ast);
}

void IRExprToSMT::postorder(const IR::Sub *op) {
  auto lv = get(op->left);
  CHECK_NULL(lv);
  auto rv = get(op->right);
  CHECK_NULL(rv);
  auto ast = to_expr(*context, *lv) - to_expr(*context, *rv);
  set(op, ast);
}

void IRExprToSMT::postorder(const IR::BAnd *op) {
  auto lv = get(op->left);
  CHECK_NULL(lv);
  auto rv = get(op->right);
  CHECK_NULL(rv);
  auto ast = to_expr(*context, *lv) & to_expr(*context, *rv);
  set(op, ast);
}

void IRExprToSMT::postorder(const IR::Cmpl *op) {
  set(op, ~to_expr(*context, *get(op->expr)));
}

void IRExprToSMT::postorder(const IR::MethodCallExpression *expr) {
  auto mi = P4::MethodInstance::resolve(expr, refMap, typeMap);
  if (auto bim = mi->to<P4::BuiltInMethod>()) {
    auto applyKind = typeMap->getType(bim->appliedTo);
    if (applyKind->is<IR::Type_Header>()) {
      if (bim->name.name == IR::Type_Header::isValid) {
        auto memberDef = get(expr->method);
        BUG_CHECK(memberDef != nullptr, "terribly wrong happenings in %1%",
                  expr);
        set(expr, *memberDef);
      }
    }
  }
}

void IRExprToSMT::postorder(const IR::ArrayIndex *aindex) {
  std::stringstream sstream;
  sstream << partial_string_repr[aindex->left] << "["
          << aindex->right->to<IR::Constant>() << "]";
  partial_string_repr[aindex] = sstream.str();
  create_new(aindex, sstream.str());
}

void IRExprToSMT::postorder(const IR::BXor *op) {
  auto lv = get(op->left);
  CHECK_NULL(lv);
  auto rv = get(op->right);
  CHECK_NULL(rv);
  LOG1("" << op << " = " << *lv << " type " << to_expr(*context, *lv).get_sort()
          << " == " << *rv << " type " << to_expr(*context, *rv).get_sort());
  try {
    auto ast = (to_expr(*context, *lv) ^ to_expr(*context, *rv));
    set(op, ast);
  } catch (const z3::exception &exc) {
    LOG1("caught " << exc.msg());
    throw exc;
  }
}

void IRExprToSMT::postorder(const IR::Slice *slice) {
  auto high = slice->getH();
  auto lo = slice->getL();
  auto old = get(slice->e0);
  auto old_expr = to_expr(*context, *old);
  auto new_expr = old_expr.extract(high, lo);
  set(slice, new_expr);
}

void IRExprToSMT::postorder(const IR::Cast *cast) {
  auto dstType = typeMap->getType(cast);
  auto srcType = typeMap->getType(cast->expr);
  if (dstType->is<IR::Type_Bits>()) {
    auto dst = dstType->to<IR::Type_Bits>();
    auto width = dst->width_bits();
    auto old_expr = to_expr(*context, *get(cast->expr));
    auto initial = srcType->to<IR::Type_Bits>();
    auto init_width = initial->width_bits();
    if (init_width < width) {
      set(cast, zext(old_expr, static_cast<unsigned int>(width - init_width)));
    } else if (init_width == width) {
      set(cast, *get(cast->expr));
    } else {
      set(cast, old_expr.extract(static_cast<unsigned int>(width - 1), 0));
      LOG1("casting to lower width... " << cast);
    }
  }
}

void IRExprToSMT::postorder(const IR::BOr *op) {
  auto lv = get(op->left);
  CHECK_NULL(lv);
  auto rv = get(op->right);
  CHECK_NULL(rv);
  LOG1("" << op << " = " << *lv << " type " << to_expr(*context, *lv).get_sort()
          << " == " << *rv << " type " << to_expr(*context, *rv).get_sort());
  try {
    auto ast = (to_expr(*context, *lv) | to_expr(*context, *rv));
    set(op, ast);
  } catch (const z3::exception &exc) {
    LOG1("caught " << exc.msg());
    throw exc;
  }
}

void IRExprToSMT::postorder(const IR::Constant *lit) {
  auto solve = typeMap->getType(lit);
  if (solve->is<IR::Type_Type>()) {
    solve = solve->to<IR::Type_Type>();
  }
  if (solve->is<IR::Type_InfInt>()) {
    set(lit, context->int_val(lit->asUnsigned()));
    return;
  }
  BUG_CHECK(solve->is<IR::Type_Bits>(), "type %1% should be bits for %2%",
            solve, lit);
  auto width = solve->to<IR::Type_Bits>()->width_bits();
  auto expr = context->bv_val(lit->asUint64(), (unsigned)width);
  set(lit, expr);
}

void IRExprToSMT::postorder(const IR::Neq *op) {
  auto ast =
      to_expr(*context, *get(op->left)) != to_expr(*context, *get(op->right));
  set(op, ast);
}

void IRExprToSMT::create_new(const IR::Expression *what, cstring name) {
  auto type = typeMap->getType(what);
  if (type->is<IR::Type_Bits>() || type->is<IR::Type_Boolean>() ||
      type->is<IR::Type_Enum>()) {
    // ok, we can do it, just create the current parms, because we
    // have no advance type or location knowledge
    z3::ast to_add(*context);
    if (type->is<IR::Type_Boolean>()) {
      auto p = vars->emplace(name, context->bool_const(name));
      to_add = p.first->second;
    } else if (type->is<IR::Type_Bits>()) {
      auto width = type->to<IR::Type_Bits>()->width_bits();
      auto p = vars->emplace(
          name, context->bv_const(name, static_cast<unsigned int>(width)));
      to_add = p.first->second;
    } else {
      auto the_enum = type->to<IR::Type_Enum>();
      auto enum_name = the_enum->getName().name;
      z3::sort *psort = nullptr;
      if (enum_sorts.count(enum_name)) {
        psort = &enum_sorts.find(enum_name)->second;
      } else {
        const char **names =
            new const char *[the_enum->getDeclarations()->count()];
        auto i = 0;
        for (auto decl : *the_enum->getDeclarations()) {
          names[i++] = decl->getName().name.c_str();
        }
        func_decl_vector ts(*context), cs(*context);
        auto srt = context->enumeration_sort(
            enum_name,
            static_cast<unsigned int>(the_enum->getDeclarations()->count()),
            names, cs, ts);
        auto ret = enum_sorts.emplace(enum_name, srt);
        psort = &ret.first->second;
        enum_constants.emplace(enum_name, cs);
      }
      if (what->is<IR::Member>()) {
        auto conv = what->to<IR::Member>();
        auto obj = conv->expr;
        auto resType = typeMap->getType(obj);
        if (resType->is<IR::Type_Type>()) {
          // means => constant
          auto tp = resType->to<IR::Type_Type>();
          BUG_CHECK(tp->type->is<IR::Type_Enum>(),
                    "object must be of kind enum ");
          auto IT =
              std::find_if(the_enum->members.begin(), the_enum->members.end(),
                           [conv](const IR::Declaration_ID *decl) {
                             return decl->name.name == conv->member.name;
                           });
          auto idx = IT - the_enum->members.begin();
          auto &fdv = enum_constants.find(enum_name)->second;
          const auto &ct = fdv[(int)idx];
          to_add = ct();
        } else {
          // means => struct field or bla bla field
          auto p = vars->emplace(name, context->constant(name, *psort));
          to_add = p.first->second;
        }
      }
    }
    set(what, to_add);
  }
}

void IRExprToSMT::postorder(const IR::PathExpression *pathExpression) {
  if (vars->count(pathExpression->toString())) {
    set(pathExpression, vars->find(pathExpression->toString())->second);
  }
  create_new(pathExpression, pathExpression->path->name.name);
  partial_string_repr[pathExpression] = pathExpression->toString();
}

void IRExprToSMT::postorder(const IR::Shl *op) {
  auto lv = get(op->left);
  CHECK_NULL(lv);
  z3::ast *rv = nullptr;
  if (op->right->is<IR::Constant>()) {
    auto solved = typeMap->getType(op->left)->to<IR::Type_Bits>();
    BUG_CHECK(solved != nullptr, "cannot shift %1%", op);
    auto shiftby = op->right->to<IR::Constant>()->asUnsigned();
    auto width = solved->width_bits();
    rv = new z3::ast(context->bv_val(shiftby, width));
  } else {
    rv = get(op->right);
  }
  CHECK_NULL(rv);
  try {
    auto ast = shl(to_expr(*context, *lv), to_expr(*context, *rv));
    set(op, ast);
  } catch (const z3::exception &exc) {
    LOG1("caught " << exc.msg());
    throw exc;
  }
}

void IRExprToSMT::postorder(const IR::Member *mem) {
  auto Il = partial_string_repr.find(mem->expr);
  if (Il != partial_string_repr.end()) {
    auto full_mem = Il->second + '.' + mem->member.name;
    if (vars->count(full_mem)) {
      LOG1("member " << mem << " found in initial defs");
      set(mem, vars->find(full_mem)->second);
    } else {
      LOG1("member " << mem << " found in initial defs, but not in ast");
      partial_string_repr[mem] = full_mem;
      create_new(mem, full_mem);
      if (mem->member.name == IR::Type_Header::isValid) {
        auto exprType = typeMap->getType(mem->expr);
        if (exprType->is<IR::Type_Header>()) {
          auto p = vars->emplace(full_mem.c_str(),
                                 context->bool_const(full_mem.c_str()));
          set(mem, p.first->second);
        }
      }
    }
  } else {
    auto typ = typeMap->getType(mem);
    if (typ->is<IR::Type_Enum>()) {
      auto exp = mem->expr;
      if (exp->is<IR::TypeNameExpression>()) {
        std::stringstream sstream;
        sstream << mem->expr->to<IR::TypeNameExpression>()->typeName->path->name
                << '.' << mem->member.name;
        create_new(mem, sstream.str());
        return;
      }
    }
    BUG("member %1% not found in initial defs, nor in partial_string_repr",
        mem->expr);
  }
}

void IRExprToSMT::set(const IR::Expression *ex, z3::ast a) {
  ast_mappings.emplace(ex, a);
}

void IRExprToSMT::postorder(const IR::Shr *op) {
  auto lv = get(op->left);
  CHECK_NULL(lv);
  z3::ast rv(*context);
  if (op->right->is<IR::Constant>()) {
    auto solved = typeMap->getType(op->left)->to<IR::Type_Bits>();
    BUG_CHECK(solved != nullptr, "cannot shift %1%", op);
    auto shiftby = op->right->to<IR::Constant>()->asUnsigned();
    auto width = solved->width_bits();
    rv = context->bv_val(shiftby, width);
  } else {
    rv = *get(op->right);
  }
  try {
    auto ast = lshr(to_expr(*context, *lv), to_expr(*context, rv));
    set(op, ast);
  } catch (const z3::exception &exc) {
    LOG1("caught " << exc.msg());
    throw exc;
  }
}

unsigned ComputeMaxStackSize::maxStack(const IR::Type *decl) {
  auto tp = typeMap->getTypeType(decl, true);
  if (tp->is<IR::Type_Stack>()) {
    auto ts = tp->to<IR::Type_Stack>();
    auto crt = ts->getSize();
    return std::max(crt, maxStack(ts->elementType));
  } else if (tp->is<IR::Type_StructLike>()) {
    auto str = tp->to<IR::Type_StructLike>();
    unsigned max = 0;
    for (auto fl : str->fields) {
      max = std::max(max, maxStack(fl->type));
    }
    return max;
  } else {
    return 0;
  }
}

unsigned ComputeMaxStackSize::maxStack(const IR::Declaration *decl) {
  return maxStack(typeMap->getType(decl));
}

unsigned ComputeMaxStackSize::maxStack(const IR::ParameterList *parms) {
  std::vector<unsigned> maxes;
  std::transform(parms->begin(), parms->end(), std::back_inserter(maxes),
                 [this](const IR::Parameter *p) { return maxStack(p); });
  return *std::max_element(maxes.begin(), maxes.end());
}

unsigned ComputeMaxStackSize::maxStackSize(const IR::P4Parser *parser,
                                           P4::TypeMap *typeMap) {
  ComputeMaxStackSize computeMaxStackSize(typeMap);
  return computeMaxStackSize.maxStack(parser->getApplyParameters());
}

LVs::LVs(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap), isLv(refMap, typeMap) {}
bool LVs::preorder(const IR::Expression *e) {
  if (isLv(e)) {
    current->emplace(e);
    return false;
  }
  return true;
}
std::unordered_set<const IR::Expression *> *LVs::operator()(const IR::Node *n) {
  auto EMI = res.emplace(n, std::unordered_set<const IR::Expression *>());
  if (EMI.second) {
    current = &EMI.first->second;
    n->apply(*this);
  }
  return &EMI.first->second;
}
}
