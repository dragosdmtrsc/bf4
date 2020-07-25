//
// Created by dragos on 30.05.2019.
//

#include "DataDependencies.h"

void analysis::HasUses::add(const ProgramPoints *points) {
  for (auto e : *points) {
    auto last = e.last();
    if (last != nullptr) {
      LOG3("Found use for " << dbp(last) << " "
                            << (last->is<IR::Statement>() ? last : nullptr));
      auto it = used.find(last);
      if (it == used.end())
        used.emplace(last, 1);
      else
        used.emplace(last, it->second + 1);
    }
  }
}

void analysis::HasUses::remove(const ProgramPoint point) {
  auto last = point.last();
  auto it = used.find(last);
  if (it->second == 1)
    used.erase(it);
  else
    used.emplace(last, it->second - 1);
}

bool analysis::HasUses::hasUses(const IR::Node *node) const {
  return used.find(node) != used.end();
}

void analysis::HasUses::add(const ProgramPoints *points,
                            const ProgramPoint readFrom) {
  for (auto e : *points) {
    auto last = e.last();
    if (last != nullptr) {
      LOG3("Found use for " << dbp(last) << " "
                            << (last->is<IR::Statement>() ? last : nullptr)
                            << " at " << readFrom.last());
      usages[last].emplace(readFrom.last());
    }
  }
}

const LocationSet *
analysis::FindUninitialized::getReads(const IR::Expression *expression,
                                      bool nonNull) const {
  auto result = ::get(readLocations, expression);
  if (nonNull)
    BUG_CHECK(result != nullptr, "no locations known for %1%", dbp(expression));
  return result;
}

void analysis::FindUninitialized::reads(const IR::Expression *expression,
                                        const LocationSet *loc) {
  LOG3(expression << " reads " << loc);
  CHECK_NULL(expression);
  CHECK_NULL(loc);
  readLocations.emplace(expression, loc);
}

bool analysis::FindUninitialized::preorder(const IR::ParserState *state) {
  LOG3("FU Visiting state " << state->name.name);
  context = ProgramPoint(state);
  currentPoint = ProgramPoint(state); // point before the first statement
  visit(state->components, "components");
  if (state->selectExpression != nullptr)
    visit(state->selectExpression);
  context = ProgramPoint();
  return false;
}

Definitions *analysis::FindUninitialized::getCurrentDefinitions() const {
  LOG3("FU Current point is (after) " << currentPoint);
  auto defs = definitions->getDefinitions(currentPoint, true);
  return defs;
}

void analysis::FindUninitialized::checkOutParameters(
    const IR::IDeclaration *block, const IR::ParameterList *parameters,
    Definitions *defs, bool checkReturn) {
  for (auto p : parameters->parameters) {
    if (p->direction == IR::Direction::Out ||
        p->direction == IR::Direction::InOut) {
      auto storage = definitions->storageMap->getStorage(p);
      if (storage == nullptr)
        continue;

      const LocationSet *loc = new LocationSet(storage);
      auto points = defs->getPoints(loc);
      hasUses->add(points);
      // Check uninitialized non-headers (headers can be invalid).
      // inout parameters can never match here, so we could skip them.
      loc = storage->removeHeaders();
      points = defs->getPoints(loc);
      if (points->containsBeforeStart())
        DIAGNOSE_WARN("uninitialized_out_param",
                      "out parameter %1% may be uninitialized when "
                      "%2% terminates",
                      p, block->getName());
    }
  }

  if (checkReturn) {
    // check returned value
    auto storage = definitions->storageMap->getRetVal();
    if (storage != nullptr && defs->hasLocation(storage))
      // If this definition is "live" it means that we have
      // not returned on all paths; returns kill this definition.
      ::error("Function %1% does not return a value on all paths", block);
  }
}

bool analysis::FindUninitialized::preorder(const IR::P4Control *control) {
  LOG3("FU Visiting control " << control->name.name << "[" << control->id << "]");
  // don't really understand this check
//  BUG_CHECK(context.isBeforeStart(),
//            "non-empty context in FindUnitialized::P4Control");
  currentPoint = ProgramPoint(control);
  for (auto d : control->controlLocals)
    if (d->is<IR::Declaration_Instance>())
      // visit virtual Function implementation if any
      visit(d);
  visit(control->body);
  checkOutParameters(control, control->getApplyMethodType()->parameters,
                     getCurrentDefinitions());
  return false;
}

bool analysis::FindUninitialized::preorder(const IR::Function *func) {
  LOG3("FU Visiting function " << func->name.name << "[" << func->id << "]");
  LOG5(func);
  // FIXME -- this throws away the context of the current point, which seems
  // wrong,
  // FIXME -- but otherwise analysis fails
  currentPoint = ProgramPoint(func);
  visit(func->body);
  bool checkReturn = !func->type->returnType->is<IR::Type_Void>();
  checkOutParameters(func, func->type->parameters, getCurrentDefinitions(),
                     checkReturn);
  return false;
}

bool analysis::FindUninitialized::preorder(const IR::P4Parser *parser) {
  LOG3("FU Visiting parser " << parser->name.name << "[" << parser->id << "]");
  visit(parser->states, "states");
  auto accept =
      ProgramPoint(parser->getDeclByName(IR::ParserState::accept)->getNode());
  auto acceptdefs = definitions->getDefinitions(accept, true);
  if (!acceptdefs->empty())
    // acceptdefs is empty when the accept state is unreachable
    checkOutParameters(parser, parser->getApplyMethodType()->parameters,
                       acceptdefs);
  return false;
}

bool analysis::FindUninitialized::preorder(
    const IR::AssignmentStatement *statement) {
  LOG3("FU Visiting " << dbp(statement) << " " << statement);
  auto assign = statement->to<IR::AssignmentStatement>();
  lhs = true;
  visit(assign->left);
  lhs = false;
  visit(assign->right);
  return setCurrent(statement);
}

bool analysis::FindUninitialized::preorder(
    const IR::ReturnStatement *statement) {
  LOG3("FU Visiting " << statement);
  if (statement->expression != nullptr)
    visit(statement->expression);
  return setCurrent(statement);
}

bool analysis::FindUninitialized::preorder(
    const IR::MethodCallStatement *statement) {
  LOG3("FU Visiting " << statement);
  visit(statement->methodCall);
  return setCurrent(statement);
}

bool analysis::FindUninitialized::preorder(
    const IR::BlockStatement *statement) {
  LOG3("FU Visiting " << statement);
  visit(statement->components, "components");
  return setCurrent(statement);
}

bool analysis::FindUninitialized::preorder(const IR::IfStatement *statement) {
  LOG3("FU Visiting " << statement);
  visit(statement->condition);
  auto saveCurrent = currentPoint;
  visit(statement->ifTrue);
  if (statement->ifFalse != nullptr) {
    currentPoint = saveCurrent;
    visit(statement->ifFalse);
  }
  return setCurrent(statement);
}

bool analysis::FindUninitialized::preorder(
    const IR::SwitchStatement *statement) {
  LOG3("FU Visiting " << statement);
  visit(statement->expression);
  currentPoint =
      ProgramPoint(context, statement->expression); // CTD -- added context
  auto saveCurrent = currentPoint;
  for (auto c : statement->cases) {
    if (c->statement != nullptr) {
      LOG3("Visiting " << c);
      currentPoint = saveCurrent;
      visit(c);
    }
  }
  return setCurrent(statement);
}

bool analysis::FindUninitialized::preorder(const IR::Literal *expression) {
  reads(expression, LocationSet::empty);
  return false;
}

bool analysis::FindUninitialized::preorder(
    const IR::TypeNameExpression *expression) {
  reads(expression, LocationSet::empty);
  return false;
}

bool analysis::FindUninitialized::isFinalRead(
    const Visitor::Context *ctx, const IR::Expression *expression) {
  if (ctx == nullptr)
    return true;

  // If this expression is a child of a Member of a left
  // child of an ArrayIndex then we don't report it here, only
  // in the parent.
  auto parentexp = ctx->node->to<IR::Expression>();
  if (parentexp != nullptr) {
    if (parentexp->is<IR::Member>())
      return false;
    if (parentexp->is<IR::ArrayIndex>()) {
      // Since we are doing the visit using a custom order,
      // ctx->child_index is not accurate, so we check
      // manually whether this is the left child.
      auto ai = parentexp->to<IR::ArrayIndex>();
      if (ai->left == expression)
        return false;
    }
  }
  return true;
}

void analysis::FindUninitialized::registerUses(const IR::Expression *expression,
                                               bool reportUninitialized) {
  if (!isFinalRead(getContext(), expression))
    return;
  const LocationSet *read = getReads(expression);
  if (read == nullptr || read->isEmpty())
    return;
  auto currentDefinitions = getCurrentDefinitions();
  auto points = currentDefinitions->getPoints(read);
  if (reportUninitialized && !lhs && points->containsBeforeStart()) {
    // Do not report uninitialized values on the LHS.
    // This could happen if we are writing to an array element
    // with an unknown index.
    auto type = typeMap->getType(expression, true);
    cstring message;
    if (type->is<IR::Type_Base>())
      message = "%1% may be uninitialized";
    else
      message = "%1% may not be completely initialized";
    DIAGNOSE_WARN("uninitialized_use", message, expression);
  }
  hasUses->add(points, getExecuting());
}

bool analysis::FindUninitialized::preorder(
    const IR::PathExpression *expression) {
  LOG3("FU Visiting [" << expression->id << "]: " << expression);
  if (lhs) {
    reads(expression, LocationSet::empty);
    return false;
  }
  auto decl = refMap->getDeclaration(expression->path, true);
  auto storage = definitions->storageMap->getStorage(decl);
  const LocationSet *result;
  if (storage != nullptr)
    result = new LocationSet(storage);
  else
    result = LocationSet::empty;
  reads(expression, result);
  registerUses(expression);
  return false;
}

bool analysis::FindUninitialized::preorder(const IR::P4Action *action) {
  LOG3("FU Visiting " << action);
  currentPoint = ProgramPoint(context, action);
  visit(action->body);
  checkOutParameters(action, action->parameters, getCurrentDefinitions());
  return false;
}

bool analysis::FindUninitialized::preorder(const IR::P4Table *table) {
  LOG3("FU Visiting " << table->name.name);
  auto savePoint = ProgramPoint(context, table);
  currentPoint = savePoint;
  auto key = table->getKey();
  visit(key);
  auto actions = table->getActionList();
  for (auto ale : actions->actionList) {
    BUG_CHECK(ale->expression->is<IR::MethodCallExpression>(),
              "%1%: unexpected entry in action list", ale);
    visit(ale->expression);
    currentPoint = savePoint; // restore the current point
    // it is modified by the inter-procedural analysis
  }
  return false;
}

bool analysis::FindUninitialized::preorder(
    const IR::MethodCallExpression *expression) {
  LOG3("FU Visiting [" << expression->id << "]: " << expression);
  visit(expression->method);
  auto mi = MethodInstance::resolve(expression, refMap, typeMap);
  if (auto bim = mi->to<BuiltInMethod>()) {
    auto base = getReads(bim->appliedTo, true);
    cstring name = bim->name.name;
    if (name == IR::Type_Stack::push_front ||
        name == IR::Type_Stack::pop_front) {
      // Reads all array fields
      reads(expression, base);
      registerUses(expression, false);
      return false;
    } else if (name == IR::Type_Header::isValid) {
      auto storage = base->getField(StorageFactory::validFieldName);
      reads(expression, storage);
      registerUses(expression);
      return false;
    }
  }

  // Symbolically call some methods (actions and tables, extern methods)
  std::vector<const IR::IDeclaration *> callee = callees(mi);

  if (!callee.empty()) {
    LOG3("Analyzing " << callee);
    ProgramPoint pt(context, expression);
    auto pfu = clone(pt);
    for (auto c : callee)
      (void)c->getNode()->apply(*pfu);
  }

  for (auto p : *mi->substitution.getParametersInArgumentOrder()) {
    auto expr = mi->substitution.lookup(p);
    if (p->direction == IR::Direction::Out) {
      // out parameters are not read; they behave as if they are on
      // the LHS of an assignment
      bool save = lhs;
      lhs = true;
      visit(expr);
      lhs = save;
    } else {
      visit(expr);
    }
  }
  reads(expression, LocationSet::empty);
  return false;
}

bool analysis::FindUninitialized::preorder(const IR::Member *expression) {
  LOG3("FU Visiting [" << expression->id << "]: " << expression);
  visit(expression->expr);
  if (expression->expr->is<IR::TypeNameExpression>()) {
    // this is a constant
    reads(expression, LocationSet::empty);
    return false;
  }
  if (TableApplySolver::isHit(expression, refMap, typeMap) ||
      TableApplySolver::isActionRun(expression, refMap, typeMap))
    return false;
  auto type = typeMap->getType(expression, true);
  if (type->is<IR::Type_Method>())
    // dealt within the parent
    return false;

  auto storage = getReads(expression->expr, true);
  auto basetype = typeMap->getType(expression->expr, true);
  if (basetype->is<IR::Type_Stack>()) {
    if (expression->member.name == IR::Type_Stack::next ||
        expression->member.name == IR::Type_Stack::last) {
      reads(expression, storage);
      registerUses(expression, false);
      if (!lhs && expression->member.name == IR::Type_Stack::next)
        ::warning(ErrorType::WARN_UNINITIALIZED,
                  "%1%: reading uninitialized value", expression);
      return false;
    } else if (expression->member.name == IR::Type_Stack::lastIndex) {
      auto index = storage->getArrayLastIndex();
      reads(expression, index);
      registerUses(expression, false);
      return false;
    }
  }

  auto fields = storage->getField(expression->member);
  reads(expression, fields);
  registerUses(expression);
  return false;
}

bool analysis::FindUninitialized::preorder(const IR::Slice *expression) {
  LOG3("FU Visiting [" << expression->id << "]: " << expression);
  bool save = lhs;
  lhs = false; // slices on the LHS also read the data
  visit(expression->e0);
  auto storage = getReads(expression->e0, true);
  reads(expression, storage); // true even in LHS
  registerUses(expression);
  lhs = save;
  return false;
}

bool analysis::FindUninitialized::preorder(const IR::ArrayIndex *expression) {
  LOG3("FU Visiting [" << expression->id << "]: " << expression);
  if (expression->right->is<IR::Constant>()) {
    if (lhs) {
      reads(expression, LocationSet::empty);
    } else {
      auto cst = expression->right->to<IR::Constant>();
      auto index = cst->asInt();
      visit(expression->left);
      auto storage = getReads(expression->left, true);
      auto result = storage->getIndex(index);
      reads(expression, result);
    }
  } else {
    // We model a write with an unknown index as a read/write
    // to the whole array.
    auto save = lhs;
    lhs = false;
    visit(expression->right);
    visit(expression->left);
    auto storage = getReads(expression->left, true);
    lhs = save;
    reads(expression, storage);
  }
  registerUses(expression);
  return false;
}

bool analysis::FindUninitialized::preorder(
    const IR::Operation_Unary *expression) {
  BUG_CHECK(!lhs, "%1%: Unary operation on LHS?", expression);
  visit(expression->expr);
  // This expression in fact reads the result of the operation,
  // which is a temporary storage location, which we do not model
  // in the def-use analysis.
  reads(expression, LocationSet::empty);
  registerUses(expression);
  return false;
}

bool analysis::FindUninitialized::preorder(
    const IR::Operation_Binary *expression) {
  BUG_CHECK(!lhs, "%1%: Binary operation on LHS?", expression);
  visit(expression->left);
  visit(expression->right);
  // This expression in fact reads the result of the operation,
  // which is a temporary storage location, which we do not model
  // in the def-use analysis.
  reads(expression, LocationSet::empty);
  registerUses(expression);
  return false;
}

analysis::FindUninitialized::FindUninitialized(
    analysis::FindUninitialized *parent, ProgramPoint context)
    : context(context), refMap(parent->definitions->storageMap->refMap),
      typeMap(parent->definitions->storageMap->typeMap),
      definitions(parent->definitions), lhs(false), currentPoint(context),
      hasUses(parent->hasUses) {
  visitDagOnce = false;
}

analysis::FindUninitialized::FindUninitialized(AllDefinitions *definitions,
                                               analysis::HasUses *hasUses)
    : refMap(definitions->storageMap->refMap),
      typeMap(definitions->storageMap->typeMap), definitions(definitions),
      lhs(false), currentPoint(), hasUses(hasUses) {
  CHECK_NULL(refMap);
  CHECK_NULL(typeMap);
  CHECK_NULL(definitions);
  CHECK_NULL(hasUses);
  visitDagOnce = false;
}

bool analysis::FindUninitialized::setCurrent(const IR::Statement *statement) {
  currentPoint = ProgramPoint(context, statement);
  return false;
}

ProgramPoint analysis::FindUninitialized::getExecuting() {
  auto stat = findContext<IR::Statement>();
  const IR::Node *theNode = stat;
  if (auto ifs = stat->to<IR::IfStatement>()) {
    theNode = ifs->condition;
  } else if (auto ss = stat->to<IR::SwitchStatement>()) {
    theNode = ss->expression;
  }
  return ProgramPoint(currentPoint, theNode);
}

std::vector<const IR::IDeclaration *>
analysis::FindUninitialized::callees(const P4::MethodInstance *mi) {
  std::vector<const IR::IDeclaration *> callee;
  if (auto ac = mi->to<ActionCall>()) {
    callee.push_back(ac->action);
  } else if (mi->isApply()) {
    auto am = mi->to<ApplyMethod>();
    if (am->isTableApply()) {
      auto table = am->object->to<IR::P4Table>();
      callee.push_back(table);
    }
    // skip control apply calls...
  } else if (auto em = mi->to<ExternMethod>()) {
    LOG4("##call to extern " << mi->expr);
    callee = em->mayCall();
  }
  return callee;
}
