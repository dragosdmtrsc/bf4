//
// Created by dragos on 30.05.2019.
//

#ifndef P4C_DATADEPENDENCIES_H
#define P4C_DATADEPENDENCIES_H

#include "frontends/p4/def_use.h"
#include "frontends/p4/tableApply.h"
#include "cfg_algos.h"
#include <common/resolveReferences/referenceMap.h>
#include <p4/typeMap.h>

using namespace P4;

namespace analysis {
class HasUses {
  // Set of program points whose left-hand sides are used elsewhere
  // in the program together with their use count
  std::unordered_map<const IR::Node *, unsigned> used;
public:
  std::map<node_t, std::set<node_t>> usages;
  HasUses() = default;
  void add(const ProgramPoints *points, const ProgramPoint point);
  void add(const ProgramPoints *points);
  void remove(const ProgramPoint point);
  bool hasUses(const IR::Node *node) const;
};

// Run for each parser and control separately
// Somewhat of a misnamed pass -- the main point of this pass is to find all the
// uses
// of each definition, and fill in the `hasUses` output with all the definitions
// that have
// uses so RemoveUnused can remove unused things.  It incidentally finds uses
// that have
// no definitions and issues uninitialized warnings about them.
class FindUninitialized : public Inspector {
protected:
  ProgramPoint context; // context as of the last call or state transition
  ReferenceMap *refMap;
  TypeMap *typeMap;
  AllDefinitions *definitions;
  bool lhs;                  // checking the lhs of an assignment
  ProgramPoint currentPoint; // context of the current expression/statement
  // For some simple expresssions keep here the read location sets.
  // This does not include location sets read by subexpressions.
  std::map<const IR::Expression *, const LocationSet *> readLocations;
  HasUses *hasUses; // output

  const LocationSet *getReads(const IR::Expression *expression,
                              bool nonNull = false) const;
  // 'expression' is reading the 'loc' location set
  void reads(const IR::Expression *expression, const LocationSet *loc);
  bool setCurrent(const IR::Statement *statement);

  ProgramPoint getExecuting();

  FindUninitialized(FindUninitialized *parent, ProgramPoint context);

public:
  virtual FindUninitialized *clone(ProgramPoint context) {
    return new FindUninitialized(this, context);
  }

  FindUninitialized(AllDefinitions *definitions, HasUses *hasUses);

  // we control the traversal order manually, so we always 'prune()'
  // (return false from preorder)

  bool preorder(const IR::ParserState *state) override;

  Definitions *getCurrentDefinitions() const;

  void checkOutParameters(const IR::IDeclaration *block,
                          const IR::ParameterList *parameters,
                          Definitions *defs, bool checkReturn = false);

  bool preorder(const IR::P4Control *control) override;

  bool preorder(const IR::Function *func) override;

  bool preorder(const IR::P4Parser *parser) override;

  bool preorder(const IR::AssignmentStatement *statement) override;

  bool preorder(const IR::ReturnStatement *statement) override;

  bool preorder(const IR::MethodCallStatement *statement) override;

  bool preorder(const IR::BlockStatement *statement) override;

  bool preorder(const IR::IfStatement *statement) override;

  bool preorder(const IR::SwitchStatement *statement) override;

  ////////////////// Expressions

  bool preorder(const IR::Literal *expression) override;

  bool preorder(const IR::TypeNameExpression *expression) override;

  // Check whether the expression the child of a Member or
  // ArrayIndex.  I.e., for and expression such as a.x within a
  // larger expression a.x.b it returns "false".  This is because
  // the expression is not reading a.x, it is reading just a.x.b.
  // ctx must be the context of the current expression in the
  // visitor.
  bool isFinalRead(const Visitor::Context *ctx,
                   const IR::Expression *expression);

  // Keeps track of which expression producers have uses in the given expression
  void registerUses(const IR::Expression *expression,
                    bool reportUninitialized = true);

  // For the following we compute the read set and save it.
  // We check the read set later.
  bool preorder(const IR::PathExpression *expression) override;

  bool preorder(const IR::P4Action *action) override;

  bool preorder(const IR::P4Table *table) override;

  bool preorder(const IR::MethodCallExpression *expression) override;

  bool preorder(const IR::Member *expression) override;

  bool preorder(const IR::Slice *expression) override;

  bool preorder(const IR::ArrayIndex *expression) override;

  bool preorder(const IR::Operation_Unary *expression) override;

  bool preorder(const IR::Operation_Binary *expression) override;

  virtual std::vector<const IR::IDeclaration *> callees(const P4::MethodInstance *mi);
};
}

#endif // P4C_DATADEPENDENCIES_H
