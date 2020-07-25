//
// Created by dragos on 20.04.2019.
//

#include "RemoveTableCalls.h"
#include "analysis_helpers.h"
#include "cfg_algos.h"
#include "sovler.h"
#include <common/resolveReferences/resolveReferences.h>
#include <fstream>
#include <p4/cloner.h>
#include <p4/coreLibrary.h>
#include <p4/enumInstance.h>
#include <p4/methodInstance.h>
#include <p4/tableApply.h>
#include <p4/typeChecking/typeChecker.h>

namespace analysis {
class DoComputeTableDecls {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

public:
  DoComputeTableDecls(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}
  cstring getParmName(const IR::P4Action *action,
                      const IR::Parameter *param) const {
    auto fullName = action->name.name + "." + param->name.name;
    auto cp_name = cstring(fullName).replace(".", "__");
    return cp_name;
  }
  cstring structTypeName(const IR::P4Table *table) {
    auto main_struct_name = "flow_def_" + table->name.name.replace(".", "__");
    return main_struct_name;
  }
  IR::Declaration_Variable *mkDeclVariable(Util::SourceInfo src,
                                           const IR::P4Table *tab) {
    auto tp = structTypeName(tab);
    auto var = refMap->newName(tab->getName());
    auto vardecl =
        new IR::Declaration_Variable(src, var, new IR::Type_Name(tp));
    return vardecl;
  }
  void declareEndFunction(const IR::P4Table *table,
                          std::map<const IR::P4Table *,
                                   std::vector<const IR::Node *>> *please_add) {
    (*please_add)[table].push_back(new IR::Method(
        endFunctionName(table),
        new IR::Type_Method(IR::Type_Void::get(), new IR::ParameterList())));
  }
  const IR::Statement *mkInstruction(const IR::ActionListElement *ale,
                                     const IR::PathExpression *flowRef) const {
    auto *args = new IR::Vector<IR::Argument>();
    auto path = ale->getPath()->clone();
    auto theAction = refMap->getDeclaration(ale->getPath())->to<IR::P4Action>();
    if (ale->expression->is<IR::MethodCallExpression>()) {
      for (auto arg :
           *ale->expression->to<IR::MethodCallExpression>()->arguments) {
        args->push_back(arg);
      }
    }
    auto pe = new IR::PathExpression(path);
    for (auto p : *theAction->getParameters()) {
      if (p->direction == IR::Direction::None) {
        auto parmMember = getParmName(theAction, p);
        auto exp = new IR::Member(flowRef, parmMember);
        args->push_back(new IR::Argument(exp));
      }
    }
    auto actcall = new IR::MethodCallExpression(pe, args);
    auto mcs = new IR::MethodCallStatement(actcall);
    auto angel = new IR::MethodCallStatement(new IR::MethodCallExpression(
        new IR::PathExpression(
            analysis::AnalysisLibrary::instance.angelicAssert.name),
        new IR::Vector<IR::Argument>(
            {new IR::Argument(new IR::BoolLiteral(true))})));
    if (ale->getAnnotation("defaultonly"))
      return mcs;
    auto bs = new IR::BlockStatement({angel, mcs});
    return bs;
  }
  const IR::Expression *enumMember(const IR::P4Table *table, cstring name) {
    cstring enumName = structTypeName(table) + "__action_type_t";
    auto pe = new IR::PathExpression(enumName);
    return new IR::Member(pe, name);
  }
  const IR::Expression *enumMember(const IR::P4Table *table,
                                   const IR::ActionListElement *ale) {
    return enumMember(table, ale->getName().name);
  }
  IR::Statement *doCallTable(const IR::P4Table *tab,
                             IR::Declaration_Variable *var) {
    auto flowRef = new IR::PathExpression(var->getName());
    IR::Statement *stat = new IR::EmptyStatement();
    if (tab->getActionList()) {
      for (const IR::ActionListElement *ale :
           tab->getActionList()->actionList) {
        auto crt = mkInstruction(ale, flowRef);
        auto act = new IR::Member(flowRef, IR::Type_Table::action_run);
        auto selector = enumMember(tab, ale);
        auto cond = new IR::Equ(act, selector);
        CHECK_NULL(crt);
        stat = new IR::IfStatement(cond, crt, stat);
      }
    }
    return stat;
  }

  IR::MethodCallExpression *callTable(const IR::P4Table *tab) {
    auto met = new IR::PathExpression(queryFunctionName(tab));
    auto *arguments = new IR::Vector<IR::Argument>;
    if (tab->getKey()) {
      for (auto kelem : tab->getKey()->keyElements) {
        P4::ClonePathExpressions cloner;
        arguments->push_back(
            new IR::Argument(cloner.clone<IR::Expression>(kelem->expression)));
      }
    }
    return new IR::MethodCallExpression(met, arguments);
  }

  IR::AssignmentStatement *
  callTableAndAssign(const IR::Declaration_Variable *var,
                     const IR::P4Table *tab) {
    return new IR::AssignmentStatement(new IR::PathExpression(var->name),
                                       callTable(tab));
  }

  IR::Method *queryFunction(const IR::P4Table *table) {
    auto qfname = queryFunctionName(table);
    auto strname = structTypeName(table);
    auto rettype = new IR::Type_Name(strname);
    auto parms = new IR::ParameterList();
    if (table->getKey()) {
      for (auto kelem : table->getKey()->keyElements) {
        auto expType = typeMap->getType(kelem->expression);
        auto parmName = keyToParmName(table, kelem);
        auto annot = new IR::Annotation(
            "matchKind", IR::Vector<IR::Expression>(new IR::StringLiteral(
                             kelem->matchType->path->name)));
        auto annots = new IR::Annotations({annot});
        parms->push_back(
            new IR::Parameter(parmName, annots, IR::Direction::In, expType));
      }
    }
    auto methodType = new IR::Type_Method(rettype, parms);
    auto methodDecl = new IR::Method(qfname, methodType);
    methodDecl->annotations =
        methodDecl->annotations->addAnnotation("controlled", nullptr);
    return methodDecl;
  }

  void declareQueryFun(const IR::P4Table *table,
                       std::map<const IR::P4Table *,
                                std::vector<const IR::Node *>> *please_add) {
    auto methodDecl = queryFunction(table);
    (*please_add)[table].emplace_back(methodDecl);
  }
  const IR::Type_Enum *enumForTab(const IR::P4Table *table) {
    auto main_struct_name = "flow_def_" + table->name.name.replace(".", "__");
    if (table->getActionList()) {
      auto vec = IR::IndexedVector<IR::Declaration_ID>();
      for (const auto ale : table->getActionList()->actionList) {
        auto declid = new IR::Declaration_ID(ale->getName().name);
        vec.push_back(declid);
      }
      return new IR::Type_Enum(IR::ID(main_struct_name + "__action_type_t"),
                               vec);
    }
    return nullptr;
  }

  cstring keyToParmName(const IR::P4Table *table, const IR::KeyElement *kelem) {
    cstring parmName = "";
    if (auto anot = kelem->getAnnotation("name")) {
      parmName = cstring(table->name.name + "_" +
                         anot->expr[0]->to<IR::StringLiteral>()->value);
    } else {
      parmName = cstring(table->name.name + "_" + refMap->newName("parm"));
    }
    parmName = parmName.replace('.', '_')
                   .replace('[', '_')
                   .replace(']', '_')
                   .replace('$', '_')
                   .replace(':', '_');
    return parmName;
  }
  cstring keyToFieldName(const IR::P4Table *table,
                         const IR::KeyElement *kelem) {
    return cstring("key_") + keyToParmName(table, kelem);
  }

  const IR::Type_Struct *tableStructure(const IR::P4Table *table) {
    auto main_struct_name = "flow_def_" + table->name.name.replace(".", "__");
    IR::IndexedVector<IR::StructField> flds;
    auto hit =
        new IR::StructField(IR::Type_Table::hit, IR::Type_Boolean::get());
    auto reach = new IR::StructField("reach", IR::Type_Boolean::get());
    if (table->getActionList()) {
      auto label = new IR::StructField(
          IR::Type_Table::action_run,
          new IR::Type_Name(IR::ID(main_struct_name + "__action_type_t")));
      flds.push_back(hit);
      flds.push_back(reach);
      flds.push_back(label);
      for (const auto ale : table->getActionList()->actionList) {
        auto expr = ale->expression;
        if (expr->is<IR::MethodCallExpression>()) {
          auto mce = expr->to<IR::MethodCallExpression>();
          auto mi = P4::MethodInstance::resolve(mce, refMap, typeMap);
          if (mi->is<P4::ActionCall>()) {
            auto action = mi->to<P4::ActionCall>()->action;
            for (const auto param : action->getParameters()->parameters) {
              if (param->direction == IR::Direction::None) {
                cstring cp_name = getParmName(action, param);

                auto parmType = typeMap->getType(param);
                auto structField = new IR::StructField(
                    cp_name, new IR::Annotations(), parmType);
                flds.push_back(structField);
                auto nm = param->getAnnotation("name");
                if (nm) {
                  structField->annotations->add(nm);
                }
              }
            }
          }
        }
      }
    }
    if (auto k = table->getKey()) {
      for (auto kelem : k->keyElements) {
        cstring fName = keyToFieldName(table, kelem);
        auto annot = new IR::Annotation(
            "matchKind", IR::Vector<IR::Expression>(new IR::StringLiteral(
                             kelem->matchType->path->name)));
        auto expType = typeMap->getType(kelem->expression);
        auto annots = new IR::Annotations({annot});
        if (kelem->matchType->path->name == "ternary") {
          flds.push_back(
              new IR::StructField(cstring(fName + "__val"), annots, expType));
          flds.push_back(
              new IR::StructField(cstring(fName + "__mask"), annots, expType));
        } else if (kelem->matchType->path->name == "selector" ||
                   kelem->matchType->path->name == "exact") {
          flds.push_back(new IR::StructField(fName, annots, expType));
        } else if (kelem->matchType->path->name == "lpm") {
          flds.push_back(
              new IR::StructField(cstring(fName + "__val"), annots, expType));
          flds.push_back(new IR::StructField(cstring(fName + "__prefix"),
                                             annots, expType));
        } else if (kelem->matchType->path->name == "range") {
          flds.push_back(
              new IR::StructField(cstring(fName + "__min"), annots, expType));
          flds.push_back(
              new IR::StructField(cstring(fName + "__max"), annots, expType));
        } else {
          LOG1("don't know how to handle this match kind yet "
               << kelem->matchType);
        }
      }
    }
    return new IR::Type_Struct(IR::ID(main_struct_name), std::move(flds));
  }
  std::vector<const IR::Expression *>
  matchConditions(const IR::P4Table *table,
                  const IR::Declaration_Variable *var) {
    auto local_var_ref = new IR::PathExpression(var->name);
    auto key = table->getKey();
    std::vector<const IR::Expression *> conditions;
    if (key) {
      for (auto k : key->keyElements) {
        auto type = typeMap->getType(k->expression);
        auto fname = keyToFieldName(table, k);
        {
          if (k->matchType->path->name == "ternary") {
            auto band = [&](const IR::Expression *l,
                            const IR::Expression *r) -> const IR::Expression * {
              if (type->is<IR::Type_Boolean>()) {
                return new IR::LAnd(l, r);
              } else {
                return new IR::BAnd(l, r);
              }
            };
            if (type->is<IR::Type_Boolean>()) {
            }
            auto maskMember =
                new IR::Member(local_var_ref, IR::ID(fname + "__mask"));
            auto expr = new IR::Equ(
                band(k->expression, maskMember),
                band(new IR::Member(local_var_ref, IR::ID(fname + "__val")),
                     maskMember));
            conditions.push_back(expr);
          } else if (k->matchType->path->name == "selector" ||
                     k->matchType->path->name == "exact") {
            auto expr = new IR::Equ(
                k->expression, new IR::Member(local_var_ref, IR::ID(fname)));
            conditions.push_back(expr);
          } else if (k->matchType->path->name == "lpm") {
            auto prefmember =
                new IR::Member(local_var_ref, IR::ID(fname + "__prefix"));

            auto sb =
                new IR::Sub(new IR::Shl(new IR::Constant(type, 1), prefmember),
                            new IR::Constant(type, 1));
            auto expr = new IR::Equ(
                new IR::BAnd(k->expression, sb),
                new IR::BAnd(
                    new IR::Member(local_var_ref, IR::ID(fname + "__val")),
                    sb));
            conditions.push_back(expr);
          } else if (k->matchType->path->name == "range") {
            auto mine = new IR::Member(local_var_ref, IR::ID(fname + "__min"));
            auto maxe = new IR::Member(local_var_ref, IR::ID(fname + "__max"));
            auto expr = new IR::LAnd(new IR::Leq(k->expression, maxe),
                                     new IR::Geq(k->expression, mine));
            conditions.push_back(expr);
          } else {
            LOG1("don't know how to handle this match kind yet "
                 << k->matchType);
          }
        }
      }
    }

    return conditions;
  }
  IR::Expression *match(const IR::P4Table *table,
                        const IR::Declaration_Variable *var) {
    auto conditions = matchConditions(table, var);
    IR::Expression *crt = nullptr;
    for (auto cd : conditions) {
      if (crt)
        crt = new IR::LAnd(crt, cd);
      else
        crt = cd->clone();
    }
    return crt;
  }

  const IR::Statement *doMatch(const IR::P4Table *table,
                               const IR::Declaration_Variable *var) {
    if (!table->getKey() || table->getKey()->keyElements.empty())
      return new IR::EmptyStatement;
    ValidityCheck validityCheck(refMap, typeMap);
    auto mat = match(table, var);
    auto hits =
        new IR::Member(new IR::PathExpression(var->name), IR::Type_Table::hit);
    const IR::Statement *matstat = call_key_match(mat);
    if (table->getAnnotation(analysis::AnalysisLibrary::instance
                                 .instrumentKeysAnnotation.name)) {
      auto matcs = matchConditions(table, var);
      auto bs = new IR::BlockStatement({matstat});
      for (auto cd : matcs) {
        bs->push_back(new IR::MethodCallStatement(new IR::MethodCallExpression(
            new IR::PathExpression("__instrument_expression__"),
            new IR::Vector<IR::Argument>({new IR::Argument(cd)}))));
      }
      matstat = bs;
    }
    return new IR::IfStatement(hits, matstat, nullptr);
  }

  void getStructureDeclarations(
      const IR::P4Table *table,
      std::map<const IR::P4Table *, std::vector<const IR::Node *>>
          *please_add) {
    const IR::Type_Enum *enumfortab = enumForTab(table);
    if (enumfortab)
      (*please_add)[table].emplace_back(enumfortab);
    (*please_add)[table].emplace_back(tableStructure(table));
  }
  IR::BlockStatement *mkTableApply(Util::SourceInfo srcInfo,
                                   const IR::P4Table *tab) {
    auto decl = mkDeclVariable(srcInfo, tab);
    auto call = callTableAndAssign(decl, tab);
    auto act = doCallTable(tab, decl);
    auto end = mcs_call(endFunctionName(tab), {});
    call->srcInfo = srcInfo;
    auto blockStatement = new IR::BlockStatement();
    blockStatement->push_back(decl);
    blockStatement->push_back(call);
    blockStatement->push_back(doMatch(tab, decl));
    blockStatement->push_back(act);
    blockStatement->push_back(end);
    return blockStatement;
  }
};

class DoAddTableTypeDeclarations : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  DoComputeTableDecls decls;
  std::map<const IR::P4Table *, std::vector<const IR::Node *>> &please_add;
  std::map<const IR::P4Table *, std::vector<const IR::Node *>> new_objects;
  std::map<const IR::Node *, std::vector<const IR::Node *>> also_add;

public:
  DoAddTableTypeDeclarations(
      P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
      std::map<const IR::P4Table *, std::vector<const IR::Node *>> &please_add)
      : refMap(refMap), typeMap(typeMap), decls(refMap, typeMap),
        please_add(please_add) {}

  const IR::Node *preorder(IR::P4Program *p) override {
    new_objects.clear();
    return p;
  }

  void declare(IR::P4Program *program) {
    IR::Vector<IR::Node> objects;
    auto decls = program->getDeclsByName("forall");
    if (!decls->count()) {
      auto typeParams = new IR::TypeParameters();
      auto tvar = new IR::Type_Var(IR::ID("H"));
      typeParams->push_back(tvar);
      auto parmList = new IR::ParameterList();
      parmList->push_back(
          new IR::Parameter(IR::ID("bound"), IR::Direction::In, tvar));
      parmList->push_back(new IR::Parameter(IR::ID("max"), IR::Direction::In,
                                            new IR::Type_InfInt()));
      parmList->push_back(new IR::Parameter(
          IR::ID("condition"), IR::Direction::In, IR::Type_Boolean::get()));
      auto type =
          new IR::Type_Method(typeParams, IR::Type_Boolean::get(), parmList);
      auto funDecl =
          new IR::Method(program->getSourceInfo(),
                         IR::ID(program->getSourceInfo(), "forall"), type);
      objects.push_back(funDecl);
    }
    decls = program->getDeclsByName("assert_point");
    if (!decls->count()) {
      auto typeParams = new IR::TypeParameters();
      auto tvar = new IR::Type_Var(IR::ID("H"));
      typeParams->push_back(tvar);
      auto parmList = new IR::ParameterList();
      parmList->push_back(
          new IR::Parameter(IR::ID("condition"), IR::Direction::In, tvar));
      auto type = new IR::Type_Method(typeParams, nullptr, parmList);
      auto funDecl = new IR::Method(
          program->getSourceInfo(),
          IR::ID(program->getSourceInfo(), "assert_point"), type);
      objects.push_back(funDecl);
    }
    for (auto &p : new_objects) {
      objects.insert(objects.end(), p.second.begin(), p.second.end());
    }
    objects.insert(objects.end(), program->objects.begin(),
                   program->objects.end());
    for (auto &x : also_add) {
      auto I = std::find(objects.begin(), objects.end(), x.first);
      if (I != objects.end()) {
        ++I;
      } else {
        I = objects.begin();
      }
      objects.insert(I, x.second.begin(), x.second.end());
    }
    program->objects = std::move(objects);
  }

  const IR::Node *postorder(IR::P4Program *program) override {
    declare(program);
    return program;
  }

  const IR::Node *preorder(IR::P4ValueSet *vs) override {
    auto ts = typeMap->getType(getOriginal())->to<IR::Type_Set>();
    auto argtype = ts->elementType;
    auto plist = new IR::ParameterList();
    const IR::Node *after = nullptr;
    if (auto td = argtype->to<IR::Type_Declaration>()) {
      argtype = new IR::Type_Name(td->name);
      after =
          (*(findOrigCtxt<IR::P4Program>()->getDeclsByName(td->name)->begin()))
              ->to<IR::Node>();
    }
    plist->push_back(new IR::Parameter("x", IR::Direction::In, argtype));
    auto mt = new IR::Type_Method(new IR::Type_Boolean(), plist);
    auto met = new IR::Method(cstring(cstring("query_") + vs->name.name), mt);
    met->annotations =
        met->annotations
            ->addAnnotation(IR::Annotation::nameAnnotation,
                            new IR::StringLiteral(vs->externalName("")))
            ->addAnnotation("valueSet", nullptr)
            ->addAnnotation("controlled", nullptr);
    also_add[after].emplace_back(met);
    return vs;
  }

  const IR::Node *preorder(IR::P4Table *tab) override {
    auto orig = getOriginal<IR::P4Table>();
    if (please_add
            .emplace(std::make_pair(orig, std::vector<const IR::Node *>()))
            .second) {
      decls.getStructureDeclarations(orig, &new_objects);
      decls.declareQueryFun(orig, &new_objects);
      decls.declareEndFunction(orig, &new_objects);
    }
    return tab;
  }
};

class RewriteTableApplies : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  DoComputeTableDecls decls;

public:
  RewriteTableApplies(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap), decls(refMap, typeMap) {}

  const IR::Node *postorder(IR::IfStatement *statement) override {
    auto orig = getOriginal<IR::IfStatement>();
    if (auto tab =
            P4::TableApplySolver::isHit(orig->condition, refMap, typeMap)) {
      auto blockStatement = decls.mkTableApply(orig->srcInfo, tab);
      auto decl = blockStatement->components[0]->to<IR::Declaration_Variable>();
      auto hits = new IR::Member(new IR::PathExpression(decl->name),
                                 IR::Type_Table::hit);
      statement->condition = hits;
      blockStatement->push_back(statement);
      return blockStatement;
    }
    return statement;
  }
  const IR::Node *postorder(IR::AssignmentStatement *statement) override {
    auto orig = getOriginal<IR::AssignmentStatement>();
    if (auto tab = P4::TableApplySolver::isHit(orig->right, refMap, typeMap)) {
      auto blockStatement = decls.mkTableApply(orig->srcInfo, tab);
      auto decl = blockStatement->components[0]->to<IR::Declaration_Variable>();
      auto hits = new IR::Member(new IR::PathExpression(decl->name),
                                 IR::Type_Table::hit);
      statement->right = hits;
      blockStatement->push_back(statement);
      return blockStatement;
    } else {
      if (auto tab =
              P4::TableApplySolver::isActionRun(orig->right, refMap, typeMap)) {
        auto blockStatement = decls.mkTableApply(orig->srcInfo, tab);
        auto decl =
            blockStatement->components[0]->to<IR::Declaration_Variable>();
        auto ar = new IR::Member(new IR::PathExpression(decl->name),
                                 IR::Type_Table::action_run);
        statement->right = ar;
        blockStatement->push_back(statement);
        return blockStatement;
      }
    }
    return statement;
  }

  const IR::Node *postorder(IR::MethodCallStatement *mcs) override {
    auto orig = getOriginal<IR::MethodCallStatement>();
    auto mi = P4::MethodInstance::resolve(orig, refMap, typeMap);
    if (auto app = mi->to<P4::ApplyMethod>()) {
      if (app->isTableApply()) {
        auto tab = app->object->to<IR::P4Table>();
        return decls.mkTableApply(orig->srcInfo, tab);
      }
    }
    return mcs;
  }

  const IR::Node *postorder(IR::SwitchStatement *stat) override {
    auto orig = getOriginal<IR::SwitchStatement>();
    if (auto tab = P4::TableApplySolver::isActionRun(orig->expression, refMap,
                                                     typeMap)) {
      auto blockStatement = decls.mkTableApply(orig->srcInfo, tab);
      auto decl = blockStatement->components[0]->to<IR::Declaration_Variable>();
      auto ar = new IR::Member(new IR::PathExpression(decl->name),
                               IR::Type_Table::action_run);
      const IR::Statement *last = new IR::EmptyStatement();
      for (auto cs : orig->cases) {
        if (cs->label->is<IR::DefaultExpression>()) {
          last = cs->statement;
        }
      }
      for (auto cs : orig->cases) {
        const IR::Expression *condition = nullptr;
        if (cs->label->is<IR::ListExpression>()) {
          auto lexp = cs->label->to<IR::ListExpression>();
          for (auto cp : lexp->components) {
            if (cp->is<IR::PathExpression>()) {
              auto en = decls.enumMember(
                  tab, cs->label->to<IR::PathExpression>()->path->name);
              if (!condition)
                condition = new IR::Equ(ar, en);
              else {
                condition = new IR::LOr(condition, new IR::Equ(ar, en));
              }
            }
          }
        } else if (cs->label->is<IR::PathExpression>()) {
          auto en = decls.enumMember(
              tab, cs->label->to<IR::PathExpression>()->path->name);
          condition = new IR::Equ(ar, en);
        } else
          continue;
        last = new IR::IfStatement(
            condition,
            (cs->statement) ? cs->statement
                            : (new IR::EmptyStatement())->to<IR::Statement>(),
            last);
      }
      blockStatement->push_back(last);
      return blockStatement;
    }
    return stat;
  }
};

class TransformPopulatedTables : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

public:
  TransformPopulatedTables(ReferenceMap *refMap, TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}

private:
  const IR::Node *postorder(IR::P4Table *tab) override {
    unsigned tableSize = 1024;
    if (auto tabsize = tab->getSizeProperty()) {
      tableSize = tabsize->asUnsigned();
    }
    size_t actualsize = 1;
    bool allexact = true;
    if (auto k = tab->getKey()) {
      for (const auto &kelem : k->keyElements) {
        if (kelem->matchType->path->name !=
            P4::P4CoreLibrary::instance.exactMatch.name) {
          allexact = false;
          break;
        }
      }
      if (allexact) {
        for (const auto &kelem : k->keyElements) {
          size_t ks = 0;
          auto tp = typeMap->getType(kelem->expression);
          if (auto tb = tp->to<IR::Type_Bits>()) {
            ks = static_cast<size_t>(1ul << tb->size);
          } else if (tp->to<IR::Type_Boolean>()) {
            ks = 1ul << 1;
          } else if (auto ei = tp->to<IR::Type_Enum>()) {
            ks = static_cast<size_t>(ei->members.size());
          } else if (auto err = tp->to<IR::Type_Error>()) {
            ks = static_cast<size_t>(err->members.size());
          } else {
            BUG("unknown type for key %1%", tp);
          }
          actualsize *= ks;
          if (actualsize > tableSize)
            break;
        }
      }
    }
    if (allexact && actualsize <= tableSize) {
      LOG4("table " << dbp(tab) << " is fully populated");
      auto acts = tab->getActionList()->clone();
      for (auto I = acts->actionList.begin(); I != acts->actionList.end();) {
        auto ale = *I;
        if (ale->getAnnotation("defaultonly")) {
          LOG4("removing default only " << ale);
          I = acts->actionList.erase(I);
        } else {
          ++I;
        }
      }
      auto tabprops = tab->properties->clone();
      tabprops->properties.removeByName(
          IR::TableProperties::defaultActionPropertyName);
      auto It = std::find_if(
          tabprops->properties.begin(), tabprops->properties.end(),
          [&](const IR::Property *prop) {
            return prop->name.name == IR::TableProperties::actionsPropertyName;
          });
      auto actprop = new IR::Property(IR::TableProperties::actionsPropertyName,
                                      acts, false);
      tabprops->properties.replace(It, actprop);
      tab->properties = tabprops;
      tab->annotations = tab->annotations->addAnnotation("nodefault", nullptr);
    }
    return tab;
  }
};

MakePopulatedTables::MakePopulatedTables(ReferenceMap *refMap, TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap) {
  passes.push_back(new TransformPopulatedTables(refMap, typeMap));
  passes.push_back(new P4::ResolveReferences(refMap));
  passes.push_back(new P4::ClearTypeMap(typeMap));
  passes.push_back(new P4::TypeChecking(refMap, typeMap, false));
}

class MakeKeyInstrumentation : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

public:
  MakeKeyInstrumentation(ReferenceMap *refMap, TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}

private:
  const IR::Node *postorder(IR::MethodCallStatement *mcs) override {
    if (is_extern_function(mcs->methodCall, refMap, typeMap,
                           "__instrument_expression__")) {
      auto arg = *mcs->methodCall->arguments->begin();
      ValidityCheck validityCheck(refMap, typeMap);
      auto expr = validityCheck.is_valid(arg->expression);
      if (auto bl = expr->to<IR::BoolLiteral>()) {
        if (!bl->value) {
          return analysis::call_bug();
        } else {
          return nullptr;
        }
      }
      auto check_key = new IR::IfStatement(new IR::LNot(expr),
                                           analysis::call_bug(), nullptr);
      return check_key;
    }
    return mcs;
  }
};

class DeclareInstrumentFunction : public Transform {
  const IR::Node *postorder(IR::Method *met) override {
    if (met->name == "__instrument_expression__")
      return nullptr;
    return met;
  }
  const IR::Node *postorder(IR::P4Program *program) override {
    cstring name = "__instrument_expression__";
    if (!program->getDeclsByName(name)->count()) {
      auto type = new IR::Type_Method(
          IR::Type_Void::get(),
          new IR::ParameterList({new IR::Parameter(
              "condition", IR::Direction::In, IR::Type_Boolean::get())}));
      auto funDecl =
          new IR::Method(program->getSourceInfo(),
                         IR::ID(program->getSourceInfo(), name), type);
      program->objects.insert(program->objects.begin(), funDecl);
    }
    return program;
  }
};

class HandleValueSetCalls : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  std::map<const IR::P4Parser *, std::vector<const IR::ParserState *>> extras;

public:
  HandleValueSetCalls(ReferenceMap *refMap, TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}

private:
  const IR::Method *vsMethod(const IR::P4ValueSet *vs) {
    auto prog = findOrigCtxt<IR::P4Program>();
    auto dec =
        *(prog->getDeclsByName(cstring(cstring("query_") + vs->name.name))
              ->begin());
    return dec->to<IR::Method>();
  }

  const IR::Node *postorder(IR::ParserState *state) override {
    auto prs = findOrigCtxt<IR::P4Parser>();
    if (auto selex = state->selectExpression->to<IR::SelectExpression>()) {
      auto isvs = [&](const IR::SelectCase *selectCase) {
        if (auto pe = selectCase->keyset->to<IR::PathExpression>()) {
          auto tp = typeMap->getType(pe);
          if (tp->is<IR::Type_Set>()) {
            auto decl = refMap->getDeclaration(pe->path)->to<IR::P4ValueSet>();
            CHECK_NULL(decl);
            return true;
          }
        }
        return false;
      };
      auto I = std::find_if(selex->selectCases.begin(),
                            selex->selectCases.end(), isvs);
      BUG_CHECK(!std::any_of(I + 1, selex->selectCases.end(), isvs),
                "can't handle two vs calls in state %1%", state);
      if (I != selex->selectCases.end()) {
        auto pe = (*I)->keyset->to<IR::PathExpression>();
        auto vs = refMap->getDeclaration(pe->path)->to<IR::P4ValueSet>();
        auto mytrans = (*I)->state;
        IR::Vector<IR::SelectCase> before, after;
        std::copy(selex->selectCases.begin(), I, std::back_inserter(before));
        std::copy(I + 1, selex->selectCases.end(), std::back_inserter(after));
        auto state1 = state->clone();
        auto state2 = new IR::ParserState(refMap->newName(state->name),
                                          new IR::PathExpression("bla"));
        auto state3 = new IR::ParserState(refMap->newName(state->name),
                                          new IR::PathExpression("bla"));
        if (before.empty()) {
          state1->selectExpression = new IR::PathExpression(state2->name);
        } else {
          auto sel1 = new IR::SelectExpression(selex->select, before);
          state1->selectExpression = sel1;
        }
        {
          // handle state2
          auto var = new IR::Declaration_Variable(refMap->newName("r"),
                                                  IR::Type_Boolean::get());
          auto met = vsMethod(vs);
          auto tt = typeMap->getTypeType(vs->elementType, true);
          const IR::Expression *arg = selex->select;
          if (!tt->is<IR::Type_StructLike>()) {
            arg = selex->select->components.at(0);
          }
          auto metcall = new IR::MethodCallExpression(
              new IR::PathExpression(met->name),
              new IR::Vector<IR::Argument>({new IR::Argument(arg)}));
          auto asg = new IR::AssignmentStatement(
              new IR::PathExpression(var->name), metcall);
          state2->components.push_back(var);
          state2->components.push_back(asg);
          IR::Vector<IR::SelectCase> cases;

          cases.push_back(
              new IR::SelectCase(new IR::BoolLiteral(true), mytrans));
          cases.push_back(
              new IR::SelectCase(new IR::DefaultExpression(),
                                 new IR::PathExpression(state3->name)));
          auto selex2 = new IR::SelectExpression(
              new IR::ListExpression({new IR::PathExpression(var->name)}),
              cases);
          state2->selectExpression = selex2;
        }
        {
          // handle state 3
          BUG_CHECK(!after.empty(), "default must be after call %1%", state);
          auto selex3 = new IR::SelectExpression(selex->select, after);
          state3->selectExpression = selex3;
        }
        extras[prs].push_back(state1);
        extras[prs].push_back(state2);
        extras[prs].push_back(state3);
        return nullptr;
      }
    }
    return state;
  }
  const IR::Node *postorder(IR::P4Parser *p) override {
    auto orig = getOriginal<IR::P4Parser>();
    auto extra = extras[orig];
    for (auto ex : extra) {
      p->states.push_back(ex);
    }
    return p;
  }
};
}

analysis::RemoveTableCalls::RemoveTableCalls(P4::ReferenceMap *refMap,
                                             P4::TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap) {
  setName("MidEnd_RemoveTableCalls");
  passes.push_back(new DeclareInstrumentFunction);
  passes.push_back(new DoAddTableTypeDeclarations(refMap, typeMap, please_add));
  passes.push_back(new HandleValueSetCalls(refMap, typeMap));
  addPasses({new P4::ClearTypeMap(typeMap),
             new P4::TypeChecking(refMap, typeMap, false)});
  passes.push_back(new PassRepeated({
      new RewriteTableApplies(refMap, typeMap),
      new P4::ResolveReferences(refMap), new P4::ClearTypeMap(typeMap),
      new P4::TypeChecking(refMap, typeMap, false),
      new MakeKeyInstrumentation(refMap, typeMap),
      new P4::ResolveReferences(refMap), new P4::ClearTypeMap(typeMap),
      new P4::TypeChecking(refMap, typeMap, false),
  }));
  passes.push_back(new DeclareInstrumentFunction);
}
