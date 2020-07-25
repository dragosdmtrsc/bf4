//
// Created by dragos on 07.06.2019.
//

#ifndef P4C_MAKEIMPLEMENTATIONS_H
#define P4C_MAKEIMPLEMENTATIONS_H

#include <common/resolveReferences/referenceMap.h>
#include <p4/cloner.h>
#include <p4/methodInstance.h>
#include <p4/typeChecking/typeChecker.h>
#include <p4/typeMap.h>
#include <p4/uniqueNames.h>

namespace analysis {

class DoCreateMutablePacket : public Transform {
  const IR::Node *postorder(IR::P4Program *prog) override;
  const IR::Node *postorder(IR::Parameter *param) override;
};

class DoAddErrorField : public Transform {
  const IR::Node *postorder(IR::Type_Parser *tp) override;
};

class DoCastReplace : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

 public:
  DoCastReplace(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
  const IR::Node *postorder(IR::MethodCallExpression *mce) override;
  const IR::Node *preorder(IR::MethodCallStatement *mcs) override {
    if (mcs->methodCall->method->is<IR::PathExpression>()) {
      if (mcs->methodCall->method->to<IR::PathExpression>()->path->name ==
          "do_cast") {
        prune();
        return nullptr;
      }
    }
    return mcs;
  }

  void end_apply(const IR::Node *n) override;

  const IR::Expression *cast(const IR::Expression *e, const IR::Type *t);

  const IR::Type_Bits *getBits(const IR::Type *srct,
                               std::vector<const IR::Type *> &traversed) const;
};

class CastReplace : public PassManager {
 public:
  CastReplace(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};

// whenever a type appears next to a declaration_var
// declaration_instance, parameter, constructor call expression
// in the type arguments of specialized canonical bla
// replace type_name with canonical type
class DoRemoveTypeNames : public Transform {
  P4::ReferenceMap *refMap;

 public:
  DoRemoveTypeNames(P4::ReferenceMap *refMap) : refMap(refMap) {}

  const IR::Node *postorder(IR::TypeNameExpression *tne) override;
  const IR::Node *postorder(IR::Type_Name *tn) override;
  const IR::Node *preorder(IR::ConstructorCallExpression *cce) override;
  const IR::Node *preorder(IR::Declaration_Instance *di) override;
  const IR::Node *preorder(IR::Type_Specialized *ts) override;
};

class RemoveTypeNames : public PassRepeated {
 public:
  RemoveTypeNames(P4::ReferenceMap *refMap) {
    passes.push_back(new DoRemoveTypeNames(refMap));
  }
};

class MakeImplementations : public PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

 public:
  MakeImplementations(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};

struct scope;
struct scope_context {
  unsigned crtId = 0;
  scope *new_scope();
};
struct scope {
  scope_context *ctx;
  std::map<const IR::IDeclaration *, unsigned> declarations;
  std::vector<scope *> children;
  scope *parent;
  void addDeclaration(const IR::IDeclaration *decl);
  scope(scope_context *context);
};
class BuildScopeTree : public Inspector {
  scope_context *ctx;
  scope *crtScope = nullptr;
  std::map<const IR::Node *, scope *> &scopes;
  void mkScope(const IR::Node *node);
  void pop();
  void registerTypeParameters(const IR::TypeParameters *parms);
  void registerParameters(const IR::ParameterList *parms);

 public:
  bool preorder(const IR::P4Program *p) override;
  bool preorder(const IR::Function *fun) override;
  bool preorder(const IR::Type_Extern *text) override;
  bool preorder(const IR::Method *m) override;
  bool preorder(const IR::Type_StructLike *sl) override;
  bool preorder(const IR::P4Control *control) override;
  bool preorder(const IR::P4Parser *control) override;
  bool preorder(const IR::ParserState *state) override;
  bool preorder(const IR::BlockStatement *statement) override;
  bool preorder(const IR::Node *n) override;

  BuildScopeTree(std::map<const IR::Node *, scope *> &scopes);
};

std::map<const IR::IDeclaration *, unsigned int> variable_declarations(
    const IR::P4Program *p, const std::map<const IR::Node *, scope *> &scopes);
std::map<const IR::IDeclaration *, unsigned> variable_declarations(
    const IR::P4Program *p);
std::map<const IR::Node *, scope *> scopes(const IR::P4Program *prog);

class MakeDie : public PassManager {
 public:
  MakeDie(P4::ReferenceMap *refMap);
};

class RemoveTypedefs : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

 public:
  RemoveTypedefs(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}

  const IR::Node *preorder(IR::Type_Newtype *x) override {
    prune();
    return x;
  }
  const IR::Node *preorder(IR::Type_Typedef *x) override {
    prune();
    return x;
  }
  const IR::Node *postorder(IR::Type *tt) override;
};

class Normalize : public PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

 public:
  Normalize(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};

class MoveReturnsInward : public PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

 public:
  MoveReturnsInward(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};

class PacketExtract : public PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

 public:
  PacketExtract(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};

class RenameParameters : public PassManager {
  P4::ReferenceMap *refMap;
  P4::RenameMap renameMap;

 public:
  RenameParameters(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};

class RenameImplParameters : public PassManager {
  P4::ReferenceMap *refMap;
  P4::RenameMap renameMap;

public:
  RenameImplParameters(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};

class MaterializeConstants : public PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
public:
  MaterializeConstants(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};

class SplitInouts : public PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
public:
  SplitInouts(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};

class DisentangleExternParams : public PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
public:
  DisentangleExternParams(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};

class HandleValueSets : public PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
public:
  HandleValueSets(P4::ReferenceMap *refMap, P4::TypeMap *typeMap);
};

}

#endif  // P4C_MAKEIMPLEMENTATIONS_H
