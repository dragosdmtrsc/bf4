//
// Created by dragos on 17.12.2018.
//

#ifndef P4C_SMT_HELPERS_H
#define P4C_SMT_HELPERS_H

#include <common/resolveReferences/referenceMap.h>
#include <p4/typeMap.h>
#include <z3++.h>

namespace analysis {

using namespace z3;
inline z3::expr mk_numeral(z3::context &ctx, const char *nr, z3::sort sort) {
  Z3_ast r = Z3_mk_numeral(ctx, nr, sort);
  ctx.check_error();
  return z3::expr(ctx, r);
}
inline func_decl tuple_sort(context &ctx, char const *name, unsigned n,
                            char const *const *names, sort const *sorts,
                            func_decl_vector &projs, sort &sort) {
  array<Z3_symbol> _names(n);
  array<Z3_sort> _sorts(n);
  for (unsigned i = 0; i < n; i++) {
    _names[i] = Z3_mk_string_symbol(ctx, names[i]);
    _sorts[i] = sorts[i];
  }
  array<Z3_func_decl> _projs(n);
  Z3_symbol _name = Z3_mk_string_symbol(ctx, name);
  Z3_func_decl tuple;
  sort = to_sort(ctx, Z3_mk_tuple_sort(ctx, _name, n, _names.ptr(),
                                       _sorts.ptr(), &tuple, _projs.ptr()));
  ctx.check_error();
  for (unsigned i = 0; i < n; i++) {
    projs.push_back(func_decl(ctx, _projs[i]));
  }
  return func_decl(ctx, tuple);
}
class SmtTypeWrapper {
  std::map<cstring, z3::sort *> uninterpreted;
  std::map<const IR::Type *, z3::sort *> tuple_mapping;
  std::map<const IR::Type *, std::map<std::string, z3::func_decl>>
      tuple_accessors;
  std::map<const IR::Type *, z3::func_decl> tuple_constructors;
  std::map<const IR::Type *, z3::sort *> enum_mapping;
  std::map<const IR::Type *, std::map<std::string, z3::func_decl>>
      enum_accessors;
  std::map<const IR::Type *, z3::func_decl_vector> enum_tests;
  std::map<const IR::Type *, z3::sort *> basic_mapping;
  std::map<const IR::Type *, z3::sort *> array_mapping;
  z3::context *ctx;

  void put_enum_internal(const IR::Type *type, unsigned int n,
                         const char **names, z3::sort *sort,
                         z3::func_decl_vector *cs, z3::func_decl_vector *ts);

 public:
  SmtTypeWrapper(z3::context *ctx) : ctx(ctx) {}

  z3::context *context() { return ctx; }
  void set_type(cstring name, z3::sort &s) { uninterpreted.emplace(name, &s); }
  void clear() {
    tuple_mapping.clear();
    basic_mapping.clear();
    enum_mapping.clear();
    array_mapping.clear();
  }
  z3::sort *is_builtin(const IR::Type *tp);
  z3::sort *is_enum(const IR::Type *p);
  z3::sort *is_array(const IR::Type *p);
  z3::sort *is_tuple(const IR::Type *p);
  z3::sort *get_type(const IR::Type *type);
  void put_tuple(const IR::Type_StructLike *type, z3::sort *sort,
                 z3::func_decl *constructor, unsigned int n, const char **names,
                 z3::func_decl_vector *projections);
  z3::func_decl get_tuple_accessor(const IR::Type *t, const char *name);

  z3::func_decl get_enum_member_constructor(const IR::Type *t,
                                            const char *name);
  z3::expr enum_member(const IR::Type *t, const char *name) {
    return get_enum_member_constructor(t, name)();
  }
  const z3::func_decl_vector &get_enum_members_tests(const IR::Type *t) {
    return enum_tests.find(t)->second;
  }
  void put_enum(const IR::Type_Error *type, unsigned int n, const char **names,
                z3::sort *sort, z3::func_decl_vector *cs,
                z3::func_decl_vector *ts);
  void put_enum(const IR::Type_Enum *type, unsigned int n, const char **names,
                z3::sort *sort, z3::func_decl_vector *cs,
                z3::func_decl_vector *ts) {
    put_enum_internal(type, n, names, sort, cs, ts);
  }
  void put_enum(const IR::Type *tenum);
  z3::func_decl get_tuple_constructor(const IR::Type *t) {
    return tuple_constructors.find(t)->second;
  }
  void put_array(const IR::Type_Stack *type, unsigned int max, z3::sort *srt);
  void print(std::ostream &o);
};

class TypeMapProxy {
 public:
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  SmtTypeWrapper *wrapper;

  TypeMapProxy(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
               SmtTypeWrapper *wrapper);

  z3::sort *getSort(const IR::Node *n) {
    return wrapper->get_type(typeMap->getType(n));
  }
};

class IRToSmtTypeMap : public Inspector {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  z3::context *ctx;
  SmtTypeWrapper *wrapper;

 public:
  IRToSmtTypeMap(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                 z3::context *ctx, SmtTypeWrapper *wrapper)
      : refMap(refMap), typeMap(typeMap), ctx(ctx), wrapper(wrapper) {}
  bool preorder(const IR::P4Program *p) override;
  void postorder(const IR::Type_Error *en) override;
  void postorder(const IR::Type_Enum *en) override;
  void postorder(const IR::Type_Stack *stack) override;
  void postorder(const IR::Type_StructLike *td) override;
};
};

#endif  // P4C_SMT_HELPERS_H
