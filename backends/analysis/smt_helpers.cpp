//
// Created by dragos on 17.12.2018.
//
#include "smt_helpers.h"
#include <common/constantFolding.h>
#include <p4/evaluator/evaluator.h>
#include <z3++.h>
#include <fstream>
#include "analysis_helpers.h"

namespace analysis {
void SmtTypeWrapper::put_enum_internal(const IR::Type *type, unsigned int n,
                                       const char **names, z3::sort *sort,
                                       z3::func_decl_vector *cs,
                                       z3::func_decl_vector *ts) {
  enum_mapping.emplace(type, sort);
  auto &acc_map =
      enum_accessors.emplace(type, std::map<std::string, z3::func_decl>())
          .first->second;
  for (unsigned i = 0; i != n; ++i) {
    acc_map.emplace(names[i], (*cs)[i]);
  }
  enum_tests.emplace(type, *ts);
}

z3::sort *SmtTypeWrapper::is_builtin(const IR::Type *tp) {
  if (auto tb = tp->to<IR::Type_Bits>()) {
    return basic_mapping
        .emplace(tb, new z3::sort(ctx->bv_sort(
                         static_cast<unsigned int>(tb->width_bits()))))
        .first->second;
  } else if (tp->is<IR::Type_Boolean>()) {
    return basic_mapping.emplace(tp, new z3::sort(ctx->bool_sort()))
        .first->second;
  } else if (tp->is<IR::Type_InfInt>()) {
    return basic_mapping.emplace(tp, new z3::sort(ctx->bv_sort(32)))
        .first->second;
  } else {
    return nullptr;
  }
}

z3::sort *SmtTypeWrapper::is_enum(const IR::Type *p) {
  auto I = enum_mapping.find(p);
  if (I != enum_mapping.end()) return I->second;
  if (p->is<IR::Type_Enum>() || p->is<IR::Type_Error>()) {
    put_enum(p);
    auto I = enum_mapping.find(p);
    if (I != enum_mapping.end()) return I->second;
  }
  return nullptr;
}

z3::sort *SmtTypeWrapper::is_array(const IR::Type *p) {
  auto I = array_mapping.find(p);
  if (I != array_mapping.end()) return I->second;
  return nullptr;
}

z3::sort *SmtTypeWrapper::is_tuple(const IR::Type *p) {
  auto I = tuple_mapping.find(p);
  if (I != tuple_mapping.end()) return I->second;
  return nullptr;
}

z3::sort *SmtTypeWrapper::get_type(const IR::Type *type) {
  if (auto bin = is_builtin(type)) {
    return bin;
  } else if (auto e = is_enum(type)) {
    return e;
  } else if (auto a = is_array(type)) {
    return a;
  } else if (auto tn = type->to<IR::Type_Name>()) {
    auto x = getOrEmplace(uninterpreted, tn->path->name.name, [&]() {
      return new z3::sort(
          context()->uninterpreted_sort(tn->path->name.name.c_str()));
    });
    return x.first;
  } else {
    return is_tuple(type);
  }
}

void SmtTypeWrapper::put_tuple(const IR::Type_StructLike *type, z3::sort *sort,
                               z3::func_decl *constructor, unsigned int n,
                               const char **names,
                               z3::func_decl_vector *projections) {
  tuple_mapping.emplace(type, sort);
  // todo: add to the map all the other fields
  auto &acc_map =
      tuple_accessors.emplace(type, std::map<std::string, z3::func_decl>())
          .first->second;
  auto actual_n = (type->is<IR::Type_Header>()) ? (n - 1) : n;
  unsigned i = 0;
  for (i = 0; i != actual_n; ++i) {
    acc_map.emplace(names[i], (*projections)[i]);
  }
  if (actual_n != n) acc_map.emplace("isValid", (*projections)[i]);
  tuple_constructors.emplace(type, *constructor);
}

z3::func_decl SmtTypeWrapper::get_tuple_accessor(const IR::Type *t,
                                                 const char *name) {
  return tuple_accessors[t].find(name)->second;
}

z3::func_decl SmtTypeWrapper::get_enum_member_constructor(const IR::Type *t,
                                                          const char *name) {
  return enum_accessors[t].find(name)->second;
}

void SmtTypeWrapper::put_enum(const IR::Type_Error *type, unsigned int n,
                              const char **names, z3::sort *sort,
                              z3::func_decl_vector *cs,
                              z3::func_decl_vector *ts) {
  put_enum_internal(type, n, names, sort, cs, ts);
}

void SmtTypeWrapper::put_array(const IR::Type_Stack *type, unsigned int,
                               z3::sort *srt) {
  array_mapping[type] = srt;
}

void SmtTypeWrapper::print(std::ostream &o) {
  o << "enums:";
  for (auto e : enum_mapping) {
    o << e.first << " " << *e.second << '\n';
  }
  o << "tuples:";
  for (auto e : tuple_mapping) {
    o << e.first << " " << *e.second << '\n';
  }
  o << "arrays:";
  for (auto e : array_mapping) {
    o << e.first << " " << *e.second << '\n';
  }
}

void SmtTypeWrapper::put_enum(const IR::Type *tenum) {
  BUG_CHECK(tenum->is<IR::Type_Enum>() || tenum->is<IR::Type_Error>(),
            "expecting enum or error, got %1%", tenum);
  auto terror = tenum->to<IR::Type_Error>();
  auto tennum = tenum->to<IR::Type_Enum>();
  unsigned nr = 0;
  const IR::IndexedVector<IR::Declaration_ID> *decls = nullptr;
  if (tennum) {
    decls = &tennum->members;
  } else if (terror) {
    decls = &terror->members;
  }
  nr = static_cast<unsigned>(decls->size());
  const auto **names = new const char *[nr];
  unsigned i = 0;
  auto *cs = new z3::func_decl_vector(*ctx);
  auto *ts = new z3::func_decl_vector(*ctx);
  for (auto m : *decls) {
    names[i++] = m->name.name.c_str();
  }
  auto ensort = ctx->enumeration_sort(
      (tennum) ? tennum->name.name.c_str() : terror->name.name.c_str(), nr,
      names, *cs, *ts);
  if (terror) {
    put_enum(terror, nr, names, new z3::sort(ensort), cs, ts);
  } else if (tennum) {
    put_enum(tennum, nr, names, new z3::sort(ensort), cs, ts);
  }
}

bool IRToSmtTypeMap::preorder(const IR::P4Program *) {
  wrapper->clear();
  return true;
}

void IRToSmtTypeMap::postorder(const IR::Type_Error *en) {
  auto nr = static_cast<unsigned>(en->members.size());
  const auto **names = new const char *[nr];
  unsigned i = 0;
  auto *cs = new z3::func_decl_vector(*ctx);
  auto *ts = new z3::func_decl_vector(*ctx);
  for (auto m : en->members) {
    names[i++] = m->name.name.c_str();
  }
  auto ensort =
      ctx->enumeration_sort(en->name.name.c_str(), nr, names, *cs, *ts);
  wrapper->put_enum(en, nr, names, new z3::sort(ensort), cs, ts);
}

void IRToSmtTypeMap::postorder(const IR::Type_Enum *en) {
  en = typeMap->getTypeType(en, true)->to<IR::Type_Enum>();
  wrapper->put_enum(en);
}

void IRToSmtTypeMap::postorder(const IR::Type_Stack *stack) {
  BUG_CHECK(stack->size->is<IR::Constant>(),
            "can only handle fixed array sizes");
  auto max = stack->size->to<IR::Constant>()->value;
  auto tt = typeMap->getType(stack->elementType);
  BUG_CHECK(tt->is<IR::Type_Type>(), "can only have Type_Type");
  auto canon =
      typeMap->getType(stack)->to<IR::Type_Type>()->type->to<IR::Type_Stack>();
  wrapper->put_array(
      canon, static_cast<unsigned int>(max.get_ui()),
      new z3::sort(ctx->array_sort(
          ctx->int_sort(), *wrapper->get_type(tt->to<IR::Type_Type>()->type))));
}

void IRToSmtTypeMap::postorder(const IR::Type_StructLike *td) {
  auto name = td->name.name;
  td = typeMap->getType(td)
           ->to<IR::Type_Type>()
           ->type->to<IR::Type_StructLike>();
  auto *ref = new z3::sort(*ctx);
  auto ct = ((td->is<IR::Type_Header>()) ? 1 : 0);
  auto nfields = static_cast<unsigned int>(td->fields.size() + ct);
  std::vector<z3::sort> sorts;
  auto *projs = new z3::func_decl_vector(*ctx);

  const auto **names = new const char *[nfields];
  unsigned i = 0;
  for (auto field : td->fields) {
    auto nm = field->name.name;
    auto tp = typeMap->getType(field);
    sorts.emplace_back(*wrapper->get_type(tp));
    names[i] = nm.c_str();
    ++i;
  }
  if (td->is<IR::Type_Header>()) {
    sorts.emplace_back(*wrapper->get_type(IR::Type_Boolean::get()));
    names[i] = "isValid";
  }
  auto constructor = tuple_sort(*ctx, name.c_str(), nfields, names,
                                sorts.data(), *projs, *ref);
  wrapper->put_tuple(td, ref, new z3::func_decl(constructor), nfields, names,
                     projs);
}

TypeMapProxy::TypeMapProxy(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                           SmtTypeWrapper *wrapper)
    : refMap(refMap), typeMap(typeMap), wrapper(wrapper) {}
}
