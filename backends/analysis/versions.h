//
// Created by dragos on 17.12.2018.
//

#ifndef P4C_VERSIONS_H
#define P4C_VERSIONS_H

#include "analysis_helpers.h"
#include <common/resolveReferences/referenceMap.h>
#include <frontends/p4/typeChecking/typeChecker.h>
#include <ir/ir.h>
#include <p4/typeMap.h>

namespace analysis {

struct EitherIntOrString {
  cstring str;
  int nr;

  EitherIntOrString(cstring str) : str(str), nr(-1) {}

  EitherIntOrString(int nr) : str(nullptr), nr(nr) {}

  bool is_str() const { return nr < 0; }

  bool is_num() const { return nr >= 0; }
  bool operator==(const EitherIntOrString &o) const {
    if (is_num() != o.is_num())
      return false;
    if (is_num())
      return nr == o.nr;
    return str == o.str;
  }
  inline bool operator<(const EitherIntOrString &o) const {
    if (is_num() != o.is_num())
      return !is_num();
    if (is_num())
      return nr < o.nr;
    return str < o.str;
  }
};

typedef std::vector<EitherIntOrString> Path;

struct MemPath {
  const IR::IDeclaration *decl;
  Path path;
  unsigned version = -1u;

  MemPath(const IR::IDeclaration *decl) : decl(decl) {}

  MemPath() = default;

  void append(EitherIntOrString other) { path.emplace_back(other); }

  void pop() { path.pop_back(); }

  friend std::ostream &operator<<(std::ostream &os, const MemPath &mp) {
    if (mp.decl) {
      os << mp.decl->getName().name;
    }
    for (auto p : mp.path) {
      if (p.is_str())
        os << "." << p.str;
      else
        os << "[" << p.nr << "]";
    }
    os << ":" << mp.version;
    return os;
  }
  bool operator==(const MemPath &other) const;
  bool operator<(const MemPath &r) const;
};
typedef std::set<MemPath> PathSet;

std::size_t hash_value(const EitherIntOrString &cp);

std::size_t hash_value(const MemPath &mp);
}

namespace std {
template <> struct hash<analysis::MemPath> {
  std::size_t operator()(const analysis::MemPath &mp) const {
    return analysis::hash_value(mp);
  }
};
}

namespace analysis {
class PathGetter : public Inspector {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  P4::TypeInference tc;

public:
  IsLv isLv;

private:
  MemPath *out;
  std::unordered_map<const IR::Node *, MemPath *> paths;
  std::unordered_map<MemPath, const IR::Expression *> reversePaths;

  bool preorder(const IR::Expression *e) override {
    if (auto ve = e->to<IR::VersionedExpression>()) {
      visit(ve->leftValue);
      out->version = ve->version;
      return false;
    }
    return true;
  }
  void postorder(const IR::PathExpression *pe) override {
    out->decl = refMap->getDeclaration(pe->path);
  }
  void postorder(const IR::Member *member) override {
    if (typeMap->getType(member)->is<IR::Type_MethodBase>())
      return;
    out->append(member->member.name);
  }
  void postorder(const IR::ArrayIndex *ai) override {
    out->append(ai->right->to<IR::Constant>()->value.get_ui());
  }
  void postorder(const IR::MethodCallExpression *mce) override {
    if (is_is_valid(mce, refMap, typeMap)) {
      out->append(cstring("isValid"));
    }
  }

public:
  PathGetter(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap), tc(refMap, typeMap),
        isLv(refMap, typeMap) {}

  const IR::Expression *operator()(const MemPath &mp) {
    auto I = reversePaths.find(mp);
    if (I != reversePaths.end())
      return I->second;
    auto pe = new IR::PathExpression(mp.decl->getName());
    refMap->setDeclaration(pe->path, mp.decl);
    typeMap->setLeftValue(pe);
    const IR::Expression *crt = pe;
    for (auto p : mp.path) {
      if (p.is_num()) {
        crt = new IR::ArrayIndex(crt, new IR::Constant(p.nr));
      } else {
        crt = new IR::Member(crt, p.str);
      }
      typeMap->setLeftValue(crt);
    }
    crt->apply(tc);
    if (mp.version != -1u) {
      auto oldtype = typeMap->getType(crt);
      crt = new IR::VersionedExpression(crt, mp.version);
      typeMap->setType(crt, oldtype);
    }
    return reversePaths.emplace(mp, crt).first->second;
  }
  MemPath *operator()(const IR::Node *lv) {
    if (!isLv(lv))
      return nullptr;
    auto I = paths.find(lv);
    if (I != paths.end())
      return I->second;
    out = new MemPath();
    if (lv->is<IR::Declaration>()) {
      out->decl = lv->to<IR::Declaration>();
    } else if (lv->is<IR::Expression>()) {
      lv->apply(*this);
      paths.emplace(lv, out);
    } else {
      BUG("can't get path for %1%", lv);
    }
    return out;
  }

  std::vector<MemPath> terminals(const MemPath &mp) {
    auto tp = typeMap->getType(mp.decl->getNode());
    for (auto p : mp.path) {
      if (p.is_num()) {
        tp = typeMap->getTypeType(tp->to<IR::Type_Stack>()->elementType, true);
      } else {
        tp = typeMap->getType(tp->to<IR::Type_StructLike>()
                                  ->fields.getDeclaration(p.str)
                                  ->getNode(),
                              true);
      }
    }
    std::vector<MemPath> paths;
    std::function<void(const IR::Type *, MemPath &)> rec;
    rec = [&](const IR::Type *tp, MemPath &crt) {
      if (tp->is<IR::Type_StructLike>()) {
        for (auto f : tp->to<IR::Type_StructLike>()->fields) {
          crt.append(f->name.name);
          rec(typeMap->getTypeType(f->type, true), crt);
          crt.pop();
        }
      } else if (tp->is<IR::Type_Stack>()) {
        auto ts = tp->to<IR::Type_Stack>();
        for (unsigned i = 0; i != ts->getSize(); ++i) {
          crt.append(i);
          rec(typeMap->getTypeType(ts->elementType, true), crt);
          crt.pop();
        }
      } else {
        paths.emplace_back(crt);
      }
    };
    auto cmp = mp;
    rec(tp, cmp);
    return std::move(paths);
  }
};
};

#endif // P4C_VERSIONS_H
