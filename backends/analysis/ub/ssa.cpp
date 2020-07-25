//
// Created by dragos on 29.08.2019.
//

#include "ssa.h"
#include "AnalysisContext.h"

namespace analysis {
std::unordered_set<MemPath> all(const EdgeHolder &g, const node_t &start,
                                P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                                NodeToFunctionMap *funMap) {
  std::unordered_set<MemPath> mps;
  ReadSet rs(refMap, typeMap, funMap);
  WriteSet ws(refMap, typeMap, funMap);
  traverse_df_pernode(&g, start, [&](const node_t &n) {
    mps.insert(rs[n].begin(), rs[n].end());
    mps.insert(ws[n].begin(), ws[n].end());
  });
  return mps;
}

template <bool RW>
Reads<RW>::Reads(ReferenceMap *refMap, TypeMap *typeMap,
                 NodeToFunctionMap *funMap)
    : refMap(refMap), typeMap(typeMap), funMap(funMap), lvs(refMap, typeMap),
      pathGetter(refMap, typeMap) {}

template <bool RW>
void Reads<RW>::compute_reads(const node_t &n,
                              std::unordered_set<MemPath> &res) {
  if (auto asg = is_assign(n)) {
    if (RW) {
      read(res, asg->rv);
    } else {
      read(res, asg->lv);
    }
  } else if (auto emc = is_extern_method_call(n)) {
    if (is_terminal(emc->methodCallStatement))
      return;
    if (is_set_invalid(emc->methodCallStatement, refMap, typeMap) ||
        is_set_valid(emc->methodCallStatement, refMap, typeMap)) {
      if (RW) {
        return;
      } else {
        // TODO: never reachable
        auto p = *pathGetter(
            emc->methodCallStatement->methodCall->method->to<IR::Member>()
                ->expr);
        p.append(IR::Type_Header::isValid);
        res.emplace(p);
        return;
      }
    }
    handle_in_params(res, n, false, true);
    handle_in_params(res, n, true, true);
  } else if (auto call = is_method_call(n)) {
    handle_in_params(res, n, false, false);
  } else if (auto ret = is_if(n, typeMap)) {
    if (RW)
      read(res, ret->cond);
  } else if (n.type == NodeType::RETURN) {
    handle_in_params(res, n, true, false);
  } else if (selex_node(n)) {
    if (RW) {
      for (auto cp : n.node->to<IR::SelectExpression>()->select->components) {
        read(res, cp);
      }
    }
  }
}

template <bool RW>
void Reads<RW>::handle_in_params(std::unordered_set<MemPath> &res,
                                 const node_t &n, bool is_return,
                                 bool is_extern) {
  auto instance = P4::MethodInstance::resolve(
      n.node->to<IR::MethodCallStatement>(), refMap, typeMap);
  auto params = instance->getActualParameters();
  for (auto parm : *params) {
    auto arg = instance->substitution.lookupByName(parm->name);
    if ((!is_return && parm->direction == IR::Direction::In) ||
        (is_return && parm->direction == IR::Direction::Out) ||
        parm->direction == IR::Direction::InOut) {
      if (!is_return) {
        // case call: reads all exprs with dir == IN/INOUT
        // writes all params with dir == IN/INOUT
        if (RW) {
          read(res, arg->expression);
        } else {
          if (!is_extern) {
            auto p = pathGetter(parm);
            for (auto &mp : pathGetter.terminals(*p)) {
              res.emplace(mp);
            }
          }
        }
      } else {
        // case return: reads all params with dir == OUT/INOUT
        // case call: writes all exprs with dir == OUT/INOUT
        if (RW) {
          if (!is_extern) {
            auto p = pathGetter(parm);
            for (auto &mp : pathGetter.terminals(*p)) {
              res.emplace(mp);
            }
          }
        } else {
          read(res, arg->expression);
        }
      }
    }
  }
}
template <bool RW>
void Reads<RW>::read(std::unordered_set<MemPath> &res,
                     const IR::Expression *rvex) {
  auto reads = lvs(rvex);
  for (auto e : *reads) {
    auto p = pathGetter(e);
    for (const auto &mp : pathGetter.terminals(*p)) {
      res.emplace(mp);
    }
  }
}
template <bool RW>
std::unordered_set<MemPath> &Reads<RW>::operator[](const node_t &n) {
  auto EMI = reads.emplace(n, std::unordered_set<MemPath>());
  if (EMI.second) {
    compute_reads(n, EMI.first->second);
  }
  return EMI.first->second;
}

template <bool RW>
std::unordered_set<MemPath> Reads<RW>::operator()(const IR::Expression *nd) {
  std::unordered_set<MemPath> paths;
  read(paths, nd);
  return paths;
}

template class Reads<true>;
template class Reads<false>;
const IR::Node *Replace::preorder(IR::Expression *expression) {
  auto orig = getOriginal<IR::Expression>();
  if (isLv(orig)) {
    auto p = pathGetter(orig);
    CHECK_NULL(p);
    auto replI = replacements.find(*p);
    if (replI != replacements.end()) {
      if (replI->second != orig) {
        if (isLv(replI->second)) {
          if (*pathGetter(replI->second) == *p) {
            prune();
            return expression;
          }
        }
        prune();
        auto ctx = getContext();
        while (ctx) {
          if (ctx->original == replI->second || ctx->node == replI->second) {
            WARNING(
                "something seems not right: expression tries to over-expand "
                << replI->second);
            return expression;
          }
          ctx = ctx->parent;
        }
        return replI->second;
      }
    }
    prune();
  }
  return expression;
}
const IR::Node *Replace::operator()(const IR::Node *e) {
  auto res = e->apply(*this);
  if (res != e) {
    res->apply(tc);
    return res;
  }
  return e;
}

const IR::Node *Replace::preorder(IR::Argument *arg) {
  if (!readonly)
    return arg;
  auto orig = getOriginal<IR::Argument>();
  auto mce = findOrigCtxt<IR::MethodCallExpression>();
  if (mce) {
    auto mi = P4::MethodInstance::resolve(mce, refMap, typeMap);
    auto p = mi->substitution.findParameter(orig);
    CHECK_NULL(p);
    if (p->direction != IR::Direction::In) {
      prune();
    }
  }
  return arg;
}

ReplaceAll::ReplaceAll(
    ReferenceMap *refMap, TypeMap *typeMap,
    std::unordered_map<MemPath, const IR::Expression *> rreplacements,
    std::unordered_map<MemPath, const IR::Expression *> wreplacements)
    : refMap(refMap), typeMap(typeMap), pathTypes(typeMap, false),
      tc(refMap, typeMap, true),
      rreplace(refMap, typeMap, std::move(rreplacements)),
      wreplace(refMap, typeMap, std::move(wreplacements)) {
  for (auto &x : rreplace.replacements) {
    typeMap->setType(x.second, pathTypes[x.first]);
    typeMap->setLeftValue(x.second);
  }
  for (auto &x : wreplace.replacements) {
    typeMap->setType(x.second, pathTypes[x.first]);
    typeMap->setLeftValue(x.second);
  }
}

const IR::Node *ReplaceAll::operator()(const IR::Node *n) {
  return getOrEmplace(transforms, n,
                      [&]() {
                        auto newnode = n->apply(*this);
                        if (newnode != n) {
                          newnode->apply(tc);
                          return newnode;
                        } else {
                          return n;
                        }
                      })
      .first;
}

const IR::Node *ReplaceAll::preorder(IR::AssignmentStatement *asg) {
  prune();
  asg->left = asg->left->apply(wreplace);
  asg->right = asg->right->apply(rreplace);
  return asg;
}

const IR::Node *ReplaceAll::preorder(IR::Node *d) {
  prune();
  auto orig = getOriginal();
  auto r = orig->apply(rreplace);
  if (r != orig)
    return r;
  return d;
}

const IR::Node *ReplaceAll::preorder(IR::MethodCallStatement *expression) {
  auto mi = P4::MethodInstance::resolve(getOriginal<IR::MethodCallStatement>(),
                                        refMap, typeMap);
  prune();
  bool any_change = false;
  auto p_args = new IR::Vector<IR::Argument>();
  for (auto p : mi->getActualParameters()->parameters) {
    auto arg = mi->substitution.lookupByName(p->name);
    auto old = arg;
    if (p->direction == IR::Direction::Out) {
      auto arclone = arg->clone();
      auto e = arg->expression->apply(wreplace)->to<IR::Expression>();
      if (arclone->expression != e) {
        arclone->expression = e;
        arg = arclone;
      }
    } else if (p->direction == IR::Direction::In) {
      auto arclone = arg->clone();
      auto e = arg->expression->apply(rreplace)->to<IR::Expression>();
      if (arclone->expression != e) {
        arclone->expression = e;
        arg = arclone;
      }
    } else if (p->direction == IR::Direction::InOut) {
      BUG("inout params must have been removed by now, found %1%", p);
    }
    if (arg != old)
      any_change = true;
    p_args->push_back(arg);
  }
  if (any_change) {
    auto mce = expression->methodCall->clone();
    mce->arguments = p_args;
    expression->methodCall = mce;
  }
  return expression;
}

const IR::Node *ReplaceAll::preorder(IR::IfStatement *ifs) {
  prune();
  auto cd = ifs->condition->apply(rreplace);
  if (ifs->condition != cd) {
    ifs->condition = cd;
  }
  return ifs;
}

const IR::Node *ReplaceAll::preorder(IR::SelectExpression *sexp) {
  prune();
  auto selc = sexp->select->apply(rreplace)->to<IR::ListExpression>();
  if (selc != sexp->select)
    sexp->select = selc;
  return sexp;
}
}
