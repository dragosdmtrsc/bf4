//
// Created by dragos on 25.01.2020.
//

#include "RemovePacketLookahead.h"

namespace analysis {

const IR::Expression *eatup(const IR::Expression *l, node_t nd,
                            P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                            NodeValues<const IR::Node *> &replacements) {
  auto bits = typeMap->getType(l)->to<IR::Type_Bits>();
  auto bitsize = bits->size;
  for (const auto instr : instructions(nd)) {
    if (auto mcs = is_extern_method_call(instr)) {
      auto mi = P4::MethodInstance::resolve(mcs->methodCallStatement, refMap,
                                            typeMap);
      if (auto ef = mi->to<P4::ExternFunction>()) {
        if (ef->method->name.name ==
            AnalysisLibrary::instance.packetModel.peek.name) {
          BUG("no luh after luh");
        } else if (ef->method->name.name ==
                   AnalysisLibrary::instance.packetModel.pop.name) {
          auto arg2 = ef->expr->arguments->at(2)->expression;
          auto popbits = typeMap->getType(arg2)->to<IR::Type_Bits>();
          BUG_CHECK(popbits != nullptr, "pop must be of bits type");
          auto popbitsize = popbits->size;
          const IR::Node *stat = nullptr;
          if (popbitsize > bitsize) {
            auto typeSafeDecl = [&](const cstring name, const IR::Type *tp) {
              auto dec = new IR::Declaration_Variable(name, tp);
              typeMap->setType(dec, tp);
              return dec;
            };
            auto v1 = typeSafeDecl(refMap->newName("tmp"),
                                   new IR::Type_Bits(bitsize, false));
            auto v2 =
                typeSafeDecl(refMap->newName("tmp"),
                             new IR::Type_Bits(popbitsize - bitsize, false));
            // v1 = l
            // pop<Bits<popbitsize - bitsize>>(p, p', v2)
            auto pathToVar = [&](const IR::IDeclaration *decl) {
              auto pe = new IR::PathExpression(decl->getName());
              refMap->setDeclaration(pe->path, decl);
              return pe;
            };
            auto asg1 = new IR::AssignmentStatement(pathToVar(v1), l);
            auto clmet = mcs->methodCallStatement->methodCall->clone();
            clmet->method = clmet->method->clone();
            auto clmetargs = clmet->arguments->clone();
            auto clmettypeparms = clmet->typeArguments->clone();
            clmetargs->at(2) = new IR::Argument(pathToVar(v2));
            clmettypeparms->at(0) = v2->type;
            clmet->typeArguments = clmettypeparms;
            clmet->arguments = clmetargs;
            auto clmcs = mcs->methodCallStatement->clone();
            clmcs->methodCall = clmet;
            auto asg2 = new IR::AssignmentStatement(
                arg2, new IR::Concat(pathToVar(v1), pathToVar(v2)));
            stat = new IR::BlockStatement({v1, v2, asg1, clmcs, asg2});
          } else if (popbitsize < bitsize) {
            auto rv = new IR::Slice(l, bitsize - 1, bitsize - popbitsize);
            stat = new IR::AssignmentStatement(arg2, rv);
            l = new IR::Slice(l, bitsize - popbitsize - 1, 0);
          } else {
            stat = new IR::AssignmentStatement(arg2, l);
          }
          replacements[instr] = stat;
          bitsize -= popbitsize;
        }
      }
    }
    if (bitsize <= 0) {
      return nullptr;
    }
  }
  return l;
}

void solve_lookaheads(EdgeHolder &h, node_t start, P4::ReferenceMap *refMap,
                      P4::TypeMap *typeMap) {
  solve_lookaheads(h, nullptr, start, refMap, typeMap);
}

void solve_lookaheads(EdgeHolder &h, EdgeHolder *p_rev, node_t start,
                      P4::ReferenceMap *refMap, P4::TypeMap *typeMap) {
  TypeInference typeChecking(refMap, typeMap, true);
  NodeSet lookaheads;
  NodeValues<const IR::Expression *> lookahead_expression;
  traverse_df_pernode(&h, start, [&](const node_t &nd) {
    for (const auto instr : instructions(nd)) {
      if (auto mcs = is_extern_method_call(instr)) {
        auto mi = P4::MethodInstance::resolve(mcs->methodCallStatement, refMap,
                                              typeMap);
        if (auto ef = mi->to<P4::ExternFunction>()) {
          if (ef->method->name.name ==
              AnalysisLibrary::instance.packetModel.peek.name) {
            BUG_CHECK(lookaheads.emplace(nd).second,
                      "can't have 2 lookaheads in the same bb");
            auto arg1 = ef->expr->arguments->at(1)->expression;
            auto tp = typeMap->getType(arg1);
            auto bits = tp->to<IR::Type_Bits>();
            BUG_CHECK(bits != nullptr, "luh must extract single field");
            lookahead_expression[nd] = arg1;
          } else if (ef->method->name.name ==
                     AnalysisLibrary::instance.packetModel.pop.name) {
            BUG_CHECK(!lookaheads.count(nd), "luh must be last in basic block");
          }
        }
      }
    }
  });
  auto tsclone = [&](const IR::Node *nd) {
    auto cl = nd->clone();
    if (nd->is<IR::Declaration_Instance>()) {
      auto declType = typeMap->getType(nd);
      if (declType) {
        typeMap->setType(cl, declType);
      }
    } else {
      cl->apply(typeChecking);
    }
    return cl;
  };
  if (!lookaheads.empty()) {
    auto initerrcnt = ::errorCount();
    auto sorted = topo_sort(&h, start);
    for (auto l : lookaheads) {
      auto luhe = lookahead_expression[l];
      NodeValues<const IR::Node *> replacements;
      if (!p_rev) {
        p_rev = reverse(&h);
      }
      auto &rev = *p_rev;
      NodeValues<const IR::Expression *> out;
      out[start] = nullptr;
      auto idx = std::find(sorted.begin(), sorted.end(), l) - sorted.begin();
      while (idx >= 0) {
        auto n = sorted[idx];
        if (n == l) {
          out[n] = luhe;
        } else {
          std::unordered_map<const IR::Expression *, EdgeEnumerator>
              partition_per_input;
          auto &predn = rev[n];
          if (predn.empty()) {
            --idx;
            continue;
          }
          for (const auto &ed : predn) {
            partition_per_input[out[ed.first]].emplace_back(ed);
          }
          auto nrPartitions = partition_per_input.size();
          if (nrPartitions > 1) {
            auto dumb = new IR::Vector<IR::Node>();
            auto &hdumb = (h[dumb] = std::move(h[n]));
            auto &rdumb = rev[dumb];
            for (const auto &ed : hdumb) {
              rev[ed.first].emplace_back(dumb, ed.second);
            }
            auto oldsize = sorted.size();
            sorted.resize(sorted.size() + nrPartitions);
            for (auto i = oldsize - 1; i != idx; --i) {
              sorted[i + nrPartitions] = sorted[i];
            }
            sorted[idx++] = dumb;
            sorted[idx++] = n;
            for (auto I = partition_per_input.begin();
                 I != partition_per_input.end(); ++I) {
              node_t ncp = n;
              if (I != partition_per_input.begin()) {
                auto mut = mutate(n)->clone();
                for (unsigned i = 0; i != mut->size(); ++i) {
                  mut->at(i) = tsclone(mut->at(i));
                }
                ncp = mut;
                sorted[idx++] = ncp;
              }
              rev[ncp] = I->second;
              h[ncp] = {{dumb, 0}};
              rdumb.emplace_back(ncp, 0);
            }
            --idx;
            continue;
          }
          BUG_CHECK(nrPartitions == 1, "expecting one partition, got %1%",
                    nrPartitions);
          auto part = *partition_per_input.begin();
          if (part.first) {
            auto nxt = eatup(part.first, n, refMap, typeMap, replacements);
            if (nxt != part.first) {
              //              BUG_CHECK(
              //                  nxt == nullptr,
              //                  "luh must be consumed by basic block or left
              //                  unchanged");
              if (nxt) {
                nxt->apply(typeChecking);
              }
              if (nxt) {
                LOG4("transforming " << part.first << " into " << nxt);
              } else {
                LOG4("completely eaten up " << part.first);
              }
              auto mut = mutate(n);
              IR::Vector<IR::Node> newvec;
              for (auto instr : instructions(n)) {
                auto J = replacements.find(instr);
                if (J != replacements.end()) {
                  if (J->second->is<IR::BlockStatement>()) {
                    newvec.insert(
                        newvec.end(),
                        J->second->to<IR::BlockStatement>()->components.begin(),
                        J->second->to<IR::BlockStatement>()->components.end());
                  } else {
                    newvec.push_back(J->second);
                  }
                } else {
                  newvec.push_back(instr);
                }
              }
              *mut = std::move(newvec);
              for (auto instr : instructions(n)) {
                instr->apply(typeChecking);
                if (initerrcnt != ::errorCount()) {
                  BUG("type checking fails in %1% because %2%", instr, ::errorCount());
                }
              }
              replacements.clear();
            }
            out[n] = nxt;
          } else {
            out[n] = nullptr;
          }
        }
        --idx;
      }
    }
    const IR::Method *pop = nullptr;
    traverse_df_with_check(
        &h, start,
        [&](const node_t &nd) {
          if (pop)
            return;
          for (const auto instr : instructions(nd)) {
            if (auto mcs = is_extern_method_call(instr)) {
              if (auto ef = P4::MethodInstance::resolve(
                                mcs->methodCallStatement, refMap, typeMap)
                                ->to<P4::ExternFunction>()) {
                if (ef->method->name.name ==
                    AnalysisLibrary::instance.packetModel.pop.name) {
                  auto pth = ef->expr->method->to<IR::PathExpression>()->path;
                  pop = refMap->getDeclaration(pth)->to<IR::Method>();
                  CHECK_NULL(pop);
                }
              }
            }
          }
        },
        [&pop](const node_t &, const std::pair<node_t, int> &) {
          return pop == nullptr;
        });
    CHECK_NULL(pop);
    traverse_df_pernode(&h, start, [&](const node_t &nd) {
      auto mut = mutate(nd);
      for (unsigned i = 0; i != mut->size(); ++i) {
        auto &instr = mut->at(i);
        if (auto mcs = is_extern_method_call(instr)) {
          if (auto ef = P4::MethodInstance::resolve(mcs->methodCallStatement,
                                                    refMap, typeMap)
                            ->to<P4::ExternFunction>()) {
            if (ef->method->name.name ==
                AnalysisLibrary::instance.packetModel.peek.name) {
              auto arg0 = ef->expr->arguments->at(0)->expression;
              auto arg1 = ef->expr->arguments->at(1)->expression;
              auto arg2 = arg0->clone();
              auto tp = typeMap->getType(arg1);
              auto bits = tp->to<IR::Type_Bits>();
              auto pth = new IR::Path(pop->name);
              refMap->setDeclaration(pth, pop);
              auto pe = new IR::PathExpression(pth);
              auto targs = new IR::Vector<IR::Type>({bits});
              auto aargs = new IR::Vector<IR::Argument>(
                  {new IR::Argument(arg0), new IR::Argument(arg2),
                   new IR::Argument(arg1)});
              auto mce = new IR::MethodCallExpression(pe, targs, aargs);
              instr = new IR::MethodCallStatement(mce);
              instr->apply(typeChecking);
            }
          }
        }
      }
    });
  }
}
}