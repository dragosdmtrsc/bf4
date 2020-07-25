//
// Created by dragos on 08.09.2019.
//

#include "AnalysisContext.h"
#include <analysis/constprop/ConstantPropagation.h>
#include <p4/enumInstance.h>

namespace analysis {
Analysis::Analysis(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                   const IR::P4Program *program, cstring startFunction)
    : refMap(refMap), typeMap(typeMap), program(program),
      startFunction(startFunction) {}

const IR::Expression *
SelectToExpression::selectCaseOne(const IR::Expression *chosen_head,
                                  const IR::Expression *component) {
  if (auto msk = chosen_head->to<IR::Mask>()) {
    auto rv = msk->left;
    auto rm = msk->right;
    return new IR::Equ(new IR::BAnd(component, rm), rv);
  } else if (auto val = chosen_head->to<IR::Literal>()) {
    auto rv = val;
    return new IR::Equ(component, rv);
  } else if (auto mem = chosen_head->to<IR::Member>()) {
    auto ei = P4::EnumInstance::resolve(mem, typeMap);
    if (!ei) {
      BUG("unexpected select head: %1%", mem);
    }
    return new IR::Equ(component, mem);
  } else if (chosen_head->is<IR::DefaultExpression>()) {
    return new IR::BoolLiteral(true);
  } else {
    BUG("unknown head: %1% %2%", chosen_head, chosen_head->static_type_name());
  }
}

const IR::Expression *
SelectToExpression::selectCase(const IR::ListExpression *select,
                               const IR::SelectCase *selcase) {
  if (auto lstexp = selcase->keyset->to<IR::ListExpression>()) {
    auto lstexpIT = lstexp->components.begin();
    const IR::Expression *crt = nullptr;
    for (auto component : select->components) {
      auto lex = *lstexpIT;
      if (!crt)
        crt = selectCaseOne(lex, component);
      else
        crt = new IR::LAnd(crt, selectCaseOne(lex, component));
      ++lstexpIT;
    }
    return crt;
  } else {
    return selectCaseOne(selcase->keyset, *select->components.begin());
  }
}

const IR::Expression *
SelectToExpression::computeExpression(const IR::SelectExpression *selex,
                                      int what) {
  const IR::Expression *e = nullptr;
  if (what == 0) {
    e = selectCase(selex->select,
                   selex->selectCases.at(static_cast<size_t>(what)));
  } else {
    for (auto i = 0; i != what; ++i) {
      auto exp = selectCase(selex->select,
                            selex->selectCases.at(static_cast<size_t>(i)));
      if (i == 0)
        e = new IR::LNot(exp);
      else
        e = new IR::LAnd(e, new IR::LNot(exp));
    }
    e = new IR::LAnd(
        e, selectCase(selex->select,
                      selex->selectCases.at(static_cast<size_t>(what))));
  }
  (void)e->apply(tc);
  return e;
}

const IR::Expression *SelectToExpression::
operator()(const IR::SelectExpression *selex, int what) {
  auto EMI = expressions.emplace(std::make_pair(selex, what), nullptr);
  if (EMI.second) {
    EMI.first->second = computeExpression(selex, what);
  }
  return EMI.first->second;
}

SelectToExpression::SelectToExpression(ReferenceMap *refMap, TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap), tc(refMap, typeMap) {}

const IR::Expression *MultiAssignment::exp(const IR::Node *n, bool lv) {
  if (n->is<IR::Declaration>()) {
    auto d = n->to<IR::Declaration>();
    auto pe = new IR::PathExpression(d->name);
    refMap->setDeclaration(pe->path, d);
    fixExpression(pe, typeMap->getType(d), lv);
    return pe;
  } else if (n->is<IR::Expression>()) {
    return n->to<IR::Expression>();
  }
  BUG("n must be either Declaration or Expression, but %1% found", n);
}

void MultiAssignment::fixExpression(const IR::Expression *e, const IR::Type *t,
                                    bool lv) {
  if (lv)
    typeMap->setLeftValue(e);
  typeMap->setType(e, t);
}

void MultiAssignment::recurseExprs(
    const IR::Expression *le, const IR::Expression *re,
    std::vector<const IR::AssignmentStatement *> &vec) {
  auto ltype = typeMap->getType(le);
  if (ltype->is<IR::Type_StructLike>()) {
    auto sl = ltype->to<IR::Type_StructLike>();
    for (auto sf : sl->fields) {
      auto m = new IR::Member(le, sf->name);
      fixExpression(m, typeMap->getType(sf), true);
      const IR::Expression *mr = new IR::Member(re, sf->name);
      if (auto sie = re->to<IR::StructInitializerExpression>()) {
        mr = sie->components.getDeclaration<IR::NamedExpression>(sf->name)
                 ->expression;
      } else {
        fixExpression(mr, typeMap->getType(sf), false);
      }
      recurseExprs(m, mr, vec);
    }
  } else if (ltype->is<IR::Type_Stack>()) {
    auto st = ltype->to<IR::Type_Stack>();
    auto elemt = typeMap->getTypeType(st->elementType, true);
    for (size_t idx = 0; idx != st->getSize(); ++idx) {
      auto infi = new IR::Constant(new IR::Type_InfInt(), idx);
      // dirty hack
      typeMap->setType(infi, new IR::Type_InfInt());
      auto m = new IR::ArrayIndex(le, infi);
      fixExpression(m, elemt, true);
      auto mr = new IR::ArrayIndex(re, infi);
      fixExpression(mr, elemt, false);
      recurseExprs(m, mr, vec);
    }
  } else {
    vec.push_back(new IR::AssignmentStatement(le, re));
  }
}

void MultiAssignment::compute(
    const IR::Node *l, const IR::Node *r,
    std::vector<const IR::AssignmentStatement *> &vec) {
  recurseExprs(exp(l, true), exp(r, false), vec);
}

const std::vector<const IR::AssignmentStatement *> *MultiAssignment::
operator()(const IR::Node *l, const IR::Node *r) {
  auto EMI = cache.emplace(std::make_pair(l, r),
                           std::vector<const IR::AssignmentStatement *>());
  if (EMI.second) {
    compute(l, r, EMI.first->second);
  }
  return &EMI.first->second;
}

MultiAssignment::MultiAssignment(ReferenceMap *refMap, TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap), tc(refMap, typeMap, true) {}

CFG push_ifs(const CFG &main, P4::ReferenceMap *refMap, P4::TypeMap *typeMap) {
  auto cpy = main;
  SelectToExpression selectToExpression(refMap, typeMap);
  EdgeHolder extra;
  std::unordered_map<node_t, const IR::Node *> repl;
  for (auto &np : cpy.holder) {
    if (np.first.node->is<IR::IfStatement>()) {
      repl.emplace(np.first, new IR::EmptyStatement());
      auto iff = np.first.node->to<IR::IfStatement>();
      auto nif = iff->clone();
      nif->condition = new IR::LNot(iff->condition);
      node_t iffnode(iff);
      iffnode = iffnode.clone(++node_t::LABEL);
      node_t nifnode(nif);
      nifnode = nifnode.clone(++node_t::LABEL);
      typeMap->setType(nif->condition, IR::Type_Boolean::get());
      for (auto &ed : np.second) {
        if (ed.second) {
          extra[iffnode].emplace_back(ed.first, 1);
          ed.first = iffnode;
        } else {
          extra[nifnode].emplace_back(ed.first, 1);
          ed.first = nifnode;
        }
      }
    } else if (np.first.node->is<IR::SelectExpression>()) {
      repl.emplace(np.first, new IR::EmptyStatement());
      auto selex = np.first.node->to<IR::SelectExpression>();
      for (auto &ed : np.second) {
        auto iff = new IR::IfStatement(selectToExpression(selex, ed.second),
                                       new IR::EmptyStatement(), nullptr);
        node_t iffnode(iff);
        iffnode = iffnode.clone(++node_t::LABEL);
        extra[iffnode].emplace_back(ed.first, 1);
        ed.first = iffnode;
      }
    }
  }
  auto ifreplace = [&](const node_t &n) -> node_t {
    if (n.node->is<IR::IfStatement>() || n.node->is<IR::SelectExpression>()) {
      auto I = repl.find(n);
      if (I != repl.end())
        return I->second;
    }
    return n;
  };
  for (auto &ext : extra) {
    auto &hld = cpy.holder[ext.first];
    hld = std::move(ext.second);
  }
  cpy.holder = analysis::gmap(std::move(cpy.holder), ifreplace).first;
  cpy.start_node = ifreplace(cpy.start_node);
  return cpy;
}

void make_ssa(EdgeHolder &basicBlocks, EdgeHolder &rBasicBlocks,
              node_t basicBlockStart, P4::ReferenceMap *refMap,
              P4::TypeMap *typeMap, NodeToFunctionMap *funMap,
              bool livevaropt) {
  EdgeHolder domf;
  NodeValues<std::vector<node_t>> children;
  dom_frontier(basicBlocks, rBasicBlocks, basicBlockStart, children, domf);
  LiveVariables liveVariables(refMap, typeMap, &basicBlocks, basicBlockStart,
                              funMap);
  PathGetter pathGetter(refMap, typeMap);
  auto &indices = *liveVariables.indices;
  std::vector<std::unordered_set<node_t>> defsites(indices.size());
  NodeValues<bvset<MemPath>> A_orig;
  NodeValues<bvset<MemPath>> A_phi;
  auto &rs = liveVariables.rs;
  auto &ws = liveVariables.ws;
  traverse_df_pernode(&basicBlocks, basicBlockStart, [&](const node_t &n) {
    auto &crt = A_orig.emplace(n, &indices).first->second;
    for (auto inst : instructions(n)) {
      auto &writes = ws[inst];
      for (auto &mp : writes) {
        auto ii = indices[mp];
        crt.arr.set(ii);
        defsites[ii].emplace(n);
      }
    }
  });
  auto is = [](const std::unordered_map<node_t, bvset<MemPath>> &A,
               const node_t &n, size_t idx) {
    auto I = A.find(n);
    if (I != A.end()) {
      return I->second.arr[idx];
    }
    return false;
  };
  auto addPhi = [&](std::unordered_map<node_t, bvset<MemPath>> &A,
                    const node_t &Y, size_t idx) -> void {
    getOrEmplace(A, Y, [&]() {
      return analysis::bvset<MemPath>(&indices);
    }).first.arr.set(idx);
  };
  // place PHI functions:
  for (auto &a : indices) {
    // let a a variable
    auto W = defsites[a.second];
    while (!W.empty()) {
      auto n = *W.begin();
      W.erase(W.begin());
      for (const auto &Yy : domf[n]) {
        auto Y = Yy.first;
        if (!is(A_phi, Y, a.second)) {
          if (!livevaropt || liveVariables.live(Y, a.first)) {
            // A_phi[Y].contains(a) -> BB Y was not added a definition for var
            // a
            addPhi(A_phi, Y, a.second);
            if (!is(A_orig, Y, a.second)) {
              // adding phi triggers processing for BB Y iff Y is not among
              // the
              // definers of a
              W.emplace(Y);
            }
          } else {
            LOG4("pruning phi function for " << a.first);
          }
        }
      }
    }
  }

  // A_phi maps node -> all required phis
  // do renaming
  std::vector<unsigned> counts(indices.size(), 0);
  std::vector<std::vector<unsigned>> varStack(indices.size(), {0});
  std::function<void(const node_t &)> rename;

  struct std_replacement {
    node_t at;
    boost::variant<const IR::Node *, FullEdge_t> instr;
    MemPath mp;
    unsigned version;

    std_replacement(const node_t &at, const FullEdge_t &ed, MemPath mp,
                    unsigned int version)
        : at(at), instr(ed), mp(std::move(mp)), version(version) {}
  };
  std::vector<std_replacement> phiReplacements;
  NodeValues<std::unordered_map<MemPath, unsigned>> phiGenerated;
  rename = [&](const node_t &n) {
    std::vector<unsigned> num_push(indices.size());
    auto MYPhis = A_phi.find(n);
    auto &phin = phiGenerated[n];
    if (MYPhis != A_phi.end()) {
      // if this basic block begins with phi functions:
      // for each phi(V) => treat as a regular write to V (we are not
      // modifying
      // the CFG in previous step)
      for (auto &idx : indices) {
        // mimic for each phi(n)
        if (MYPhis->second.arr[idx.second]) {
          auto forid = ++counts[idx.second];
          varStack[idx.second].push_back(forid);
          num_push[idx.second]++;
          // no need to do anything (?), just raise versions
          phin[idx.first] = forid;
        }
      }
    }
    auto instrs = n.node->to<IR::Vector<IR::Node>>();
    CHECK_NULL(instrs);
    auto mut = const_cast<IR::Vector<IR::Node> *>(instrs);
    IR::Vector<IR::Node> temp;
    for (auto instr : instructions(n)) {
      if (instr->is<IR::IDeclaration>() || instr->is<IR::EmptyStatement>()) {
        continue;
      }
      auto &paths = rs[instr];
      std::unordered_map<MemPath, const IR::Expression *> rreplacements;
      std::unordered_map<MemPath, const IR::Expression *> wreplacements;
      for (auto &lv : paths) {
        auto id = indices[lv];
        auto &forid = varStack[id];
        auto i = forid.back();
        // register read replacement here: (n, instr, id, i)
        rreplacements.emplace(
            lv, IR::fixType(new IR::VersionedExpression(pathGetter(lv), i),
                            typeMap));
      }
      auto &wpaths = ws[instr];
      for (auto &lv : wpaths) {
        auto id = indices[lv];
        auto forid = ++counts[id];
        varStack[id].push_back(forid);
        // register write replacement here: (n, instr, id, forid)
        wreplacements.emplace(
            lv, IR::fixType(new IR::VersionedExpression(pathGetter(lv), forid),
                            typeMap));
        num_push[id]++;
      }
      if (!wreplacements.empty() || !rreplacements.empty()) {
        ReplaceAll replaceAll(refMap, typeMap, std::move(rreplacements),
                              std::move(wreplacements));
        auto newi = replaceAll(instr);
        temp.push_back(newi);
      } else {
        temp.push_back(instr);
      }
    }
    *mut = std::move(temp);
    for (auto &succ : basicBlocks[n]) {
      auto IPhis = A_phi.find(succ.first);
      if (IPhis != A_phi.end()) {
        for (auto &idx : indices) {
          // mimic for each phi(a)
          if (IPhis->second.arr[idx.second]) {
            auto &topV = varStack[idx.second];
            auto inVersion = topV.back();
            // register phi replacement: (succ, FullEdge_t(n, succ), idx,
            // inVersion)
            phiReplacements.emplace_back(succ.first, FullEdge_t(n, succ),
                                         idx.first, inVersion);
          }
        }
      }
    }
    for (auto &succ : children[n]) {
      rename(succ);
    }

    for (size_t i = 0, e = num_push.size(); i != e; ++i) {
      if (num_push[i]) {
        for (unsigned j = 0; j != num_push[i]; ++j)
          varStack[i].pop_back();
      }
    }
  };
  rename(basicBlockStart);
  std::vector<std::vector<IR::Declaration *>> newdecls(indices.size());
  size_t all = 0;
  for (auto &lvid : indices) {
    auto cnt = counts[lvid.second];
    if (cnt > 0)
      newdecls[lvid.second].resize(cnt);
    all += cnt;
  }
  LOG4("renamed vars: " << all << " vs " << indices.size());

  // push phi functions up
  for (auto &phirep : phiReplacements) {
    auto instr = boost::get<analysis::FullEdge_t>(phirep.instr);
    auto srcnode = instr.source;
    auto bbnodes = srcnode.node->to<IR::Vector<IR::Node>>();
    CHECK_NULL(bbnodes);
    auto mut = const_cast<IR::Vector<IR::Node> *>(bbnodes);
    auto exp = pathGetter(phirep.mp);
    auto vread =
        IR::fixType(new IR::VersionedExpression(exp, phirep.version), typeMap);
    auto phig = phiGenerated[instr.dst][phirep.mp];
    auto vwritten =
        IR::fixType(new IR::VersionedExpression(exp, phig), typeMap);
    auto asg = new IR::AssignmentStatement(vwritten, vread);
    mut->push_back(asg);
    if (vread->version >= vwritten->version) {
      LOG4("anomaly: " << asg);
    }
    LOG5("pushing up " << asg);
  }
}

void domtree_simplifications(EdgeHolder &basicBlocks, node_t &basicBlockStart,
                             P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                             NodeToFunctionMap *funMap) {
  auto sorted = analysis::topo_sort(&basicBlocks, basicBlockStart);
  ReadSet readSet(refMap, typeMap, funMap);
  WriteSet writeSet(refMap, typeMap, funMap);
  START(domtree);
  size_t totalchop = 0;
  size_t chopped = 0;
  do {
    std::unordered_map<const IR::Node *, const IR::Node *> already_computed;
    chopped = 0;
    auto defs = ReachingDefinitions::reachingDefinitions(
        refMap, typeMap, basicBlocks, basicBlockStart, funMap);
    auto &idx = defs.begin()->second;
    easy_index easyIndex(idx.idx);
    size_t nrreps = 0;
    for (auto I = sorted.rbegin(); I != sorted.rend(); ++I) {
      auto &bb = *I;
      auto Iin = defs.find(bb);
      if (Iin != defs.end()) {
        auto &in = Iin->second;
        auto it = easyIndex.with(&in);
        for (auto &instr : instructions(bb)) {
          auto &rs = readSet[instr];
          std::unordered_map<MemPath, const IR::Expression *> replace;
          for (const auto &rd : rs) {
            auto cnt = it.count(rd);
            if (cnt == 1) {
              auto that = it.of(rd)[0];
              if (auto asg = is_assign(that)) {
                auto with = asg->rv;
                auto IT = already_computed.find(asg->rv);
                if (IT != already_computed.end()) {
                  with = IT->second->to<IR::Expression>();
                }
                LOG4("replacing: " << rd << " with " << with);
                replace[rd] = with;
              }
            } else if (cnt > 1) {
              // pulling cheap constant propagation
              auto writes = it.of(rd);
              auto first = writes[0];
              if (auto asg = first->to<IR::AssignmentStatement>()) {
                auto rv0 = ScalarValue::fromExpression(asg->right, typeMap);
                if (rv0.state == ScalarState::CONSTANT) {
                  unsigned i;
                  for (i = 1; i != cnt; ++i) {
                    if (auto asgi = writes[i]->to<IR::AssignmentStatement>()) {
                      auto rvi =
                          ScalarValue::fromExpression(asgi->right, typeMap);
                      if (rvi.state == ScalarState::CONSTANT) {
                        if (rv0 == rvi) {
                          continue;
                        }
                      }
                    }
                    break;
                  }
                  if (i == cnt) {
                    // common constant found
                    replace[rd] = rv0.value;
                    LOG4("replacing: " << rd << " with " << rv0);
                  }
                }
              }
            }
          }
          if (!replace.empty()) {
            Replace rep(refMap, typeMap, std::move(replace));
            auto old = instr;
            const_cast<const IR::Node *&>(instr) = rep(instr);
            if (old != instr) {
              LOG4("replaced: " << actual_node(old) << " with "
                                << actual_node(instr));
              ++nrreps;
            }
            if (old->is<IR::AssignmentStatement>()) {
              auto orv = old->to<IR::AssignmentStatement>()->right;
              auto nrv = instr->to<IR::AssignmentStatement>()->right;
              if (orv != nrv) {
                already_computed[orv] = nrv;
              }
            }
          }
        }
      }
    }
    do {
      std::unordered_map<MemPath, std::unordered_set<const IR::Node *>> read;
      std::unordered_set<const IR::Node *> removed;
      for (auto I = sorted.rbegin(); I != sorted.rend(); ++I) {
        for (auto instr : instructions(*I)) {
          auto &rs = readSet[instr];
          for (const auto &mp : rs) {
            read[mp].emplace(instr);
          }
        }
      }
      chopped = 0;
      size_t allinstrs = 0;
      for (auto &x : sorted) {
        auto vec = const_cast<IR::Vector<IR::Node> *>(
            x.node->to<IR::Vector<IR::Node>>());
        auto nrinstrs = vec->size();
        for (long i = nrinstrs - 1; i >= 0; --i) {
          auto instr = (*vec)[i];
          if (!instr->is<IR::EmptyStatement>()) {
            ++allinstrs;
          }
          auto &ws = writeSet[instr];
          if (!ws.empty() &&
              std::all_of(ws.begin(), ws.end(), [&](const MemPath &mp) {
                auto &v = read[mp];
                return v.empty() ||
                       std::all_of(v.begin(), v.end(), [&](const IR::Node *nd) {
                         return removed.count(nd) != 0;
                       });
              })) {
            LOG4("removing " << instr);
            LOG4("removing " << (*vec)[i]);
            removed.emplace(instr);
            (*vec)[i] = new IR::EmptyStatement;
            ++chopped;
          }
        }
      }
      totalchop += chopped;
      std::cerr << "dom tree simplifications for " << nrreps << "," << chopped
                << "/" << allinstrs << "\n";
    } while (chopped);
  } while (chopped != 0);
  END(domtree);
  std::cerr << "dom tree simplifications for " << totalchop << "/"
            << basicBlocks.size() << ' ' << DURATION(domtree) << "ms\n";
}

void intra_basic_block_simplifications(EdgeHolder &basicBlocks,
                                       node_t &basicBlockStart,
                                       P4::ReferenceMap *refMap,
                                       P4::TypeMap *typeMap,
                                       NodeToFunctionMap *funMap) {
  auto sorted = analysis::topo_sort(&basicBlocks, basicBlockStart);
  ReadSet readSet(refMap, typeMap, funMap);
  WriteSet writeSet(refMap, typeMap, funMap);
  // intra basic block optimizations
  START(intrabb);
  NodeValues<std::unordered_map<MemPath, const IR::Expression *>> outgoing;
  for (const auto &st : sorted) {
    auto &last_write = outgoing[st];
    for (auto I = instructions(st).begin(); I != instructions(st).end(); ++I) {
      auto instr = *I;
      auto &ws = writeSet[instr];
      if (!last_write.empty()) {
        Replace repl(refMap, typeMap, last_write);
        *const_cast<const IR::Node **>(I) = repl(instr);
        instr = *I;
      }
      if (!ws.empty()) {
        if (!is_extern_method_call(instr)) {
          // propagate written stuff if not method call
          auto asg = is_assign(instr);
          BUG_CHECK(asg.is_initialized(),
                    "%1% is writing but is no function nor assign", instr);
          for (const auto &mp : ws) {
            last_write[mp] = asg->rv;
          }
        } else {
          // erase written stuff
          for (const auto &mp : ws) {
            last_write.erase(mp);
          }
        }
      }
    }
  }
  END(intrabb);
  std::cerr << "intra-basic block simplifications " << DURATION(intrabb)
            << "ms\n";
}

void simplify_ifs(EdgeHolder &graph, const node_t &start,
                  P4::ReferenceMap *refMap, P4::TypeMap *typeMap) {
  size_t simplified = 0;
  size_t removed = 0;
  traverse_df_pernode(&graph, start, [&](const node_t &s) {
    unsigned idx = 0;
    auto mut = mutate(s);
    for (const auto &instr : instructions(s)) {
      if (instr->is<IR::IfStatement>()) {
        PassRepeated passManager(
            {new P4::DoConstantFolding(refMap, typeMap),
             new P4::TypeInference(refMap, typeMap, false)});
        auto ifs = instr->to<IR::IfStatement>();
        auto cd = ifs->condition->apply(passManager);
        if (cd != ifs->condition) {
          auto cl = ifs->clone();
          cl->condition = cd;
          simplified++;
          mut->at(idx) = cl;
        }
      }
      ++idx;
    }
  });
  traverse_df_pernode(&graph, start, [&](const node_t &s) {
    unsigned idx = 0;
    auto mut = mutate(s);
    for (auto instr : instructions(s)) {
      bool canremove = false;
      if (auto ifs = instr->to<IR::IfStatement>()) {
        if (ifs->condition->is<IR::BoolLiteral>() &&
            ifs->condition->to<IR::BoolLiteral>()->value) {
          canremove = true;
        }
      } else if (instr->is<IR::EmptyStatement>()) {
        canremove = true;
      }
      if (!canremove) {
        mut->at(idx) = instr;
        ++idx;
      } else {
        removed++;
      }
    }
    mut->resize(idx);
  });
  std::cerr << "simplified " << simplified << ',' << removed
            << " if conditions\n";
  removeDeadNodes(&graph, start, [&](const node_t &nd) {
    return std::any_of(
        instructions(nd).begin(), instructions(nd).end(),
        [&](const IR::Node *nd) {
          if (auto ifs = nd->to<IR::IfStatement>()) {
            if (ifs->condition->is<IR::BoolLiteral>()) {
              return !ifs->condition->to<IR::BoolLiteral>()->value;
            }
          }
          return false;
        });
  });
}

void ifs_to_dnf(EdgeHolder &graph, const node_t &start,
                P4::ReferenceMap *refMap, P4::TypeMap *typeMap) {
  traverse_df_pernode(&graph, start, [&](const node_t &s) {
    unsigned idx = 0;
    auto mut = mutate(s);
    for (const auto &instr : instructions(s)) {
      mut->at(idx) = if_to_dnf(instr, refMap, typeMap);
      ++idx;
    }
    mut->resize(idx);
  });
}

node_t make_artificial_end(EdgeHolder &graph, EdgeHolder &rgraph,
                           node_t start) {
  NodeSet ends;
  traverse_df_pernode(&graph, start, [&](const node_t &nd) {
    if (auto neighs = neighbors_or_null(graph, nd)) {
      if (neighs->empty())
        ends.emplace(nd);
    } else {
      ends.emplace(nd);
    }
  });
  auto artificial = new IR::EmptyStatement();
  for (const auto &e : ends) {
    graph[e].emplace_back(artificial, 0);
    rgraph[artificial].emplace_back(e, 0);
  }
  return artificial;
}

NodeValues<node_t> get_parents(const NodeValues<NodeVector> &domtree) {
  NodeValues<node_t> parents;
  for (const auto &x : domtree) {
    for (const auto &y : x.second) {
      parents[y] = x.first;
    }
  }
  return parents;
}

bool dominates(const NodeValues<node_t> &parents, const node_t &by,
               const node_t &x) {
  if (x == by)
    return true;
  auto Iparent = parents.find(x);
  while (Iparent != parents.end()) {
    if (Iparent->second == by)
      return true;
    Iparent = parents.find(Iparent->second);
  }
  return false;
}

domtree_iterable dominators_for(NodeValues<node_t> &parent, node_t nd) {
  return {parent, nd};
}

NodeSet dominees_of(const NodeValues<NodeVector> &domtree, node_t nd) {
  NodeSet visited;
  std::vector<node_t> q({nd});
  while (!q.empty()) {
    auto l = q.back();
    q.pop_back();
    auto I = domtree.find(l);
    if (I != domtree.end()) {
      std::copy(I->second.begin(), I->second.end(),
                std::inserter(visited, visited.end()));
      std::copy(I->second.begin(), I->second.end(), std::back_inserter(q));
    }
  }
  return visited;
}

void pdom_frontier(const EdgeHolder &graph, const EdgeHolder &rgraph,
                   const node_t &start,
                   std::unordered_map<node_t, std::vector<node_t>> &children,
                   EdgeHolder &domf) {
  WithArtificialEnd wae(const_cast<EdgeHolder &>(graph),
                        const_cast<EdgeHolder &>(rgraph), start);
  dom_frontier(rgraph, graph, wae.getEnd(), children, domf);
}

const IR::Node *if_to_dnf(const IR::Node *instr, P4::ReferenceMap *refMap,
                          P4::TypeMap *typeMap) {
  if (instr->is<IR::IfStatement>()) {
    PassManager passManager({new Cuber(refMap, typeMap),
                             new P4::TypeInference(refMap, typeMap, false)});
    auto ifs = instr->to<IR::IfStatement>();
    auto cd = ifs->condition->apply(passManager);
    if (cd != ifs->condition) {
      auto cl = ifs->clone();
      cl->condition = cd;
      return cl;
    }
  }
  return instr;
}

const IR::Expression *negate(const IR::Expression *e) {
  if (auto neg = e->to<IR::LNot>()) {
    return neg->expr;
  } else if (auto land = e->to<IR::LAnd>()) {
    return new IR::LOr(negate(land->left), negate(land->right));
  } else if (auto lor = e->to<IR::LOr>()) {
    return new IR::LAnd(negate(lor->left), negate(lor->right));
  } else if (auto blit = e->to<IR::BoolLiteral>()) {
    return new IR::BoolLiteral(!blit->value);
  } else if (auto neq = e->to<IR::Neq>()) {
    return new IR::Equ(neq->left, neq->right);
  } else {
    return new IR::LNot(e);
  }
}

class RmNeq : public Transform {
  const IR::Node *postorder(IR::Neq *n) override {
    return new IR::LNot(new IR::Equ(n->left, n->right));
  }
};

class ToNNF : public Transform {
  const IR::Node *preorder(IR::LNot *lnot) override {
    prune();
    auto e = negate(lnot->expr);
    if (auto newl = e->to<IR::LNot>()) {
      if (newl->expr == lnot->expr)
        return lnot;
    }
    return e;
  }
};

class DoDNF : public Transform {
  const IR::Node *postorder(IR::LAnd *land) override {
    if (!land->left->is<IR::LOr>() && !land->right->is<IR::LOr>()) {
      return land;
    }
    auto left = land->left;
    auto right = land->right;
    if (!left->is<IR::LOr>() && right->is<IR::LOr>()) {
      std::swap(left, right);
    }
    auto lor = left->to<IR::LOr>();
    auto c = lor->left;
    auto d = lor->right;
    return new IR::LOr(new IR::LAnd(right, c), new IR::LAnd(right, d));
  }
};
const IR::Node *if_to_nnf(const IR::Node *instr, P4::ReferenceMap *refMap,
                          P4::TypeMap *typeMap) {
  if (instr->is<IR::IfStatement>()) {
    PassManager passManager(
        {new RmNeq, new ToNNF, new P4::TypeInference(refMap, typeMap, false)});
    auto ifs = instr->to<IR::IfStatement>();
    auto cd = ifs->condition->apply(passManager);
    if (cd != ifs->condition) {
      auto cl = ifs->clone();
      cl->condition = cd;
      return cl;
    }
  }
  return instr;
}

void ifs_to_nnf(EdgeHolder &graph, const node_t &start,
                P4::ReferenceMap *refMap, P4::TypeMap *typeMap) {
  traverse_df_pernode(&graph, start, [&](const node_t &s) {
    unsigned idx = 0;
    auto mut = mutate(s);
    for (const auto &instr : instructions(s)) {
      mut->at(idx) = if_to_nnf(instr, refMap, typeMap);
      ++idx;
    }
    mut->resize(idx);
  });
}

std::set<const IR::Expression *>
get_atoms(const IR::Expression *exp, P4::ReferenceMap *, P4::TypeMap *typeMap) {
  struct GetAtoms : public Inspector {
    std::set<const IR::Expression *> atoms;
    bool preorder(const IR::Expression *e) {
      atoms.emplace(e);
      return false;
    }
    bool preorder(const IR::LAnd *) override { return true; }
    bool preorder(const IR::LOr *) override { return true; }
    bool preorder(const IR::LNot *) override { return true; }
    bool preorder(const IR::Neq *neq) override {
      BUG("%1% must have been eliminated by nnf", neq);
    }
  };
  BUG_CHECK(typeMap->getType(exp)->is<IR::Type_Boolean>(),
            "expecting bool expression, got %1%", exp);
  GetAtoms getAtoms;
  exp->apply(getAtoms);
  return std::move(getAtoms.atoms);
}

Cuber::Cuber(ReferenceMap *refMap, TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap) {
  passes.push_back(new PassRepeated(
      {new ToNNF, new P4::TypeInference(refMap, typeMap, false)}));
  passes.push_back(new PassRepeated({new DoDNF}));
}

void cubes::recurse(const IR::Expression *e) {
  const IR::Expression *left = nullptr;
  const IR::Expression *right = nullptr;
  if (lor) {
    if (auto _lor = e->to<IR::LOr>()) {
      left = _lor->left;
      right = _lor->right;
    }
  } else {
    if (auto _land = e->to<IR::LAnd>()) {
      left = _land->left;
      right = _land->right;
    }
  }
  if (!left) {
    _cubes.emplace_back(e);
  } else {
    recurse(left);
    recurse(right);
  }
}

domtree_iterable::domtree_iterable(NodeValues<analysis::node_t> &parent,
                                   node_t of)
    : parent(parent), of(of) {}

domtree_iterator &domtree_iterator::operator++() {
  if (Iparent == parent.end())
    return *this;
  auto Ipp = parent.find(Iparent->second);
  this->Iparent = Ipp;
  return *this;
}

WithArtificialEnd::WithArtificialEnd(EdgeHolder &graph, EdgeHolder &rgraph,
                                     const node_t &start)
    : graph(graph), rgraph(rgraph) {
  artiend = make_artificial_end(graph, rgraph, start);
}

WithArtificialEnd::~WithArtificialEnd() {
  auto I = rgraph.find(artiend);
  if (I != rgraph.end()) {
    for (const auto &x : I->second) {
      auto &gx = graph[x.first];
      auto It = remove_if(gx, [&](const std::pair<node_t, int> &y) {
        return y.first == artiend;
      });
      if (It == gx.begin())
        graph.erase(x.first);
      else
        gx.resize(static_cast<unsigned long>(It - gx.begin()));
    }
  }
  rgraph.erase(I);
}

const node_t &WithArtificialEnd::getEnd() const { return artiend; }
}