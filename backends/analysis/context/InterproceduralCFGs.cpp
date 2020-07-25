//
// Created by dragos on 29.07.2019.
//

#include "InterproceduralCFGs.h"
#include <analysis/constprop/ConstantPropagation.h>
#include <analysis/ub/loop.h>
#include <fstream>

analysis::CFG *analysis::BuildIPCFG::build(CFG *current) {
  START(graph_buildup);
  doBuild(current);
  END(graph_buildup);

  auto main = new CFG(nullptr);
  std::unordered_set<const IR::Node *> added;
  std::vector<const IR::Node *> from({current->maps_to});
  START(linking);
  if (!lazy_link) {
    std::function<void(const IR::Node *)> materialize_gotos;
    materialize_gotos = [&](const IR::Node *now) {
      if (added.emplace(now).second) {
        auto cfg = cfgs->get(now, true);
        CHECK_NULL(cfg);
        auto &goes_to = remaining_gotos[now];
        for (auto &x : goes_to)
          materialize_gotos(std::get<2>(x.second)->maps_to);
        link_gotos(cfg, remaining_gotos[now]);
      }
    };
    materialize_gotos(current->maps_to);
    added.clear();
    while (!from.empty()) {
      auto now = from.back();
      from.pop_back();
      if (added.emplace(now).second) {
        auto cfg = cfgs->get(now, true);
        CHECK_NULL(cfg);
        if (!main->holder.empty())
          std::copy(std::make_move_iterator(cfg->holder.begin()),
                    std::make_move_iterator(cfg->holder.end()),
                    std::inserter(main->holder, main->holder.begin()));
        else
          main->holder = std::move(cfg->holder);
        auto &goes_to = gotos[now];
        for (auto x : goes_to)
          from.push_back(x);
      }
    }
  }
  END(linking);
  main->start_node = current->start_node;

  std::function<const IR::Node *(const node_t &)> setMethod;
  setMethod = [&](const node_t &nd) -> const IR::Node * {
    auto It = node_to_method.find(nd);
    if (It != node_to_method.end())
      return It->second;
    auto Iparent = parents.find(nd);
    if (Iparent == parents.end()) {
      BUG("reached root node %1% but no method set", nd);
    }
    return (node_to_method[nd] = setMethod(Iparent->second));
  };

  //  DefaultDiscipline defaultDiscipline(main, current->start_node);
  //  {
  //    SimplifyGraph simplifyGraph(refMap, typeMap, funMap, true);
  //    auto sorted = topo_sort(&main->holder, main->start_node);
  //    simplifyGraph(main->holder, main->start_node, sorted);
  //  }
  auto d = DURATION(graph_buildup);
  std::cerr << "done graph buildup  " << main->holder.size() << " in " << d
            << "ms, linking in " << DURATION(linking) << "ms\n";
  if (LOGGING(5)) {
    std::ofstream os("post_buildup.dot");
    main->toDot(os);
  }
  (void)ConstantPropagation::propagate_and_simplify(refMap, typeMap, *main,
                                                    funMap, &parents);
  unroll(&main->holder, main->start_node, funMap, 0, true, &parents);
  // FIXME: clean way to re-do reference mapping due to
  // hanging method calls such as bug, oob resulting from unroll
  fixGraph(main);
  for (const auto &cp : parents) {
    setMethod(cp.first);
  }
  return main;
}

void analysis::BuildIPCFG::fixGraph(const analysis::CFG *main) {
  P4::TypeInference tc(this->refMap, this->typeMap, true);
  traverse_df_pernode(
      &main->holder, main->start_node, [&](const analysis::node_t &n) {
        if (auto mcs = is_extern_method_call(n)) {
          auto mt = this->typeMap->getType(mcs->methodCallStatement);
          if (!mt) {
            auto pe = mcs->methodCallStatement->methodCall->method
                          ->to<IR::PathExpression>();
            if (pe) {
              auto bg =
                  this->program->getDeclsByName(pe->path->name)
                      ->where([&](const IR::IDeclaration *d) {
                        return d->to<IR::IFunctional>()->callMatches(
                            mcs->methodCallStatement->methodCall->arguments);
                      });
              auto nd = *bg->begin();
              this->refMap->setDeclaration(
                  mcs->methodCallStatement->methodCall->method
                      ->to<IR::PathExpression>()
                      ->path,
                  nd);
              (void)mcs->methodCallStatement->apply(tc);
            }
          }
        }
      });
}

analysis::BuildIPCFG::BuildIPCFG(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                                 const IR::P4Program *program,
                                 analysis::ContextFactory *contextFactory,
                                 analysis::CFGs *cfgs,
                                 analysis::NodeToFunctionMap *funMap, bool lazy)
    : refMap(refMap), typeMap(typeMap), program(program),
      contextFactory(contextFactory), cfgs(cfgs), funMap(funMap),
      lazy_link(lazy) {}

void analysis::BuildIPCFG::doBuild(CFG *current) {
  NodeValues<std::tuple<node_t, node_t, CFG *>> caller_to_fun;
  CHECK_NULL(current->maps_to);
  labelCFG(current, current->maps_to);
  IdentifyMethodCalls identifyMethodCalls(refMap, typeMap);
  traverse_df_pernode(
      &current->holder, current->start_node,
      [&identifyMethodCalls, current, this, &caller_to_fun](node_t cfgNode) {
        bool found = false;
        auto methods = identifyMethodCalls.getMethods(actual_node(cfgNode));
        for (auto met : methods) {
          if (met->is<P4::BuiltInMethod>()) {
            // will not consider built-ins al elligibile for CFG
            // construction, just ignore them
            continue;
          }
          auto fullContext = contextFactory->makeContext(met);
          auto ctx = fullContext->instantiated;
          CHECK_NULL(ctx);
          CFG *callee = nullptr;
          bool has_no_return = false;
          if (ctx->is<IR::Method>()) {
            // TODO: find a more generic strategy for implementations if need
            // be
            has_no_return =
                ctx->to<IR::Method>()->getAnnotation("noreturn") != nullptr;
            if (auto f = ITracker::getImplementation(program,
                                                     ctx->to<IR::Method>())) {
              ImplementationFactory implementationFactory(contextFactory);
              fullContext =
                  implementationFactory.implement(f, fullContext, true);
              ctx = fullContext->instantiated;
            }
          }
          if (!cfgs->built(ctx)) {
            callee = cfgs->get(ctx, true);
            if (callee) {
              doBuild(callee);
            }
          } else {
            callee = cfgs->get(ctx, true);
          }
          if (callee) {
            if (ctx->is<IR::P4Parser>()) {
              LOG3(dbp(ctx)
                   << " starts at " << actual_node(callee->start_node));
              auto maxstack = ComputeMaxStackSize::maxStackSize(
                  ctx->to<IR::P4Parser>(), typeMap);
              if (LOGGING(6)) {
                auto filename = refMap->newName("preunroll") + ".dot";
                std::ofstream noret(filename);
                LOG3("@" << dbp(current->maps_to) << "/" << cfgNode
                         << ((!has_no_return) ? (" calls ") : (" goes to "))
                         << dbp(callee->maps_to) << ": " << filename);
                callee->toDot(noret);
              }
              analysis::unroll(&callee->holder, callee->start_node, funMap,
                               maxstack + 1, false, &parents);
              fixGraph(callee);
              auto EE =
                  analysis::findEndNodes(&callee->holder, callee->start_node);
              std::unordered_set<node_t> X;
              std::copy_if(EE.begin(), EE.end(), std::inserter(X, X.begin()),
                           [](node_t n) {
                             if (auto mcs =
                                     analysis::is_extern_method_call(n)) {
                               return !is_terminal(mcs->methodCallStatement);
                             }
                             return true;
                           });
              BUG_CHECK(X.size() == 1, "multi exit node from parser %1%", ctx);
              callee->end_node = *X.begin();
            }
            if (!has_no_return) {
              BUG_CHECK(callee->holder.empty() ||
                            callee->end_node.type == NodeType::END,
                        "end node must be of type END");
            }
            if (LOGGING(5)) {
              auto filename = refMap->newName("noret") + ".dot";
              std::ofstream noret(filename);
              LOG3("@" << dbp(current->maps_to) << "/" << cfgNode
                       << ((!has_no_return) ? (" calls ") : (" goes to "))
                       << dbp(callee->maps_to) << ": " << filename);
              callee->toDot(noret);
            }
            BUG_CHECK(callee->holder.empty() ||
                          callee->start_node.type == NodeType::START,
                      "start node must be of type START");
            auto crt = funMap->callee(cfgNode);
            BUG_CHECK(!found, "two calls in the same CFG node %1%, can't do it",
                      actual_node(cfgNode));
            BUG_CHECK(crt == nullptr || crt == callee->maps_to,
                      "mapping the same cfg node to two different methods %1%",
                      cfgNode);
            if (funMap->put({cfgNode, NodeType::CALL}, callee->maps_to, met)) {
              funMap->put({cfgNode, NodeType::RETURN}, callee->maps_to, met);
              LOG4("@" << dbp(current->maps_to) << " candidate " << cfgNode
                       << " " << callee->start_node);
              auto &c = (caller_to_fun[cfgNode] =
                             std::make_tuple(node_t(callee->start_node),
                                             node_t(callee->end_node), callee));
              if (has_no_return) {
                std::get<1>(c) = node_t::before();
              }
              found = true;
            }
          } else {
            if (auto ef = met->to<P4::ExternFunction>()) {
              funMap->put(cfgNode, ef->method, met);
            } else if (auto em = met->to<P4::ExternMethod>()) {
              funMap->put(cfgNode, em->method, met);
            }
          }
        }
      });
  if (!lazy_link)
    linkCFG(current, caller_to_fun);
  removeDeadNodes(&current->holder, current->start_node);
  if (LOGGING(5)) {
    auto filename = refMap->newName("inlined") + ".dot";
    std::ofstream noret(filename);
    LOG3("inlined @" << dbp(current->maps_to) << ": " << filename);
    current->toDot(noret);
  }
  auto &rems = remaining_gotos[current->maps_to];
  for (auto &c2f : caller_to_fun) {
    auto calleeend = std::get<1>(c2f.second);
    if (calleeend == node_t::before()) {
      rems[c2f.first] = c2f.second;
    }
  }
}

void analysis::BuildIPCFG::linkCFG(
    CFG *current,
    const analysis::NodeValues<std::tuple<analysis::node_t, analysis::node_t,
                                          analysis::CFG *>> &caller_to_fun) {
  auto bw = analysis::reverse(&current->holder);
  for (auto &c2f : caller_to_fun) {
    auto &callsite = c2f.first;
    auto calleeend = std::get<1>(c2f.second);
    auto G = std::get<2>(c2f.second);
    auto call = funMap->instance({callsite, NodeType::CALL});
    auto parms = funMap->calleeParameters({callsite, NodeType::CALL});
    if (calleeend != node_t::before()) {
      // is call
      LOG3("from " << dbp(current->maps_to) << " inline method " << callsite
                   << " -> " << dbp(G->maps_to));
      auto gClone = *G;
      gClone.holder = analysis::freshClone(
          std::move(gClone.holder), gClone.start_node, calleeend, &parents);
      auto calleestart = gClone.start_node;
      traverse_df_pernode(&gClone.holder, gClone.start_node, [&](node_t n) {
        if (auto mc = is_extern_method_call(n)) {
          auto mi = P4::MethodInstance::resolve(mc->methodCallStatement, refMap,
                                                typeMap);
          const IR::IDeclaration *d = nullptr;
          if (mi->is<P4::ExternFunction>()) {
            d = mi->to<P4::ExternFunction>()->method;
          } else if (mi->is<P4::ExternMethod>()) {
            d = mi->to<P4::ExternMethod>()->method;
          }
          CHECK_NULL(d);
          funMap->put(n, d->getNode(), mi);
        }
      });
      auto inparms = pass_params(parms, call, false, false);
      auto outparms = pass_params(parms, call, true, false);
      gClone = replace_inouts(std::move(gClone), parms, call, calleestart,
                              calleeend);
      auto calleestart_prime = calleestart;
      if (!inparms.empty()) {
        calleestart_prime = inparms.front();
        labelNode(inparms.front(), gClone.maps_to);
        size_t idx = 1;
        // link each assignment
        for (; idx != inparms.size(); ++idx) {
          gClone[inparms[idx - 1]].emplace_back(inparms[idx], 0);
          labelNode(inparms[idx], gClone.maps_to);
        }
        // link last assignment to the start of the other method
        gClone[inparms[idx - 1]].emplace_back(calleestart, 0);
      }
      auto calleeend_prime = calleeend;
      if (!outparms.empty()) {
        gClone[calleeend].emplace_back(outparms[0], 0);
        labelNode(outparms[0], gClone.maps_to);
        for (size_t idx = 1; idx != outparms.size(); ++idx) {
          gClone[outparms[idx - 1]].emplace_back(outparms[idx], 0);
          labelNode(outparms[idx], gClone.maps_to);
        }
        calleeend_prime = outparms[outparms.size() - 1];
      }
      gClone.start_node = calleestart_prime;
      gClone.end_node = calleeend_prime;
      for (auto &n : gClone.holder) {
        current->holder[n.first] = std::move(n.second);
      }
      auto succs = std::move(current->holder[callsite]);
      current->holder.erase(callsite);
      auto dummyCallSite = new IR::EmptyStatement();
      for (auto p : (*bw)[callsite]) {
        for (auto &n : current->holder[p.first]) {
          if (n.second == p.second && n.first == callsite) {
            n.first = dummyCallSite;
          }
        }
      }
      labelNode(dummyCallSite, current->maps_to);
      current->holder[dummyCallSite].emplace_back(calleestart_prime,
                                                  toNumber(EdgeType::CALL));
      BUG_CHECK(succs.size() <= 1, "no more than one successor");
      auto dummyend = new IR::EmptyStatement();
      current->holder[calleeend_prime].emplace_back(dummyend,
                                                    toNumber(EdgeType::RETURN));
      for (auto s : succs) {
        current->holder[dummyend].emplace_back(s);
      }
      labelNode(dummyend, current->maps_to);
    }
  }
}
const std::vector<const IR::Statement *>
analysis::BuildIPCFG::pass_params(const IR::ParameterList *parms,
                                  P4::MethodInstance *call, bool ret,
                                  bool has_inout) {
  MultiAssignment multiAssignment(refMap, typeMap);
  std::vector<const IR::Statement *> stats;
  if (!ret)
    stats.push_back(new IR::EmptyStatement());
  for (auto p : parms->parameters) {
    if ((!ret && p->direction == IR::Direction::In) ||
        (ret && p->direction == IR::Direction::Out) ||
        (has_inout && p->direction == IR::Direction::InOut)) {
      auto arg = call->substitution.lookupByName(p->name);
      auto exp = new IR::PathExpression(p->name);
      refMap->setDeclaration(exp->path, p);
      //          if (!ret) {
      //            stats.push_back(new IR::AssignmentStatement(exp,
      //            arg->expression));
      //          } else {
      //            stats.push_back(new
      //            IR::AssignmentStatement(arg->expression, exp));
      //          }
      // split assignment statement into its components, to ease def-use
      typeMap->setLeftValue(exp);
      typeMap->setType(exp, typeMap->getType(p));
      if (!ret) {
        auto muas = multiAssignment(exp, arg->expression);
        stats.insert(stats.end(), muas->begin(), muas->end());
      } else {
        auto muas = multiAssignment(arg->expression, exp);
        stats.insert(stats.end(), muas->begin(), muas->end());
      }
    }
  }
  if (ret)
    stats.push_back(new IR::EmptyStatement());
  return stats;
}

template <typename Fun, typename K, typename V> struct Cache {
  std::unordered_map<K, V> cache;
  Fun f;

  Cache(Fun f) : f(std::move(f)) {}

  V operator()(const K &key) {
    return analysis::getOrEmplace(cache, key, [this, &key]() { return f(key); })
        .first;
  }
};

template <typename K, typename V, typename Fun>
Cache<Fun, K, V> make_cache(Fun f) {
  return f;
};

analysis::CFG analysis::BuildIPCFG::replace_inouts(
    analysis::CFG c, const IR::ParameterList *parms, P4::MethodInstance *call,
    node_t &start, node_t &end) {
  std::unordered_map<MemPath, const IR::Expression *> replacements;
  PathGetter pathGetter(refMap, typeMap);
  for (auto p : parms->parameters) {
    if (p->direction == IR::Direction::InOut) {
      auto terminals = pathGetter.terminals(*pathGetter(p));
      auto terminals2 = pathGetter.terminals(*pathGetter(
          call->substitution.lookupByName(p->name.name)->expression));
      for (size_t i = 0, e = terminals.size(); i != e; ++i) {
        replacements.emplace(terminals[i], pathGetter(terminals2[i]));
      }
    }
  }
  Replace replace(refMap, typeMap, std::move(replacements));
  replace.readonly = false;
  auto nrep = make_cache<node_t, node_t>([&](node_t n) -> node_t {
    auto old = n;
    if (n.node->is<IR::IfStatement>()) {
      auto ifs = n.node->to<IR::IfStatement>();
      auto cl = ifs->clone();
      auto newcd = replace(cl->condition);
      if (newcd != cl->condition) {
        cl->condition = newcd->to<IR::Expression>();
        n.node = cl;
        parents[n] = old;
      }
    } else {
      n.node = replace(n.node);
      if (old != n) {
        parents[n] = old;
      }
    }
    return n;
  });
  c.holder = analysis::gmap(std::move(c.holder), std::ref(nrep)).first;
  c.start_node = nrep(c.start_node);
  start = nrep(start);
  end = nrep(end);
  traverse_df_pernode(&c.holder, start, [&](node_t n) {
    if (auto mc = is_extern_method_call(n)) {
      auto mi =
          P4::MethodInstance::resolve(mc->methodCallStatement, refMap, typeMap);
      const IR::IDeclaration *d = nullptr;
      if (mi->is<P4::ExternFunction>()) {
        d = mi->to<P4::ExternFunction>()->method;
      } else if (mi->is<P4::ExternMethod>()) {
        d = mi->to<P4::ExternMethod>()->method;
      }
      CHECK_NULL(d);
      funMap->put(n, d->getNode(), mi);
    }
  });
  return c;
}

void analysis::BuildIPCFG::labelNode(const analysis::node_t &nd,
                                     const IR::Node *n) {
  CHECK_NULL(n);
  node_to_method[nd] = n;
}

void analysis::BuildIPCFG::labelCFG(const analysis::CFG *c, const IR::Node *n) {
  CHECK_NULL(n);
  traverse_df_pernode(&c->holder, c->start_node,
                      [&](const node_t &nd) { labelNode(nd, n); });
}

const IR::Node *analysis::BuildIPCFG::getMethod(const analysis::node_t &nd) {
  auto It = node_to_method.find(nd);
  if (It != node_to_method.end()) {
    return It->second;
  }
  BUG("node unmapped %1% to method", nd);
  return nullptr;
}

void analysis::BuildIPCFG::link_gotos(
    analysis::CFG *current,
    const std::unordered_map<analysis::node_t,
                             std::tuple<analysis::node_t, analysis::node_t,
                                        analysis::CFG *>> &caller_to_fun) {
  auto bw = analysis::reverse(&current->holder);
  auto &goes_to = gotos[current->maps_to];
  for (auto &c2f : caller_to_fun) {
    auto &callsite = c2f.first;
    auto calleestart = std::get<0>(c2f.second);
    auto calleeend = std::get<1>(c2f.second);
    auto G = std::get<2>(c2f.second);
    auto call = funMap->instance({callsite, NodeType::CALL});
    auto parms = funMap->calleeParameters({callsite, NodeType::CALL});
    auto callernode = funMap->callee({callsite, NodeType::CALL});
    if (calleeend == node_t::before()) {
      // is goto
      LOG4("@" << dbp(current->maps_to) << " goto method " << callsite << " = "
               << dbp(G->maps_to));
      goes_to.emplace(callernode);
      auto inparms = pass_params(parms, call, false, true);
      node_t callsite_prime = new IR::EmptyStatement();
      if (!inparms.empty()) {
        size_t idx = 1;
        callsite_prime = inparms.at(0);
        labelNode(callsite_prime, current->maps_to);
        // link each assignment
        for (; idx != inparms.size(); ++idx) {
          (*current)[inparms[idx - 1]].emplace_back(inparms[idx], 0);
          labelNode(inparms[idx], current->maps_to);
        }
        // edge is trailing, will super-impose graph later
        (*current)[inparms[idx - 1]].emplace_back(calleestart,
                                                  toNumber(EdgeType::GOTO));
        labelNode(calleestart, G->maps_to);
      } else {
        (*current)[callsite_prime].emplace_back(calleestart,
                                                toNumber(EdgeType::GOTO));
        labelNode(calleestart, G->maps_to);
      }
      labelNode(callsite_prime, current->maps_to);
      for (auto p : (*bw)[callsite]) {
        for (auto &n : current->holder[p.first]) {
          if (n.second == p.second && n.first == callsite) {
            n.first = callsite_prime;
          }
        }
      }
      current->holder.erase(callsite);
    }
  }
  if (LOGGING(5)) {
    auto filename = refMap->newName("gotos_parms") + ".dot";
    std::ofstream noret(filename);
    LOG3("gotos passed @" << dbp(current->maps_to) << ": " << filename);
    current->toDot(noret);
  }
}

const IR::Function *analysis::ITracker::findFunction(const IR::P4Program *prog,
                                                     cstring name) {
  auto decl = prog->getDeclsByName(name);
  if (decl) {
    return decl->begin().operator*()->to<IR::Function>();
  }
  return nullptr;
}

const IR::Function *
analysis::ITracker::getImplementation(const IR::P4Program *program,
                                      const IR::Method *method) {
  auto impl = method->getAnnotation("impl");
  if (impl) {
    if (impl->expr.at(0)->is<IR::StringLiteral>()) {
      auto sl = impl->expr.at(0)->to<IR::StringLiteral>();
      if (auto fun = ITracker::findFunction(program, sl->value)) {
        return fun;
      }
    }
  }
  return nullptr;
}

bool analysis::NodeToFunctionMap::put(node_t n, const IR::Node *fun,
                                      P4::MethodInstance *mi) {
  auto &mapping = functionMappings[n];
  if (mapping && fun != mapping)
    BUG("mapping already there for %1% -> %2%, now %3%", n, mapping, fun);
  if (mapping)
    return false;
  instances[n] = mi;
  mapping = fun;
  return true;
}

P4::MethodInstance *analysis::NodeToFunctionMap::instance(node_t cfgn) {
  auto I = instances.find(cfgn);
  if (I == instances.end()) {
    return nullptr;
  }
  return I->second;
}

const IR::Node *analysis::NodeToFunctionMap::callee(node_t cfgn) const {
  auto I = functionMappings.find(cfgn);
  if (I != functionMappings.end()) {
    return I->second;
  }
  return nullptr;
}

bool analysis::NodeToFunctionMap::hasReturn(node_t cfgn) {
  auto clee = callee(cfgn);
  BUG_CHECK(clee != nullptr, "no callee found for %1%", cfgn);
  if (clee) {
    if (clee->is<IR::Function>()) {
      auto f = clee->to<IR::Function>();
      return f->type->returnType && !f->type->returnType->is<IR::Type_Void>();
    } else if (clee->is<IR::P4Control>()) {
      return false;
    } else if (clee->is<IR::P4Parser>()) {
      return false;
    }
  }
  BUG("can't get callee %1% parameters", clee);
}

const IR::IndexedVector<IR::Declaration> *
analysis::NodeToFunctionMap::locals(node_t cfgn) {
  auto clee = callee(cfgn);
  BUG_CHECK(clee != nullptr, "no callee found for %1%", cfgn);
  if (clee) {
    if (clee->is<IR::Function>()) {
      return new IR::IndexedVector<IR::Declaration>();
    } else if (clee->is<IR::P4Control>()) {
      return &clee->to<IR::P4Control>()->controlLocals;
    } else if (clee->is<IR::P4Parser>()) {
      return &clee->to<IR::P4Parser>()->parserLocals;
    }
  }
  BUG("can't get callee %1% parameters", clee);
}

const IR::ParameterList *
analysis::NodeToFunctionMap::calleeParameters(node_t cfgn) {
  auto clee = callee(cfgn);
  BUG_CHECK(clee != nullptr, "no callee found for %1%", cfgn);
  if (clee) {
    if (clee->is<IR::Function>()) {
      return clee->to<IR::Function>()->getParameters();
    } else if (clee->is<IR::P4Control>()) {
      return clee->to<IR::P4Control>()->getApplyParameters();
    } else if (clee->is<IR::P4Parser>()) {
      return clee->to<IR::P4Parser>()->getApplyParameters();
    } else if (clee->is<IR::Method>()) {
      return clee->to<IR::Method>()->getParameters();
    }
  }
  BUG("can't get callee %1% parameters", clee);
}
const IR::Type *analysis::NodeToFunctionMap::returnType(analysis::node_t cfgn) {
  auto clee = callee(cfgn);
  BUG_CHECK(clee != nullptr, "no callee found for %1%", cfgn);
  if (clee) {
    if (clee->is<IR::Function>()) {
      return instance(cfgn)->actualMethodType->returnType;
    } else if (clee->is<IR::P4Control>()) {
      return nullptr;
    } else if (clee->is<IR::P4Parser>()) {
      return nullptr;
    }
  }
  BUG("can't get callee %1% parameters", clee);
}
