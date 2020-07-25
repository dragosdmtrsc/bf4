//
// Created by dragos on 29.08.2019.
//

#include "MutexInstrument.h"
#include <analysis/analysis_helpers.h>
#include <common/resolveReferences/resolveReferences.h>
#include <p4/typeChecking/typeChecker.h>

namespace analysis {

class MutexHeaderHolder {
 protected:
  // inout: mutexHeaders -> will get populated with the mutex matrix
  MutexHeaders *mutexHeaders;
  P4::ReferenceMap *refMap() const { return mutexHeaders->refMap; }
  P4::TypeMap *typeMap() const { return mutexHeaders->typeMap; }

 public:
  MutexHeaderHolder(MutexHeaders *mutexHeaders) : mutexHeaders(mutexHeaders) {}
};

class MutexFinder : public Inspector, MutexHeaderHolder {
  cstring parserName;
  bool preorder(const IR::P4Parser *p) override {
    if (p->name.name == parserName) {
      // TODO: analysis goes here
    }
    return false;
  }

 public:
  MutexFinder(MutexHeaders *mutexHeaders, cstring parser)
      : MutexHeaderHolder(mutexHeaders), parserName(parser) {}
};

class DoMutexInstrument : public Transform, MutexHeaderHolder {
  cstring controlName;
  const IR::Node *preorder(IR::P4Parser *p) override {
    prune();
    return p;
  }
  const IR::Node *preorder(IR::Function *f) override {
    prune();
    return f;
  }
  const IR::Node *preorder(IR::P4Control *control) override {
    // stops recursing if not in the control we care about
    if (control->name.name != controlName) {
      prune();
    }
    return control;
  }
  const IR::Node *postorder(IR::MethodCallStatement *stat) override {
    if (auto mi = is_set_valid(stat, refMap(), typeMap())) {
      auto ef = mi->to<P4::ExternMethod>();
      auto what = ef->expr->method->to<IR::Member>();
      (void)ef;
      (void)what;
      // TODO: instrumentation goes here => forall h' \in mutex(what);
      // if (h'.isValid()) bug();
    }
    return stat;
  }

 public:
  DoMutexInstrument(MutexHeaders *mutexHeaders, cstring controlName)
      : MutexHeaderHolder(mutexHeaders), controlName(controlName) {}
};

MutexInstrument::MutexInstrument(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                                 cstring parser, cstring control)
    : refMap(refMap),
      typeMap(typeMap),
      parser(parser),
      control(control),
      mutexHeaders(refMap, typeMap) {
  passes.push_back(new MutexFinder(&mutexHeaders, parser));
  passes.push_back(new DoMutexInstrument(&mutexHeaders, parser));
  // fix type map and references to ensure later invariants
  addPasses({new P4::ClearTypeMap(typeMap), new P4::ResolveReferences(refMap),
             new P4::TypeInference(refMap, typeMap, false)});
}

MutexHeaders::MutexHeaders(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap) {}
};
