//
// Created by dragos on 29.01.2020.
//

#include "KeyAdder.h"
namespace analysis {

KeyAdder::KeyAdder(ReferenceMap *refMap, TypeMap *typeMap,
                   NodeValues<std::set<analysis::MemPath>> patches)
    : refMap(refMap), typeMap(typeMap), patches(std::move(patches)),
      pt(typeMap), pg(refMap, typeMap) {
  init();
}

void KeyAdder::init() {
  for (auto &t2patch : this->patches) {
    auto tabcall = t2patch.first->to<IR::MethodCallStatement>();
    auto &extras = t2patch.second;
    auto mi = P4::MethodInstance::resolve(tabcall, refMap, typeMap);
    method2keys[mi->to<P4::ExternFunction>()->method->name] = extras;
  }
}

const IR::Node *KeyAdder::postorder(IR::Method *met) {
  auto Ipat = method2keys.find(met->name);
  if (Ipat != method2keys.end()) {
    auto mtcl = met->type->clone();
    auto pclone = mtcl->parameters->clone();
    for (const auto &ps : Ipat->second) {
      pclone->push_back(new IR::Parameter(refMap->newName("af4_key"),
                                          IR::Direction::In, pt[ps]));
    }
    mtcl->parameters = pclone;
    met->type = mtcl;
  }
  return met;
}

const IR::Node *KeyAdder::postorder(IR::MethodCallStatement *stat) {
  auto mi = P4::MethodInstance::resolve(stat->methodCall, refMap, typeMap);
  if (auto ef = mi->to<P4::ExternFunction>()) {
    auto Ipat = method2keys.find(ef->method->name);
    if (Ipat != method2keys.end()) {
      auto mceclone = stat->methodCall->clone();
      auto argclone = mceclone->arguments->clone();
      for (const auto &ps : Ipat->second) {
        auto no_version = ps;
        no_version.version = -1u;
        argclone->emplace_back(pg(no_version));
      }
      mceclone->arguments = argclone;
      stat->methodCall = mceclone;
    }
  }
  return stat;
}
}