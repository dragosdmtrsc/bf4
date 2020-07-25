//
// Created by a-drdum on 6/22/2019.
//

#ifndef P4C_VIMPLEMENTATIONMAP_H
#define P4C_VIMPLEMENTATIONMAP_H

#include "ir/ir.h"

class ImplementationMap {
  std::map<const IR::Type *, const IR::Type *> implementations;
  static ImplementationMap *instance;
public:
  static ImplementationMap *get() {
    if (!instance) {
      instance = new ImplementationMap;
    }
    return instance;
  }
  static ImplementationMap *getCleared() {
    auto g = get();
    g->implementations.clear();
    return g;
  }
  void put(const IR::Type *interface, const IR::Type *concrete) {
    implementations.emplace(interface, concrete);
  }
  const IR::Type *implemented(const IR::Type *what) {
    auto I = implementations.find(what);
    if (I != implementations.end()) {
      return I->second;
    }
    return nullptr;
  }
};


#endif //P4C_VIMPLEMENTATIONMAP_H
