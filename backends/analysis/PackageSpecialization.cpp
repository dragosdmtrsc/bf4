//
// Created by dragos on 19.04.2019.
//

#include <p4/cloner.h>
#include "PackageSpecialization.h"

const IR::Node *analysis::PackageSpecialization::preorder(IR::Declaration_Instance *di) {
  auto instance = P4::Instantiation::resolve(getOriginal<IR::Declaration_Instance>(),
                                             refMap, typeMap
  );
  if (auto pi = instance->to<P4::PackageInstantiation>()) {
    LOG4("type of package " << pi->package);
    auto newpack = refMap->newName(pi->package->name);
    auto parmList = new IR::ParameterList();
    auto nodes = new IR::Vector<IR::Node>;
    for (auto ca : *pi->constructorArguments) {
      auto tp = typeMap->getType(ca);
      if (tp->is<IR::P4Parser>() || tp->is<IR::P4Control>()) {
        tp = typeMap->getTypeType(tp, true);
      }
      cstring typeName = "";
      if (tp->is<IR::Type_Parser>()) {
        typeName = refMap->newName("parser");
        nodes->push_back(new IR::Type_Parser(di->srcInfo, typeName, tp->to<IR::Type_Parser>()->applyParams));
      } else if (tp->is<IR::Type_Control>()) {
        typeName = refMap->newName("control");
        nodes->push_back(new IR::Type_Control(di->srcInfo, typeName, tp->to<IR::Type_Control>()->applyParams));
      }
      auto oldParm = pi->substitution.findParameter(ca);
      auto parm = new IR::Parameter(oldParm->name, oldParm->direction, new IR::Type_Name(di->srcInfo, new IR::Path(di->srcInfo, typeName)));
      parmList->push_back(parm);
    }
    auto packtype = new IR::Type_Package(di->srcInfo, newpack, parmList);
    P4::ClonePathExpressions cloner;
    auto args = cloner.clone<IR::Vector<IR::Argument>>(di->arguments)->clone();
    auto instance = new IR::Declaration_Instance(
        di->srcInfo, di->getName(), new IR::Type_Name(newpack), args);
    nodes->push_back(packtype);
    nodes->push_back(instance);
    prune();
    return nodes;
  }
  return di;
}
