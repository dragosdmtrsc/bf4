//
// Created by dragos on 06.05.2019.
//

#include <p4/methodInstance.h>
#include <p4/typeChecking/typeChecker.h>
#include "SpecializeExternFunctions.h"


namespace analysis {
class FindExternFunctionsToSpecialize : public Inspector {
  ExternFunMap *funMap;
public:
  FindExternFunctionsToSpecialize(ExternFunMap *funMap) : funMap(funMap) {}

  void postorder(const IR::MethodCallExpression *mce) override {
    auto mi = P4::MethodInstance::resolve(mce, funMap->refMap, funMap->typeMap);
    if (auto ef = mi->to<P4::ExternFunction>()) {
      auto orig = ef->originalMethodType;
      if (orig != ef->actualMethodType) {
        funMap->put(mce, ef->method, ef->actualMethodType->to<IR::Type_Method>());
        LOG4("found specialized extern function for " << ef->method << " = " << ef->actualMethodType);
      }
    }
  }
};

class AddFunctionDefinitions : public Transform {
  ExternFunMap *funMap;
  std::map<const IR::Type_Method *, cstring> methodMapping;
public:
  AddFunctionDefinitions(ExternFunMap *funMap) : funMap(funMap) {}

  IR::Type_Method *mkTypeMethod(Util::SourceInfo src, const IR::Type_Method *meth) {
    auto cl = meth->clone();
    auto plist = new IR::ParameterList();
    for (auto p : *cl->parameters) {
      auto tp = funMap->typeMap->getTypeType(p->type, false);
      if (!tp) {
        plist->push_back(p);
      } else {
        auto pclone = p->clone();
        pclone->srcInfo = src;
        if (auto td = tp->to<IR::Type_Declaration>()) {
          pclone->type = new IR::Type_Name(src, new IR::Path(src, td->name));
        }
        plist->push_back(pclone);
      }
    }
    auto tp = cl->returnType->clone();
    if (auto td = tp->to<IR::Type_Declaration>()) {
      tp = new IR::Type_Name(src, new IR::Path(src, td->name));
    }
    cl->returnType = tp;
    cl->parameters = plist;
    cl->srcInfo = src;
    return cl;
  }

  const IR::Node *preorder(IR::P4Program *program) override {
    std::set<const IR::Type_Method *> already;
    std::map<int, std::vector<const IR::Node *>> addAfter;
    for (auto idx = static_cast<int>(program->objects.size() - 1); idx >= 0; --idx) {
      auto o = program->objects[idx];
      if (auto td = o->to<IR::IDeclaration>()) {
        auto I = funMap->revTypeDependencies.find(td);
        if (I == funMap->revTypeDependencies.end() && td->is<IR::Type_Declaration>()) {
          auto t = funMap->typeMap->getType(td->getNode(), false);
          if (t && t->is<IR::Type_Type>())
            I = funMap->revTypeDependencies.find(t->to<IR::Type_Type>()->type->to<IR::Type_Declaration>());
        }
        if (I != funMap->revTypeDependencies.end()) {
          for (auto def : I->second) {
            if (already.emplace(def).second) {
              auto method = funMap->revSpecMap[def];
              auto newname = funMap->refMap->newName(method->name);
              LOG4("will add " << def << " after " << o << " with name " << newname);
              methodMapping[def] = newname;
              auto met = new IR::Method(o->srcInfo, newname, mkTypeMethod(o->srcInfo, def));
              addAfter[idx].emplace_back(met);
            }
          }
        }
      }
    }
    for (auto I = addAfter.rbegin(); I != addAfter.rend(); ++I) {
      auto &p = *I;
      program->objects.insert(program->objects.begin() + p.first + 1, p.second.begin(), p.second.end());
    }
    return program;
  }

  const IR::Node *postorder(IR::MethodCallExpression *mce) override {
    auto orig = getOriginal<IR::MethodCallExpression>();
    auto I = funMap->functionsToReplace.find(orig);
    if (I != funMap->functionsToReplace.end()) {
      auto J = methodMapping.find(I->second);
      if (J != methodMapping.end()) {
        LOG4("need to transform " << mce << " to " << J->second);
        mce->typeArguments = new IR::Vector<IR::Type>;
        mce->method = new IR::PathExpression(J->second);
      }
    }
    return mce;
  }
};

ExternFunMap::ExternFunMap(P4::ReferenceMap *refMap, P4::TypeMap *typeMap) : refMap(refMap), typeMap(typeMap) {}

void ExternFunMap::put(const IR::MethodCallExpression *mce, const IR::Method *met, const IR::Type_Method *methodType) {
  specMap[met].emplace(methodType);
  revSpecMap[methodType] = met;
  functionsToReplace[mce] = methodType;
  for (auto parm : *methodType->parameters) {
    auto tp = typeMap->getTypeType(parm->type, false);
    if (!tp)
      continue;
    if (auto td = tp->to<IR::Type_Declaration>()) {
      LOG4(methodType << " depends on " << td);
      typeDependencies[methodType].emplace(td);
      revTypeDependencies[td].emplace(methodType);
    }
  }
  typeDependencies[methodType].emplace(met);
  revTypeDependencies[met].emplace(methodType);
  auto tp = typeMap->getTypeType(methodType->returnType, false);
  if (tp) {
    if (auto td = tp->to<IR::Type_Declaration>()) {
      typeDependencies[methodType].emplace(td);
      revTypeDependencies[td].emplace(methodType);
    }
  }
}
}

analysis::SpecializeExternFunctions::SpecializeExternFunctions(P4::ReferenceMap *refMap, P4::TypeMap *typeMap) : refMap(
  refMap), typeMap(typeMap), funMap(refMap, typeMap) {
  setName("MidEnd_specializefuns");
  passes.push_back(new FindExternFunctionsToSpecialize(&funMap));
  passes.push_back(new AddFunctionDefinitions(&funMap));
  passes.push_back(new P4::ClearTypeMap(typeMap));
  passes.push_back(new P4::TypeChecking(refMap, typeMap, false));
}
