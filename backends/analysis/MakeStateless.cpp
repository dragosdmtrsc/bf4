//
// Created by dragos on 18.04.2019.
//

#include "MakeStateless.h"
#include <common/resolveReferences/resolveReferences.h>
#include <p4/cloner.h>
#include <p4/typeChecking/typeChecker.h>

namespace analysis {

class FindStateInfo : public Inspector {
  StateInfos *states;

public:
  FindStateInfo(StateInfos *states) : states(states) {}

  void postorder(const IR::Type_Declaration *tp) override {
    if (auto text = tp->to<IR::Type_Extern>()) {
      if (text->typeParameters->empty()) {
        declareExternState(text);
        auto tt =
            states->typeMap->getTypeType(text, true)->to<IR::Type_Extern>();
        declareExternState(tt);
      }
    }
  }

  StateInfo declareExternState(const IR::Type_Extern *text) const {
    StateInfo stateInfo;
    stateInfo.of = text;
    for (auto m : text->methods) {
      if (m->name == text->name) {
        // this is a constructor
        for (auto p : *m->getParameters()) {
          auto thetype = states->getType(states->typeMap->getType(p));
          if (thetype)
            stateInfo.declToTypes.emplace(p, thetype);
        }
      }
    }
    states->put(text, stateInfo);
    return stateInfo;
  }
};

IR::Type_Struct *StateInfo::mkStruct(cstring name) {
  if (name.isNullOrEmpty()) {
    name = of->to<IR::Type_Declaration>()->getName() + "_state";
  }
  auto str = new IR::Type_Struct(name);
  for (auto d : declToTypes) {
    str->fields.push_back(new IR::StructField(d.first->name, d.second));
  }
  return str;
}

const IR::Type *StateInfos::getType(const IR::Type *other) {
  auto I = info.find(other);
  cstring newname = "";
  if (other->is<IR::Type_Declaration>()) {
    if (I != info.end()) {
      if (other->is<IR::Type_Declaration>()) {
        newname = cstring(other->to<IR::Type_Declaration>()->name + "_state");
        return new IR::Type_Name(newname);
      } else {
        BUG("type in state infos must be a declaration");
      }
    } else if (other->is<IR::Type_Enum>() || other->is<IR::Type_Error>() ||
               other->is<IR::Type_StructLike>()) {
      return new IR::Type_Name(other->to<IR::Type_Declaration>()->getName());
    }
  } else if (other->is<IR::Type_Base>()) {
    return other;
  }
  return nullptr;
}

class DeclareState : public Transform {
  StateInfos *infos;

  const IR::Node *preorder(IR::P4Program *program) override {
    for (auto &info : infos->info) {
      auto I = std::find(program->objects.begin(), program->objects.end(),
                         info.first);
      if (I != program->objects.end()) {
        LOG4("inserting state struct " << info.second.mkStruct(""));
        program->objects.insert(I, info.second.mkStruct(""));
      }
    }
    prune();
    return program;
  }

public:
  DeclareState(StateInfos *infos) : infos(infos) {}
};

class FindExternBehavior : public Inspector {
  StateInfos *infos;
  Behaviors *behaviors;
  std::map<const IR::Type_Extern *, std::vector<const IR::Method *>>
      *externInstances;

public:
  FindExternBehavior(StateInfos *infos, Behaviors *behaviors,
                     std::map<const IR::Type_Extern *,
                              std::vector<const IR::Method *>> *externInstances)
      : infos(infos), behaviors(behaviors), externInstances(externInstances) {}

  void postorder(const IR::Type_Extern *ext) override {
    auto I = infos->info.find(ext);
    if (I != infos->info.end()) {
      auto stateType = I->second.mkStruct("");
      auto tt = infos->typeMap->getTypeType(ext, true)->to<IR::Type_Extern>();
      addExternBehavior(tt, stateType, true);
      addExternBehavior(ext, stateType, false);
    }
  }

  void addExternBehavior(const IR::Type_Extern *ext,
                         const IR::Type_Struct *stateType,
                         bool isCanonical) const {
    for (auto method : ext->methods) {
      cstring newMethodName = ext->name + "_" + method->getName();
      auto mt = method->type->clone();
      auto parms = new IR::ParameterList();
      parms->push_back(
          new IR::Parameter("self", IR::Direction::InOut, stateType));
      for (auto p : *mt->parameters) {
        parms->push_back(p);
      }
      mt->parameters = parms;
      P4::ClonePathExpressions cloner;
      auto clonemethod = cloner.clone<IR::Method>(method)->clone();
      clonemethod->srcInfo = ext->getSourceInfo();
      clonemethod->type = mt;
      clonemethod->name = newMethodName;
      if (!isCanonical)
        (*externInstances)[ext].emplace_back(clonemethod);
      behaviors->put(ext, method, clonemethod);
    }
  }
};

class DeclareExternBehavior : public Transform {
  std::map<const IR::Type_Extern *, std::vector<const IR::Method *>>
      *externInstances;

public:
  DeclareExternBehavior(
      std::map<const IR::Type_Extern *, std::vector<const IR::Method *>>
          *externInstances)
      : externInstances(externInstances) {}
  const IR::Node *preorder(IR::P4Program *program) override {
    for (auto &p : *externInstances) {
      auto I =
          std::find(program->objects.begin(), program->objects.end(), p.first);
      if (I != program->objects.end()) {
        program->objects.insert(I, p.second.begin(), p.second.end());
      }
    }
    prune();
    return program;
  }
};

class MakeExternBehavior : public PassManager {
  StateInfos *infos;
  Behaviors *behaviors;
  std::map<const IR::Type_Extern *, std::vector<const IR::Method *>>
      externInstances;

public:
  MakeExternBehavior(StateInfos *infos, Behaviors *behaviors)
      : infos(infos), behaviors(behaviors) {
    passes.push_back(
        new FindExternBehavior(infos, behaviors, &externInstances));
    passes.push_back(new DeclareExternBehavior(&externInstances));
    passes.push_back(new P4::ResolveReferences(infos->refMap));
  }
};

class AddApplyBehavior : public Transform {
  Behaviors *behaviors;

public:
  AddApplyBehavior(Behaviors *behaviors) : behaviors(behaviors) {}

  const IR::Node *preorder(IR::P4Program *program) override {
    for (auto &b : behaviors->otherBehaviors) {
      auto I = std::find(program->objects.begin(), program->objects.end(),
                         b.first->to<IR::Node>());
      if (I != program->objects.end()) {
        program->objects.insert(I, b.second->to<IR::Type_Declaration>());
      }
    }
    prune();
    return program;
  }
};

class FindApplyBehavior : public Inspector {
  StateInfos *infos;
  Behaviors *behaviors;

public:
  FindApplyBehavior(StateInfos *infos, Behaviors *behaviors)
      : infos(infos), behaviors(behaviors) {}

  void postorder(const IR::P4Control *control) override {
    auto I = infos->info.find(control);
    if (I != infos->info.end()) {
      auto statekind = infos->getType(control);
      auto newparamlist = new IR::ParameterList();
      newparamlist->push_back(
          new IR::Parameter("self", IR::Direction::InOut, statekind));
      for (auto p : *control->type->applyParams) {
        newparamlist->push_back(p);
      }
      auto controlType = control->type->clone();
      controlType->name = cstring(control->name + "_behavior");
      controlType->applyParams = newparamlist;
      P4::ClonePathExpressions cloner;
      auto controlcopy = cloner.clone<IR::P4Control>(control)->clone();
      controlcopy->type = controlType;
      controlcopy->name = cstring(control->name + "_behavior");
      behaviors->put(control, controlcopy);
    }
  }
  void postorder(const IR::P4Parser *parser) {
    auto I = infos->info.find(parser);
    if (I != infos->info.end()) {
      auto statekind = infos->getType(parser);
      auto newparamlist = new IR::ParameterList();
      newparamlist->push_back(
          new IR::Parameter("self", IR::Direction::InOut, statekind));
      for (auto p : *parser->type->applyParams) {
        newparamlist->push_back(p);
      }
      auto controlType = parser->type->clone();
      controlType->name = cstring(parser->name + "_behavior");
      controlType->applyParams = newparamlist;
      P4::ClonePathExpressions cloner;
      auto parserCopy = cloner.clone<IR::P4Parser>(parser)->clone();
      parserCopy->type = controlType;
      parserCopy->name = cstring(parser->name + "_behavior");
      behaviors->put(parser, parserCopy);
    }
  }
};

class AddExternDeclarations : public Transform {
  StateInfos *infos;

public:
  AddExternDeclarations(StateInfos *infos) : infos(infos) {}
  const IR::Node *postorder(IR::Declaration *decl) override {
    auto tt = infos->typeMap->getType(getOriginal());
    if (auto te = tt->to<IR::Type_Extern>()) {
      auto I = infos->info.find(te);
      BUG_CHECK(I != infos->info.end(), "can't find type %1% in state map", te);
      auto newdecl = infos->getType(te);
      if (auto p = decl->to<IR::Parameter>()) {
        auto dir = p->direction;
        if (dir == IR::Direction::None)
          dir = IR::Direction::InOut;
        auto parm =
            new IR::Parameter(decl->getSourceInfo(),
                              cstring(p->getName()), dir, newdecl);
        return parm;
      } else if (decl->is<IR::Declaration_Variable>()) {
        auto var = new IR::Declaration_Variable(
            decl->getSourceInfo(), cstring(decl->getName()),
            newdecl);
        return var;
      } else if (decl->is<IR::Declaration_Instance>()) {
        auto var = new IR::Declaration_Variable(
            decl->getSourceInfo(), cstring(decl->getName()),
            newdecl);
//        return new IR::IndexedVector<IR::Declaration>({decl, var});
        return var;
      }
    }
    return decl;
  }
};

class RemoveExternMethods : public Transform {
  StateInfos *infos;

public:
  RemoveExternMethods(StateInfos *infos) : infos(infos) {}
  const IR::Node *postorder(IR::MethodCallExpression *mce) override {
    auto mi = P4::MethodInstance::resolve(
        getOriginal<IR::MethodCallExpression>(), infos->refMap, infos->typeMap);
    if (auto em = mi->to<P4::ExternMethod>()) {
      auto obj = em->object->to<IR::Declaration>();
      cstring statename = obj->getName();
      auto expr = new IR::PathExpression(statename);
      auto met = em->method;
      cstring metname = em->actualExternType->getName() + "_" + met->getName();
      auto args = new IR::Vector<IR::Argument>({new IR::Argument(expr)});
      args->insert(args->end(), mce->arguments->begin(), mce->arguments->end());
      return new IR::MethodCallExpression(mce->srcInfo,
                                          new IR::PathExpression(metname),
                                          mce->typeArguments, args);
    }
    return mce;
  }
};

class FindMoveStateToApply : public Inspector {
  StateInfos *infos;
  std::map<const IR::Type_Declaration *, const IR::Type_Declaration *> *changes;

public:
  FindMoveStateToApply(StateInfos *infos,
                       std::map<const IR::Type_Declaration *,
                                const IR::Type_Declaration *> *changes)
      : infos(infos), changes(changes) {}
  void computeChange(const IR::Type_Declaration *object,
                     const IR::ParameterList *constructorParams,
                     const IR::IndexedVector<IR::Declaration> *p_locals,
                     const IR::Type_Declaration *signatureType,
                     const IR::Type_Declaration *declaredType,
                     Util::SourceInfo srcInfo) {
    LOG4("canonical type " << signatureType << " = "
                           << ((uint64_t)signatureType));
    LOG4("non canonical type " << declaredType << " = "
                               << ((uint64_t)declaredType));
    auto apply = signatureType->to<IR::IApply>();
    auto typeControl = declaredType->clone();
    auto applyparams = apply->getApplyParameters()->clone();
    bool changed = false;
    for (auto cp : *constructorParams) {
      auto p2 = cp->clone();
      p2->direction = getDirection(cp);
      changed = true;
      applyparams->push_back(p2);
    }
    auto locals = p_locals->clone();
    for (auto I = locals->begin(); I != locals->end();) {
      auto loc = *I;
      const IR::Type *t = nullptr;
      if (auto dv = loc->to<IR::Declaration_Variable>()) {
        t = dv->type;
      } else if (auto di = loc->to<IR::Declaration_Instance>()) {
        t = di->type;
      } else {
        ++I;
        continue;
      }
      auto dir = getDirection(loc);
      auto parm = new IR::Parameter(srcInfo, loc->name, dir, t);
      changed = true;
      applyparams->push_back(parm);
      I = locals->erase(I);
    }
    if (typeControl->is<IR::Type_Control>()) {
      auto tc = typeControl->to<IR::Type_Control>()->clone();
      tc->applyParams = applyparams;
      typeControl = tc;
    } else if (typeControl->is<IR::Type_Parser>()) {
      auto tc = typeControl->to<IR::Type_Parser>()->clone();
      tc->applyParams = applyparams;
      typeControl = tc;
    }

    if (changed) {
      (*changes)[signatureType] = typeControl;
      auto thetype =
          infos->typeMap->getTypeType(object, true)->to<IR::Type_Declaration>();
      if (auto prs = object->to<IR::P4Parser>()) {
        auto cl = prs->clone();
        cl->constructorParams = new IR::ParameterList();
        cl->type = typeControl->to<IR::Type_Parser>();
        cl->parserLocals = std::move(*locals);
        (*changes)[thetype] = cl;
      } else if (auto ctrl = object->to<IR::P4Control>()) {
        auto cl = ctrl->clone();
        cl->constructorParams = new IR::ParameterList();
        cl->controlLocals = std::move(*locals);
        cl->type = typeControl->to<IR::Type_Control>();
        (*changes)[thetype] = cl;
      }
      LOG4("found signature change in " << signatureType << " -> "
                                        << typeControl);
    }
  }

  bool preorder(const IR::P4Control *control) override {
    auto signatureType = infos->typeMap->getTypeType(control->type, true)
                             ->to<IR::Type_Control>();
    computeChange(control, control->getConstructorParameters(),
                  &control->controlLocals, signatureType, control->type,
                  control->srcInfo);
    return false;
  }
  bool preorder(const IR::P4Parser *parser) override {
    auto signatureType =
        infos->typeMap->getTypeType(parser->type, true)->to<IR::Type_Parser>();
    computeChange(parser, parser->getConstructorParameters(),
                  &parser->parserLocals, signatureType, parser->type,
                  parser->srcInfo);
    return false;
  }

  IR::Direction getDirection(const IR::Declaration *cp) const {
    IR::Direction dir = IR::Direction::InOut;
    auto tp = infos->typeMap->getType(cp);
    if (tp->is<IR::Type_Extern>())
      dir = IR::Direction::None;
    return dir;
  }
};

class DoMoveStateToApply : public Transform {
  StateInfos *infos;
  std::map<const IR::Type_Declaration *, const IR::Type_Declaration *> *changes;

public:
  DoMoveStateToApply(StateInfos *infos,
                     std::map<const IR::Type_Declaration *,
                              const IR::Type_Declaration *> *changes)
      : infos(infos), changes(changes) {}
  const IR::Node *preorder(IR::P4Control *control) override {
    auto canonical = infos->typeMap->getTypeType(control->type, true)
                         ->to<IR::Type_Control>();
    LOG4("canonical type control " << ((uint64_t)canonical) << " vs "
                                   << ((uint64_t)control->type));
    if (changes->count(canonical)) {
      auto typeControl = (*changes)[canonical]->to<IR::Type_Control>();
      auto &locals = control->controlLocals;
      for (auto I = locals.begin(); I != locals.end();) {
        auto loc = *I;
        if (loc->to<IR::Declaration_Variable>()) {
        } else if (loc->to<IR::Declaration_Instance>()) {
        } else {
          ++I;
          continue;
        }
        I = locals.erase(I);
      }
      control->constructorParams = new IR::ParameterList();
      control->type = typeControl;
    }
    return control;
  }
  const IR::Node *preorder(IR::P4Parser *parser) override {
    auto canonical =
        infos->typeMap->getTypeType(parser->type, true)->to<IR::Type_Parser>();
    LOG4("canonical type parser " << ((uint64_t)canonical) << " vs "
                                  << ((uint64_t)parser->type));
    if (changes->count(canonical)) {
      auto typeControl = (*changes)[canonical]->to<IR::Type_Parser>();
      auto &locals = parser->parserLocals;
      for (auto I = locals.begin(); I != locals.end();) {
        auto loc = *I;
        if (loc->to<IR::Declaration_Variable>()) {
        } else if (loc->to<IR::Declaration_Instance>()) {
        } else {
          ++I;
          continue;
        }
        I = locals.erase(I);
      }
      parser->constructorParams = new IR::ParameterList();
      parser->type = typeControl;
    }
    return parser;
  }
};

class FindChangedSignatures : public Inspector {
  StateInfos *infos;
  std::map<const IR::Type_Declaration *, const IR::Type_Declaration *>
      *signatureChanges;
  std::map<const IR::Type_Package *, const IR::Type_Package *> *typeChanges;

  std::map<const IR::Argument *, const IR::Type_Declaration *> changedArguments;

public:
  FindChangedSignatures(
      StateInfos *infos,
      std::map<const IR::Type_Declaration *, const IR::Type_Declaration *>
          *signatureChanges,
      std::map<const IR::Type_Package *, const IR::Type_Package *> *typeChanges)
      : infos(infos), signatureChanges(signatureChanges),
        typeChanges(typeChanges) {}

  void postorder(const IR::Argument *arg) override {
    auto tp = infos->typeMap->getType(arg);
    if (tp->is<IR::Type_Parser>() || tp->is<IR::Type_Control>()) {
      auto td = tp->to<IR::Type_Declaration>();
      auto I = signatureChanges->find(td);
      if (I != signatureChanges->end()) {
        LOG4("changing argument type " << arg);
        changedArguments[arg] = I->second;
      }
    }
  }
  void postorder(const IR::Declaration_Instance *di) override {
    auto tp = infos->typeMap->getType(di);
    if (!changedArguments.empty() && tp->is<IR::Type_Package>()) {
      auto packtype = tp->to<IR::Type_Package>();
      auto inst = P4::Instantiation::resolve(di, infos->refMap, infos->typeMap);
      auto newconstructorParms = new IR::ParameterList();
      for (auto p : *inst->constructorParameters) {
        auto arg = inst->substitution.lookup(p);
        const IR::Type *toBeReplaced = p->type;
        if (changedArguments.count(arg)) {
          toBeReplaced = changedArguments[arg];
        }
        auto pclone = p->clone();
        pclone->type = toBeReplaced;
        newconstructorParms->push_back(pclone);
      }
      auto newpack = new IR::Type_Package(packtype->srcInfo, packtype->name,
                                          newconstructorParms);
      LOG4("will change package " << packtype << " (" << ((uint64_t)packtype)
                                  << ")");
      (*typeChanges)[packtype] = newpack;
      changedArguments.clear();
    }
  }
  void postorder(const IR::ConstructorCallExpression *cce) override {
    auto tp = infos->typeMap->getTypeType(cce->constructedType, true);
    if (!changedArguments.empty() && tp->is<IR::Type_Package>()) {
      auto packtype = tp->to<IR::Type_Package>();
      auto inst =
          P4::ConstructorCall::resolve(cce, infos->refMap, infos->typeMap);
      auto newconstructorParms = new IR::ParameterList();
      for (auto p : *inst->constructorParameters) {
        auto arg = inst->substitution.lookup(p);
        const IR::Type *toBeReplaced = p->type;
        if (changedArguments.count(arg)) {
          toBeReplaced = changedArguments[arg];
        }
        auto pclone = p->clone();
        pclone->type = toBeReplaced;
        newconstructorParms->push_back(pclone);
      }
      auto newpack = new IR::Type_Package(packtype->srcInfo, packtype->name,
                                          newconstructorParms);
      (*typeChanges)[packtype] = newpack;
      changedArguments.clear();
    }
  }
};

class DoChangePackages : public Transform {
  StateInfos *infos;
  std::map<const IR::Type_Package *, const IR::Type_Package *> *packageChanges;

public:
  DoChangePackages(StateInfos *infos,
                   std::map<const IR::Type_Package *, const IR::Type_Package *>
                       *packageChanges)
      : infos(infos), packageChanges(packageChanges) {}

  const IR::Node *postorder(IR::Type_Package *tp) override {
    auto tt = infos->typeMap->getTypeType(getOriginal<IR::Type_Package>(), true)
                  ->to<IR::Type_Package>();
    LOG4("looking for package " << tt << " (" << ((uint64_t)tt) << ")");
    LOG4("looking for package " << getOriginal<IR::Type_Package>() << " ("
                                << ((uint64_t)getOriginal<IR::Type_Package>())
                                << ")");
    auto found = packageChanges->find(tt);
    if (found != packageChanges->end()) {
      return found->second;
    }
    return tp;
  }
};

class DoRefactorTypeDeclarations : public Transform {
  StateInfos *infos;
  std::map<const IR::Type_Declaration *, const IR::Type_Declaration *>
      *signatureChanges;

public:
  DoRefactorTypeDeclarations(
      StateInfos *infos,
      std::map<const IR::Type_Declaration *, const IR::Type_Declaration *>
          *signatureChanges)
      : infos(infos), signatureChanges(signatureChanges) {}

  const IR::Node *preorder(IR::Type_Declaration *td) override {
    if (td->is<IR::P4Control>() || td->is<IR::P4Parser>()) {
      auto canon =
          infos->typeMap->getTypeType(getOriginal<IR::Type_Declaration>(), true)
              ->to<IR::Type_Declaration>();
      LOG4("actually " << canon << " (" << ((uint64_t)canon) << ")"
                       << " vs "
                       << ((uint64_t)getOriginal<IR::Type_Declaration>()));
      auto I = signatureChanges->find(canon);
      if (I != signatureChanges->end()) {
        LOG4("refactoring " << getOriginal<IR::Type_Declaration>());
        LOG4("to " << I->second);
        prune();
        return I->second;
      }
    }
    return td;
  }
  profile_t init_apply(const IR::Node *a) override {
    LOG4("to be replaced: ");
    for (auto &s : *signatureChanges) {
      LOG4(s.first << " (" << ((uint64_t)s.first) << ")");
    }
    return Transform::init_apply(a);
  }
};

class MakeTypeNames : public Transform {
  StateInfos *infos;

public:
  MakeTypeNames(StateInfos *infos) : infos(infos) {}

  const IR::Node *postorder(IR::Type_Package *di) override {
    auto nodes = new IR::Vector<IR::Node>;
    auto newparms = new IR::ParameterList();
    for (auto p : *di->constructorParams) {
      // if a type declaration has somehow slipped into
      // a syntactic object, make sure to declare it up front,
      // then rename it
      auto tp = p->type;
      if (auto td = tp->to<IR::Type_Declaration>()) {
        auto nm = td->name;
        auto newname = infos->refMap->newName(nm);
        if (auto tpack = td->to<IR::Type_Package>()) {
          auto tclone = tpack->clone();
          tclone->name = newname;
          nodes->push_back(tclone);
        } else if (auto tparser = td->to<IR::Type_Parser>()) {
          auto tclone = tparser->clone();
          tclone->name = newname;
          nodes->push_back(tclone);
        } else if (auto tcontrol = td->to<IR::Type_Control>()) {
          auto tclone = tcontrol->clone();
          tclone->name = newname;
          nodes->push_back(tclone);
        } else {
          BUG("can't be");
        }
        tp = new IR::Type_Name(di->srcInfo, new IR::Path(di->srcInfo, newname));
      }
      auto pc = p->clone();
      pc->type = tp;
      newparms->push_back(pc);
    }
    di->constructorParams = newparms;
    nodes->push_back(di);
    return nodes;
  }
};

class RefactorPackages : public PassManager {
  StateInfos *infos;
  std::map<const IR::Type_Declaration *, const IR::Type_Declaration *>
      *signatureChanges;
  std::map<const IR::Type_Package *, const IR::Type_Package *> typeChanges;

public:
  RefactorPackages(StateInfos *infos,
                   std::map<const IR::Type_Declaration *,
                            const IR::Type_Declaration *> *signatureChanges)
      : infos(infos), signatureChanges(signatureChanges) {
    setName("MidEnd_refactorpackages");
    passes.push_back(
        new FindChangedSignatures(infos, signatureChanges, &typeChanges));
    passes.push_back(new DoChangePackages(infos, &typeChanges));
    passes.push_back(new DoRefactorTypeDeclarations(infos, signatureChanges));
    passes.push_back(new MakeTypeNames(infos));
    passes.push_back(new P4::ClearTypeMap(infos->typeMap));
    passes.push_back(new P4::TypeChecking(infos->refMap, infos->typeMap, true));
  }
};

class MoveStateToApply : public PassManager {
  StateInfos *infos;
  std::map<const IR::Type_Declaration *, const IR::Type_Declaration *>
      signatureChanges;
  std::map<const IR::Type_Package *, const IR::Type_Package *> typeChanges;

public:
  MoveStateToApply(StateInfos *infos) : infos(infos) {
    setName("MidEnd_movestatetoapply");
    passes.push_back(new FindMoveStateToApply(infos, &signatureChanges));
    passes.push_back(new RefactorPackages(infos, &signatureChanges));
  }
};

class FindAnyExternCall : public Inspector {
  StateInfos *infos;

public:
  FindAnyExternCall(StateInfos *infos) : infos(infos) {}
  void postorder(const IR::MethodCallExpression *mce) override {
    auto mi = P4::MethodInstance::resolve(mce, infos->refMap, infos->typeMap);
    BUG_CHECK(!mi->is<P4::ExternMethod>(),
              "extern method calls should be removed by now, but %1% found",
              mce);
  }
};

class FindExternTypeDeclsInApply : public Inspector {
  StateInfos *infos;
  std::map<const IR::Type_Declaration *, const IR::Type_Declaration *> *changes;
  std::map<const IR::Type_Declaration *, std::vector<const IR::Declaration *>>
      removeInApply;
  std::map<const IR::Type_Declaration *, std::vector<const IR::Declaration *>>
      removeInLocals;
  std::map<const IR::Type_Declaration *, std::vector<const IR::Declaration *>>
      removeInConstructor;

public:
  FindExternTypeDeclsInApply(StateInfos *infos,
                             std::map<const IR::Type_Declaration *,
                                      const IR::Type_Declaration *> *changes)
      : infos(infos), changes(changes) {}

  void postorder(const IR::Declaration *decl) override {
    auto tp = infos->typeMap->getType(decl);
    if (tp->to<IR::Type_Extern>()) {
      if (auto incontrol = findContext<IR::P4Control>()) {
        auto td = infos->typeMap->getTypeType(incontrol->type, true)
                      ->to<IR::Type_Control>();
        auto cl = td->clone();
        // is an apply parameter
        if (auto byName =
                incontrol->getApplyParameters()->getDeclByName(decl->name)) {
          auto parms = cl->getApplyParameters()->clone();
          parms->parameters.removeByName(byName->getName());
          removeInApply[incontrol].emplace_back(decl);
        } else if (incontrol->controlLocals.getDeclaration(decl->name)) {
          removeInLocals[incontrol].emplace_back(decl);
        } else if (incontrol->constructorParams->getDeclByName(
                           decl->name)) {
          removeInConstructor[incontrol].emplace_back(decl);
        }
      } else if (auto inparser = findContext<IR::P4Parser>()) {
        auto td = infos->typeMap->getTypeType(inparser->type, true)
                      ->to<IR::Type_Parser>();
        auto cl = td->clone();
        // is an apply parameter
        if (inparser->getApplyParameters()->getDeclByName(decl->name)) {
          removeInApply[inparser].emplace_back(decl);
        } else if (auto inlocals =
                       inparser->parserLocals.getDeclaration(decl->name)) {
          removeInLocals[inparser].emplace_back(decl);
        } else if (inparser->constructorParams->getDeclByName(decl->name)) {
          removeInConstructor[inparser].emplace_back(decl);
        }
      }
    }
  }
  // FIXME: duplicate code... a looot
  void postorder(const IR::P4Parser *control) override {
    auto IL = removeInLocals.find(control);
    auto IC = removeInConstructor.find(control);
    auto IA = removeInApply.find(control);
    auto controlType =
        infos->typeMap->getTypeType(control->type, true)->to<IR::Type_Parser>();
    auto p4ControlType =
        infos->typeMap->getTypeType(control, true)->to<IR::P4Parser>();

    auto controlTypeClone = controlType->clone();
    auto p4ControlTypeClone = p4ControlType->clone();

    if (IA != removeInApply.end()) {
      // this means that there is need to change: 1) control type 2)
      // P4ControlType
      auto appparms = controlTypeClone->applyParams->clone();
      for (auto d : IA->second) {
        appparms->parameters.removeByName(d->name);
      }
      controlTypeClone->applyParams = appparms;
      (*changes)[controlType] = controlTypeClone;
    }
    if (IC != removeInConstructor.end()) {
      auto consparms = p4ControlTypeClone->constructorParams->clone();
      for (auto d : IC->second) {
        consparms->parameters.removeByName(d->name);
      }
      p4ControlTypeClone->constructorParams = consparms;
    }
    if (IL != removeInLocals.end()) {
      auto localStuff = p4ControlTypeClone->parserLocals.clone();
      for (auto d : IL->second) {
        localStuff->removeByName(d->name);
      }
      p4ControlTypeClone->parserLocals = std::move(*localStuff);
    }
    p4ControlTypeClone->type = controlTypeClone;
    (*changes)[p4ControlType] = p4ControlTypeClone;
  }
  void postorder(const IR::P4Control *control) override {
    auto IL = removeInLocals.find(control);
    auto IC = removeInConstructor.find(control);
    auto IA = removeInApply.find(control);
    auto controlType = infos->typeMap->getTypeType(control->type, true)
                           ->to<IR::Type_Control>();
    auto p4ControlType =
        infos->typeMap->getTypeType(control, true)->to<IR::P4Control>();

    auto controlTypeClone = controlType->clone();
    auto p4ControlTypeClone = p4ControlType->clone();

    if (IA != removeInApply.end()) {
      // this means that there is need to change: 1) control type 2)
      // P4ControlType
      auto appparms = controlTypeClone->applyParams->clone();
      for (auto d : IA->second) {
        appparms->parameters.removeByName(d->name);
      }
      controlTypeClone->applyParams = appparms;
      (*changes)[controlType] = controlTypeClone;
    }
    if (IC != removeInConstructor.end()) {
      auto consparms = p4ControlTypeClone->constructorParams->clone();
      for (auto d : IC->second) {
        consparms->parameters.removeByName(d->name);
      }
      p4ControlTypeClone->constructorParams = consparms;
    }
    if (IL != removeInLocals.end()) {
      auto localStuff = p4ControlTypeClone->controlLocals.clone();
      for (auto d : IL->second) {
        localStuff->removeByName(d->name);
      }
      p4ControlTypeClone->controlLocals = std::move(*localStuff);
    }
    p4ControlTypeClone->type = controlTypeClone;
    (*changes)[p4ControlType] = p4ControlTypeClone;
  }
};

class RemoveExternTypeDeclarations : public PassManager {
  StateInfos *infos;
  std::map<const IR::Type_Declaration *, const IR::Type_Declaration *>
      signatureChanges;
  std::map<const IR::Type_Package *, const IR::Type_Package *> typeChanges;

public:
  RemoveExternTypeDeclarations(StateInfos *infos) : infos(infos) {
    passes.push_back(new FindExternTypeDeclsInApply(infos, &signatureChanges));
    passes.push_back(new RefactorPackages(infos, &signatureChanges));
  }
};

class FindExternsInLocals : public Inspector {
  StateInfos *infos;
  std::map<const IR::IContainer *, std::set<const IR::Declaration_Instance *>>
      *locals;
  std::map<const IR::Declaration_Instance *, const IR::IContainer *> *revLocals;

public:
  FindExternsInLocals(
      StateInfos *infos,
      std::map<const IR::IContainer *,
               std::set<const IR::Declaration_Instance *>> *locals,
      std::map<const IR::Declaration_Instance *, const IR::IContainer *>
          *revLocals)
      : infos(infos), locals(locals), revLocals(revLocals) {}
  void postorder(const IR::Declaration_Instance *instance) override {
    auto ns = findContext<IR::ISimpleNamespace>();
    if (ns && (ns->is<IR::P4Control>() || ns->is<IR::P4Parser>())) {
      LOG4("will make " << instance << " global");
      // make this one global
      (*locals)[ns->to<IR::IContainer>()].emplace(instance);
      (*revLocals)[instance] = ns->to<IR::IContainer>();
    }
  }
};

class MkExternsGlobal : public Transform {
  StateInfos *infos;
  std::map<const IR::IContainer *, std::set<const IR::Declaration_Instance *>>
      *locals;
  std::map<const IR::Declaration_Instance *, const IR::IContainer *> *revLocals;

public:
  MkExternsGlobal(StateInfos *infos,
                  std::map<const IR::IContainer *,
                           std::set<const IR::Declaration_Instance *>> *locals,
                  std::map<const IR::Declaration_Instance *,
                           const IR::IContainer *> *revLocals)
      : infos(infos), locals(locals), revLocals(revLocals) {}

  const IR::Node *handle(const IR::IContainer *ct) {
    auto container = getOriginal<IR::IContainer>();
    auto vec = new IR::Vector<IR::Node>;
    auto I = locals->find(container);
    if (I != locals->end()) {
      for (auto decl : I->second) {
        auto cl = decl->clone();
        cl->srcInfo = container->getSourceInfo();
        cl->name = (cstring)(container->getName().name + "_" + cl->name.name);
        vec->push_back(cl);
      }
      vec->push_back(ct->getNode());
      return vec;
    }
    return container->getNode();
  }
  const IR::Node *postorder(IR::PathExpression *pathExpression) override {
    auto ref = infos->refMap->getDeclaration(pathExpression->path);
    if (auto di = ref->to<IR::Declaration_Instance>()) {
      auto I = revLocals->find(di);
      if (I != revLocals->end()) {
        auto newpath = pathExpression->path->clone();
        newpath->name =
            (cstring)(I->second->getName().name + "_" + newpath->name.name);
        pathExpression->path = newpath;
      }
    }
    return pathExpression;
  }
  const IR::Node *postorder(IR::Declaration_Instance *instance) override {
    if (revLocals->count(getOriginal<IR::Declaration_Instance>()))
      return nullptr;
    return instance;
  }
  const IR::Node *postorder(IR::P4Control *control) override {
    return handle(control);
  }
  const IR::Node *postorder(IR::P4Parser *parser) override {
    return handle(parser);
  }
};
}

analysis::MakeStateless::MakeStateless(P4::ReferenceMap *refMap,
                                       P4::TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap), info(refMap, typeMap),
      behaviors(refMap, typeMap) {
  setName("MidEnd_make_stateless");
  passes.push_back(new P4::ResolveReferences(refMap, true));
  passes.push_back(new P4::ClearTypeMap(typeMap));
  passes.push_back(new P4::TypeChecking(refMap, typeMap, true));
  passes.push_back(new FindStateInfo(&info));
  passes.push_back(new DeclareState(&info));
  passes.push_back(new MakeExternBehavior(&info, &behaviors));
  passes.push_back(new AddExternDeclarations(&info));
  passes.push_back(new RemoveExternMethods(&info));
  passes.push_back(new P4::ClearTypeMap(typeMap));
  passes.push_back(new P4::TypeChecking(refMap, typeMap, true));
  //  passes.push_back(new MoveStateToApply(&info));

  auto locals = new std::map<const IR::IContainer *,
                             std::set<const IR::Declaration_Instance *>>();
  auto revLocals =
      new std::map<const IR::Declaration_Instance *, const IR::IContainer *>();
  passes.push_back(new FindExternsInLocals(&info, locals, revLocals));
  passes.push_back(new MkExternsGlobal(&info, locals, revLocals));
  //    passes.push_back(new RemoveExternTypeDeclarations(&info));
  passes.push_back(new P4::ClearTypeMap(typeMap));
  passes.push_back(new P4::TypeChecking(refMap, typeMap, false));
}
