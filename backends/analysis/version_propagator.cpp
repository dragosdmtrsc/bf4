//
// Created by dragos on 18.12.2018.
//

#include "version_propagator.h"
#include "analysis_helpers.h"
#include <frontends/common/resolveReferences/referenceMap.h>
#include <frontends/p4/typeMap.h>

const IR::Type *analysis::get_type(const analysis::MemPath &path,
                                   const P4::TypeMap *typeMap, bool replace) {
  if (replace && path.decl->getAnnotation(analysis::AnalysisLibrary::instance.mutablePacket.name)) {
    return new IR::Type_Name(analysis::AnalysisLibrary::instance.mutablePacket.name);
  }
  auto decl = typeMap->getType(path.decl->to<IR::Declaration>());
  for (auto cp : path.path) {
    if (cp.is_num()) {
      decl = typeMap->getType(decl->to<IR::Type_Stack>()->elementType)
        ->to<IR::Type_Type>()
        ->type;
    } else {
      auto strt = decl->to<IR::Type_StructLike>();
      if (cp.str == "isValid")
        return IR::Type_Boolean::get();
      auto fld = strt->getDeclByName(cp.str)->to<IR::StructField>();
      if (fld != nullptr)
        decl = typeMap->getType(fld);
    }
  }
  return decl;
}

cstring analysis::to_string(const analysis::MemPath &adj) {
  std::stringstream sstr;
  sstr << '.' << adj.decl->getName().name << "_" << id(adj.decl);
  for (auto cp : adj.path) {
    if (cp.is_num()) {
      sstr << '[' << cp.nr << ']';
    } else {
      sstr << '.' << cp.str;
    }
  }
  return sstr.str();
}
