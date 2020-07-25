//
// Created by dragos on 05.06.2019.
//

#ifndef P4C_RENDERTEMPLATE_H
#define P4C_RENDERTEMPLATE_H

#include <common/resolveReferences/referenceMap.h>
#include <p4/evaluator/evaluator.h>
#include <p4/typeMap.h>

namespace analysis {
typedef std::map<const IR::CompileTimeValue *, std::vector<const IR::Node *>>
    instance_tree;
class RenderTemplate : public PassManager {
  static std::map<std::string, std::vector<std::string>> COMPONENTS;

  std::set<std::string> declared;
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  cstring templateFile;
  cstring out;
  P4::Evaluator *evaluator;
  void render();
  void renderTofino();
  void renderv1();
  const IR::IContainer *find_container(instance_tree &nodes,
                             const std::vector<std::string> &path);
  const IR::CompileTimeValue *find_compile_time_value(instance_tree &nodes,
                                       const std::vector<std::string> &path);
  std::string declare(instance_tree &nodes, const std::string &name,
  const std::map<std::string, std::vector<std::string>> &);
  std::string implement(std::vector<std::string> stuff, std::string templ);
  std::string type_name(const IR::Parameter *parm);
  std::string type_name(const IR::Type *parm);

public:
  RenderTemplate(P4::ReferenceMap *refMap, P4::TypeMap *typeMap,
                 const cstring &templateFile, cstring out);
};
}

#endif // P4C_RENDERTEMPLATE_H
