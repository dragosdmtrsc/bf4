//
// Created by dragos on 20.01.2019.
//

#ifndef P4C_INFER_H
#define P4C_INFER_H

#include "analysis_context.h"
#include "cegis.h"
#include "cfg_algos.h"
#include "fixes.h"
#include <chrono>
#include <common/resolveReferences/referenceMap.h>
#include <fstream>
#include <p4/typeMap.h>
#include <z3++.h>

namespace analysis {

class PrintTableStats : public Inspector {
  std::set<const IR::P4Table *> tables;

public:
  bool preorder(const IR::P4Table *tab) override;
};

class DoInfer : public Inspector {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  std::ofstream ofs, output_ofs;
  std::map<node_t, std::vector<const IR::Expression *>> *fixes;
  bool optimize;

  bool preorder(const IR::P4Parser *parser) override;

public:
  DoInfer(P4::ReferenceMap *refMap, P4::TypeMap *typeMap, cstring out_file,
          std::map<node_t, std::vector<const IR::Expression *>> *fixes,
          bool optimize)
      : refMap(refMap), typeMap(typeMap), ofs("infer.txt"),
        output_ofs(out_file), fixes(fixes), optimize(optimize) {}
};

class Verify : public Inspector {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  bool p4v_style = true;
  bool vera_style = false;
  bool preorder(const IR::P4Parser *parser) override;

public:
  Verify(P4::ReferenceMap *refMap, P4::TypeMap *typeMap, bool p4v_style,
         bool vera_style)
      : refMap(refMap), typeMap(typeMap), p4v_style(p4v_style),
        vera_style(vera_style) {}
};

class Infer : public PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  std::ofstream fix_file;
  std::map<node_t, std::vector<const IR::Expression *>> simple_fixes;
  std::map<std::pair<cstring, cstring>, std::vector<const IR::Expression *>>
      fixes;
  const IR::P4Program *&old_program;
  DoFixOldProgram *fix_gen;

public:
  Infer(P4::ReferenceMap *refMap, P4::TypeMap *typeMap, cstring out_file,
        const IR::P4Program *&old_program, cstring fixed_file, bool optimize);
};
}

#endif // P4C_INFER_H
