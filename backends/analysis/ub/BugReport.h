//
// Created by dragos on 28.11.2019.
//

#ifndef P4C_BUGREPORT_H
#define P4C_BUGREPORT_H

#include <common/resolveReferences/referenceMap.h>
#include <ir/visitor.h>
#include <p4/typeMap.h>

namespace analysis {
struct bug_report_options {
  cstring packet_file;
};

class BugReport : public PassManager {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;
  bug_report_options bugReportOptions;
public:
  BugReport(P4::ReferenceMap *refMap, P4::TypeMap *typeMap, bug_report_options);
  void analyzeProgram(const IR::P4Program *program);
};
}

#endif // P4C_BUGREPORT_H
