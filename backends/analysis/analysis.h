//
// Created by dragos on 09.03.2020.
//

#ifndef P4C_ANALYSIS_H
#define P4C_ANALYSIS_H

#include <common/options.h>
#include <boost/algorithm/string.hpp>

namespace analysis {
class Options : public CompilerOptions {
public:
  bool usePacket = false;
  cstring graphsDir{"."};
  cstring slash_file = "";
  cstring dump_instrumented = "";
  cstring commands = "";
  cstring commandsOutput = "";
  bool slash_generate = false;
  bool instrument_keys = true;
  bool instrument_ifs = true;
  bool with_control = false;
  bool handle_revived = false;
  bool instrument_only = false;
  bool no_instrument = false;
  bool with_defaults = false;
  bool verify_only = false;
  bool p4v_style = true;
  bool vera_style = false;
  bool optimize = false;
  bool render_only = false;
  cstring fixes;
  cstring spec;
  cstring renderIntegration;
  cstring integrationTemplate = "./psa_integration.p4";
  cstring cleanupTofino;
  cstring expand_to;
  std::vector<std::pair<std::string, std::string>> parser_invariants;
  bool serve = false;
  boost::optional<std::pair<std::string, unsigned>> serverAddress;

  cstring generatePacket;
  bool noslice = false;

  Options();
};
using AnalysisContext = P4CContextWithOptions<Options>;

}

#endif //P4C_ANALYSIS_H
