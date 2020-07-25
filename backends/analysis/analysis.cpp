//
// Created by dragos on 27.09.2018.
//

#include "analysis.h"
#include "DependencyGraph.h"
#include "ExternSpecialization.h"
#include "HandleHeaders.h"
#include "HandleStacks.h"
#include "ImplementPacket.h"
#include "InlineActionsInControls.h"
#include "InstantiatePackageModels.h"
#include "Interpreter.h"
#include "MakeImplementations.h"
#include "MakeStateless.h"
#include "PackageSpecialization.h"
#include "RemoveBuiltins.h"
#include "RemoveTableCalls.h"
#include "RenameMethods.h"
#include "RenderTemplate.h"
#include "SpecializeExternFunctions.h"
#include "fixes.h"
#include "infer.h"
#include "instrumentation_helper.h"
#include "sovler.h"
#include "v1_integrator.h"
#include "vTypeChecker.h"
#include <analysis/analysis_server/DatabaseServer.h>
#include <analysis/analysis_server/ProgramDatabase.h>
#include <analysis/commands/CommandParser.h>
#include <analysis/commands/InstantiateCommands.h>
#include <analysis/mutexhdrs/MutexInstrument.h>
#include <analysis/ub/BugReport.h>
#include <analysis/ub/ExplicitUB.h>
#include <common/applyOptionsPragmas.h>
#include <common/parseInput.h>
#include <graphs/controls.h>
#include <graphs/parsers.h>
#include <lib/crash.h>
#include <midend/complexComparison.h>
#include <midend/copyStructures.h>
#include <midend/eliminateTuples.h>
#include <midend/expandEmit.h>
#include <midend/nestedStructs.h>
#include <midend/parserUnroll.h>
#include <p4/actionsInlining.h>
#include <p4/createBuiltins.h>
#include <p4/inlining.h>
#include <p4/removeReturns.h>
#include <p4/simplifyDefUse.h>
#include <p4/toP4/toP4.h>

#include <analysis/tofino/TofinoIntegration.h>
#include <analysis/ub/bmv2/EgressSpecNotSet.h>
#include <thrift/protocol/TBinaryProtocol.h>
#include <thrift/server/TSimpleServer.h>
#include <thrift/transport/TBufferTransports.h>
#include <thrift/transport/TServerSocket.h>

#undef __PROFILE__
#ifdef __PROFILE__
#include <valgrind/callgrind.h>
#endif

using namespace ::apache::thrift;
using namespace ::apache::thrift::protocol;
using namespace ::apache::thrift::transport;
using namespace ::apache::thrift::server;

using boost::shared_ptr;

using namespace ::p4_thrift;

namespace analysis {

class AF4Frontend {
  Options &options;
  P4::ReferenceMap refMap;
  P4::TypeMap typeMap;

public:
  AF4Frontend(Options &options) : options(options) {}

  const IR::P4Program *run(const IR::P4Program *parsedProgram) {
    P4::ParseAnnotations::HandlerMap handlers = {PARSE("model", Expression),
                                                 PARSE("impl", Expression)};
    P4::ParseAnnotations pe("analysis", true, handlers, true);
    auto pab = new ParseAnnotationBodies(&pe, &typeMap);
    auto thisevaluator = new P4::Evaluator(&refMap, &typeMap);
    std::ofstream logger("log.p4");
    PassManager passManager(
        {pab,
         new P4::CreateBuiltins(),
         new CreateAnalysisHelpers(),
         new DoCreateMutablePacket(),
         new DoAddErrorField,
         new P4::UniqueNames(&refMap),
         new P4::MoveDeclarations(),
         new P4::MoveInitializers(),
         new P4::ResolveReferences(&refMap),
         new P4::TypeInference(&refMap, &typeMap, false),
         new RenameParameters(&refMap, &typeMap),
         new analysis::CastReplace(&refMap, &typeMap),
         new P4::RemoveReturns(&refMap),
         new P4::ResolveReferences(&refMap),
         new P4::TypeInference(&refMap, &typeMap, false),
         new PassRepeated({new analysis::RemoveTypedefs(&refMap, &typeMap)}),
         new P4::ClearTypeMap(&typeMap),
         new P4::ResolveReferences(&refMap),
         new P4::TypeInference(&refMap, &typeMap, false),
         new HandleHeaders(&refMap, &typeMap),
         new PacketExtract(&refMap, &typeMap),
         new ImplementPacket(&refMap, &typeMap),
         new analysis::RemoveTypedefs(&refMap, &typeMap),
         new P4::ClearTypeMap(&typeMap),
         new P4::ResolveReferences(&refMap),
         new P4::TypeInference(&refMap, &typeMap, false),
         new MaterializeConstants(&refMap, &typeMap),
         new analysis::Normalize(&refMap, &typeMap),
         new analysis::MoveReturnsInward(&refMap, &typeMap),
         new analysis::HandleArrayIndices(&refMap, &typeMap),
         new analysis::MakeMultiAssign(&refMap, &typeMap),
         new analysis::SplitInouts(&refMap, &typeMap),
         new analysis::DisentangleExternParams(&refMap, &typeMap),
         new P4::ToP4(&logger, false)});
    if (options.generatePacket.isNullOrEmpty()) {
    } else {
      // model check
      bug_report_options bug_report_options;
      bug_report_options.packet_file = options.generatePacket;
      passManager.addPasses(
          {new BugReport(&refMap, &typeMap, bug_report_options)});
    }
    passManager.addPasses({thisevaluator});
    passManager.setName("AF4Frontend");
    passManager.addDebugHook(options.getDebugHook(), true);
    passManager.setStopOnError(true);
    parsedProgram = parsedProgram->apply(passManager);
    return parsedProgram;
  }
};

class RenderBackend : public PassManager {
  Options &options;
  P4::ReferenceMap refMap;
  P4::TypeMap typeMap;

public:
  RenderBackend(Options &options) : options(options) {
    setName("RenderBackend");
    std::ifstream f(options.integrationTemplate);
    if (!f.good()) {
      BUG("integration template %1% doesn't exist",
          options.integrationTemplate);
    }
    f.close();
    addPasses(
        {new P4::ResolveReferences(&refMap),
         new P4::TypeInference(&refMap, &typeMap, false),
         new DoCreateMutablePacket, new CreateAnalysisHelpers,
         new RenderTemplate(&refMap, &typeMap, options.integrationTemplate,
                            options.renderIntegration)});
  }
};

class InstrumentBackend : public PassManager {
  Options &options;
  P4::ReferenceMap refMap;
  P4::TypeMap typeMap;
  START(instrumentation);
  END(instrumentation);
  std::ofstream dump_to;

public:
  InstrumentBackend(Options &options)
      : options(options), dump_to(options.dump_instrumented) {
    BUG_CHECK(!options.dump_instrumented.isNullOrEmpty(),
              "expecting option --dump-instrument");
    setName("InstrumentBackend");
    auto evaluator = new P4::EvaluatorPass(&refMap, &typeMap);
    passes.push_back(
        new VisitFunctor([this]() { START_ASG(instrumentation); }));
    addPasses({new P4::ResolveReferences(&refMap),
               new P4::TypeInference(&refMap, &typeMap, false)});
    addPasses({new CreateAnalysisHelpers});
    passes.push_back(new P4::RemoveLeftSlices(&refMap, &typeMap));
    passes.push_back(evaluator);
    passes.push_back(new RemoveV1Controls(&refMap, &typeMap));
    passes.push_back(new GenerateAssertions(
        &refMap, &typeMap, options.instrument_keys, options.instrument_ifs));
    passes.push_back(new P4::ExpandEmit(&refMap, &typeMap));
    for (auto &p : options.parser_invariants) {
      passes.push_back(
          new MutexInstrument(&refMap, &typeMap, p.first, p.second));
    }
    // bmv2 specific instrumentation
    addPasses({new P4::ClearTypeMap(&typeMap),
               new P4::ResolveReferences(&refMap),
               new P4::TypeInference(&refMap, &typeMap, false)});
    passes.push_back(new EgressSpecNotSet(&refMap, &typeMap));
    passes.push_back(new RegistersOutOfBounds(&refMap, &typeMap));
    passes.push_back(new TofinoBugs(&refMap, &typeMap));
    passes.push_back(new P4::ToP4(&dump_to, false));
    passes.push_back(new VisitFunctor([this]() {
      END_ASG(instrumentation);
      LOG3("instrumentation time " << DURATION(instrumentation));
    }));
  }
};

class ExpandBackend : public PassManager {
  Options &options;
  P4::ReferenceMap refMap;
  P4::TypeMap typeMap;
  std::ofstream dump_to;

public:
  ExpandBackend(Options &options)
      : options(options), dump_to(options.expand_to) {
    setName("ExpandBackend");
    auto evaluator = new P4::EvaluatorPass(&refMap, &typeMap);
    addPasses({new P4::ResolveReferences(&refMap),
               new P4::TypeInference(&refMap, &typeMap, false)});
    addPasses({new CreateAnalysisHelpers});
    passes.push_back(new RemoveV1Controls(&refMap, &typeMap));
    passes.push_back(new MakePopulatedTables(&refMap, &typeMap));
    passes.push_back(new RemoveTableCalls(&refMap, &typeMap));
    passes.push_back(new HandleStacks(&refMap, &typeMap));
    passes.push_back(evaluator);
    passes.push_back(new P4::Inline(&refMap, &typeMap, evaluator));
    passes.push_back(new P4::InlineActions(&refMap, &typeMap));
    passes.push_back(new P4::InlineActionsInControls(&refMap, &typeMap));
    passes.push_back(evaluator);
    passes.push_back(new P4::ToP4(&dump_to, false));
  }
};

class CommandsBackend : public PassManager {
  Options &options;
  P4::ReferenceMap refMap;
  P4::TypeMap typeMap;
  std::ofstream dump_to;

public:
  CommandsBackend(Options &options)
      : options(options), dump_to(options.slash_file) {
    setName("CommandsBackend");
    BUG_CHECK(!options.slash_file.isNullOrEmpty(),
              "expecting --slash-file option");
    analysis::CommandParser cmdparser;
    auto cmds = cmdparser.readCommands(options.commands);
    auto all = new Commands(std::move(cmds));
    addPasses({new P4::ResolveReferences(&refMap),
               new P4::TypeInference(&refMap, &typeMap, false),
               new InstantiateCommands(&refMap, &typeMap, *all)});
    passes.push_back(new ToP4(&dump_to, false));
  }
};

class AF4Backend : public PassManager {
  Options &options;
  P4::ReferenceMap refMap;
  P4::TypeMap typeMap;

public:
  AF4Backend(Options &options) : options(options) {
    setName("AF4Backend");
    // af4
    addPasses({new P4::ResolveReferences(&refMap),
               new P4::TypeInference(&refMap, &typeMap, false)});
    if (options.serverAddress) {
      addPasses({new VisitFunctor([&](const IR::Node *prog) {
        analysis::ProgramDatabase programDatabase(
            &refMap, &typeMap, prog->to<IR::P4Program>(), "run");
        std::shared_ptr<DatabaseServer> handler(
            new analysis::DatabaseServer(&programDatabase));
        std::shared_ptr<TProcessor> processor(new p4_serviceProcessor(handler));
        std::shared_ptr<TServerTransport> serverTransport(new TServerSocket(
            options.serverAddress->first, options.serverAddress->second));
        std::shared_ptr<TTransportFactory> transportFactory(
            new TBufferedTransportFactory());
        std::shared_ptr<TProtocolFactory> protocolFactory(
            new TBinaryProtocolFactory());
        TSimpleServer server(processor, serverTransport, transportFactory,
                             protocolFactory);
        server.serve();
        return prog;
      })});
    } else {
      addPasses({new ExplicitUB(&refMap, &typeMap)});
    }
  }
};

class MidEnd : public PassManager {
public:
  START(instrumentation);
  END(instrumentation);

  P4::ReferenceMap refMap;
  P4::TypeMap typeMap;
  IR::ToplevelBlock *toplevel = nullptr;
  std::set<const IR::P4Action *> sureFailures;
  std::set<const IR::Statement *> uselessStatements;
  std::set<const IR::P4Action *> uselessActions;
  const IR::P4Program *old_prog = nullptr;
  std::ofstream *fix_file = nullptr;

  explicit MidEnd(Options &options) {
    bool isv1 = options.langVersion == CompilerOptions::FrontendVersion::P4_14;
    refMap.setIsV1(isv1);
    auto evaluator = new P4::EvaluatorPass(&refMap, &typeMap);
    passes.push_back(new TypeChecking(&refMap, &typeMap));
    passes.push_back(
        new VisitFunctor([this](const IR::Node *program) -> const IR::Node * {
          BUG_CHECK(program->is<IR::P4Program>(), "expected P4Program %1%",
                    program);
          return (old_prog = program->to<IR::P4Program>());
        }));

    if (!options.renderIntegration.isNullOrEmpty()) {
      if (!options.no_instrument) {
        passes.push_back(
            new VisitFunctor([this]() { START_ASG(instrumentation); }));
        passes.push_back(new P4::RemoveLeftSlices(&refMap, &typeMap));
        passes.push_back(evaluator);
        passes.push_back(new GenerateAssertions(&refMap, &typeMap,
                                                options.instrument_keys,
                                                options.instrument_ifs));
        passes.push_back(new P4::ExpandEmit(&refMap, &typeMap));
        for (auto &p : options.parser_invariants) {
          passes.push_back(
              new MutexInstrument(&refMap, &typeMap, p.first, p.second));
        }

        passes.push_back(new RemoveTableCalls(&refMap, &typeMap));
        passes.push_back(new HandleStacks(&refMap, &typeMap));
        passes.push_back(evaluator);
        passes.push_back(new P4::Inline(&refMap, &typeMap, evaluator));
        passes.push_back(new P4::InlineActions(&refMap, &typeMap));
        passes.push_back(new P4::InlineActionsInControls(&refMap, &typeMap));
        passes.push_back(evaluator);
        passes.push_back(new VisitFunctor([this]() {
          END_ASG(instrumentation);
          LOG3("instrumentation time " << DURATION(instrumentation));
        }));
        //        passes.push_back(new RenameMethods(&refMap, &typeMap));
      }
      passes.push_back(new DoCreateMutablePacket);
      passes.push_back(new CreateAnalysisHelpers);
      passes.push_back(new RenderTemplate(&refMap, &typeMap,
                                          options.integrationTemplate,
                                          options.renderIntegration));
      if (!options.render_only) {
        passes.push_back(new VisitFunctor([&, this]() {
          auto old = options.file;
          options.file = options.renderIntegration;
          auto parsedProgram = P4::parseP4File(options);
          AF4Frontend frontend(options);
          frontend.run(parsedProgram);
          options.file = old;
        }));
      }
      passes.push_back(evaluator);
    } else if (!options.spec.isNullOrEmpty()) {
      if (!options.fixes.isNullOrEmpty()) {
        passes.push_back(
            new ToP4(new std::ofstream(options.fixes + ".orig"), false));
      }
      passes.push_back(new PrintTableStats());
      if (!options.dump_instrumented.isNullOrEmpty()) {
        passes.push_back(
            new ToP4(new std::ofstream(options.dump_instrumented), false));
      }
      if (!options.instrument_only && !options.verify_only)
        passes.push_back(new Infer(&refMap, &typeMap, options.spec, old_prog,
                                   options.fixes, options.optimize));
      if (options.verify_only)
        passes.push_back(new Verify(&refMap, &typeMap, options.p4v_style,
                                    options.vera_style));
    } else if (options.commands) {
      analysis::CommandParser cmdparser;
      auto cmds = cmdparser.readCommands(options.commands);
      auto all = new Commands(std::move(cmds));
      passes.push_back(new InstantiateCommands(&refMap, &typeMap, *all));
      passes.push_back(new RemoveTableCalls(&refMap, &typeMap));
      passes.push_back(evaluator);
      passes.push_back(new P4::Inline(&refMap, &typeMap, evaluator));
      passes.push_back(new P4::InlineActions(&refMap, &typeMap));
      passes.push_back(new P4::InlineActionsInControls(&refMap, &typeMap));
      passes.push_back(evaluator);
    }
    addPasses({evaluator, new VisitFunctor([this, evaluator]() {
                 toplevel = evaluator->getToplevelBlock();
               })});
    setName("AnalyzerMidEnd");
  }
  IR::ToplevelBlock *process(const IR::P4Program *&program) {
    program = program->apply(*this);
    return toplevel;
  }
};

analysis::Options::Options() {
  registerOption("--use-packet", nullptr,
                 [this](const char *) {
                   usePacket = true;
                   return true;
                 },
                 "use rich packet model with z3 support");
  registerOption("--serve", nullptr,
                 [this](const char *) {
                   serve = true;
                   serverAddress = std::make_pair<std::string, unsigned>(
                       "localhost", 12345);
                   return true;
                 },
                 "start server");
  registerOption("--server-address", "server_address",
                 [this](const char *arg) {
                   std::vector<std::string> split;
                   boost::split(split, arg, boost::is_any_of(":"));
                   unsigned port = 12345;
                   if (split.size() > 1) {
                     port =
                         static_cast<unsigned int>(std::atoi(split[1].c_str()));
                   }
                   serverAddress = std::make_pair(split[0], port);
                   return true;
                 },
                 "dump packet here");
  registerOption("--generate-packet", "file",
                 [this](const char *arg) {
                   generatePacket = arg;
                   return true;
                 },
                 "dump packet here");
  registerOption("--commands", "file",
                 [this](const char *arg) {
                   commands = arg;
                   return true;
                 },
                 "takes as input a commands file and outputs slashed program "
                 "to slash_file");
  registerOption("--render-integration", "file",
                 [this](const char *arg) {
                   renderIntegration = arg;
                   return true;
                 },
                 "dump integration code");
  registerOption("--no-slice", nullptr,
                 [this](const char *) {
                   noslice = true;
                   return true;
                 },
                 "don't use slicing anymore");
  registerOption("--no-instrument", nullptr,
                 [this](const char *) {
                   no_instrument = true;
                   return true;
                 },
                 "don't instrument");
  registerOption("--render-only", nullptr,
                 [this](const char *) {
                   render_only = true;
                   return true;
                 },
                 "only render template, no af4 run");
  registerOption("--alias-instrument", "alias",
                 [this](const char *arg) {
                   std::string x = arg;
                   auto comma = x.find(',');
                   if (comma != std::string::npos) {
                     auto parser = x.substr(0, comma);
                     auto control = x.substr(comma + 1);
                     parser_invariants.emplace_back(parser, control);
                   }
                   return true;
                 },
                 "do instrumentation for a pair of parser,control. The "
                 "format is parsername,control");
  registerOption(
      "--integration-template", "file",
      [this](const char *arg) {
        integrationTemplate = arg;
        return true;
      },
      "integration template to render (default: ./psa_integration.p4");
  registerOption("--cleanup-tofino", "file",
                 [this](const char *arg) {
                   cleanupTofino = arg;
                   return true;
                 },
                 "cleanup tofino program - i.e. remove RegisterAction");
  registerOption("--optimize", nullptr,
                 [this](const char *) {
                   optimize = true;
                   return true;
                 },
                 "try to optimize inference algo\n");
  registerOption("--verify-only", nullptr,
                 [this](const char *) {
                   verify_only = true;
                   return true;
                 },
                 "only run verification pass\n");
  registerOption("--vera-style", nullptr,
                 [this](const char *) {
                   vera_style = true;
                   return true;
                 },
                 "only run verification pass\n");
  registerOption("--no-p4v-style", nullptr,
                 [this](const char *) {
                   p4v_style = false;
                   return true;
                 },
                 "only run verification pass\n");
  registerOption("--with-defaults", nullptr,
                 [this](const char *) {
                   with_defaults = true;
                   return true;
                 },
                 "case split on default actions\n");
  registerOption("--instrument-only", nullptr,
                 [this](const char *) {
                   instrument_only = true;
                   return true;
                 },
                 "only do instrumentation and stop\n");
  registerOption(
      "--expand-to", "expanded",
      [this](const char *f) {
        expand_to = f;
        return true;
      },
      "enable table call expansion and friends and dump to expanded\n");
  registerOption("--revive-packet", nullptr,
                 [this](const char *) {
                   handle_revived = true;
                   return true;
                 },
                 "instrument packet revived bug - i.e. set egress spec after "
                 "packet has been dropped\n");
  registerOption("--slash-file", "slash_file",
                 [this](const char *arg) {
                   slash_file = arg;
                   return true;
                 },
                 "csv file which describes inhibited parser transitions"
                 "(default is no file = all transitions allowed)\n");
  registerOption("--slash-generate", nullptr,
                 [this](const char *) {
                   slash_generate = true;
                   return true;
                 },
                 "csv file which describes inhibited parser transitions"
                 "(default is no file = all transitions allowed)\n");
  registerOption("--fixes", "fixes",
                 [this](const char *arg) {
                   fixes = arg;
                   return true;
                 },
                 "output file after fixing is complete"
                 "(default is no file = no analysis to be performed)\n");
  registerOption("--infer", "infer_file",
                 [this](const char *arg) {
                   spec = arg;
                   return true;
                 },
                 "output controller spec file"
                 "(default is no file = no analysis to be performed)\n");
  registerOption("--without-keys", nullptr,
                 [this](const char *) {
                   instrument_keys = false;
                   return true;
                 },
                 "instrument table keys"
                 "(default is true)\n");
  registerOption("--without-ifs", nullptr,
                 [this](const char *) {
                   instrument_ifs = false;
                   return true;
                 },
                 "stop if instrumentation"
                 "(default is true)\n");
  registerOption("--with-control", nullptr,
                 [this](const char *) {
                   with_control = true;
                   return true;
                 },
                 "instrument instructions in control flow"
                 "(default is false)\n");
  registerOption("--dump-instrumented", "dump_instrumented",
                 [this](const char *arg) {
                   dump_instrumented = arg;
                   return true;
                 },
                 "instrument instructions in control flow"
                 "(default is false)\n");
}
}; // end analysis

int main(int argc, char **argv) {
  setup_gc_logging();
  setup_signals();

  AutoCompileContext autoAnalysisContext(new ::analysis::AnalysisContext);
  auto &options = ::analysis::AnalysisContext::get().options();
  options.langVersion = CompilerOptions::FrontendVersion::P4_16;
  options.compilerVersion = "0.0.5";

  if (options.process(argc, argv) != nullptr)
    options.setInputFile();
  if (::errorCount() > 0)
    return 1;

  auto hook = options.getDebugHook();

  auto program = P4::parseP4File(options);
  if (program == nullptr || ::errorCount() > 0)
    return 1;

  try {
    P4::P4COptionPragmaParser optionsPragmaParser;
    program->apply(P4::ApplyOptionsPragmas(optionsPragmaParser));
    P4::ParseAnnotations::HandlerMap handlers = {PARSE("model", Expression)};
    P4::ParseAnnotations pe("analysis", true, handlers, true);
    if (!options.renderIntegration.isNullOrEmpty() ||
        !options.commands.isNullOrEmpty() ||
        !options.dump_instrumented.isNullOrEmpty() ||
        !options.expand_to.isNullOrEmpty() ||
        !options.cleanupTofino.isNullOrEmpty()) {
      P4::FrontEnd fe(pe);
      fe.addDebugHook(hook);
      program = fe.run(options, program);
      if (program == nullptr || ::errorCount() > 0)
        return 1;
      PassManager *be = nullptr;
      if (!options.cleanupTofino.isNullOrEmpty()) {
        BUG("tofino backend is not implemented in this version");
        be = new analysis::CleanupTofinoBackend(options.cleanupTofino);
      } else if (!options.renderIntegration.isNullOrEmpty()) {
        be = new analysis::RenderBackend(options);
      } else if (!options.commands.isNullOrEmpty()) {
        be = new analysis::CommandsBackend(options);
      } else if (!options.dump_instrumented.isNullOrEmpty()) {
        be = new analysis::InstrumentBackend(options);
      } else if (!options.expand_to.isNullOrEmpty()) {
        be = new analysis::ExpandBackend(options);
      } else {
        BUG("");
      }
      be->addDebugHook(hook, true);
      program = program->apply(*be);
    } else {
      START(front);
#ifdef __PROFILE__
      CALLGRIND_START_INSTRUMENTATION;
#endif
      std::cerr << "starting frontend\n";
      analysis::AF4Frontend fe(options);
      program = fe.run(program);
#ifdef __PROFILE__
      CALLGRIND_STOP_INSTRUMENTATION;
      CALLGRIND_DUMP_STATS;
#endif
      END(front);
      if (program == nullptr || ::errorCount() > 0)
        return 1;
      std::cerr << "frontend done in " << DURATION(front) << "ms\n";
      // af4
      analysis::AF4Backend backend(options);
      program->apply(backend);
    }
    if (program == nullptr || ::errorCount() > 0)
      return 1;
  } catch (const Util::P4CExceptionBase &bug) {
    std::cerr << bug.what() << std::endl;
    return 1;
  }
  return 0;
}
