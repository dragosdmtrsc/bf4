# Copyright 2013-present Barefoot Networks, Inc.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Makefile for a backend that generates code for the Behavioral Model version 2 (BMv2)
# compiling for the simple_switch target.

# sources for backend executable

set (THRIFT_SRCS gen-cpp/p4_api_constants.cpp gen-cpp/p4_api_constants.h
        gen-cpp/p4_api_types.cpp gen-cpp/p4_api_types.h
        gen-cpp/p4_service.cpp gen-cpp/p4_service.h)

set (ANALYSIS_SRCS analysis.cpp
        solver.cpp sovler.h
        cegis.cpp cegis.h
        smt_helpers.h smt_helpers.cpp cfg_algos.cpp cfg_algos.h
        analysis_helpers.h versions.h version_propagator.cpp version_propagator.h
        v1_integrator.cpp v1_integrator.h
        constprop/constant_propagation.cpp constprop/constant_propagation.h
        analysis_helpers.cpp
        instrumentation_helper.cpp instrumentation_helper.h
        ExternSpecialization.cpp ExternSpecialization.h MakeStateless.cpp MakeStateless.h PackageSpecialization.cpp
        PackageSpecialization.h RemoveTableCalls.cpp RemoveTableCalls.h RemoveBuiltins.cpp RemoveBuiltins.h HandleStacks.cpp
        HandleStacks.h ParsersUnroll.cpp ParsersUnroll.h SpecializeExternFunctions.cpp SpecializeExternFunctions.h
        HandleHeaders.cpp HandleHeaders.h InlineActionsInControls.cpp
        InlineActionsInControls.h
        InstantiatePackageModels.cpp InstantiatePackageModels.h
        DependencyGraph.cpp DependencyGraph.h DataDependencies.cpp
        DataDependencies.h RenderTemplate.cpp RenderTemplate.h
        MakeImplementations.cpp MakeImplementations.h
        dj_set_expl.cpp dj_set_expl.h
        Interpreter.cpp Interpreter.h RenameMethods.cpp RenameMethods.h TypeConstructors.cpp TypeConstructors.h
        vTypeChecker.cpp vTypeChecker.h vTypeUnification.cpp vTypeUnification.h vTypeConstraints.cpp vTypeConstraints.h
        vImplementationMap.cpp vImplementationMap.h
        commands/CommandParser.cpp commands/CommandParser.h commands/InstantiateCommands.cpp commands/InstantiateCommands.h
        ub/ExplicitUB.cpp ub/ExplicitUB.h context/Context.cpp context/Context.h context/InterproceduralCFGs.cpp
        context/InterproceduralCFGs.h
        lattice/Lattice.cpp lattice/Lattice.h ub/UBLattice.cpp ub/UBLattice.h
        ub/StorageLattice.cpp ub/StorageLattice.h
        mutexhdrs/MutexInstrument.cpp mutexhdrs/MutexInstrument.h
        ub/ssa.cpp ub/ssa.h
        ub/PropagateFormulas.cpp ub/PropagateFormulas.h
        ub/loop.cpp ub/loop.h ub/variables.cpp ub/variables.h
        ub/AnalysisContext.cpp ub/AnalysisContext.h
        constprop/ConstantPropagation.cpp constprop/ConstantPropagation.h
        ub/IOLattice.cpp ub/IOLattice.h bvset/bvset.cpp bvset/bvset.h
        ub/ReachingDefinitions.cpp ub/ReachingDefinitions.h
        constprop/ConstantPropagationAgain.cpp constprop/ConstantPropagationAgain.h ImplementPacket.cpp
        ImplementPacket.h VersionedExpression.cpp VersionedExpression.h ub/BugReport.cpp ub/BugReport.h
        analysis_server/ProgramDatabase.cpp analysis_server/ProgramDatabase.h
        ${THRIFT_SRCS} analysis_server/DatabaseServer.cpp analysis_server/DatabaseServer.h
        template/GenerateMethods.cpp template/GenerateMethods.h ub/ControlLattice.cpp ub/ControlLattice.h
        ub/symbex.cpp ub/symbex.h ub/bmv2/EgressSpecNotSet.cpp ub/bmv2/EgressSpecNotSet.h ub/ExpressionCanonicalizer.cpp ub/ExpressionCanonicalizer.h ub/RemovePacketLookahead.cpp ub/RemovePacketLookahead.h versions.cpp ub/KeyAdder.cpp ub/KeyAdder.h tofino/TofinoIntegration.cpp tofino/TofinoIntegration.h analysis.h)
set (ANALYSIS_HDRS analysis.h)


add_cpplint_files(${CMAKE_CURRENT_SOURCE_DIR} "${ANALYSIS_SRCS};${ANALYSIS_HDRS}")
build_unified(ANALYSIS_SRCS ALL)
add_executable(p4c-analysis ${ANALYSIS_SRCS} ${EXTENSION_P4_14_CONV_SOURCES})
find_program(Z3 z3)

find_library(Z3_LIB z3 libz3)
find_library(THRIFT_LIB libthrift.so thrift)
message(${Z3_LIB})
add_dependencies(p4c-analysis genIR)
add_dependencies(p4c-analysis p4c-graphs)
add_dependencies(p4c-analysis bm2ss midend)

target_link_libraries (p4c-analysis ${P4C_LIBRARIES} ${P4C_LIB_DEPS} ${Z3_LIB} ${THRIFT_LIB} bm2ss midend)


install (TARGETS p4c-analysis
        RUNTIME DESTINATION ${P4C_RUNTIME_OUTPUT_DIRECTORY})
set(IR_DEF_FILES ${IR_DEF_FILES} ${CMAKE_CURRENT_SOURCE_DIR}/analysistypes.def PARENT_SCOPE)
set(EXTENSION_FRONTEND_SOURCES "${EXTENSION_FRONTEND_SOURCES};${CMAKE_CURRENT_SOURCE_DIR}/ir.cpp" PARENT_SCOPE)

# This link is not required but it is convenient to have access to this
# backend in the top-level build directory, along with all the other backends.
add_custom_target(linkanalysis
        COMMAND ${CMAKE_COMMAND} -E create_symlink ${CMAKE_CURRENT_BINARY_DIR}/p4c-analysis ${P4C_BINARY_DIR}/p4c-analysis
        )
add_custom_target(cptemplate ALL
        #FIXME -- should only run this when headers change -- how to accomplish that?
        COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_SOURCE_DIR}/psa_integration.p4 ${P4C_BINARY_DIR}/psa_integration.p4
        COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_SOURCE_DIR}/v1_integration.p4 ${P4C_BINARY_DIR}/v1_integration.p4
        COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_SOURCE_DIR}/tna_ig_integration.p4 ${P4C_BINARY_DIR}/tna_ig_integration.p4
        )

#add_dependencies(p4c_driver linkgraphs)