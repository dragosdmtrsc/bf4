/*
Copyright 2016 VMware, Inc.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

#ifndef _MIDEND_PARSERUNROLL_H_
#define _MIDEND_PARSERUNROLL_H_

#include <p4/parserCallGraph.h>
#include <lib/path.h>
#include <lib/nullstream.h>
#include <boost/algorithm/string.hpp>
#include "ir/ir.h"
#include "frontends/common/resolveReferences/referenceMap.h"
#include "frontends/p4/typeChecking/typeChecker.h"
#include "frontends/p4/typeMap.h"
#include "frontends/p4/callGraph.h"
#include "interpreter.h"
#include<fstream>
#include <p4/simplifyParsers.h>

namespace P4 {

//////////////////////////////////////////////
// The following are for a single parser

// Information produced for a parser state by the symbolic evaluator
struct ParserStateInfo {
    const IR::P4Parser*    parser;
    const IR::ParserState* state;  // original state this is produced from
    const ParserStateInfo* predecessor;  // how we got here in the symbolic evaluation
    cstring                name;  // new state name
    ValueMap*              before;
    ValueMap*              after;

    ParserStateInfo(cstring name, const IR::P4Parser* parser, const IR::ParserState* state,
                    const ParserStateInfo* predecessor, ValueMap* before) :
            parser(parser), state(state), predecessor(predecessor),
            name(name), before(before), after(nullptr)
    { CHECK_NULL(parser); CHECK_NULL(state); CHECK_NULL(before); }
};

// Information produced for a parser by the symbolic evaluator
class ParserInfo {
    // for each original state a vector of states produced by unrolling
    std::map<cstring, std::vector<ParserStateInfo*>*> states;
 public:
    const std::vector<ParserStateInfo*>* get(cstring origState) const {
        std::vector<ParserStateInfo*> *vec;
        auto it = states.find(origState);
        if (it == states.end()) {
            return nullptr;
        } else {
            vec = it->second;
        }
        return vec;
    }

    std::vector<ParserStateInfo*>* get(cstring origState) {
        std::vector<ParserStateInfo*> *vec;
        auto it = states.find(origState);
        if (it == states.end()) {
            vec = new std::vector<ParserStateInfo*>;
            states.emplace(origState, vec);
        } else {
            vec = it->second;
        }
        return vec;
    }
    void add(ParserStateInfo* si) {
        cstring origState = si->state->name.name;
        auto vec = get(origState);
        vec->push_back(si);
    }
};

typedef CallGraph<const IR::ParserState*> StateCallGraph;

// Information about a parser in the input program
class ParserStructure {
    std::map<cstring, const IR::ParserState*> stateMap;
    StateCallGraph* callGraph;
 public:
    const IR::P4Parser*    parser;
    const IR::ParserState* start;
    const ParserInfo*      result;
    void setParser(const IR::P4Parser* parser) {
        CHECK_NULL(parser);
        callGraph = new StateCallGraph(parser->name);
        this->parser = parser;
        start = nullptr;
    }
    void addState(const IR::ParserState* state)
    { stateMap.emplace(state->name, state); }
    const IR::ParserState* get(cstring state) const
    { return ::get(stateMap, state); }
    void calls(const IR::ParserState* caller, const IR::ParserState* callee)
    { callGraph->calls(caller, callee); }
    void rmCall(const IR::ParserState* caller, const IR::ParserState* callee) {
        auto callees = callGraph->getCallees(caller);
        if (callees) {
            auto IT = std::find(callees->begin(), callees->end(), callee);
            if (IT != callees->end())
                callees->erase(IT);
        }
    }
    bool hasCallees(const IR::ParserState* caller) {
        if (caller) {
            auto callees = callGraph->getCallees(caller);
            return callees && !callees->empty();
        }
        return false;
    }

    void analyze(ReferenceMap* refMap, TypeMap* typeMap, bool unroll, bool verbose = true);
};

class AnalyzeParser : public Inspector {
    const ReferenceMap* refMap;
    ParserStructure*    current;
 public:
    AnalyzeParser(const ReferenceMap* refMap, ParserStructure* current) :
            refMap(refMap), current(current) {
        CHECK_NULL(refMap); CHECK_NULL(current); setName("AnalyzeParser");
        visitDagOnce = false;
    }

    bool preorder(const IR::ParserState* state) override;
    void postorder(const IR::PathExpression* expression) override;
};

class SubParserSpec {
public:
    virtual bool contains(const IR::P4Parser *, const IR::ParserState *, const IR::ParserState *) const = 0;
};

class TakeAllSubparserSpec final : public SubParserSpec {
public:
    bool contains(const IR::P4Parser *, const IR::ParserState *, const IR::ParserState *) const override {
        return true;
    }
};

class SimpleSubparserSpec : public SubParserSpec {
    mutable ordered_map<cstring, ordered_set<std::pair<cstring, cstring> > > filtered_transitions;
public:
    static SubParserSpec *fromFile(cstring file) {
        ordered_map<cstring, ordered_set<std::pair<cstring, cstring> > > filtered;
        auto path = Util::PathName(file);
        auto in = std::ifstream(path.toString());
        if (!in.is_open()) {
            ::error("Failed to open file %1%", path.toString());
            return nullptr;
        }
        std::string line = "";
        while (getline(in, line)) {
            std::vector<std::string> vec;
            boost::algorithm::split(vec, line, boost::is_any_of(","));
            if (vec.size() == 3) {
                filtered[vec[0]].emplace(vec[1], vec[2]);
            } else {
                WARNING("skipping bad input in slash file " << line);
            }
        }
        if (filtered.empty()) {
            return new TakeAllSubparserSpec;
        } else {
            return new SimpleSubparserSpec(std::move(filtered));
        }
    }

    SimpleSubparserSpec(ordered_map<cstring, ordered_set<std::pair<cstring, cstring> > > &&filtered_transitions) :
            filtered_transitions(filtered_transitions) {}

    bool contains(const IR::P4Parser *parser, const IR::ParserState *from, const IR::ParserState *to) const override {
        return filtered_transitions[parser->getName().originalName].count(std::make_pair(from->getName().originalName,
                                         to->getName().originalName)) == 0;
    }
};

class SlashParser : public Transform {
    const ReferenceMap* refMap;
    const SubParserSpec *spec;
public:
    SlashParser(const ReferenceMap* refMap, const SubParserSpec *spec) :
            refMap(refMap), spec(spec) {
        CHECK_NULL(refMap); setName("SlashParser");
        visitDagOnce = false;
    }

    const IR::Node *postorder(IR::PathExpression* path) override;
};

#if 1
class ParserUnroller : public Transform {
    ReferenceMap*    refMap;
    TypeMap*         typeMap;
    ParserStructure* parser;
 public:
    ParserUnroller(ReferenceMap* refMap, TypeMap* typeMap, ParserStructure* parser) :
            refMap(refMap), typeMap(typeMap), parser(parser) {
        CHECK_NULL(refMap); CHECK_NULL(typeMap); CHECK_NULL(parser);
        setName("ParserUnroller");
        visitDagOnce = false;
    }

    const IR::Node *postorder(IR::P4Parser *) override;
};
#endif


class ParserAnalyzer : public PassManager {
public:
    ParserStructure  current;

    ParserAnalyzer(ReferenceMap* refMap, TypeMap* typeMap) {
        CHECK_NULL(refMap); CHECK_NULL(typeMap);

        passes.push_back(new AnalyzeParser(refMap, &current));
        passes.push_back(new VisitFunctor (
                [this, refMap, typeMap](const IR::Node* root) -> const IR::Node* {
                    current.analyze(refMap, typeMap, false, false);
                    return root;
                }));
    }

    ValueMap *getValues() const {
        auto accept = current.result->get(IR::ParserState::accept);
        if (!accept)
            return nullptr;
        return accept->back()->before;
    }

    Visitor::profile_t init_apply(const IR::Node* node) override {
        LOG1("Scanning " << node);
        BUG_CHECK(node->is<IR::P4Parser>(), "%1%: expected a parser", node);
        current.parser = node->to<IR::P4Parser>();
        return PassManager::init_apply(node);
    }
};

// Applied to a P4Parser object.
class ParserRewriter : public PassManager {
public:
    ParserStructure  current;

    ParserRewriter(ReferenceMap* refMap, TypeMap* typeMap, bool unroll) {
        CHECK_NULL(refMap); CHECK_NULL(typeMap);

        passes.push_back(new AnalyzeParser(refMap, &current));
        passes.push_back(new VisitFunctor (
            [this, refMap, typeMap, unroll](const IR::Node* root) -> const IR::Node* {
                current.analyze(refMap, typeMap, unroll);
                return root;
            }));
#if 0
        if (unroll)
            passes.push_back(new ParserUnroller(refMap, typeMap, &current));
#endif
    }
    Visitor::profile_t init_apply(const IR::Node* node) override {
        LOG1("Scanning " << node);
        BUG_CHECK(node->is<IR::P4Parser>(), "%1%: expected a parser", node);
        current.parser = node->to<IR::P4Parser>();
        return PassManager::init_apply(node);
    }
};

///////////////////////////////////////////////////////
// The following are applied to the entire program

class RewriteAllParsers : public Transform {
    ReferenceMap* refMap;
    TypeMap*      typeMap;
    bool          unroll;
 public:
    RewriteAllParsers(ReferenceMap* refMap, TypeMap* typeMap, bool unroll) :
            refMap(refMap), typeMap(typeMap), unroll(unroll)
    { CHECK_NULL(refMap); CHECK_NULL(typeMap); }
    const IR::Node* postorder(IR::P4Parser* parser) override {
        ParserRewriter rewriter(refMap, typeMap, unroll);
        return parser->apply(rewriter);
    }
};

class ParserSlash : public PassManager {
    ParserCallGraph transitions;
    SubParserSpec *slash_spec;
public:
    ParserSlash(ReferenceMap* refMap, TypeMap* typeMap, SubParserSpec *slash_spec) :
            transitions("transitions"), slash_spec(slash_spec) {
        passes.push_back(new TypeChecking(refMap, typeMap));
        passes.push_back(new SlashParser(refMap, slash_spec));
        passes.push_back(new TypeChecking(refMap, typeMap));
        passes.push_back(new ComputeParserCG(refMap, &transitions));
        passes.push_back(new P4::SimplifyParsers(refMap));
        setName("ParserSlash");
    }
};

class ParsersUnroll : public PassManager {
public:
    ParsersUnroll(bool unroll, ReferenceMap* refMap, TypeMap* typeMap) {
        passes.push_back(new TypeChecking(refMap, typeMap));
        passes.push_back(new RewriteAllParsers(refMap, typeMap, unroll));
        setName("ParsersUnroll");
    }
};

}  // namespace P4

#endif /* _MIDEND_PARSERUNROLL_H_ */
