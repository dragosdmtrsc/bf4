//
// Created by dragos on 19.01.2019.
//
#include <fstream>
#include <z3++.h>
#include <common/resolveReferences/referenceMap.h>
#include <p4/typeMap.h>
#include <chrono>
#include <midend/interpreter.h>
#include <regex>
#include "cfg_algos.h"
#include "smt_helpers.h"
#include "versions.h"
#include <analysis/constprop/constant_propagation.h>
#include "version_propagator.h"
#include "cegis.h"
#include "fixes.h"

bool analysis::Node2StateAndTable::preorder(const IR::Node *node) {
    auto I = simple_fixes->find(node);
    if (I != simple_fixes->end()) {
        auto asg = node->to<IR::AssignmentStatement>();
        auto lv = asg->left->to<IR::PathExpression>()->path->name.name;
        auto strlv = std::string(lv.c_str());
        auto tab_name = strlv.substr(std::string("pre_call_").size());
        auto control_name = findContext<IR::ParserState>()->name;
        fixes->emplace(make_pair(control_name, tab_name), std::move(I->second));
        return false;
    }
    return true;
}

const IR::Expression *analysis::DoComputeFixes::str_to_expr(const std::string &s) {
    std::string nstring = s;
    if (s.find("controls_") == 0) {
        nstring = s.substr(9);
    }
    nstring = nstring.substr(1);
    bool first = true;
    IR::Expression *ex = nullptr;
    while (!nstring.empty()) {
        auto next_ = nstring.find('.');
        bool last = (next_ == std::string::npos);
        if (last) {
            next_ = nstring.size() - 1;
            while ((nstring[next_] >= '0' && nstring[next_] <= '9') ||
                   nstring[next_] == '_') {
                --next_;
            }
            ++next_;
        }
        auto crt = nstring.substr(0, next_);
        nstring = nstring.substr(next_ + 1);
        if (first) {
            ex = new IR::PathExpression(IR::ID(cstring(crt)));
        } else {
            std::regex rex("(.*?)\\[([0-9]+)\\]");
            std::smatch smatch;
            if (std::regex_match(crt, smatch, rex)) {
                auto mem = smatch[1].str();
                auto nr = std::stoi(smatch[2].str());
                ex = new IR::ArrayIndex(new IR::Member(ex, cstring(mem)), new IR::Constant(nr));
            } else {
                ex = new IR::Member(ex, cstring(crt));
            }
        }
        if (last && crt == "isValid") {
            ex = new IR::MethodCallExpression(ex);
        }
        if (last)
            break;
        first = false;
    }
    return ex;
}

bool analysis::DoComputeFixes::preorder(const IR::P4Parser *parser) {
    auto start_all = std::chrono::system_clock::now();
    auto smttypewrapper = new SmtTypeWrapper(context);
    auto computeTypes = new IRToSmtTypeMap(refMap, typeMap, context, smttypewrapper);
    auto prog = findContext<IR::P4Program>();
    prog->apply(*computeTypes);
    auto fw = graph_computer.get_forward(parser);
    auto bw = analysis::reverse(fw);
    std::map<node_t, analysis::VersionMemory_t *> mem;
    std::map<node_t, P4::ValueMap *> vals;
    std::vector<node_t> sorted;
    analysis::constant_propagate(parser, parser->parserLocals, fw, &vals, &sorted, refMap, typeMap);
    for (auto I = fw->begin(); I != fw->end();) {
        auto crt = I->first;
        bool eraseI = false;
        if (!vals.count(crt)) {
            eraseI = true;
        }
        if (!eraseI) {
            for (auto J = I->second.begin(); J != I->second.end(); ) {
                if (!vals.count(J->first)) {
                    J = I->second.erase(J);
                } else {
                    ++J;
                }
            }
            ++I;
        } else {
            I = fw->erase(I);
        }
    }
    analysis::findVersions(parser, parser->parserLocals, fw, &mem, &sorted, refMap, typeMap);
    std::map<std::pair<node_t, int>, z3::expr> transformers;
    std::map<node_t, z3::expr> labels;
    std::set<node_t> assertion_points;
    std::map<std::pair<node_t, int>, Adjustment> adjustments;
    std::map<std::pair<node_t, int>, analysis::VersionMemory_t *> outs;
    compute_outs(fw, sorted, mem, outs);
    compute_phis(fw, sorted, mem, adjustments);
    traverse_df(fw, sorted.back(), [&](const IR::Node *crt, const std::pair<const IR::Node *, int> &edge) {
        auto val = edge.second;
        auto expr = analysis::node_to_smt(crt, val, &mem, refMap, typeMap, smttypewrapper);
        auto out_version = mem.find(edge.first)->second;
        auto myout_version = outs.find(std::make_pair(crt, val))->second;
        auto I = transformers.emplace(std::make_pair(crt, val), expr);
        auto phi = adjustments.find(std::make_pair(crt, val));
        if (phi != adjustments.end()) {
            for (auto &adj : phi->second) {
                auto v0 = get_qualified_name(adj, myout_version);
                auto v1 = get_qualified_name(adj, out_version);
                auto z3type = smttypewrapper->get_type(get_type(adj, typeMap));
                I.first->second = I.first->second && (context->constant(v0.c_str(), *z3type) ==
                                                      context->constant(v1.c_str(), *z3type));
            }
        }
    });
    for (auto crt : sorted) {
        if (auto asg = crt->to<IR::AssignmentStatement>()) {
            if (auto lpe = asg->left->to<IR::PathExpression>()) {
                if (lpe->path->name.name.startsWith("pre_call")) {
                    if (auto rmce = asg->right->to<IR::MethodCallExpression>()) {
                        if (is_havoc(rmce, refMap, typeMap)) {
                            assertion_points.emplace(crt);
                        }
                    }
                }
            }
        }
    };
    analysis::reachability_conditions_compute(fw, sorted, transformers, *context, &labels);
    std::set<const IR::Node *> bug_points;
    std::set<const IR::Node *> ok_points;
    traverse_df_pernode(fw, sorted.back(), [&](const IR::Node *crt) {
        auto furtherIT = fw->find(crt);
        bool is_terminal = false;
        if (furtherIT == fw->end()) {
            is_terminal = true;
        } else {
            if (furtherIT->second.empty())
                is_terminal = true;
        }
        if (is_terminal) {
            bool is_bug = false;
            if (auto mcs = crt->to<IR::MethodCallStatement>())
                if (analysis::is_bug(mcs)) {
                    is_bug = true;
                    bug_points.emplace(crt);
                }
            if (!is_bug) {
                if (auto eok = crt->to<IR::Expression>()) {
                    if (auto pe = eok->to<IR::PathExpression>()) {
                        if (pe->path->name == IR::ParserState::accept) {
                            ok_points.emplace(crt);
                        }
                    }
                }
            }
        }
    });
    ofs << "#accepts:" << ok_points.size() << '\n';
    ofs << "#bugs:" << bug_points.size() << '\n';
    std::set<const IR::Node *> &active = bug_points;
    ofs << "#active bugs:" << active.size() << '\n';
    ofs.flush();
    std::map<const IR::Node *, std::vector<const IR::Node *>> controlling;
    std::map<const IR::Node *, std::vector<const IR::Node *>> control_to_bugs;
    for (auto bp : active) {
        auto &v = controlling[bp];
        traverse_df_pernode(bw, bp, [&](const IR::Node *crt) {
            auto found = assertion_points.find(crt);
            if (found != assertion_points.end()) {
                v.emplace_back(crt);
            }
        });
        if (!v.empty())
            control_to_bugs[v.front()].emplace_back(bp);
    }
    std::vector<const IR::Node *> level_1_uncontrolled;
    ofs << "#active control points: " << control_to_bugs.size() << '\n';
    std::chrono::milliseconds elapsed(0);
    for (auto &control_bugs : control_to_bugs) {
        auto flow = control_bugs.first->to<IR::AssignmentStatement>()->left->to<IR::PathExpression>();
        z3::expr oki = context->bool_val(false);
        for (auto ok : ok_points) {
            auto crt = labels.find(ok)->second;
            auto version = mem.find(ok)->second;
            auto mp = get_path(flow, version);
            mp.append(cstring("reach"));
            auto z3e = get_z3_expr(mp, version, smttypewrapper);
            oki = (z3e && crt) || oki;
        }
        auto nxt = fw->find(control_bugs.first)->second.begin()->first;
        auto post_version = mem.find(nxt)->second;
        auto mp = get_path(flow, post_version);
        auto mps = get_basic_versions(mp, post_version);
        std::set<std::string> allowable;
        for (auto &new_mp : mps) {
            if (new_mp.path.back().is_str() && new_mp.path.back().str == "reach") {
                continue;
            } else {
                allowable.emplace(get_qualified_name(new_mp, post_version));
            }
        }
        z3::expr bug_condition = context->bool_val(false);
        bool first = true;
        for (auto trouble : control_bugs.second) {
            auto bug_label = labels.find(trouble)->second.simplify();
            if (first)
                bug_condition = bug_label;
            else
                bug_condition = merge_or(bug_condition, bug_label);
            first = false;
        }
        z3::expr_vector do_add(*context);
        for (auto trouble : control_bugs.second) {
            auto bug_label = to_nnf(labels.find(trouble)->second.simplify());
            auto prevI = bw->find(trouble)->second.begin();
            auto prevn = prevI->first;
            auto prevc = prevI->second;
            auto trans = transformers.find(std::make_pair(prevn, prevc))->second;
            auto prevcd = labels.find(prevn)->second;
            level_1_uncontrolled.emplace_back(trouble);
            auto e = to_nnf(labels.find(prevn)->second.simplify());
            z3::solver slv_prev(*context);
            slv_prev.add(e);
            auto bv = get_basic_versions(post_version);
            std::set<std::string> may_control;
            for (auto &path : bv) {
                may_control.emplace(get_qualified_name(path, post_version));
            }
            auto start_fix = std::chrono::system_clock::now();
            auto osize = do_add.size();
            if (get_extra_control(slv_prev, trans, allowable, may_control, get_atoms(prevcd), do_add)) {
                auto end_fix = std::chrono::system_clock::now();
                auto fix_duration = std::chrono::duration_cast<std::chrono::milliseconds>(
                        end_fix - start_fix);
                ofs << "done in " << fix_duration.count() << "ms for\n";
                for (auto i = osize; i != do_add.size(); ++i) {
                    ofs << do_add[i] << '\n';
                }
            } else {
                ofs << "can't do it...\n";
            }
        }
        ofs.flush();
        for (unsigned i = 0, e = do_add.size(); i != e; ++i) {
            auto exp = do_add[i];
            auto varname = exp.decl().name().str();
            auto please_add = str_to_expr(varname);
            (*simple_fixes)[control_bugs.first].emplace_back(please_add);
        }
    }
    auto end_all = std::chrono::system_clock::now();
    ofs << "total fixes time " << std::chrono::duration_cast<std::chrono::milliseconds>(
            end_all - start_all).count() << "ms\n";
    ofs.flush();
    return false;
}

class BuggyPathResolution : public  Transform {
    Util::SourceInfo with;
    const IR::Node *postorder(IR::Path *p) override {
        if (!p->name.getSourceInfo().isValid()) {
            p->name = IR::ID(with, p->name + "_replace");
        } else {
            if (p->name.name.endsWith("_replace")) {
                p->name.name = p->name.name.substr(0, p->name.name.size() - 8);
            }
        }
        return p;
    }

    BuggyPathResolution(Util::SourceInfo with) : with(with) {}
public:
    static const IR::Node *solve(const IR::Node *from, Util::SourceInfo w) {
        BuggyPathResolution buggyPathResolution(w);
        auto ret = from->apply(buggyPathResolution)->apply(buggyPathResolution);
        return ret;
    }
};

const IR::Node *analysis::DoFixOldProgram::preorder(IR::P4Table *table) {
    auto control = findContext<IR::P4Control>();
    auto I = fixes->find(std::make_pair(control->name.name, table->name.name));
    if (I != fixes->end()) {
        LOG3("fixing bug in table " << table->name.name << " / " << control->name.name);
        IR::Key *k = nullptr;
        if (table->getKey()) {
            k = table->getKey()->clone();
        } else {
            IR::Vector<IR::KeyElement> kelems;
            k = new IR::Key(kelems);
        }
        for (auto pe : I->second) {
            auto kelem = new IR::KeyElement(
                    BuggyPathResolution::solve(pe, table->getSourceInfo())->to<IR::Expression>(),
                    new IR::PathExpression(P4CoreLibrary::instance.exactMatch.Id(table->getSourceInfo())));
            k->push_back(kelem);
        }
        auto props = table->properties->clone();
        props->properties.removeByName(IR::TableProperties::keyPropertyName);
        props->push_back(new IR::Property(IR::TableProperties::keyPropertyName, k, false));
        table->properties = props;
        return table;
    }
    return table;
}
