//
// Created by dragos on 01.07.2019.
//

#include "CommandParser.h"
#include <lib/log.h>

cstring analysis::ActionCall::EMPTY = "EMPTY";

namespace analysis {
class print_t : public boost::static_visitor<std::ostream &> {
  std::ostream &os;

public:
  bool print_args = false;
  print_t(std::ostream &os) : os(os) {}
  std::ostream &operator()(const Member &m) {
    if (!print_args)
      return os << "member(" << m.member << ")";
    return os;
  }
  std::ostream &operator()(const ActionCall &actionCall) {
    if (!print_args)
      return os << actionCall.actName;
    bool first = true;
    for (auto arg : actionCall.args) {
      if (!first)
        os << ' ';
      first = false;
      os << arg;
    }
    return os;
  }
};
}

analysis::TableAdd::TableAdd(cstring tableName) : tableName(tableName) {}

std::ostream &analysis::operator<<(std::ostream &os,
                                   const analysis::TableAdd &a) {
  analysis::print_t print(os);
  os << "table_add" << ' ';
  boost::apply_visitor(print, a.action) << ' ';
  for (auto &mat : a.matches) {
    os << mat;
    os << ' ';
  }
  print.print_args = true;
  os << "=> ";
  boost::apply_visitor(print, a.action) << ' ';
  os << a.prio;
  return os;
}

analysis::TableSetDefault::TableSetDefault(cstring tableName)
    : tableName(tableName) {}

std::ostream &operator<<(std::ostream &os, const analysis::TableSetDefault &tsd) {
  os << "table_set_default " << tsd.tableName << ' ';
  analysis::print_t print(os);
  boost::apply_visitor(print, tsd.action) << ' ' << "=> ";
  print.print_args = true;
  boost::apply_visitor(print, tsd.action);
  return os;
}

analysis::ActionProfileAdd::ActionProfileAdd(cstring actProfile)
    : actProfile(actProfile) {}

std::ostream &analysis::operator<<(std::ostream &os, const analysis::ActionProfileAdd &apa) {
  return os << "act_prof_create_member " << apa.actProfile << ' ' << apa.mem << ' ' << apa.action;
}

analysis::Member::Member(unsigned int member) : member(member) {}

analysis::ActionCall::ActionCall(cstring actName) : actName(actName) {}

std::ostream &analysis::operator<<(std::ostream &os, const analysis::ActionCall &a) {
  os << a.actName << ' ';
  bool first = true;
  for (auto &arg : a.args) {
    if (!first)
      os << ' ';
    first = false;
    os << arg;
  }
  return os;
}

analysis::Match::Match(analysis::MatchType mt, const mpz_class &param1,
                       const mpz_class &param2)
    : mt(mt), param1(param1), param2(param2) {}

std::ostream &analysis::operator<<(std::ostream &os, const analysis::Match &m) {
  switch (m.mt) {
  case analysis::MatchType::LPM:
    return os << m.param1.get_str(2) << '/' << m.param2.get_str(10);
  case analysis::MatchType::EXACT:
    return os << m.param1.get_str(2);
  case analysis::MatchType::TERNARY:
    return os << m.param1.get_str(2) << "&&&" << m.param2.get_str(2);
  case analysis::MatchType::RANGE:
    return os << m.param1.get_str(2) << ".." << m.param2.get_str(2);
  }
  return os;
}

analysis::Command::Command(
    const boost::variant<analysis::ActionProfileAdd, analysis::TableSetDefault,
                         analysis::TableAdd> &data)
    : data(data) {}

analysis::Match analysis::CommandParser::parse_match_spec(std::string spec) {
  size_t idx = 0;
  std::string first;
  std::string second;
  MatchType mt;
  if ((idx = spec.find("&&&")) != std::string::npos) {
    first = spec.substr(0, idx);
    second = spec.substr(idx + 3);
    mt = MatchType::TERNARY;
  } else if ((idx = spec.find("..")) != std::string::npos) {
    first = spec.substr(0, idx);
    second = spec.substr(idx + 2);
    mt = MatchType::RANGE;
  } else if ((idx = spec.find('/')) != std::string::npos) {
    first = spec.substr(0, idx);
    second = spec.substr(idx + 1);
    mt = MatchType::LPM;
  } else {
    first = spec.substr(0);
    mt = MatchType::EXACT;
  }
  if (mt != MatchType::EXACT)
    return {mt, get_int(first), get_int(second)};
  else
    return {mt, get_int(first), 0};
}

bool analysis::CommandParser::getAction(
    boost::variant<analysis::Member, analysis::ActionCall> &action,
    std::string actname) const {
  auto idx = actname.find("member(");
  bool has_member = false;
  if (idx == 0) {
    auto mem = actname.substr(7, actname.length() - 8);
    auto member = static_cast<unsigned int>(atoi(mem.c_str()));
    action = Member(member);
    has_member = true;
  } else {
    action = ActionCall(std::move(actname));
  }
  return has_member;
}

std::vector<analysis::Command>
analysis::CommandParser::readCommands(cstring file) {
  std::vector<Command> cmds;
  std::ifstream ifs(file);
  std::string line;
  if (!ifs.is_open()) {
    BUG("%1% commands file not there", file);
  }
  while (std::getline(ifs, line)) {
    std::vector<std::string> res;
    boost::split(res, line, boost::is_any_of(" "));
    if (res.empty()) {
      continue;
    }
    LOG3("got cmd line " << line);
    auto I = res.begin();
    auto E = res.end();
    if (*I == table_add_cmd) {
      ++I;
      if (I != E) {
        auto tab_name = *I;
        TableAdd tableAdd(tab_name);
        ++I;
        if (I != E) {
          auto &action = tableAdd.action;
          bool has_member = getAction(action, std::move(*I));
          ++I;
          while (I != E) {
            if (*I == "=>") {
              ++I;
              break;
            }
            tableAdd.matches.push_back(parse_match_spec(std::move(*I)));
            ++I;
          }
          auto any_ternary = std::any_of(
              tableAdd.matches.begin(), tableAdd.matches.end(),
              [](const Match &m) {
                return m.mt == MatchType::TERNARY || m.mt == MatchType::RANGE;
              });
          if (!any_ternary) {
            auto first_lpm = std::find_if(
                tableAdd.matches.begin(), tableAdd.matches.end(),
                [](const Match &m) { return m.mt == MatchType::LPM; });
            if (first_lpm != tableAdd.matches.end()) {
              tableAdd.prio = static_cast<unsigned int>(
                  first_lpm->param1.get_prec() - first_lpm->param2.get_ui());
            } else {
              tableAdd.prio = 0;
            }
          }
          std::string last;
          std::vector<mpz_class> *args = nullptr;
          if (!has_member)
            args = &boost::get<ActionCall>(tableAdd.action).args;
          while (I != E) {
            if (args && !(any_ternary && I + 1 == E)) {
              args->push_back(get_int(std::move(*I)));
            }
            if (I + 1 == E)
              last = *I;
            ++I;
          }
          if (any_ternary && !last.empty()) {
            tableAdd.prio =
                static_cast<unsigned int>(get_int(std::move(last)).get_ui());
          }
          cmds.emplace_back(tableAdd);
        }
      }
    } else if (*I == table_set_default_cmd) {
      ++I;
      if (I != E) {
        auto set_default = TableSetDefault(*I);
        ++I;
        if (I != E) {
          auto has_member = getAction(set_default.action, std::move(*I));
          ++I;
          if (!has_member) {
            auto &args = boost::get<ActionCall>(set_default.action).args;
            while (I != E) {
              if (!I->empty() && *I != "=>") {
                args.push_back(get_int(*I));
              }
              ++I;
            }
          }
          cmds.emplace_back(set_default);
        }
      }
    } else if (*I == act_prof_create_member_cmd) {
      ++I;
      if (I != E) {
        auto act_prof = ActionProfileAdd(std::move(*I));
        ++I;
        if (I != E) {
          auto member = get_int(std::move(*I));
          act_prof.mem = static_cast<unsigned int>(member.get_ui());
          ++I;
          if (I != E) {
            auto act = ActionCall(std::move(*I));
            ++I;
            auto &args = act.args;
            if (I != E && *I == "=>")
              ++I;
            while (I != E) {
              if (!I->empty())
                args.push_back(get_int(std::move(*I)));
              ++I;
            }
            act_prof.action = std::move(act);
            cmds.emplace_back(act_prof);
            LOG4("" << act_prof);
          }
        }
      }
    } else {
      auto &s = *I;
      LOG4("unrecognized command " << s << "@" << line);
    }
  }
  return cmds;
}

mpz_class analysis::CommandParser::get_int(std::string repr) {
  if (repr.find("0x") == 0) {
    return Util::cvtInt(repr.c_str() + 2, 16);
  } else if (repr.find("0b") == 0) {
    return Util::cvtInt(repr.c_str() + 2, 2);
  } else if (repr.find("0d") == 0) {
    return Util::cvtInt(repr.c_str() + 2, 10);
  } else {
    if (std::all_of(repr.begin(), repr.end(),
                    [](char x) { return std::isdigit(x); })) {
      return Util::cvtInt(repr.c_str(), 10);
    }
    BUG("can't parse number %1%", repr);
  }
}

analysis::Commands::Commands(std::vector<analysis::Command> &&raw_commands)
    : raw_commands(raw_commands) {
  LOG3("#" << this->raw_commands.size() << " commands");
  for (auto &cmd : this->raw_commands) {
    if (cmd.data.type() == typeid(analysis::TableSetDefault)) {
      auto &tsd = boost::get<analysis::TableSetDefault>(cmd.data);
      LOG3("set default " << tsd.tableName);
      this->default_action[tsd.tableName] = &tsd;
    } else if (cmd.data.type() == typeid(analysis::TableAdd)) {
      auto &tadd = boost::get<analysis::TableAdd>(cmd.data);
      LOG3("table add " << tadd.tableName);
      if (tadd.tableName.startsWith("pipe.")) {
        // Tofino specifics
        tadd.tableName = tadd.tableName.substr(5);
      }
      this->per_table[tadd.tableName].emplace_back(&tadd);
    } else if (cmd.data.type() == typeid(analysis::ActionProfileAdd)) {
      auto &apadd = boost::get<analysis::ActionProfileAdd>(cmd.data);
      this->profile_members[apadd.actProfile].emplace_back(&apadd);
    }
  }
  for (auto &p : per_table) {
    std::sort(p.second.begin(), p.second.end(),
              [](const analysis::TableAdd *l, const analysis::TableAdd *r) {
                return l->prio < r->prio;
              });
  }
  for (auto &e : profile_members) {
    std::sort(
        e.second.begin(), e.second.end(),
        [](const analysis::ActionProfileAdd *l,
           const analysis::ActionProfileAdd *r) { return l->mem < r->mem; });
  }
}
