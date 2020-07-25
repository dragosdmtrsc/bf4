//
// Created by dragos on 01.07.2019.
//

#ifndef P4C_COMMANDPARSER_H
#define P4C_COMMANDPARSER_H

#include <boost/algorithm/string.hpp>
#include <boost/variant.hpp>
#include <fstream>
#include <lib/cstring.h>
#include <lib/gmputil.h>

namespace analysis {

struct ActionCall {
  static cstring EMPTY;
  cstring actName;
  std::vector<mpz_class> args;
  ActionCall() {}
  ActionCall(cstring actName);
  friend std::ostream &operator<<(std::ostream &, const ActionCall &);
};
std::ostream &operator<<(std::ostream &, const ActionCall &);
struct Member {
  unsigned member;
  Member(): member(0) {}
  Member(unsigned int member);
};
enum class MatchType { EXACT, LPM, RANGE, TERNARY };
struct Match {
  MatchType mt;
  mpz_class param1;
  mpz_class param2;

  Match(MatchType mt, const mpz_class &param1, const mpz_class &param2);
  friend std::ostream &operator<<(std::ostream &, const Match &);
};
std::ostream &operator<<(std::ostream &, const Match &);
struct TableAdd {
  cstring tableName;
  unsigned prio;
  std::vector<Match> matches;
  boost::variant<Member, ActionCall> action;

  TableAdd(cstring tableName);
  friend std::ostream &operator<<(std::ostream &, const TableAdd &);
};
std::ostream &operator<<(std::ostream &, const TableAdd &);
struct TableSetDefault {
  cstring tableName;
  boost::variant<Member, ActionCall> action;

  TableSetDefault(cstring tableName);
  friend std::ostream &operator<<(std::ostream &, const TableSetDefault &);
};
std::ostream &operator<<(std::ostream &, const TableSetDefault &);
struct ActionProfileAdd {
  cstring actProfile;
  unsigned mem;
  ActionCall action;

  ActionProfileAdd(cstring actProfile);
  friend std::ostream &operator<<(std::ostream &, const ActionProfileAdd &);
};
std::ostream &operator<<(std::ostream &, const ActionProfileAdd &);

struct Command {
  boost::variant<ActionProfileAdd, TableSetDefault, TableAdd> data;
public:
  Command(const boost::variant<ActionProfileAdd, TableSetDefault, TableAdd> &data);
  friend std::ostream &operator<<(std::ostream &, const Command &);
};
std::ostream &operator<<(std::ostream &, const Command &);

class Commands {
  std::vector<Command> raw_commands;
  std::map<cstring, std::vector<TableAdd *>> per_table;
  std::map<cstring, TableSetDefault *> default_action;
  std::map<cstring, std::vector<ActionProfileAdd *>> profile_members;
public:
  Commands(std::vector<Command> &&raw_commands);
  const std::vector<TableAdd *> &tableEntries(cstring tableName) const {
    return const_cast<Commands &>(*this).per_table[tableName];
  }
  TableSetDefault *defaultAction(cstring tableName) const {
    return const_cast<Commands &>(*this).default_action[tableName];
  }
  const std::vector<ActionProfileAdd *> &profileMembers(cstring prof) const {
    return const_cast<Commands &>(*this).profile_members[prof];
  }
};

class CommandParser {
  std::string table_add_cmd = "table_add";
  std::string table_set_default_cmd = "table_set_default";
  std::string act_prof_create_member_cmd = "act_prof_create_member";
  static mpz_class get_int(std::string repr);
  static Match parse_match_spec(std::string spec);

  bool getAction(boost::variant<Member, ActionCall> &action,
                 std::string actname) const;

public:
  std::vector<Command> readCommands(cstring file);
};
}

#endif // P4C_COMMANDPARSER_H
