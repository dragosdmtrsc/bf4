/**
 * Autogenerated by Thrift Compiler (0.13.0)
 *
 * DO NOT EDIT UNLESS YOU ARE SURE THAT YOU KNOW WHAT YOU ARE DOING
 *  @generated
 */
#ifndef p4_api_TYPES_H
#define p4_api_TYPES_H

#include <iosfwd>

#include <thrift/Thrift.h>
#include <thrift/TApplicationException.h>
#include <thrift/TBase.h>
#include <thrift/protocol/TProtocol.h>
#include <thrift/transport/TTransport.h>

#include <functional>
#include <memory>


namespace p4_thrift {

struct instruction_type {
  enum type {
    call = 1,
    normal = 2,
    controlled = 3,
    evil = 4,
    nondet = 5,
    param_pass = 6,
    external = 7,
    bug = 8,
    good = 9,
    assume = 10
  };
};

extern const std::map<int, const char*> _instruction_type_VALUES_TO_NAMES;

std::ostream& operator<<(std::ostream& out, const instruction_type::type& val);

std::string to_string(const instruction_type::type& val);

struct edge_kind {
  enum type {
    normal = 0,
    call = 1,
    ret = 2,
    go_to = 3
  };
};

extern const std::map<int, const char*> _edge_kind_VALUES_TO_NAMES;

std::ostream& operator<<(std::ostream& out, const edge_kind::type& val);

std::string to_string(const edge_kind::type& val);

typedef std::string id_t;

class NoSuchMethod;

class basic_instruction;

class method;

class edge;

class method_info;

typedef struct _NoSuchMethod__isset {
  _NoSuchMethod__isset() : method(false) {}
  bool method :1;
} _NoSuchMethod__isset;

class NoSuchMethod : public ::apache::thrift::TException {
 public:

  NoSuchMethod(const NoSuchMethod&);
  NoSuchMethod& operator=(const NoSuchMethod&);
  NoSuchMethod() : method() {
  }

  virtual ~NoSuchMethod() noexcept;
  std::string method;

  _NoSuchMethod__isset __isset;

  void __set_method(const std::string& val);

  bool operator == (const NoSuchMethod & rhs) const
  {
    if (!(method == rhs.method))
      return false;
    return true;
  }
  bool operator != (const NoSuchMethod &rhs) const {
    return !(*this == rhs);
  }

  bool operator < (const NoSuchMethod & ) const;

  uint32_t read(::apache::thrift::protocol::TProtocol* iprot);
  uint32_t write(::apache::thrift::protocol::TProtocol* oprot) const;

  virtual void printTo(std::ostream& out) const;
  mutable std::string thriftTExceptionMessageHolder_;
  const char* what() const noexcept;
};

void swap(NoSuchMethod &a, NoSuchMethod &b);

std::ostream& operator<<(std::ostream& out, const NoSuchMethod& obj);

typedef struct _basic_instruction__isset {
  _basic_instruction__isset() : instruction_id(false), method_id(false), representation(true), instr_type(true), json(true) {}
  bool instruction_id :1;
  bool method_id :1;
  bool representation :1;
  bool instr_type :1;
  bool json :1;
} _basic_instruction__isset;

class basic_instruction : public virtual ::apache::thrift::TBase {
 public:

  basic_instruction(const basic_instruction&);
  basic_instruction& operator=(const basic_instruction&);
  basic_instruction() : instruction_id(), method_id(), representation(""), instr_type((instruction_type::type)2), json("") {
    instr_type = (instruction_type::type)2;

  }

  virtual ~basic_instruction() noexcept;
  id_t instruction_id;
  id_t method_id;
  std::string representation;
  instruction_type::type instr_type;
  std::string json;

  _basic_instruction__isset __isset;

  void __set_instruction_id(const id_t& val);

  void __set_method_id(const id_t& val);

  void __set_representation(const std::string& val);

  void __set_instr_type(const instruction_type::type val);

  void __set_json(const std::string& val);

  bool operator == (const basic_instruction & rhs) const
  {
    if (!(instruction_id == rhs.instruction_id))
      return false;
    if (!(method_id == rhs.method_id))
      return false;
    if (!(representation == rhs.representation))
      return false;
    if (!(instr_type == rhs.instr_type))
      return false;
    if (__isset.json != rhs.__isset.json)
      return false;
    else if (__isset.json && !(json == rhs.json))
      return false;
    return true;
  }
  bool operator != (const basic_instruction &rhs) const {
    return !(*this == rhs);
  }

  bool operator < (const basic_instruction & ) const;

  uint32_t read(::apache::thrift::protocol::TProtocol* iprot);
  uint32_t write(::apache::thrift::protocol::TProtocol* oprot) const;

  virtual void printTo(std::ostream& out) const;
};

void swap(basic_instruction &a, basic_instruction &b);

std::ostream& operator<<(std::ostream& out, const basic_instruction& obj);

typedef struct _method__isset {
  _method__isset() : method_id(false), instructions(false), edges(false), may_fail(false) {}
  bool method_id :1;
  bool instructions :1;
  bool edges :1;
  bool may_fail :1;
} _method__isset;

class method : public virtual ::apache::thrift::TBase {
 public:

  method(const method&);
  method& operator=(const method&);
  method() : method_id(), may_fail(0) {
  }

  virtual ~method() noexcept;
  id_t method_id;
  std::set<basic_instruction>  instructions;
  std::set<edge>  edges;
  bool may_fail;

  _method__isset __isset;

  void __set_method_id(const id_t& val);

  void __set_instructions(const std::set<basic_instruction> & val);

  void __set_edges(const std::set<edge> & val);

  void __set_may_fail(const bool val);

  bool operator == (const method & rhs) const
  {
    if (!(method_id == rhs.method_id))
      return false;
    if (!(instructions == rhs.instructions))
      return false;
    if (!(edges == rhs.edges))
      return false;
    if (!(may_fail == rhs.may_fail))
      return false;
    return true;
  }
  bool operator != (const method &rhs) const {
    return !(*this == rhs);
  }

  bool operator < (const method & ) const;

  uint32_t read(::apache::thrift::protocol::TProtocol* iprot);
  uint32_t write(::apache::thrift::protocol::TProtocol* oprot) const;

  virtual void printTo(std::ostream& out) const;
};

void swap(method &a, method &b);

std::ostream& operator<<(std::ostream& out, const method& obj);

typedef struct _edge__isset {
  _edge__isset() : source(false), sourceMethod(false), target(false), targetMethod(false), kind(false) {}
  bool source :1;
  bool sourceMethod :1;
  bool target :1;
  bool targetMethod :1;
  bool kind :1;
} _edge__isset;

class edge : public virtual ::apache::thrift::TBase {
 public:

  edge(const edge&);
  edge& operator=(const edge&);
  edge() : source(), sourceMethod(), target(), targetMethod(), kind((edge_kind::type)0) {
  }

  virtual ~edge() noexcept;
  id_t source;
  id_t sourceMethod;
  id_t target;
  id_t targetMethod;
  edge_kind::type kind;

  _edge__isset __isset;

  void __set_source(const id_t& val);

  void __set_sourceMethod(const id_t& val);

  void __set_target(const id_t& val);

  void __set_targetMethod(const id_t& val);

  void __set_kind(const edge_kind::type val);

  bool operator == (const edge & rhs) const
  {
    if (!(source == rhs.source))
      return false;
    if (!(sourceMethod == rhs.sourceMethod))
      return false;
    if (!(target == rhs.target))
      return false;
    if (!(targetMethod == rhs.targetMethod))
      return false;
    if (__isset.kind != rhs.__isset.kind)
      return false;
    else if (__isset.kind && !(kind == rhs.kind))
      return false;
    return true;
  }
  bool operator != (const edge &rhs) const {
    return !(*this == rhs);
  }

  bool operator < (const edge & ) const;

  uint32_t read(::apache::thrift::protocol::TProtocol* iprot);
  uint32_t write(::apache::thrift::protocol::TProtocol* oprot) const;

  virtual void printTo(std::ostream& out) const;
};

void swap(edge &a, edge &b);

std::ostream& operator<<(std::ostream& out, const edge& obj);

typedef struct _method_info__isset {
  _method_info__isset() : method_id(false), repr(false) {}
  bool method_id :1;
  bool repr :1;
} _method_info__isset;

class method_info : public virtual ::apache::thrift::TBase {
 public:

  method_info(const method_info&);
  method_info& operator=(const method_info&);
  method_info() : method_id(), repr() {
  }

  virtual ~method_info() noexcept;
  id_t method_id;
  std::string repr;

  _method_info__isset __isset;

  void __set_method_id(const id_t& val);

  void __set_repr(const std::string& val);

  bool operator == (const method_info & rhs) const
  {
    if (!(method_id == rhs.method_id))
      return false;
    if (!(repr == rhs.repr))
      return false;
    return true;
  }
  bool operator != (const method_info &rhs) const {
    return !(*this == rhs);
  }

  bool operator < (const method_info & ) const;

  uint32_t read(::apache::thrift::protocol::TProtocol* iprot);
  uint32_t write(::apache::thrift::protocol::TProtocol* oprot) const;

  virtual void printTo(std::ostream& out) const;
};

void swap(method_info &a, method_info &b);

std::ostream& operator<<(std::ostream& out, const method_info& obj);

} // namespace

#endif
