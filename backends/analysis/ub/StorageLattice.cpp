//
// Created by dragos on 14.08.2019.
//

#include "StorageLattice.h"

namespace analysis {
limited_call_string::operator P4::ProgramPoint() const {
  P4::ProgramPoint p;
  p.stack = stack;
  return p;
}

size_t limited_call_string::hash() const {
  std::size_t result = 0;
  boost::hash_range(result, stack.begin(), stack.end());
  return result;
}

bool limited_call_string::operator==(const limited_call_string &lcs) const {
  return stack == lcs.stack;
}

limited_call_string limited_call_string::push(const IR::Node *n) const {
  if (k == 0) return *this;
  limited_call_string nxt(k);
  if (stack.size() < k - 1) {
    nxt.stack = stack;
    nxt.stack.push_back(n);
  } else {
    nxt.stack.insert(nxt.stack.end(), stack.begin(),
                     stack.begin() + stack.size() - 1);
    nxt.stack.push_back(n);
  }
  return std::move(nxt);
}

limited_call_string::limited_call_string(size_t k) : k(k) {
  if (k) stack.reserve(k);
}
}