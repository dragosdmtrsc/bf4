//
// Created by dragos on 18.09.2019.
//

#ifndef P4C_BVSET_H
#define P4C_BVSET_H

#include <lib/exceptions.h>
#include <bitset>
#include <boost/dynamic_bitset.hpp>
#include <unordered_map>

namespace analysis {

template <typename V>
using Index = std::unordered_map<V, size_t, boost::hash<V>>;

template <typename V>
struct bvset {
  Index<V> *idx;
  boost::dynamic_bitset<> arr;
  bvset() { BUG("don't call it, just compile"); }
  bvset(Index<V> *idx) : idx(idx), arr(idx->size()) {}
  bvset(Index<V> *idx, const V &v) : idx(idx) { arr.set(idx->at(v)); }
  bool operator==(const bvset<V> &s) const {
    BUG_CHECK(s.idx == idx, "not comparing apples with apples");
    return arr == s.arr;
  }
  bool operator!=(const bvset<V> &s) const { return !operator==(s); }
};
}

#endif  // P4C_BVSET_H
