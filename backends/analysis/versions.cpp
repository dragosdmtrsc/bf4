//
// Created by dragos on 27.01.2020.
//

#include <boost/functional/hash.hpp>
#include "versions.h"
namespace analysis {

bool analysis::MemPath::operator<(const MemPath &r) const {
  if (decl) {
    if (!r.decl) return false;
    if (decl->getName() != r.decl->getName())
      return decl->getName().name < r.decl->getName().name;
  } else {
    // !decl
    if (r.decl) return true;
  }
  return std::make_tuple(decl, path, version) <
         std::make_tuple(r.decl, r.path, r.version);
}

bool MemPath::operator==(const MemPath &other) const {
  return decl == other.decl && path == other.path && version == other.version;
}

std::size_t hash_value(const EitherIntOrString &cp) {
  std::size_t seed;
  if (cp.is_num())
    seed = boost::hash_value(cp.nr);
  else
    seed = std::hash<cstring>()(cp.str.c_str());
  boost::hash_combine(seed, (cp.is_num()) ? 13 : 17);
  return seed;
}

std::size_t hash_value(const MemPath &mp) {
  auto H = boost::hash_range(mp.path.begin(), mp.path.end());
  boost::hash_combine(H, mp.decl);
  boost::hash_combine(H, mp.version);
  return H;
}
}