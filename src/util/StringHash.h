// This file defines a hash function and equal_to predicate for use with hash-
// based data structures. std::hash et al. do not compute a hash over the
// contents of a C string, only its address, so it is an inappropriate hash
// function in these cases.
//
// The current hash function is very simplistic and may not have desirable
// properties. Consider using [CityHash](https://code.google.com/p/cityhash/).

#ifndef STRING_HASH_H
#define STRING_HASH_H

#include <cstddef>
#include <cstring>

struct CStringHash
{
  ::std::size_t operator()(const char *str) const
  {
    ::std::size_t hash = 5381;
  
    while (char c = *str++)
      hash = ((hash << 5) + hash) + (unsigned char)c;
  
    return hash;
  }
};

struct CStringEqualityPredicate
{
  bool operator()(const char *a, const char *b) const
  {
    return strcmp(a, b) == 0;
  }
};

#endif
