/********************************************************************
 * AUTHORS: Ryan Govostes
 *
 * BEGIN DATE: Mar, 2012
 *
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
********************************************************************/

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
  ::std::size_t operator()(const char* str) const
  {
    ::std::size_t hash = 5381;

    while (char c = *str++)
      hash = ((hash << 5) + hash) + (unsigned char)c;

    return hash;
  }
};

struct CStringEqualityPredicate
{
  bool operator()(const char* a, const char* b) const
  {
    return strcmp(a, b) == 0;
  }
};

#endif
