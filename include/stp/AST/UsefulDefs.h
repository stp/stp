/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
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
#ifndef USEFULDEFS_H
#define USEFULDEFS_H

#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <stdio.h>
#include <stdlib.h>
#include <string>
#include <vector>

#include "stp/AST/ASTKind.h"
#include "stp/Globals/Globals.h"
// FIXME: External library header
#include "extlib-constbv/constantbv.h"
#include "stp/Util/Attributes.h"
#include "stp/Util/RunTimes.h"
#include "stp/Util/StringHash.h"

#include "stp/config.h"

#include <unordered_map>
#include <unordered_set>
#define INITIAL_TABLE_SIZE 100

namespace stp
{
using std::vector;

/******************************************************************
 * Important classes declared as part of AST datastructures       *
 *                                                                *
 ******************************************************************/
class STPMgr;
class ASTNode;
class ASTInternal;
class ASTInterior;
class ASTSymbol;
class ASTBVConst;
class BVSolver;

/******************************************************************
 * Useful typedefs:                                               *
 *                                                                *
 * Vector of ASTNodes, used for child nodes among other things.   *
 * It is good to define std::unordered_map and std::unordered_set in case we want to  *
 * use libraries other than STL.                                  *
 ******************************************************************/
typedef vector<ASTNode> ASTVec;
typedef unsigned int* CBV;
DLL_PUBLIC extern ASTVec _empty_ASTVec;

/******************************************************************
 * A non-owning view over a contiguous run of elements — like     *
 * std::span, but available under C++17. Returned by GetChildren()*
 * so a node's children need not be stored in a std::vector.      *
 * A template so its element-touching members are only checked on *
 * instantiation, where ASTNode is complete.                      *
 ******************************************************************/
template <class T> class Span
{
  T* _data;
  size_t _size;

public:
  Span() : _data(nullptr), _size(0) {}
  Span(T* data, size_t size) : _data(data), _size(size) {}
  // Implicit view over a std::vector<ASTNode> (the historical storage).
  Span(const ASTVec& v) : _data(v.data()), _size(v.size()) {}

  T* begin() const { return _data; }
  T* end() const { return _data + _size; }
  size_t size() const { return _size; }
  bool empty() const { return _size == 0; }
  T& operator[](size_t i) const { return _data[i]; }
  T& front() const { return _data[0]; }
  T& back() const { return _data[_size - 1]; }
  T* data() const { return _data; }

  bool operator==(const Span& o) const
  {
    if (_size != o._size)
      return false;
    for (size_t i = 0; i < _size; i++)
      if (!(_data[i] == o._data[i]))
        return false;
    return true;
  }
  bool operator!=(const Span& o) const { return !(*this == o); }
};

// The children of an interior node, as a read-only view.
typedef Span<const ASTNode> ASTChildren;

// Materialise a children view into an owned vector (only where a mutable or
// std::vector-typed copy is genuinely needed).
DLL_PUBLIC ASTVec toASTVec(const ASTChildren& c);

// Error handling function
DLL_PUBLIC extern void (*vc_error_hdlr)(const char* err_msg);

/******************************************************************
 * Class Spacer:
 *
 * Spacer class is basically just an int, but the new class allows
 * overloading of << with a special definition that prints the int
 * as that many spaces.
 ******************************************************************/
class Spacer
{
public:
  int _spaces;
  Spacer(int spaces) { _spaces = spaces; }
  friend std::ostream& operator<<(std::ostream& os, const Spacer& ind);
};

inline Spacer spaces(int width)
{
  Spacer sp(width);
  return sp;
}

// function_counters: Table for storing function count stats.
typedef std::unordered_map<const char*, int, CStringHash,
                           CStringEqualityPredicate>
    function_counters;
} // end of namespace

#endif
