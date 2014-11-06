// -*- c++ -*-
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

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <vector>
#include <iostream>
#include <sstream>
#include <string>
#include <map>
#include <set>
#include <algorithm>
#include <assert.h>

#include "stp/Globals/Globals.h"
#include "stp/AST/ASTKind.h"
// FIXME: External library header
#include "extlib-constbv/constantbv.h"
#include "RunTimes.h"
#include "stp/Util/StringHash.h"

#include "stp/config.h"

#include HASH_SET_H
#include HASH_MAP_H
#include HASH_MULTISET_H

#define hash_set HASH_SET_NAMESPACE::HASH_SET_CLASS
#define hash_map HASH_MAP_NAMESPACE::HASH_MAP_CLASS
#define hash_multiset HASH_MULTISET_NAMESPACE::HASH_MULTISET_CLASS

#define INITIAL_TABLE_SIZE 100

namespace BEEV {
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
   * It is good to define hash_map and hash_set in case we want to  *
   * use libraries other than STL.                                  *
   ******************************************************************/
  typedef vector<ASTNode> ASTVec;
  typedef unsigned int * CBV;
  extern ASTVec _empty_ASTVec;

  // Error handling function
  extern void (*vc_error_hdlr)(const char* err_msg);
  
  /******************************************************************
   * Class Spacer: 
   *
   * Spacer class is basically just an int, but the new class allows
   * overloading of << with a special definition that prints the int
   * as that many spaces.
   ******************************************************************/
  class Spacer {
  public:
    int _spaces;
    Spacer(int spaces) 
    { 
      _spaces = spaces; 
    }
    friend std::ostream& operator<<(std::ostream& os, const Spacer &ind);
  }; //End of class spacer

  inline Spacer spaces(int width) {
    Spacer sp(width);
    return sp;
  }

  // function_counters: Table for storing function count stats.
  typedef hash_map<
    const char *,
    int,
    CStringHash,
    CStringEqualityPredicate> function_counters;
} //end of namespace

#endif
