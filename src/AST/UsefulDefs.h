// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
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

#include "../main/Globals.h"
#include "ASTKind.h"
#include "../extlib-constbv/constantbv.h"
#include "RunTimes.h"

#include "config.h"

#if HAVE_HASH_SET
#include HASH_SET_H
#define hash_set HASH_SET_NAMESPACE::HASH_SET_CLASS
#endif

#if HAVE_HASH_MAP
#include HASH_MAP_H
#define hash_map HASH_MAP_NAMESPACE::HASH_MAP_CLASS
#endif

#if HAVE_HASH_MULTISET
#include HASH_MULTISET_H
#define hash_multiset HASH_MULTISET_NAMESPACE::HASH_MULTISET_CLASS
#endif

#define INITIAL_TABLE_SIZE 100

using namespace std;
namespace BEEV {

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
    friend ostream& operator<<(ostream& os, const Spacer &ind);
  }; //End of class spacer

  inline Spacer spaces(int width) {
    Spacer sp(width);
    return sp;
  }

#if 0
  struct eqstr {
    bool operator()(const char* s1, const char* s2) const {
      return strcmp(s1, s2) == 0;
    }
  };

  // function_counters: Table for storing function count stats.
  typedef hash_map<
    const char*,
    int,
    BEEV::hash<const char *>,
    eqstr> function_counters;
#endif
}; //end of namespace

#endif
