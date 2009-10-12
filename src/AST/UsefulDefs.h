// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
#ifndef TOPLEVEL_H
#define TOPLEVEL_H

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

#define  INITIAL_TABLE_SIZE 100

#ifdef EXT_HASH_MAP
 #include <ext/hash_set>
 #include <ext/hash_map>
#elif defined(TR1_UNORDERED_MAP)
 #include <tr1/unordered_map>
 #include <tr1/unordered_set>
 #define hash_map tr1::unordered_map
 #define hash_set tr1::unordered_set
 #define hash_multiset tr1::unordered_multiset
#else
 #include <hash_set>
 #include <hash_map>
#endif

#include "../main/Globals.h"
#include "ASTUtil.h"
#include "ASTKind.h"
#include "../extlib-constbv/constantbv.h"
#include "RunTimes.h"

#define HASHMAP      hash_map
#define HASHSET      hash_set
#define HASHMULTISET hash_multiset

namespace BEEV {

  using namespace std;
  using namespace MINISAT;
#ifdef EXT_HASH_MAP
  using namespace __gnu_cxx;
#endif

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
}; //end of namespace

#endif
