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
#include "../util/StringHash.h"

#include "config.h"

#include <unordered_set>
#include <unordered_map>

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
  typedef std::unordered_map<
    const char *,
    int,
    CStringHash,
    CStringEqualityPredicate> function_counters;
}; //end of namespace

#endif
