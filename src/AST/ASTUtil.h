/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
// -*- c++ -*-

#ifndef ASTUTIL_H
#define ASTUTIL_H

#include <iostream>
#include <vector>
#ifdef EXT_HASH_MAP
#include <ext/hash_set>
#include <ext/hash_map>
#elif defined(TR1_UNORDERED_MAP)
#include <tr1/unordered_map>
#include <tr1/unordered_set>
#else
#include <hash_set>
#include <hash_map>
#endif

#include <cstring>

using namespace std;
namespace BEEV {
#ifdef EXT_HASH_MAP
  using namespace __gnu_cxx;
#endif

  extern void (*vc_error_hdlr)(const char* err_msg);
  /*Spacer class is basically just an int, but the new class allows
    overloading of << with a special definition that prints the int as
    that many spaces. */
  class Spacer {
  public:
    int _spaces;
    Spacer(int spaces) { _spaces = spaces; }
    friend ostream& operator<<(ostream& os, const Spacer &ind);
  };

  inline Spacer spaces(int width) {
    Spacer sp(width);
    return sp;
  }

  struct eqstr {
    bool operator()(const char* s1, const char* s2) const {
      return strcmp(s1, s2) == 0;
    }
  };

  // Table for storing function count stats.
#ifdef TR1_UNORDERED_MAP
  typedef tr1::unordered_map<const char*,int,
    tr1::hash<const char *>,eqstr> function_counters;
#else
  typedef hash_map<const char*,int,
    hash<char *>,eqstr> function_counters;
#endif

  void CountersAndStats(const char * functionname);

  //global function which accepts an integer and looks up the
  //corresponding ASTNode and prints a string of that ASTNode
  void Convert_MINISATVar_To_ASTNode_Print(int minisat_var,
                                           int decision, int polarity=0);
}; // end namespace.
#endif
