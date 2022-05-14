/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: June, 2010
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

#ifndef BBNODEAIG_H_
#define BBNODEAIG_H_

#include "aig/aig/aig.h"
#include <iostream>

namespace stp
{
using std::cerr;
using std::endl;

// This class wraps around a pointer to an AIG (provided by the ABC tool).
// uses the default copy constructor and assignment operator.
// Used for bitblasting

class BBNodeAIG
{
  // This is only useful for printing small instances for debuging.
  void print(Aig_Obj_t* node) const
  {
    Aig_Obj_t *c0 = node->pFanin0, *c1 = node->pFanin1;
    bool c0Not = Aig_IsComplement(c0), c1Not = Aig_IsComplement(c1);
    if (c0Not)
      c0 = Aig_Not(c0);
    if (c1Not)
      c1 = Aig_Not(c1);

    cerr << Aig_Regular(node)->Id;
    cerr << "[" << node->Type << "]";
    cerr << ": (";
    if (c0 != 0)
    {
      if (c0Not)
        cerr << "-";
      cerr << c0->Id;
      cerr << ",";
    }
    if (c1 != 0)
    {
      if (c1Not)
        cerr << "-";

      cerr << c1->Id;
    }
    cerr << ")" << endl;
    if (c0 != 0)
      print(c0);
    if (c1 != 0)
      print(c1);
  }

public:
  intptr_t GetNodeNum() const { return (intptr_t)n; }

  // If the pointer is odd. Then it's the NOT of the pointer one less.
  Aig_Obj_t* n;

  // After dag aware rewriting the symbol stays at the same position in the
  // vector of PIs.
  // To get its CNF variable number we get the node at the same position.
  int symbol_index;

  BBNodeAIG() { n = NULL; }

  BBNodeAIG(Aig_Obj_t* _n)
  {
    n = _n;
    assert(n != NULL);
    if (Aig_IsComplement(n))
    {
      assert(Aig_Not(n)->Type != 0); // don't want nodes of type UNKNOWN>
    }
    else
    {
      assert(n->Type != 0);
    }
  }

  bool IsNull() const { return n == NULL; }

  bool operator==(const BBNodeAIG& other) const { return n == other.n; }
  bool operator!=(const BBNodeAIG& other) const { return !(n == other.n); }


  /*
  Negative AIG nodes are indicated by being odd.
  Each AIG node has a unique id.
  The negative, and non-negative of the same node, have the same ID.
  We use this in a set, so we need the negative and non-negative to evaluate as different.  
  */
  bool operator<(const BBNodeAIG& other) const 
  { 
    if (Aig_IsComplement(n) != Aig_IsComplement(other.n))
      return Aig_IsComplement(n);

    return Aig_Regular(n)->Id < Aig_Regular(other.n)->Id; 
  }

  void print() const { print(n); }
};
}

#endif
