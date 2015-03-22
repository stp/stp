// -*- c++ -*-
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

#include <iostream>

typedef struct Aig_Obj_t_            Aig_Obj_t;

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
  void print(Aig_Obj_t* node) const;

public:
  intptr_t GetNodeNum() const { return (intptr_t)n; }

  // If the pointer is odd. Then it's the NOT of the pointer one less.
  Aig_Obj_t* n;

  // After dag aware rewriting the symbol stays at the same position in the
  // vector of PIs.
  // To get its CNF variable number we get the node at the same position.
  int symbol_index;

  BBNodeAIG() { n = NULL; }

  BBNodeAIG(Aig_Obj_t* _n);

  bool IsNull() const { return n == NULL; }

  bool operator==(const BBNodeAIG& other) const { return n == other.n; }

  bool operator!=(const BBNodeAIG& other) const { return !(n == other.n); }

  bool operator<(const BBNodeAIG& other) const { return n < other.n; }

  void print() const { print(n); }
};
}

#endif
