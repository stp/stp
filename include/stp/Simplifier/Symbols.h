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

#ifndef SYMBOLS_H
#define SYMBOLS_H

#include <vector>
#include "assert.h"
#include "stp/AST/AST.h"

using std::vector;

// Each node is either: empty, an ASTNode, or a vector of more than one child
// nodes.

class Symbols // not copyable
{
public:
  const ASTNode found;
  const vector<Symbols*> children;

  Symbols() {}

  Symbols(const ASTNode& n) : found(n) { assert(stp::SYMBOL == n.GetKind()); }

  // This will create an "empty" node if the array is empty.
  Symbols(const vector<Symbols*>& s) : children(s.begin(), s.end())
  {
    // Children should never be empty. They shouldn't be children.
    for (vector<Symbols*>::const_iterator it = children.begin();
         it != children.end(); it++)
    {
      assert(!(*it)->empty());
    }

    assert(children.size() != 1);
  }

  bool isLeaf() { return !found.IsNull(); }

  bool empty() const { return (found.IsNull() && children.size() == 0); }
};

class SymbolPtrHasher
{
public:
  size_t operator()(const Symbols* n) const { return (size_t)n; };
}; 

#endif
