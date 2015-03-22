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

#ifndef BBNodeManagerAIG_H_
#define BBNodeManagerAIG_H_

#include <stdint.h>
#include "BBNodeAIG.h"
#include "stp/ToSat/ToSATBase.h"

class Cnf_Dat_t_;
typedef struct Aig_Man_t_            Aig_Man_t;
typedef struct Aig_Obj_t_            Aig_Obj_t;

typedef Cnf_Dat_t_ CNFData;
typedef Aig_Obj_t AIGNode;

namespace stp
{
class ASTNode;
class STPMgr; // we ignore this anyway.

extern vector<BBNodeAIG> _empty_BBNodeAIGVec;

// Creates AIG nodes with ABC and wraps them in BBNodeAIG's.
class BBNodeManagerAIG
{
public:
  Aig_Man_t* aigMgr;

  // Map from symbols to their AIG nodes.
  typedef std::map<ASTNode, vector<BBNodeAIG>> SymbolToBBNode;

  SymbolToBBNode symbolToBBNode;

  int totalNumberOfNodes();

private:
  // AIGs can only take two parameters. This makes a log_2 height
  // tower of varadic inputs.
  Aig_Obj_t* makeTower(Aig_Obj_t* (*t)(Aig_Man_t*, Aig_Obj_t*, Aig_Obj_t*),
                       vector<BBNodeAIG>& children)
  {
    std::deque<Aig_Obj_t*> names;

    for (size_t i = 0, size = children.size(); i < size; ++i)
      names.push_back(children[i].n);

    while (names.size() > 2)
    {
      Aig_Obj_t* a = names.front();
      names.pop_front();

      Aig_Obj_t* b = names.front();
      names.pop_front();

      Aig_Obj_t* n = t(aigMgr, a, b);
      names.push_back(n);
    }

    // last two now.
    assert(names.size() == 2);

    Aig_Obj_t* a = names.front();
    names.pop_front();

    Aig_Obj_t* b = names.front();
    names.pop_front();

    return t(aigMgr, a, b);
  }

  // no copy. no assignment.
  BBNodeManagerAIG& operator=(const BBNodeManagerAIG& other);
  BBNodeManagerAIG(const BBNodeManagerAIG& other);

public:
  BBNodeManagerAIG();

  void stop();

  ~BBNodeManagerAIG();

  BBNodeAIG getTrue();

  BBNodeAIG getFalse();

  // The same symbol always needs to return the same AIG node,
  // if it doesn't you will get the wrong answer.
  BBNodeAIG CreateSymbol(const ASTNode& n, unsigned i);

  BBNodeAIG CreateNode(Kind kind, vector<BBNodeAIG>& children);

  BBNodeAIG
  CreateNode(Kind kind, const BBNodeAIG& child0,
             const vector<BBNodeAIG>& back_children = _empty_BBNodeAIGVec);

  BBNodeAIG
  CreateNode(Kind kind, const BBNodeAIG& child0, const BBNodeAIG& child1,
             const vector<BBNodeAIG>& back_children = _empty_BBNodeAIGVec);

  BBNodeAIG
  CreateNode(Kind kind, const BBNodeAIG& child0, const BBNodeAIG& child1,
             const BBNodeAIG& child2,
             const vector<BBNodeAIG>& back_children = _empty_BBNodeAIGVec);

};
}

#endif /* BBNodeManagerAIG_H_ */
