/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: Aug, 2026
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

#ifndef BVEQ_CONGRUENCE_CLOSURE_H
#define BVEQ_CONGRUENCE_CLOSURE_H

#include "stp/Sat/SATSolver.h"
#include <vector>

namespace stp
{

// Word-level transitivity over the equality abstractions in one candidate
// model: the equalities the model asserts are merged, and any disequality it
// asserts between two terms that merging has brought together is a conflict.
// Each conflict is handed back to the solver as the clause
// (~e1 | ... | ~ek | d) -- the chain of asserted equalities that connects the
// disequality's two sides, which is what makes the clause a theorem of
// equality rather than a guess.
//
// Two structures, because they answer different questions. `parent_`/`rank_`
// is the union-find that decides membership, and it links whole classes by
// rank, so its edges say nothing about which equality justified a merge.
// `proofParent_`/`proofEdge_` is a separate proof forest whose edges each
// carry the one equality asserted between exactly those two endpoints; the
// chain between any two terms is then the path between them in that forest.
// Reading the explanation off the union-find instead drops the edges below
// the link -- for a=b then b=c, the merge of c into a's class is recorded as
// c's own link and the edge a=b is never on the path -- which yields a
// clause the theory does not entail, and refutes satisfiable queries.
class BVEQCongruenceClosure
{
public:
  struct EqInfo
  {
    unsigned left;
    unsigned right;
    unsigned satVar;
    bool modelTrue;
  };

  unsigned check(const std::vector<EqInfo>& equalities, SATSolver& solver);

private:
  // Membership only.
  std::vector<unsigned> parent_;
  std::vector<unsigned> rank_;

  // The proof forest. Every merge adds one edge, so its components are the
  // union-find's classes, and `proofEdge_[x]` indexes the equality asserted
  // between `x` and `proofParent_[x]` themselves.
  std::vector<unsigned> proofParent_;
  std::vector<int> proofEdge_;

  void init(unsigned n);
  unsigned find(unsigned x);
  void unite(unsigned x, unsigned y, unsigned eqIdx);

  // Turn `x` into the root of its proof tree by reversing the links along
  // the path it currently takes to the root. Each link keeps the equality it
  // carried, since that equality is between the link's two endpoints and so
  // justifies it in either direction.
  void reroot(unsigned x);

  // The equalities on the proof path from `x` to `y`, which must be in the
  // same class. Appended to `edges`.
  void explain(unsigned x, unsigned y, std::vector<unsigned>& edges);
};

} // namespace stp

#endif
