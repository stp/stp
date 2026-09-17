/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: September, 2026
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

#ifndef STP_CONGRUENCECANDIDATES_H
#define STP_CONGRUENCECANDIDATES_H

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"

#include <map>
#include <vector>

namespace stp

{

// Equalities between terms the query never says are equal.
//
// A query is hard when two of its terms are equal and nothing in the
// formula says so. The bit-blaster gives each its own circuit, everything
// built on them is duplicated, and the SAT solver has to rediscover the
// equality through both copies -- through two dividers, say, rather than
// through none.
//
// Where to look is decided by congruence. If a query applies the same
// operator to two terms in the same position with the same other operands
//
//     bvsdiv(s, 2)   and   bvsdiv(t, 2)
//
// then s == t collapses both applications into one, and everything above
// them with it. That the query built both is the evidence that they are
// worth comparing: it is a pairing the formula already chose, not a guess
// over every pair of terms.
//
// Each candidate is then *proved*, not assumed. Asking whether s == t is
// itself a bit-vector query, and a small one -- it holds the two terms and
// nothing else, where the query it came from holds everything -- so it is
// put to the solver with a conflict budget. A candidate that comes back
// unsatisfiable when negated is a theorem, and only those are kept. The
// budget means an undecided candidate is simply dropped: this never has to
// be right, only sound.
//
// Adding a theorem to a query changes neither its models nor its answer, so
// the pass is an identity whatever the candidates turn out to be. What it
// costs is the sub-solves, which is why the number of them is capped rather
// than the pass being run over every pairing a large query offers.
class CongruenceCandidates
{
  STPMgr* bm;
  NodeFactory* nf;

  size_t candidateLimit;
  int64_t conflictBudget;

  uint64_t proposed;
  uint64_t tested;
  uint64_t proved;

  // The operator, the position, and the other operands: one slot of one
  // application, which every term the query puts there shares.
  typedef std::pair<Kind, unsigned> Slot;
  typedef std::pair<Slot, std::vector<uint64_t>> Key;

  // Ordered, so that the candidates come out in one order however the walk
  // reached them.
  std::map<Key, std::vector<ASTNode>> slots;

  // Whether merging the operands of this kind is worth a sub-solve: a
  // division or a product shares a circuit, where an extract shares
  // wiring.
  static bool worthMerging(Kind k);

  void collect(const ASTNode& n);

  // Whether `a == b` holds for every assignment. Runs the equality as its
  // own query, under the conflict budget; false covers both "does not
  // hold" and "not settled within the budget".
  bool proves(const ASTNode& equality);

public:
  CongruenceCandidates(const CongruenceCandidates&) = delete;
  CongruenceCandidates& operator=(const CongruenceCandidates&) = delete;

  CongruenceCandidates(STPMgr* bm_, NodeFactory* nf_, size_t candidateLimit_,
                       int64_t conflictBudget_)
      : bm(bm_), nf(nf_), candidateLimit(candidateLimit_),
        conflictBudget(conflictBudget_), proposed(0), tested(0), proved(0)
  {
  }

  // The equalities that hold, as top-level formulas to conjoin. Empty when
  // the query offers no pairing, which is the common case for a query whose
  // terms are already shared.
  ASTVec derive(const ASTNode& input);
};
}

#endif
