/********************************************************************
 * AUTHORS: Trevor Hansen
 *
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

/*
 Common sub-sum extraction.

 Two n-ary additions that share operands each build their own adder chain,
 because a BVPLUS is hash-consed as a whole node and shares nothing with a
 different BVPLUS. Given (a + b + c) and (a + c + d), factoring out (a + c)
 lets that adder be built once:

    (a + b + c), (a + c + d)  -->  s = (a + c);  (s + b), (s + d)

 Addition is associative and commutative modulo 2^w, so any regrouping is
 value preserving; the pass needs no bit-level information.

 Greedily extracts the operand pair that occurs in the most sums, which is
 the usual adder-network CSE heuristic. Each extraction removes one adder
 from every sum it fires on, less the one spent building the shared pair.

 Nested additions hide the opportunity -- (a + (b + c)) and (b + (a + d))
 share {a,b} but no node -- so this is most effective after Flatten has
 turned the additions into flat operand lists.

 Multiplication is associative and commutative modulo 2^w for the same
 reason, so the pass is parameterised by the operator and runs once over
 the n-ary bvadd nodes and once over the n-ary bvmul nodes. Beyond
 building the shared multiplier once, a shared sub-product makes a pair of
 otherwise-unused variables visible to unconstrained-variable elimination:
 in (a*b*c) and (a*b*d) the pair {a,b} is used nowhere else, and once
 (a*b) is a node of its own that pass collapses it to a fresh variable.
*/

#ifndef COMMONSUBSUM_H_
#define COMMONSUBSUM_H_

#include "extlib-unordered-dense/ankerl/unordered_dense.h"
#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include <map>

namespace stp
{

class CommonSubSum
{
  STPMgr* stpMgr;
  NodeFactory* nf;

  // The operator whose n-ary applications are rewritten: BVPLUS or BVMULT.
  // Sums and products are tallied separately -- a pair shared between a sum
  // and a product has no single node both could use.
  const Kind kind;

  // Adders removed, counting the one spent building each shared sub-sum.
  long saved;

  // Set when a size guard stopped the search early, so the result is a
  // partial extraction rather than a fixed point.
  bool truncated;

  // Operand lists of the additions being rewritten, keyed by node number,
  // and a way back from a node number to its node.
  std::map<uint64_t, ASTVec> operands;
  std::map<uint64_t, ASTNode> byNum;

  typedef std::pair<uint64_t, uint64_t> NodePair;

  // Node numbers are allocated densely from zero, so the raw pair has almost
  // no entropy in its high bits. One multiply-xor spreads it over the whole
  // word, which is what 'is_avalanching' promises the table.
  struct PairHash
  {
    using is_avalanching = void;
    uint64_t operator()(const NodePair& p) const noexcept
    {
      return ankerl::unordered_dense::detail::wyhash::mix(
          p.first + UINT64_C(0x9E3779B97F4A7C15), p.second);
    }
  };

  // How many of the additions hold each pair of operands. Only the tally is
  // kept: the additions holding the winning pair are recovered by a scan,
  // which is far cheaper than a list of them hanging off every pair. The
  // table is patched as additions change rather than rebuilt each round.
  ankerl::unordered_dense::map<NodePair, uint32_t, PairHash> occurrences;

  // Operands worth pairing. A pair can only be shared by two additions if
  // each of its operands is, so an operand that starts out in one addition
  // can be left out of the enumeration entirely -- which on a query whose
  // additions share nothing is all of them.
  ankerl::unordered_dense::set<uint64_t> shareable;

  void collect(const ASTNode& n, ASTNodeSet& seen, ASTVec& plusNodes);
  void markShareable();
  void eligibleOf(const ASTVec& v, std::vector<uint64_t>& out) const;
  bool bump(uint64_t a, uint64_t b);
  void drop(uint64_t a, uint64_t b);
  bool addPairs(const ASTVec& v);
  bool repair(const ASTVec& before, const ASTVec& after);
  bool promote(const ASTNode& n);
  bool buildOccurrences();
  bool extractOnePair();
  ASTNode rebuild(const ASTNode& n, const std::map<uint64_t, ASTVec>& changed,
                  ASTNodeMap& cache);

public:
  CommonSubSum(const CommonSubSum&) = delete;
  CommonSubSum& operator=(const CommonSubSum&) = delete;

  CommonSubSum(STPMgr* stp_, NodeFactory* nf_, Kind kind_)
      : stpMgr(stp_), nf(nf_), kind(kind_), saved(0), truncated(false)
  {
    assert(kind == BVPLUS || kind == BVMULT);
  }

  ASTNode topLevel(const ASTNode& n);
};
}

#endif
