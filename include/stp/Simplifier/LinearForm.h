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

#ifndef STP_LINEARFORM_H
#define STP_LINEARFORM_H

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"

#include <map>
#include <unordered_map>

namespace stp
{

// One canonical spelling for every linear combination of bit-vector terms.
//
// The node factory hash-conses, so two terms that are the same node are
// bit-blasted once and share every circuit built on top of them. Two terms
// that are *equal* but spelled differently share nothing: each gets its own
// adders, its own divider, its own everything, and whatever sits above them
// -- an extract, a division, a comparison -- is duplicated too. The SAT
// solver then has to rediscover, through those duplicated circuits, an
// equality that is a fact about the arithmetic.
//
// Rewriting every bit-vector term into a canonical sum
//
//     c_1 * a_1  +  ...  +  c_n * a_n  +  k
//
// over the maximal non-linear sub-terms a_i removes the choice of spelling.
// The addends are ordered by the factory, which sorts commutative children,
// so two equal combinations are built as the same node and the sharing is
// recovered.
//
// Two groups of nodes feed a combination:
//
//   * BVPLUS, BVSUB, BVUMINUS, and a BVMULT with at most one non-constant
//     operand -- the linear operators themselves, where a constant is
//     multiplied into the coefficients below it and a sum is spliced into
//     its parent's;
//
//   * concat(extract(X, w-1-k, 0), 0_k), which is X * 2^k at width w. LLVM
//     and the front ends spell a shift left by a constant this way, and it
//     has to become a coefficient or every sum containing one is opaque.
//     A power-of-two coefficient is written back as the same shape rather
//     than as a product, which keeps the spelling canonical while leaving
//     the blaster wiring where it had wiring.
//
// Everything else is an atom: its own children are canonical, and it enters
// the combination whole. That includes a signed division, whose negative
// constant divisors the node factory already normalises to positive ones --
// so the two mirror images of a division arrive here as one node with a
// BVUMINUS over it, which is a coefficient this pass then reads.
//
// The rewrite is an identity, not an approximation. It neither adds nor
// removes models, and it is idempotent -- the canonical form of a canonical
// form is itself.
//
// Distributing a constant over a sum costs one multiply per addend where
// there was one before, so the growth is bounded per node rather than
// per DAG; `addendLimit` caps it. A combination over more atoms than that
// is left alone, which is a decision about the combination rather than
// about the spelling, so two equal terms are still either both expanded or
// both left.
class LinearForm
{
  STPMgr* bm;
  NodeFactory* nf;

  // The canonical form of a node, by node number.
  std::unordered_map<uint64_t, ASTNode> fromTo;

  // Ordered by atom node number, so that the addends come out in one order
  // however the traversal reached them.
  typedef std::map<uint64_t, std::pair<ASTNode, ASTNode>> TermMap;

  // A combination at one width: the atoms with their coefficients, and the
  // constant.
  struct Combination
  {
    unsigned width;
    TermMap terms;
    ASTNode constant;
  };

  size_t addendLimit;
  uint64_t rewritten; // atoms whose spelling this pass chose

  // Arbitrary-width constant arithmetic, through the evaluator the rest of
  // the simplifier uses: a coefficient is as wide as the term it scales.
  ASTNode constPlus(const ASTNode& a, const ASTNode& b, unsigned width) const;
  ASTNode constTimes(const ASTNode& a, const ASTNode& b, unsigned width) const;
  ASTNode constNegate(const ASTNode& a, unsigned width) const;
  ASTNode powerOfTwo(unsigned bit, unsigned width) const;
  int powerOfTwoExponent(const ASTNode& c, unsigned width) const;

  // concat(extract(X, w-1-k, 0), 0_k): a shift left by a constant, both as
  // the front ends spell it and as this pass writes a power-of-two
  // coefficient back.
  bool shiftShape(const ASTNode& n, unsigned width, ASTNode& source,
                  unsigned& shift) const;
  ASTNode shiftBy(const ASTNode& term, unsigned shift, unsigned width);

  static bool isConstant(const ASTNode& n);
  static bool isZeroConstant(const ASTNode& n);

  void addTerm(Combination& c, const ASTNode& atom, const ASTNode& coeff);

  // Add coeff * node into c. `node` is already canonical, so this reads a
  // combination back out of the spelling this pass gives it.
  void addScaled(Combination& c, const ASTNode& node, const ASTNode& coeff);

  // The combination `n` denotes, given canonical children. False when `n`
  // is not one of the shapes above, and is therefore an atom.
  bool combinationOf(const ASTNode& n, const ASTVec& children, unsigned width,
                     Combination& out);

  ASTNode emit(const Combination& c);
  ASTNode rebuild(const ASTNode& n, const ASTVec& children);
  ASTNode canonicalise(const ASTNode& n, const ASTVec& children);

  struct Frame;

public:
  LinearForm(const LinearForm&) = delete;
  LinearForm& operator=(const LinearForm&) = delete;

  LinearForm(STPMgr* stp_, NodeFactory* nf_, size_t addendLimit_)
      : bm(stp_), nf(nf_), addendLimit(addendLimit_), rewritten(0)
  {
  }

  ASTNode topLevel(const ASTNode& n);
};
}

#endif
