/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: July 2026
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

#ifndef FPTOTALISE_H
#define FPTOTALISE_H

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"

namespace stp
{

// Makes the partial floating-point operations total.
//
// SMT-LIB leaves four operations unspecified on some of their inputs:
// fp.min and fp.max may return either zero given +0 and -0, and fp.to_ubv
// and fp.to_sbv may return anything at all for NaN, the infinities, and
// values out of range for the target width. The blaster needs a concrete
// value to use in those cases, and it has to be one the solver is free to
// choose -- but also a *function* of the operands, so that equal inputs give
// equal results. An unconstrained value per occurrence would give the
// freedom and lose the congruence, which is unsound for equality reasoning.
//
// STP has no uninterpreted functions, but an array is exactly a congruent
// map: one array per operation and signature, read at an index built from
// the operands. This pass rewrites each partial operation into a total one
// carrying that read as an extra child.
//
// It has to be a pass rather than something done when the node is built or
// when it is blasted. Introducing the array during blasting is too late --
// the solver never sees it, so the counterexample evaluator cannot read a
// value for it out of the model, and the refinement loop fails to converge.
// Running here, before the array transformer and before the reads are
// counted, puts the array in the problem like any other.
//
// A pleasant side effect: the extra child is not constant, so these nodes
// stop being candidates for constant folding, which is what we want. Their
// results genuinely are not constants even when their operands are.
//
// The pass also adapts array accesses whose index or element sort is
// floating-point or RoundingMode, for the same reason at the same moment:
//
//  - A read or write over a float-indexed array has its index rewritten to
//    canonical bits. SMT-LIB '=' on floats identifies every NaN with every
//    NaN, while everything downstream -- the simplifier's read-over-write
//    rules, the array transformer's index equalities, refinement's
//    bit-level congruence axioms -- compares raw index bits. Quotienting
//    the index here, before any of them run, lets all of it stay purely
//    bitvector. (Float *constants* already intern canonically, which is
//    what keeps the node-creation-time constant comparisons sound before
//    this pass gets its turn.)
//
//  - Every read from a RoundingMode-element array is pinned to the five
//    legal encodings, exactly as declaring a RoundingMode variable pins
//    it: a select is the other way a RoundingMode value enters the formula
//    out of thin air, and without the constraint the carrier's 27 junk
//    patterns would be satisfiable "modes". Conjoined at solve time rather
//    than asserted at creation, so every route here -- parser or C API,
//    before or after push/pop/reset-assertions -- is covered.
class FpTotalise // not copyable
{
public:
  FpTotalise(STPMgr* bm_);

  FpTotalise(const FpTotalise&) = delete;
  FpTotalise& operator=(const FpTotalise&) = delete;

  // Returns `n` with every partial floating-point operation replaced by its
  // total form. Idempotent: operations that already carry an unspecified
  // value are left alone.
  ASTNode topLevel(const ASTNode& n);

  // The same rewriting for a lone term. A term cannot absorb the
  // RoundingMode-read pinnings topLevel would conjoin onto a formula,
  // so they are appended to `sideConstraints` for the caller to
  // conjoin wherever the term is used.
  ASTNode topLevelTerm(const ASTNode& term, ASTVec& sideConstraints);

private:
  ASTNode visit(const ASTNode& n);

  // The canonical form of an index over a float-indexed array whose index
  // format is (exp_width, sig_width): constants re-intern through the
  // canonicalising constant funnel, everything else goes through
  // FloatBlaster::canonicalBits.
  ASTNode canonicalIndex(const ASTNode& index, unsigned int exp_width,
                         unsigned int sig_width);

  // Collect the validity constraint of every READ over a
  // RoundingMode-element array in `n`.
  void collectRmElementReads(const ASTNode& n, ASTNodeSet& seen,
                             ASTVec& constraints);

  // Rebuild `n` around new children, preserving its widths -- including the
  // floating-point format, which is per-node state that rebuilding drops.
  ASTNode rebuild(const ASTNode& n, const ASTVec& children);

  // The array read supplying the unspecified value. `prefix`, when not null,
  // is prepended to the index; `floats` are canonicalised before being
  // concatenated into it.
  ASTNode unspecified(const char* tag, const ASTNode& prefix,
                      const ASTVec& floats, unsigned int value_width);

  STPMgr* bm;
  NodeFactory* nf;
  ASTNodeMap cache;
};

} // namespace stp

#endif
