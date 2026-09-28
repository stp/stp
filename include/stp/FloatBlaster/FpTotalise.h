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
#include "stp/Util/DagWalk.h"

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
// STP has no uninterpreted functions, so the map is built from what it does
// have. This pass rewrites each partial operation into a total one carrying
// that map's answer as an extra child.
//
// Which map depends on how big the choice's domain is. fp.to_ubv/fp.to_sbv
// are unspecified over a rounding mode and a whole packed value, so they read
// a shared array -- an array being exactly a congruent map: one per operation
// and signature, read at an index built from the operands. fp.min/fp.max are
// unspecified on four sign-bit combinations and no more (see zeroChoice), so
// they select between four free bits. Both are functions of the operands;
// only the first needs the array theory to be one.
//
// It has to be a pass rather than something done when the node is built or
// when it is blasted. Introducing the array during blasting is too late --
// the solver never sees it, so the counterexample evaluator cannot read a
// value for it out of the model, and the refinement loop fails to converge.
// Running here, before the array transformer and before the reads are
// counted, puts the array in the problem like any other. That placement is
// also why the small choice must *not* be an array: a read introduced here is
// indistinguishable from the user's to every heuristic downstream.
//
// A pleasant side effect either way: the extra child is not constant, so
// these nodes stop being candidates for constant folding, which is what we
// want. Their results genuinely are not constants even when their operands
// are.
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
//  - Every rounding mode the formula names out of thin air -- a declared
//    RoundingMode symbol, or a read from a RoundingMode-element array -- is
//    pinned to the five legal encodings. Without the constraint the
//    carrier's 27 junk patterns would be satisfiable "modes", and they are
//    not merely unlikely: they are a sixth behaviour a formula can tell
//    from all five (see topLevel).
//
//    Conjoined at solve time rather than asserted at creation, so every
//    route here -- parser or C API, before or after push/pop/
//    reset-assertions -- is covered. The symbols are also pinned where they
//    are declared, which is the right thing whenever that assertion
//    survives; it is not what makes them safe. Assertions are levelled and
//    the nodes are not, so a symbol built inside a vc_push/vc_pop bracket
//    outlives the constraint that was supposed to hold it.
class FpTotalise // not copyable
{
public:
  FpTotalise(STPMgr* bm_);

  FpTotalise(const FpTotalise&) = delete;
  FpTotalise& operator=(const FpTotalise&) = delete;

  // Returns one unprocessed solve root with every partial floating-point
  // operation replaced by its total form. Operations that already carry an
  // unspecified value are left alone, but the complete pass is deliberately
  // not structurally idempotent: feeding its output back through it would
  // canonicalise float-array indexes a second time.
  ASTNode topLevel(const ASTNode& n);

  // Copy the opaque array equalities rebuilt by the most recent topLevel()
  // call. Public expression handles retain the pre-totalisation node, while
  // solve-boundary array lowering sees the rebuilt node; the solve pipeline
  // uses these aliases to keep model evaluation of the public handle tied to
  // the exact formula that was solved.
  void copyArrayEqualityRewrites(ASTNodeMap& out) const;

private:
  ASTNode visit(const ASTNode& n);

  // The pass proper, for one node whose children visit() has already
  // answered. Split out so that visit() can fill those answers from the
  // bottom up rather than by calling itself once per level.
  ASTNode totalise(const ASTNode& n, bool knownMissing = false);

  // The canonical form of an index over a float-indexed array whose index
  // format is (exp_width, sig_width): constants re-intern through the
  // canonicalising constant funnel, source FP expressions become an explicit
  // FP_TO_IEEE_BV boundary, and legacy raw carriers use canonicalBits.
  ASTNode canonicalIndex(const ASTNode& index, unsigned int exp_width,
                         unsigned int sig_width);

  // Make a source FP value's canonical carrier boundary explicit in the
  // source DAG. FloatBlast can then share its cached unpacked value with the
  // surrounding operation instead of this pass eagerly building a separate
  // unpack/pack circuit.
  ASTNode canonicalSourceBits(const ASTNode& value);

  // Collect the validity constraint of every term in `n` that denotes a
  // rounding mode out of thin air: a declared RoundingMode symbol, or a READ
  // over a RoundingMode-element array.
  void collectRoundingModeTerms(const ASTNode& n, ASTNodeSet& seen,
                                ASTVec& constraints);

  // Rebuild `n` around new children, preserving its widths -- including the
  // floating-point format, which is per-node state that rebuilding drops.
  ASTNode rebuild(const ASTNode& n, const ASTVec& children);

  // The array read supplying the unspecified value. `index` addresses it and
  // `floats` are the operation's floating-point operands, which name the
  // array -- a format is not recoverable from a packed width, and the same
  // operation at two formats is two different unspecified functions.
  ASTNode unspecified(const char* tag, const ASTNode& index,
                      const ASTVec& floats, unsigned int value_width);

  // The index for fp.to_ubv/fp.to_sbv: the rounding mode and the float's
  // canonical bits. The result is unspecified for NaN, the infinities and
  // anything out of range, and which of those applies depends on the whole
  // value, so the whole value goes into the index.
  ASTNode conversionIndex(const ASTNode& rounding_mode, const ASTNode& value);

  // The unspecified value for fp.min/fp.max: four free bits, selected between
  // by the two operands' sign bits and nothing else. See the definition for
  // why four cells are not merely sound but exactly complete, and for why this
  // one does not go through an array.
  ASTNode zeroChoice(const char* tag, const ASTNode& left,
                     const ASTNode& right, const ASTVec& floats);

  // A float's sign, taken from its canonical packed bits.
  ASTNode signBit(const ASTNode& value);

  STPMgr* bm;
  NodeFactory* nf;

  // Debug-only: verify that priming keeps visit's call depth bounded.
  PrimeAudit memoAudit{"FpTotalise::visit", 8};
  // `traversal_cache` preserves DAG sharing only for one topLevel walk and is
  // released immediately afterwards. `persistent_cache` keeps just the
  // source FP/array nodes whose encoding changed and may be requested again
  // during model evaluation. Retaining every ordinary BV node here can keep
  // enormous pre-simplification DAGs alive for the lifetime of the model.
  ASTNodeMap traversal_cache;
  ASTNodeMap persistent_cache;

  // ARRAY_EQ is lowered by the extensionality layer after this pass. Keep
  // only the aliases whose operands preparation rebuilt, so public handles
  // and the prepared solve root identify the same opaque equality without
  // retaining the rest of the traversal DAG.
  ASTNodeMap array_equality_rewrites;
};

} // namespace stp

#endif
