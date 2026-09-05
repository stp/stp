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

#include "stp/FloatBlaster/FpTotalise.h"

#include "stp/FloatBlaster/FloatBlaster.h"
#include "stp/Util/DagWalk.h"

#include <string>

namespace stp
{

FpTotalise::FpTotalise(STPMgr* bm_) : bm(bm_), nf(bm_->defaultNodeFactory) {}

void FpTotalise::copyArrayEqualityRewrites(ASTNodeMap& out) const
{
  out.insert(array_equality_rewrites.begin(), array_equality_rewrites.end());
}

ASTNode FpTotalise::topLevel(const ASTNode& n)
{
  traversal_cache.clear();
  array_equality_rewrites.clear();
  ASTNode out = visit(n);

  // Pin every rounding mode the final formula names -- declared symbols and
  // rounding-mode-element reads alike -- to the five legal encodings (see the
  // class comment). The walk runs over the visited output so it also sees
  // reads that visit() itself introduced or reshaped.
  //
  // The symbols carry a constraint from their declaration too, but that one
  // is asserted at whatever level was current then, and the node outlives the
  // level: a symbol built inside a vc_push/vc_pop bracket comes out of it
  // hash-consed and unpinned, and answers with a junk encoding. Re-pinning
  // here is what makes the guarantee independent of the assertion stack; the
  // repeat is a duplicate conjunct whenever the original survived.
  //
  // Formulas only: the pinning is a side condition conjoined onto the
  // result, and a term has nowhere to hold one. Model evaluation totalises
  // bare floating-point terms before blasting them (see
  // TermToConstTermUsingModel); wrapping such a term in an AND hands the
  // blaster a formula kind it cannot blast.
  //
  // What makes that safe is that the terms reaching model evaluation come
  // from the assertions, whose reads this pass has already pinned -- so each
  // one resolves to a model value the pinned formula held to a legal
  // encoding. It is *not* that an unpinned carrier would be harmless. An
  // encoding matching none of the five leaves every equality in symfpu's
  // roundingDecision false, which truncates and overflows to max like RTZ
  // but, in makeRoundingResult, leaves returnZero false too -- so an
  // underflow gives the minimum subnormal where RTZ gives zero. Truncating
  // rules out RTP and underflowing to the minimum rules out RTZ: the
  // combination is a sixth behaviour, in no standard, and a formula can tell
  // it from all five. Everything that introduces a rounding mode has to pin
  // it; nothing may rely on the junk encodings being equivalent to a mode.
  if (n.GetType() == BOOLEAN_TYPE)
  {
    ASTNodeSet seen;
    ASTVec constraints;
    collectRoundingModeTerms(out, seen, constraints);
    if (!constraints.empty())
    {
      constraints.push_back(out);
      out = nf->CreateNode(AND, constraints);
    }
  }

  traversal_cache.clear();
  return out;
}

ASTNode FpTotalise::canonicalIndex(const ASTNode& index, unsigned int exp_width,
                                   unsigned int sig_width)
{
  // A second pass over prepared syntax must retain the explicit deferred
  // boundary, rather than mistake its bit-vector result for a legacy raw
  // carrier and eagerly expand another unpack/pack circuit around it.
  if (index.GetKind() == FP_TO_IEEE_BV)
  {
    if (index.Degree() != 1 ||
        index[0].GetSourceSort() !=
            SourceSort::floatingPoint(exp_width, sig_width))
      FatalError("FpTotalise: an existing canonical float array index has "
                 "the wrong source format: ",
                 index);
    return index;
  }

  const SourceSort source_sort = index.GetSourceSort();
  if (source_sort.kind() == SourceSort::Kind::FloatingPoint)
  {
    if (source_sort.exponentWidth() != exp_width ||
        source_sort.significandWidth() != sig_width)
      FatalError("FpTotalise: a float array index disagrees with the array's "
                 "declared index format: ",
                 index);

    return canonicalSourceBits(index);
  }

  // Compatibility for a plain bitvector standing where a float belongs (the
  // legacy parsers accepted these). Constants can be re-interned through the
  // typed FP funnel; a symbolic raw carrier still needs the old eager form,
  // because it has no FP source sort with which to build FP_TO_IEEE_BV.
  if (index.GetKind() == BVCONST)
    return bm->CreateFPConst(index, exp_width, sig_width);

  if (source_sort.kind() == SourceSort::Kind::BitVector ||
      source_sort.kind() == SourceSort::Kind::Unknown)
  {
    return FloatBlaster::canonicalBits(bm, index, exp_width, sig_width);
  }

  FatalError("FpTotalise: a float array index is not a scalar bitvector or "
             "floating-point source value: ",
             index);
}

ASTNode FpTotalise::canonicalSourceBits(const ASTNode& value)
{
  const SourceSort sort = value.GetSourceSort();
  if (sort.kind() != SourceSort::Kind::FloatingPoint)
    FatalError("FpTotalise expected a floating-point source value: ", value);

  // Float constants are interned in canonical SMT form already. Keeping the
  // constant avoids constructing an operation which constant evaluation
  // would immediately fold back to the same node.
  if (value.GetKind() == BVCONST)
    return value;

  return nf->CreateTerm(FP_TO_IEEE_BV, sort.packedWidth(), value);
}

// A continuation stack rather than a call per level: how deeply a float
// expression nests is the input's choice, and this walks the whole of one.
// It preserves the recursion's pre-order while retaining only ancestors, not
// every sibling in a wide frontier. See DeepDag_Test.cpp.
void FpTotalise::collectRoundingModeTerms(const ASTNode& n, ASTNodeSet& seen,
                                          ASTVec& constraints)
{
  walkPreOrder(n, [&](const ASTNode& m) {
    if (!seen.insert(m).second)
      return false;

    // Leaves are visited now, where they were skipped before: a declared
    // RoundingMode symbol is a leaf, and it is exactly as much in need of
    // pinning as a read is.
    if (m.GetKind() == SYMBOL)
    {
      if (bm->isRoundingModeSymbol(m))
        constraints.push_back(bm->roundingModeValidConstraint(m));
      return false;
    }

    if (m.GetKind() == READ && bm->arrayHasRmElement(m[0]))
      constraints.push_back(bm->roundingModeValidConstraint(m));
    return true;
  });
}

ASTNode FpTotalise::rebuild(const ASTNode& n, const ASTVec& children)
{
  ASTNode out;

  if (n.GetType() == BOOLEAN_TYPE)
    out = nf->CreateNode(n.GetKind(), children);
  else if (n.GetIndexWidth() > 0)
    out = nf->CreateArrayTerm(n.GetKind(), n.GetIndexWidth(),
                              n.GetValueWidth(), children);
  else
    out = nf->CreateTerm(n.GetKind(), n.GetValueWidth(), children);

  return FloatBlaster::withFormat(bm, out, n.GetExpWidth(), n.GetSigWidth());
}

ASTNode FpTotalise::unspecified(const char* tag, const ASTNode& index,
                                const ASTVec& floats,
                                unsigned int value_width)
{
  // `floats` rather than the index: the index is what the array is addressed
  // *by*, the formats are part of what array it is.
  return FloatBlaster::unspecifiedValue(bm, tag, floats, index, value_width);
}

ASTNode FpTotalise::conversionIndex(const ASTNode& rounding_mode,
                                    const ASTNode& value)
{
  // Index on canonical bits, not raw ones. SMT-LIB equality on floats makes
  // every NaN equal to every other, so operands that are equal may still
  // differ in payload; indexing on raw bits would let them read different
  // slots and answer differently, losing the very congruence this array
  // exists to provide. FP_TO_IEEE_BV records that round-trip as a source
  // boundary; FloatBlast later collapses the payload while keeping +0 and
  // -0 apart, and can reuse the same unpacked operand as the operation.
  const ASTNode canonical = canonicalSourceBits(value);
  const unsigned int width =
      rounding_mode.GetValueWidth() + canonical.GetValueWidth();
  return bm->CreateTerm(BVCONCAT, width, rounding_mode, canonical);
}

ASTNode FpTotalise::signBit(const ASTNode& value)
{
  const ASTNode canonical = canonicalSourceBits(value);
  const unsigned int top = canonical.GetValueWidth() - 1;
  const ASTNode position = bm->CreateBVConst(32, top);
  return nf->CreateTerm(BVEXTRACT, 1, canonical, position, position);
}

// fp.min and fp.max are unspecified only on (+0, -0) and (-0, +0), and the
// choice is a function of the two sign bits -- so the map that supplies it
// needs four cells, not one per pair of packed values.
//
// Reading symfpu's ordering() (symfpu/core/compare.h:85-152), the choice
// arrives as its `equality` argument and changes the answer in exactly three
// places: both operands the same infinity, both operands zero, and both
// operands equal in sign, exponent and significand. In the first and third
// the enclosing ITE selects between two values that are equal, so the choice
// is unobservable; only the zero case can be seen, and there the result is
// determined by which zero is returned. (unpackedFloat::wellFormed is what
// makes the first and third genuinely unobservable: it forces the default
// exponent and significand whenever the nan/inf/zero flag is set.)
//
// Four cells is therefore not an approximation but exactly complete: the
// (+0, -0) and (-0, +0) cells stay independent, as SMT-LIB requires, and the
// cells the other sign pairs select are unobservable.
//
// Having proved the domain is four points, hold it in four bits. The array
// this used to read was sound, and is still the right encoding for
// fp.to_ubv/fp.to_sbv where the domain really is a rounding mode and a whole
// packed value -- but for a four-point map it buys nothing and costs a great
// deal that is not local. FpTotalise runs before containsArrayOps and
// numberOfReadsLessThan, so a read it introduces is indistinguishable from the
// user's: ten fp.mins turn a pure QF_FP query into an "array" problem, forcing
// counterexample construction on and skipping the size-reducing fixed point,
// and three of them are enough to stop a QF_ABVFP query Ackermannising the
// user's own arrays. Narrowing the index from 2(e+s) bits to two, as this
// previously did, shrinks each index term but not the number of reads, so it
// did not address any of that.
//
// The cells are free and the selection is a mux, so the result is still a
// function of the operands; hash-consing gives the congruence the array's
// index equalities were giving. The mux is still not constant, so these nodes
// still stay out of constant folding, which is what we want -- their results
// genuinely are not constants even when their operands are.
ASTNode FpTotalise::zeroChoice(const char* tag, const ASTNode& left,
                               const ASTNode& right, const ASTVec& floats)
{
  const ASTNode cells = FloatBlaster::unspecifiedCells(bm, tag, floats, 4);

  ASTNode bit[4];
  for (unsigned int i = 0; i < 4; i++)
  {
    const ASTNode position = bm->CreateBVConst(32, i);
    bit[i] = nf->CreateTerm(BVEXTRACT, 1, cells, position, position);
  }

  const ASTNode zero = bm->CreateZeroConst(1);
  const ASTNode left_positive = nf->CreateNode(EQ, signBit(left), zero);
  const ASTNode right_positive = nf->CreateNode(EQ, signBit(right), zero);

  // Sequenced deliberately: C++ does not order a call's arguments against
  // each other, and node ids are handed out in creation order, so building
  // both branches inside the one call lets the compiler decide the numbering
  // that ends up in the CNF.
  const ASTNode leftPositiveCase =
      nf->CreateTerm(ITE, 1, right_positive, bit[0], bit[1]);
  const ASTNode leftNegativeCase =
      nf->CreateTerm(ITE, 1, right_positive, bit[2], bit[3]);
  return nf->CreateTerm(ITE, 1, left_positive, leftPositiveCase,
                        leftNegativeCase);
}

// The pass is a call per level of a float expression, and how deeply one
// nests is the input's choice: a query built from 30,000 nested fp.add
// operations died here, and was the nearest wall left once the simplifier's
// formula arms were converted. So the answers underneath are
// filled from the bottom up first, and the pass then finds every child it
// asks for already answered and stops one level down. See DagWalk.h, and
// DeepDag_Test.cpp for the depth.
//
// Sound because the pass has no exit that skips a child: it answers from a
// cache, or from having no children, or it visits all of them. So priming
// reaches exactly the nodes the recursion reached, in the same post-order.
// That matters more here than it usually would, because this pass mints fresh
// variables -- see unspecified() and zeroChoice() -- and visiting in a
// different order would number them differently and move every clause after
// them. The CNF comparison is what checks it.
ASTNode FpTotalise::visit(const ASTNode& n)
{
  PrimeAudit::Running running(memoAudit, n);

  if (n.Degree() == 0)
    return n;

  const ASTNodeMap::const_iterator persistent = persistent_cache.find(n);
  if (persistent != persistent_cache.end())
    return persistent->second;
  const ASTNodeMap::const_iterator current = traversal_cache.find(n);
  if (current != traversal_cache.end())
    return current->second;

  // Nothing below `m` needs filling: it is answered already, or it has no
  // children to be answered from.
  auto settled = [this](const ASTNode& m) {
    return m.Degree() == 0 || persistent_cache.count(m) != 0 ||
           traversal_cache.count(m) != 0;
  };

  bool fill = false;
  for (size_t i = 0; i < n.Degree() && !fill; i++)
    fill = !settled(n[i]);

  if (!fill)
    return totalise(n);

  // The walk finishes with the node it started from, so the last answer it
  // records is that one.
  ASTNode answer;
  primeMemo(
      n, [&](const ASTNode& child)
      { return settled(child) ? Walk::Skip : Walk::Descend; },
      [&](const ASTNode& m, PrimeMemoReady) { answer = totalise(m, true); });
  return answer;
}

// One node, with its children already totalised -- which is what the walk
// below arranges, and what its own calls on those children then find.
ASTNode FpTotalise::totalise(const ASTNode& n, const bool knownMissing)
{
  if (n.Degree() == 0)
    return n;

  // visit's classifier already checked both caches for primed nodes. Neither
  // totalising a descendant nor rebuilding it can cache its ancestor.
  if (!knownMissing)
  {
    const ASTNodeMap::const_iterator persistent = persistent_cache.find(n);
    if (persistent != persistent_cache.end())
      return persistent->second;
    const ASTNodeMap::const_iterator current = traversal_cache.find(n);
    if (current != traversal_cache.end())
      return current->second;
  }

  ASTVec children;
  children.reserve(n.Degree() + 1);

  bool changed = false;
  for (size_t i = 0; i < n.Degree(); i++)
  {
    const ASTNode c = visit(n[i]);
    changed = changed || (c != n[i]);
    children.push_back(c);
  }

  const Kind k = n.GetKind();

  // fp.min/fp.max: which zero comes back for (+0, -0) is unspecified. Carried
  // as a 1-bit bitvector rather than a Boolean, because every child of a term
  // has to be a term -- the array transformer walks them all. The blaster
  // turns it into a proposition.
  if ((k == FP_MIN || k == FP_MAX) && children.size() == 2)
  {
    ASTVec floats;
    floats.push_back(children[0]);
    floats.push_back(children[1]);

    children.push_back(zeroChoice(k == FP_MIN ? "min_zero" : "max_zero",
                                  children[0], children[1], floats));
    changed = true;
  }
  // fp.to_ubv/fp.to_sbv: unspecified for NaN, the infinities and anything out
  // of range. Children are (m, rm, x); the rounding mode joins the float in
  // the index, since the same float may convert differently under different
  // modes.
  else if ((k == FP_TO_UBV || k == FP_TO_SBV) && children.size() == 3)
  {
    ASTVec floats;
    floats.push_back(children[2]);

    children.push_back(
        unspecified(k == FP_TO_UBV ? "to_ubv" : "to_sbv",
                    conversionIndex(children[1], children[2]), floats,
                    n.GetValueWidth()));
    changed = true;
  }
  // An access over a float-indexed array addresses canonical bits (see the
  // class comment). Each solve totalises the raw assertions afresh -- the
  // rewritten formula is solve-local -- so a canonicalised index never
  // comes back through here, and identical raw indexes hash-cons to
  // identical canonical circuits across solves.
  else if (k == READ || k == WRITE)
  {
    unsigned int index_exp = 0;
    unsigned int index_sig = 0;
    if (bm->arrayHasFpIndex(children[0], index_exp, index_sig))
    {
      const ASTNode canon =
          canonicalIndex(children[1], index_exp, index_sig);
      if (canon != children[1])
      {
        children[1] = canon;
        changed = true;
      }
    }
  }

  const ASTNode out = changed ? rebuild(n, children) : n;

  traversal_cache[n] = out;
  if (out != n && k == ARRAY_EQ)
    array_equality_rewrites[n] = out;

  const SourceSort source_sort = n.GetSourceSort();
  const bool fp_array_access =
      (k == READ || k == WRITE) && n.Degree() > 0 &&
      n[0].GetSourceSort().kind() == SourceSort::Kind::Array &&
      n[0].GetSourceSort().index().kind() ==
          SourceSort::Kind::FloatingPoint;
  if (out != n &&
      (is_FP_kind(k) || fp_array_access ||
       source_sort.kind() == SourceSort::Kind::FloatingPoint))
    persistent_cache[n] = out;
  return out;
}

} // namespace stp
