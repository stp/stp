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

#include <string>

namespace stp
{

FpTotalise::FpTotalise(STPMgr* bm_) : bm(bm_), nf(bm_->defaultNodeFactory) {}

ASTNode FpTotalise::topLevel(const ASTNode& n)
{
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

  return out;
}

ASTNode FpTotalise::canonicalIndex(const ASTNode& index, unsigned int exp_width,
                                   unsigned int sig_width)
{
  if (index.GetKind() == BVCONST)
  {
    // A plain bitvector constant standing where a float belongs: re-intern
    // it through the canonicalising constant funnel, which maps every NaN
    // pattern to the canonical quiet NaN and hands non-NaN bits back
    // unchanged (as a float constant, equally fine as an index).
    if (index.GetExpWidth() == 0)
      return bm->CreateFPConst(index, exp_width, sig_width);
  }
  else if (index.GetExpWidth() == 0)
  {
    // A non-constant plain bitvector in index position (the parsers are lax
    // about sorts): treat it as the float its bits spell.
    return FloatBlaster::canonicalBits(bm, index, exp_width, sig_width);
  }

  if (index.GetExpWidth() != exp_width || index.GetSigWidth() != sig_width)
    FatalError("FpTotalise: a float array index disagrees with the array's "
               "declared index format: ",
               index);

  // A float constant needs no circuit: constants intern canonically.
  if (index.GetKind() == BVCONST)
    return index;

  return FloatBlaster::canonicalBits(bm, index);
}

void FpTotalise::collectRoundingModeTerms(const ASTNode& n, ASTNodeSet& seen,
                                          ASTVec& constraints)
{
  if (!seen.insert(n).second)
    return;

  // Leaves are visited now, where they were skipped before: a declared
  // RoundingMode symbol is a leaf, and it is exactly as much in need of
  // pinning as a read is.
  if (n.GetKind() == SYMBOL)
  {
    if (bm->isRoundingModeSymbol(n))
      constraints.push_back(bm->roundingModeValidConstraint(n));
    return;
  }

  if (n.GetKind() == READ && bm->arrayHasRmElement(n[0]))
    constraints.push_back(bm->roundingModeValidConstraint(n));

  for (size_t i = 0; i < n.Degree(); i++)
    collectRoundingModeTerms(n[i], seen, constraints);
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

ASTNode FpTotalise::unspecified(const char* tag, const ASTNode& prefix,
                                const ASTVec& floats,
                                unsigned int value_width)
{
  ASTNode index;
  unsigned int width = 0;

  if (!prefix.IsNull())
  {
    index = prefix;
    width = prefix.GetValueWidth();
  }

  for (size_t i = 0; i < floats.size(); i++)
  {
    // Index on canonical bits, not raw ones. SMT-LIB equality on floats makes
    // every NaN equal to every other, so operands that are equal may still
    // differ in payload; indexing on raw bits would let them read different
    // slots and answer differently, losing the very congruence this array
    // exists to provide. Round-tripping through unpack/pack collapses the
    // payloads while keeping +0 and -0 apart, which is exactly the relation
    // SMT-LIB uses.
    const ASTNode canonical = FloatBlaster::canonicalBits(bm, floats[i]);

    if (width == 0)
    {
      index = canonical;
      width = canonical.GetValueWidth();
    }
    else
    {
      width += canonical.GetValueWidth();
      index = bm->CreateTerm(BVCONCAT, width, index, canonical);
    }
  }

  // `floats` rather than the canonicalised bits: the bits are what the array
  // is indexed *by*, the formats are part of what array it is.
  return FloatBlaster::unspecifiedValue(bm, tag, floats, index, value_width);
}

ASTNode FpTotalise::visit(const ASTNode& n)
{
  if (n.Degree() == 0)
    return n;

  const ASTNodeMap::const_iterator it = cache.find(n);
  if (it != cache.end())
    return it->second;

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

    children.push_back(unspecified(k == FP_MIN ? "min_zero" : "max_zero",
                                   ASTNode(), floats, 1));
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

    children.push_back(unspecified(k == FP_TO_UBV ? "to_ubv" : "to_sbv",
                                   children[1], floats, n.GetValueWidth()));
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

  cache[n] = out;
  return out;
}

} // namespace stp
