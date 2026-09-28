/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: September, 2026
 ********************************************************************/

#include "stp/Simplifier/MultiplyOverflowIdiom.h"
#include <algorithm>

namespace stp
{

// t is a zero extension: a concat with a zero constant on top, which is what
// the simplifying node factory lowers BVZX to. Sets core to what was extended.
static bool zeroExtended(NodeFactory* nf, const ASTNode& t, ASTNode& core)
{
  if (t.GetKind() != BVCONCAT || t[0].GetKind() != BVCONST)
    return false;
  if (t[0] != nf->CreateZeroConst(t[0].GetValueWidth()))
    return false;
  core = t[1];
  return true;
}

static ASTNode extendTo(NodeFactory* nf, bool isSigned, const ASTNode& t,
                        unsigned n)
{
  const unsigned w = t.GetValueWidth();
  if (w == n)
    return t;
  if (isSigned)
    return nf->CreateTerm(BVSX, n, t, nf->CreateBVConst(32, n));
  return nf->CreateTerm(BVCONCAT, n, nf->CreateZeroConst(n - w), t);
}

// x is a term of width n extended (sign or zero as isSigned says) to its own
// width, and core is that term. The simplifier pushes an extension through
// an ite, a not, an and, an or and a plus of extensions, and turns a sign
// extension whose argument's top bit is a known zero into a zero extension;
// each is undone. A zero extension inside a signed one is accepted only when
// the rebuilt core's top bit is that constant zero, so the two extensions
// agree on it. A plus is accepted only over strict extensions from below
// n-1, where the sum cannot wrap.
static bool extendedCore(NodeFactory* nf, bool isSigned, const ASTNode& x,
                         unsigned n, ASTNode& core,
                         const TopBitKnownZero& knownZero,
                         bool underPlus = false)
{
  if (x.GetValueWidth() < n)
    return false;
  const Kind k = x.GetKind();
  ASTNode u;
  if (k == BVSX && isSigned)
  {
    u = x[0];
    if (u.GetValueWidth() > n || (underPlus && u.GetValueWidth() + 1 > n))
      return false;
    core = extendTo(nf, true, u, n);
    return true;
  }
  if (zeroExtended(nf, x, u))
  {
    const unsigned uw = u.GetValueWidth();
    if (uw > n || (underPlus && uw + 2 > n))
      return false;
    // Inside a signed product a zero extension stands for a sign extension
    // only when the extended term's top bit is zero: a literal one when the
    // rebuilt core is wider than the term, else a known one.
    if (isSigned && uw == n && !(knownZero && knownZero(u)))
      return false;
    core = extendTo(nf, false, u, n);
    return true;
  }
  if (x.GetValueWidth() == n && !underPlus)
  {
    core = x;
    return true;
  }
  if (k == ITE)
  {
    ASTNode t, e;
    if (!extendedCore(nf, isSigned, x[1], n, t, knownZero, underPlus) ||
        !extendedCore(nf, isSigned, x[2], n, e, knownZero, underPlus))
      return false;
    core = nf->CreateTerm(ITE, n, x[0], t, e);
    return true;
  }
  if (k == BVNOT && isSigned && !underPlus)
  {
    ASTNode t;
    if (!extendedCore(nf, true, x[0], n, t, knownZero))
      return false;
    core = nf->CreateTerm(BVNOT, n, t);
    return true;
  }
  if (k == BVAND || k == BVOR || (k == BVPLUS && isSigned && !underPlus))
  {
    ASTVec cores;
    for (unsigned c = 0; c < x.Degree(); c++)
    {
      ASTNode t;
      if (!extendedCore(nf, isSigned, x[c], n, t, knownZero,
                        underPlus || k == BVPLUS))
        return false;
      cores.push_back(t);
    }
    core = nf->CreateTerm(k, n, cores);
    return true;
  }
  return false;
}

// prod is a multiply of two operands of width n extended (both zero or both
// sign) to at least 2n, so the product is exact. Sets the width-n operands.
static bool exactExtendedProduct(NodeFactory* nf, bool isSigned,
                                 const ASTNode& prod, unsigned n, ASTNode& a,
                                 ASTNode& b, const TopBitKnownZero& knownZero)
{
  if (prod.GetKind() != BVMULT || prod.Degree() != 2 ||
      prod.GetValueWidth() < 2 * n)
    return false;
  return extendedCore(nf, isSigned, prod[0], n, a, knownZero) &&
         extendedCore(nf, isSigned, prod[1], n, b, knownZero);
}

// The double-width spellings of a multiplication overflow check, each turned
// into the predicate at the tested width n:
//
//   (extract [W-1:n] (bvmul (zx a) (zx b))) = 0        NOT (bvumulo a b)
//   (extract [W-1:n-1] (bvmul (sx a) (sx b))) = 0      NOT (bvsmulo a b) and
//                                                       the product's sign is 0
//   ... = all ones                                     ... and the sign is 1
//   (bvmul (zx a) (zx b)) = (zx (bvmul a b at n))       NOT (bvumulo a b)
//   (bvmul (sx a) (sx b)) = (sx (bvmul a b at n))       NOT (bvsmulo a b)
//
// The last two also match the low half written as an extract of the wide
// product before the simplifier pushes the extract into the multiply.
bool multiplyOverflowIdiom(NodeFactory* nf, const ASTNode& lhs,
                           const ASTNode& rhs, ASTNode& out,
                           const TopBitKnownZero& knownZero)
{
  ASTNode a, b;
  if (lhs.GetKind() == BVEXTRACT && rhs.GetKind() == BVCONST)
  {
    const ASTNode& prod = lhs[0];
    const unsigned W = prod.GetValueWidth();
    if (lhs[1].GetUnsignedConst() != W - 1)
      return false;
    const unsigned lo = lhs[2].GetUnsignedConst();
    const unsigned cw = rhs.GetValueWidth();
    const bool zero = rhs == nf->CreateZeroConst(cw);
    const bool ones = rhs == nf->CreateMaxConst(cw);
    if (zero && lo > 0 && exactExtendedProduct(nf, false, prod, lo, a, b, knownZero))
    {
      out = nf->CreateNode(NOT, nf->CreateNode(BVUMULO, a, b));
      return true;
    }
    if ((zero || ones) && exactExtendedProduct(nf, true, prod, lo + 1, a, b, knownZero))
    {
      const unsigned n = lo + 1;
      const ASTNode low = nf->CreateTerm(BVMULT, n, a, b);
      const ASTNode sign =
          nf->CreateTerm(BVEXTRACT, 1, low, nf->CreateBVConst(32, n - 1),
                         nf->CreateBVConst(32, n - 1));
      out = nf->CreateNode(
          AND, nf->CreateNode(NOT, nf->CreateNode(BVSMULO, a, b)),
          nf->CreateNode(EQ, sign,
                         zero ? nf->CreateZeroConst(1) : nf->CreateOneConst(1)));
      return true;
    }
    return false;
  }
  for (const bool isSigned : {false, true})
  {
    ASTNode low;
    if (isSigned ? rhs.GetKind() != BVSX : !zeroExtended(nf, rhs, low))
      continue;
    if (isSigned)
      low = rhs[0];
    const unsigned n = low.GetValueWidth();
    if (n >= rhs.GetValueWidth() ||
        !exactExtendedProduct(nf, isSigned, lhs, n, a, b, knownZero))
      continue;
    bool matches = false;
    if (low.GetKind() == BVEXTRACT)
      matches = low[0] == lhs && low[2].GetUnsignedConst() == 0;
    else if (low.GetKind() == BVMULT && low.Degree() == 2)
      matches = (low[0] == a && low[1] == b) || (low[0] == b && low[1] == a);
    if (!matches)
      continue;
    out = nf->CreateNode(NOT, nf->CreateNode(isSigned ? BVSMULO : BVUMULO, a, b));
    return true;
  }
  return false;
}

} // namespace stp
