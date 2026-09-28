/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: August, 2026
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

#include "stp/FloatBlaster/FpAbstractionRules.h"

#include "stp/FloatBlaster/FloatBlaster.h"
#include "stp/FloatBlaster/rounding_modes.h"

#include <algorithm>
#include <cassert>

namespace stp
{

const FpRuleInfo& fpRuleInfo(FpRuleId id)
{
  static const FpRuleInfo catalogue[] = {
      {"<none>", "", "", "", ""},
#define FP_RULE(token, name, operations, family, verification, selection)     \
  {name, operations, family, verification, selection},
#include "stp/FloatBlaster/FpAbstractionRuleList.h"
#undef FP_RULE
  };
  static_assert(sizeof(catalogue) / sizeof(catalogue[0]) ==
                    static_cast<unsigned>(FpRuleId::Count),
                "Every rule ID needs its metadata");
  assert(static_cast<unsigned>(id) < static_cast<unsigned>(FpRuleId::Count));
  return catalogue[static_cast<unsigned>(id)];
}

namespace
{

unsigned bitLength(uint64_t v)
{
  unsigned n = 0;
  while (v != 0)
  {
    ++n;
    v >>= 1;
  }
  return n;
}

// The rule vocabulary over one application. Every method builds a node;
// nothing here evaluates. Rounding modes are specialised at construction
// when the mode is a constant, so the emitted rules of a constant-mode
// application mention no mode at all.
class Vocabulary
{
public:
  explicit Vocabulary(const FpRuleContext& c)
      : bm(c.bm), ctx(c), eb(c.eb), sb(c.sb), fw(c.sb - 1),
        width(c.eb + c.sb), p(c.sb),
        bias(((int64_t)1 << (c.eb - 1)) - 1), emax(bias), emin(1 - bias),
        W(std::max(c.eb, bitLength(c.sb)) + 5)
  {
    assert(eb >= 2 && sb >= 2 && W <= 62);
  }

  STPMgr* bm;
  const FpRuleContext& ctx;
  const unsigned eb, sb, fw, width, p;
  const int64_t bias, emax, emin;
  const unsigned W; // width of the signed exponent arithmetic

  // ---- packed fields
  ASTNode extract(const ASTNode& v, unsigned hi, unsigned lo) const
  {
    return bm->CreateTerm(BVEXTRACT, hi - lo + 1, v, bm->CreateBVConst(32, hi),
                          bm->CreateBVConst(32, lo));
  }
  ASTNode E(const ASTNode& b) const { return extract(b, width - 2, fw); }
  ASTNode F(const ASTNode& b) const { return extract(b, fw - 1, 0); }
  ASTNode S(const ASTNode& b) const { return extract(b, width - 1, width - 1); }
  ASTNode Eones() const { return bm->CreateBVConst(eb, ((uint64_t)1 << eb) - 1); }
  ASTNode Ezero() const { return bm->CreateZeroConst(eb); }
  ASTNode Fzero() const { return bm->CreateZeroConst(fw); }

  // ---- classes, from the fields
  ASTNode nan(const ASTNode& b) const
  {
    return bm->CreateNode(AND, bm->CreateNode(EQ, E(b), Eones()),
                          bm->CreateNode(NOT, bm->CreateNode(EQ, F(b), Fzero())));
  }
  ASTNode inf(const ASTNode& b) const
  {
    return bm->CreateNode(AND, bm->CreateNode(EQ, E(b), Eones()),
                          bm->CreateNode(EQ, F(b), Fzero()));
  }
  ASTNode zero(const ASTNode& b) const
  {
    return bm->CreateNode(AND, bm->CreateNode(EQ, E(b), Ezero()),
                          bm->CreateNode(EQ, F(b), Fzero()));
  }
  ASTNode sub(const ASTNode& b) const
  {
    return bm->CreateNode(AND, bm->CreateNode(EQ, E(b), Ezero()),
                          bm->CreateNode(NOT, bm->CreateNode(EQ, F(b), Fzero())));
  }
  ASTNode nor(const ASTNode& b) const
  {
    return bm->CreateNode(AND,
                          bm->CreateNode(NOT, bm->CreateNode(EQ, E(b), Ezero())),
                          bm->CreateNode(NOT, bm->CreateNode(EQ, E(b), Eones())));
  }
  ASTNode fin(const ASTNode& b) const
  {
    return bm->CreateNode(NOT, bm->CreateNode(EQ, E(b), Eones()));
  }
  ASTNode nz(const ASTNode& b) const
  {
    return bm->CreateNode(AND, fin(b), bm->CreateNode(NOT, zero(b)));
  }
  ASTNode neg(const ASTNode& b) const
  {
    return bm->CreateNode(EQ, S(b), bm->CreateOneConst(1));
  }
  ASTNode pos(const ASTNode& b) const
  {
    return bm->CreateNode(EQ, S(b), bm->CreateZeroConst(1));
  }
  ASTNode sameSign(const ASTNode& a, const ASTNode& b) const
  {
    return bm->CreateNode(EQ, S(a), S(b));
  }
  ASTNode fractionZero(const ASTNode& b) const
  {
    return bm->CreateNode(EQ, F(b), Fzero());
  }
  ASTNode sameFraction(const ASTNode& a, const ASTNode& b) const
  {
    return bm->CreateNode(EQ, F(a), F(b));
  }

  // ---- signed exponent arithmetic, W bits
  ASTNode I(int64_t n) const
  {
    const uint64_t mask = (W >= 64) ? ~(uint64_t)0 : (((uint64_t)1 << W) - 1);
    return bm->CreateBVConst(W, (uint64_t)n & mask);
  }
  ASTNode zext(const ASTNode& v) const
  {
    return bm->CreateTerm(BVZX, W, v, bm->CreateBVConst(32, W));
  }
  // e as the rules read it (see the header).
  ASTNode e(const ASTNode& b) const
  {
    const ASTNode normal = bm->CreateTerm(BVSUB, W, zext(E(b)), I(bias));
    return bm->CreateTerm(
        ITE, W, nor(b), normal,
        bm->CreateTerm(ITE, W, fin(b), I(emin - 1), I(emax + 1)));
  }
  ASTNode add(const ASTNode& a, const ASTNode& b) const
  {
    return bm->CreateTerm(BVPLUS, W, a, b);
  }
  ASTNode add(const ASTNode& a, const ASTNode& b, const ASTNode& c) const
  {
    return add(add(a, b), c);
  }
  ASTNode subi(const ASTNode& a, const ASTNode& b) const
  {
    return bm->CreateTerm(BVSUB, W, a, b);
  }
  ASTNode le(const ASTNode& a, const ASTNode& b) const
  {
    return bm->CreateNode(BVSLE, a, b);
  }
  ASTNode ge(const ASTNode& a, const ASTNode& b) const
  {
    return bm->CreateNode(BVSGE, a, b);
  }
  ASTNode lt(const ASTNode& a, const ASTNode& b) const
  {
    return bm->CreateNode(BVSLT, a, b);
  }
  ASTNode ieq(const ASTNode& a, const ASTNode& b) const
  {
    return bm->CreateNode(EQ, a, b);
  }
  ASTNode maxi(const ASTNode& a, const ASTNode& b) const
  {
    return bm->CreateTerm(ITE, W, ge(a, b), a, b);
  }
  ASTNode mini(const ASTNode& a, const ASTNode& b) const
  {
    return bm->CreateTerm(ITE, W, le(a, b), a, b);
  }
  ASTNode halfDown(const ASTNode& a) const
  {
    return bm->CreateTerm(BVSRSHIFT, W, a, I(1));
  }
  ASTNode odd(const ASTNode& a) const
  {
    return bm->CreateNode(EQ, extract(a, 0, 0), bm->CreateOneConst(1));
  }

  // ---- order and equality over the float views
  ASTNode fplt(const ASTNode& a, const ASTNode& b) const
  {
    return bm->CreateNode(FP_LT, a, b);
  }
  ASTNode fpleq(const ASTNode& a, const ASTNode& b) const
  {
    return bm->CreateNode(FP_LEQ, a, b);
  }
  ASTNode fpabs(const ASTNode& v) const
  {
    return bm->CreateTerm(FP_ABS, width, v);
  }
  ASTNode fpneg(const ASTNode& v) const
  {
    return bm->CreateTerm(FP_NEG, width, v);
  }
  ASTNode fpeq(const ASTNode& a, const ASTNode& b) const
  {
    return bm->CreateNode(FP_SMT_EQ, a, b);
  }
  // Equality with a non-NaN constant is bit equality.
  ASTNode bitsEq(const ASTNode& b, const ASTNode& constant) const
  {
    return bm->CreateNode(EQ, b, constant);
  }
  ASTNode viewOf(const ASTNode& b) const
  {
    const ASTNode raw = bm->CreateTerm(FP_TOFP, width, bm->CreateBVConst(32, eb),
                                       bm->CreateBVConst(32, sb), b);
    return FloatBlaster::withFormat(bm, raw, eb, sb);
  }
  ASTNode fpConst(const ASTNode& packedConstant) const
  {
    return bm->CreateFPConst(packedConstant, eb, sb);
  }
  // A packed constant from its fields, at any width: the formats admitted
  // run past 64 bits, so no pattern is ever held in a machine word.
  ASTNode packed(bool negative, uint64_t exponentField,
                 bool fractionAllOnes) const
  {
    CBV cbv = CONSTANTBV::BitVector_Create(width, true);
    if (negative)
      CONSTANTBV::BitVector_Bit_On(cbv, width - 1);
    for (unsigned i = 0; i < eb; ++i)
      if ((exponentField >> i) & 1)
        CONSTANTBV::BitVector_Bit_On(cbv, fw + i);
    if (fractionAllOnes)
      for (unsigned i = 0; i < fw; ++i)
        CONSTANTBV::BitVector_Bit_On(cbv, i);
    return bm->CreateBVConst(cbv, width);
  }
  uint64_t exponentOnes() const { return ((uint64_t)1 << eb) - 1; }
  ASTNode one() const { return packed(false, (uint64_t)bias, false); }
  ASTNode minusOne() const { return packed(true, (uint64_t)bias, false); }
  ASTNode plusZero() const { return packed(false, 0, false); }
  ASTNode minusZero() const { return packed(true, 0, false); }
  ASTNode plusInf() const { return packed(false, exponentOnes(), false); }
  ASTNode maxFinite(bool negative) const
  {
    return packed(negative, exponentOnes() - 1, true);
  }

  // ---- packed neighbours and magnitudes
  // The packed successor and predecessor: one ulp away in magnitude, the
  // sign kept. Used only under a guard that makes the operand a normal, so
  // succ of the largest finite is the infinity of that sign and pred of the
  // smallest normal is the largest subnormal, as IEEE 754 orders them.
  ASTNode succ(const ASTNode& b) const
  {
    return bm->CreateTerm(BVPLUS, width, b, bm->CreateOneConst(width));
  }
  ASTNode pred(const ASTNode& b) const
  {
    return bm->CreateTerm(BVSUB, width, b, bm->CreateOneConst(width));
  }
  // "b is the zero of the given sign".
  ASTNode zeroSigned(const ASTNode& b, const ASTNode& negative) const
  {
    return ite(negative, bitsEq(b, minusZero()), bitsEq(b, plusZero()));
  }
  // The magnitude bits E.F, which order the finite values of one sign as
  // unsigned integers.
  ASTNode magnitude(const ASTNode& b) const
  {
    return extract(b, width - 2, 0);
  }
  // Comparison code for twice a finite nonzero magnitude: a subnormal's
  // field shifts up and a normal's exponent increments. In the top binade
  // this is an above-range sentinel (possibly a NaN encoding), greater
  // than every finite magnitude code, not a representation of finite 2|b|.
  // The caller handles zero separately; this helper does not encode 2*0.
  ASTNode doubledMagnitude(const ASTNode& b) const
  {
    const unsigned mw = width - 1;
    const ASTNode m = magnitude(b);
    const ASTNode shifted =
        bm->CreateTerm(BVLEFTSHIFT, mw, m, bm->CreateBVConst(mw, 1));
    const ASTNode unit = bm->CreateTerm(BVLEFTSHIFT, mw, bm->CreateOneConst(mw),
                                        bm->CreateBVConst(mw, fw));
    const ASTNode bumped = bm->CreateTerm(BVPLUS, mw, m, unit);
    return bm->CreateTerm(ITE, mw, sub(b), shifted, bumped);
  }
  ASTNode ule(const ASTNode& a, const ASTNode& b) const
  {
    return bm->CreateNode(BVLE, a, b);
  }
  ASTNode uge(const ASTNode& a, const ASTNode& b) const
  {
    return bm->CreateNode(BVGE, a, b);
  }

  // ---- the rounding mode
  ASTNode rmIn(std::initializer_list<unsigned> modes) const
  {
    if (ctx.rm != 0)
    {
      for (unsigned m : modes)
        if (m == ctx.rm)
          return bm->ASTTrue;
      return bm->ASTFalse;
    }
    assert(!ctx.rmTerm.IsNull());
    ASTVec alternatives;
    for (unsigned m : modes)
      alternatives.push_back(
          bm->CreateNode(EQ, ctx.rmTerm, bm->CreateRMConst(m)));
    return alternatives.size() == 1 ? alternatives[0]
                                    : bm->CreateNode(OR, alternatives);
  }

  // ---- connectives
  ASTNode and_(const ASTVec& xs) const
  {
    return xs.size() == 1 ? xs[0] : bm->CreateNode(AND, xs);
  }
  ASTNode and_(const ASTNode& a, const ASTNode& b) const
  {
    return bm->CreateNode(AND, a, b);
  }
  ASTNode and_(const ASTNode& a, const ASTNode& b, const ASTNode& c) const
  {
    return bm->CreateNode(AND, ASTVec{a, b, c});
  }
  ASTNode and_(const ASTNode& a, const ASTNode& b, const ASTNode& c,
               const ASTNode& d) const
  {
    return bm->CreateNode(AND, ASTVec{a, b, c, d});
  }
  ASTNode or_(const ASTVec& xs) const
  {
    return xs.size() == 1 ? xs[0] : bm->CreateNode(OR, xs);
  }
  ASTNode or_(const ASTNode& a, const ASTNode& b) const
  {
    return bm->CreateNode(OR, a, b);
  }
  ASTNode or_(const ASTNode& a, const ASTNode& b, const ASTNode& c) const
  {
    return bm->CreateNode(OR, ASTVec{a, b, c});
  }
  ASTNode not_(const ASTNode& a) const { return bm->CreateNode(NOT, a); }
  ASTNode implies(const ASTNode& g, const ASTNode& c) const
  {
    return bm->CreateNode(OR, bm->CreateNode(NOT, g), c);
  }
  ASTNode iff(const ASTNode& a, const ASTNode& b) const
  {
    return bm->CreateNode(IFF, a, b);
  }
  ASTNode ite(const ASTNode& c, const ASTNode& a, const ASTNode& b) const
  {
    return bm->CreateNode(ITE, c, a, b);
  }

  // The overflowed result under the rounding mode, given the result's sign
  // (IEEE 754-2008 7.4): RNE/RNA to infinity, RTZ to the largest finite,
  // RTP/RTN to whichever of the two is in the rounding direction.
  ASTNode overflowSelect(const ASTNode& tb, const ASTNode& negative) const
  {
    const ASTNode isInf = inf(tb);
    const ASTNode isMax =
        ite(negative, bitsEq(tb, maxFinite(true)), bitsEq(tb, maxFinite(false)));
    using namespace symbolic_fp;
    return or_(ASTVec{
        and_(rmIn({ROUND_NEAREST_TIES_TO_EVEN, ROUND_NEAREST_TIES_TO_AWAY}),
             isInf),
        and_(rmIn({ROUND_TOWARD_ZERO}), isMax),
        and_(rmIn({ROUND_TOWARD_POSITIVE}), ite(negative, isMax, isInf)),
        and_(rmIn({ROUND_TOWARD_NEGATIVE}), ite(negative, isInf, isMax))});
  }
};

// One rule: the implication, appended only when its tier is admitted.
struct Emitter
{
  const Vocabulary& V;
  unsigned tiers;
  std::vector<ASTNode>& out;
  std::vector<FpRuleId>* ids;
  unsigned count = 0;
  void rule(FpRuleId id, unsigned tier, const ASTNode& guard,
            const ASTNode& conclusion)
  {
    if (tier > tiers)
      return;
    const ASTNode r = guard == V.bm->ASTTrue ? conclusion
                                             : V.implies(guard, conclusion);
    if (r == V.bm->ASTTrue)
      return;
    out.push_back(r);
    if (ids != nullptr)
      ids->push_back(id);
    ++count;
  }
};

// ------------------------------------------- reduced-precision bands
//
// The exponent bands say which binade a result is in. These say where in
// it, to a few percent, from the top k bits of each operand's significand:
// a normal x lies in [m_x, m_x + 1) * 2^(e(x) - k + 1) for the k-bit
// integer m_x (hidden bit included), so the exact product of two normals
// lies in [m_x*m_y, (m_x+1)(m_y+1)) * 2^(e(x)+e(y)-2k+2), rounding is
// monotone, and with 2k + 1 <= p both ends are representable, so the
// rounded product lies between them too. Each end is compared with the
// result's significand as an integer at the shift its binade dictates, and
// the binade is one of the two the exponent band allows. The only circuit
// is a k x k multiplier.
//
// Division and square root are written without a divider or a root:
// t = round(x / y) satisfies t * y_hi > x_lo and t * y_lo < x_hi up to one
// rounding of t, which a k-ulp of slack on x absorbs, and with t's own
// bracket in place of t the bounds are two k x k products; t = round(sqrt x)
// is within a p-ulp of the root, so (m_t - 1)^2 and (m_t + 2)^2 at the
// right shift bracket x. Everything
// is guarded by the operands and the result being normal, and the
// products' exponents by the range that keeps the ends representable.

// The bits the flag asks for, capped so that 2k + 1 <= p; 0 when the
// format is too narrow for a band worth having.
unsigned bandBitsFor(const Vocabulary& V)
{
  const unsigned k = V.ctx.bandBits;
  if (k == 0 || V.p < 5)
    return 0;
  const unsigned eff = std::min(k, (V.p - 1) / 2);
  return eff >= 2 ? eff : 0;
}

// The top k bits of a normal's significand, hidden bit included: an
// integer in [2^(k-1), 2^k).
ASTNode topSignificand(const Vocabulary& V, const ASTNode& b, unsigned k)
{
  const ASTNode one = V.bm->CreateOneConst(1);
  if (k == 1)
    return one;
  return V.bm->CreateTerm(BVCONCAT, k, one,
                          V.extract(b, V.fw - 1, V.fw - (k - 1)));
}

// 1.F as a p-bit integer.
ASTNode fullSignificand(const Vocabulary& V, const ASTNode& b)
{
  return V.bm->CreateTerm(BVCONCAT, V.p, V.bm->CreateOneConst(1), V.F(b));
}

ASTNode widen(const Vocabulary& V, const ASTNode& v, unsigned width)
{
  assert(v.GetValueWidth() <= width);
  if (v.GetValueWidth() == width)
    return v;
  return V.bm->CreateTerm(BVZX, width, v, V.bm->CreateBVConst(32, width));
}

// v * 2^shift, at `width` bits, which must hold it.
ASTNode shiftedUp(const Vocabulary& V, const ASTNode& v, unsigned shift,
                  unsigned width)
{
  assert(v.GetValueWidth() + shift <= width);
  if (shift == 0)
    return widen(V, v, width);
  const ASTNode placed = V.bm->CreateTerm(
      BVCONCAT, v.GetValueWidth() + shift, v, V.bm->CreateZeroConst(shift));
  return widen(V, placed, width);
}

ASTNode plus(const Vocabulary& V, unsigned width, const ASTVec& terms)
{
  ASTVec widened;
  for (const ASTNode& t : terms)
    widened.push_back(widen(V, t, width));
  return V.bm->CreateTerm(BVPLUS, width, widened);
}

ASTNode times(const Vocabulary& V, unsigned width, const ASTNode& a,
              const ASTNode& b)
{
  return V.bm->CreateTerm(BVMULT, width, widen(V, a, width), widen(V, b, width));
}

void emitMulSignificandBands(const Vocabulary& V, Emitter& em)
{
  const unsigned k = bandBitsFor(V);
  if (k == 0)
    return;
  const unsigned p = V.p, W = p + 2;
  const ASTNode &xb = V.ctx.bits[0], &yb = V.ctx.bits[1], &tb = V.ctx.tb;
  const ASTNode s = V.add(V.e(xb), V.e(yb)), et = V.e(tb);
  const ASTNode mx = topSignificand(V, xb, k), my = topSignificand(V, yb, k);
  // m_x * m_y and (m_x + 1)(m_y + 1) = m_x*m_y + m_x + m_y + 1.
  const ASTNode P = times(V, 2 * k, mx, my);
  const ASTNode Q =
      plus(V, 2 * k + 1, ASTVec{P, mx, my, V.bm->CreateOneConst(2 * k + 1)});
  const ASTNode Mt = widen(V, fullSignificand(V, tb), W);
  // In binade s the result's significand scales P by 2^(p+1-2k); one
  // binade up, by 2^(p-2k).
  const auto within = [&](unsigned shift) {
    return V.and_(V.ule(shiftedUp(V, P, shift, W), Mt),
                  V.ule(Mt, shiftedUp(V, Q, shift, W)));
  };
  em.rule(FpRuleId::MUL_P1, 2,
          V.and_(V.and_(V.nor(xb), V.nor(yb), V.nor(tb)),
                 V.and_(V.le(V.I(V.emin), s), V.le(s, V.I(V.emax - 1)))),
          V.or_(V.and_(V.ieq(et, s), within(p + 1 - 2 * k)),
                V.and_(V.ieq(et, V.add(s, V.I(1))), within(p - 2 * k))));
}

void emitDivSignificandBands(const Vocabulary& V, Emitter& em)
{
  const unsigned k = bandBitsFor(V);
  if (k == 0)
    return;
  const unsigned W = 2 * k + 3;
  const ASTNode &xb = V.ctx.bits[0], &yb = V.ctx.bits[1], &tb = V.ctx.tb;
  const ASTNode s = V.subi(V.e(xb), V.e(yb)), et = V.e(tb);
  const ASTNode mx = topSignificand(V, xb, k), my = topSignificand(V, yb, k);
  const ASTNode mt = topSignificand(V, tb, k);
  // The result is within one rounding of x / y, so t * y_hi exceeds x_lo
  // less a k-ulp of x and t * y_lo falls short of x_hi plus one; with the
  // result's own bracket on t that is (m_t+1)(m_y+1) against m_x - 1 and
  // m_t m_y against m_x + 2, at the shift the binades dictate.
  const ASTNode one = V.bm->CreateOneConst(k + 1);
  const ASTNode lower = times(V, W, plus(V, k + 1, ASTVec{mt, one}),
                              plus(V, k + 1, ASTVec{my, one}));
  const ASTNode upper = times(V, W, mt, my);
  const ASTNode mxMinus1 =
      V.bm->CreateTerm(BVSUB, k, mx, V.bm->CreateOneConst(k)); // m_x >= 2
  const ASTNode mxPlus2 =
      plus(V, k + 2, ASTVec{mx, V.bm->CreateBVConst(k + 2, 2)});
  // In binade s the ends scale by 2^(k-1); one binade down, by 2^k.
  const auto within = [&](unsigned shift) {
    return V.and_(V.ule(shiftedUp(V, mxMinus1, shift, W), lower),
                  V.ule(upper, shiftedUp(V, mxPlus2, shift, W)));
  };
  em.rule(FpRuleId::DIV_P1, 2,
          V.and_(V.and_(V.nor(xb), V.nor(yb), V.nor(tb)),
                 V.and_(V.le(V.I(V.emin + 1), s), V.le(s, V.I(V.emax)))),
          V.or_(V.and_(V.ieq(et, s), within(k - 1)),
                V.and_(V.ieq(et, V.subi(s, V.I(1))), within(k))));
}

void emitSqrtSignificandBands(const Vocabulary& V, Emitter& em)
{
  const unsigned k = bandBitsFor(V);
  if (k == 0)
    return;
  const unsigned p = V.p, W = p + 6;
  const ASTNode &xb = V.ctx.bits[0], &tb = V.ctx.tb;
  const ASTNode ex = V.e(xb), et = V.e(tb);
  const ASTNode m = topSignificand(V, tb, k);
  // (m - 1)^2 and (m + 2)^2, at 2k+2 and 2k+4 bits.
  const ASTNode mMinus1 =
      V.bm->CreateTerm(BVSUB, k + 1, widen(V, m, k + 1),
                       V.bm->CreateOneConst(k + 1));
  const ASTNode mPlus2 = plus(V, k + 2, ASTVec{m, V.bm->CreateBVConst(k + 2, 2)});
  const ASTNode A = times(V, 2 * k + 2, mMinus1, mMinus1);
  const ASTNode B = times(V, 2 * k + 4, mPlus2, mPlus2);
  const ASTNode Mx = widen(V, fullSignificand(V, xb), W);
  // 2e(t) - e(x) is -1, 0 or 1 for a normal root of a normal; at each the
  // squares meet x's significand at a shift of p - 2k + 1 + that.
  const ASTNode twice = V.subi(V.add(et, et), ex);
  const auto within = [&](int c) {
    const unsigned shift = (unsigned)((int)p - 2 * (int)k + 1 + c);
    return V.and_(V.ieq(twice, V.I(c)),
                  V.and_(V.ule(shiftedUp(V, A, shift, W), Mx),
                         V.ule(Mx, shiftedUp(V, B, shift, W))));
  };
  em.rule(FpRuleId::SQRT_P1, 2, V.and_(V.nor(xb), V.pos(xb), V.nor(tb)),
          V.or_(within(-1), within(0), within(1)));
}

// t = mul(rm, x, y)
void emitMul(const Vocabulary& V, Emitter& em)
{
  const ASTNode &xb = V.ctx.bits[0], &yb = V.ctx.bits[1], &tb = V.ctx.tb;
  const ASTNode &x = V.ctx.view[0], &y = V.ctx.view[1], &t = V.ctx.t;
  const ASTNode T = V.bm->ASTTrue;
  const ASTNode ex = V.e(xb), ey = V.e(yb), et = V.e(tb);
  const ASTNode exy = V.add(ex, ey);
  const ASTNode one = V.fpConst(V.one());
  const ASTNode negProduct = V.not_(V.sameSign(xb, yb));

  // Tier 0: shell and sign.
  em.rule(FpRuleId::MUL_S1, 0, T,
          V.iff(V.nan(tb), V.or_(ASTVec{V.nan(xb), V.nan(yb),
                                        V.and_(V.zero(xb), V.inf(yb)),
                                        V.and_(V.inf(xb), V.zero(yb))})));
  em.rule(FpRuleId::MUL_S2, 0, V.not_(V.nan(tb)), V.iff(V.neg(tb), negProduct));
  em.rule(FpRuleId::MUL_S3, 0,
          V.or_(V.and_(V.inf(xb), V.not_(V.nan(yb)), V.not_(V.zero(yb))),
                V.and_(V.inf(yb), V.not_(V.nan(xb)), V.not_(V.zero(xb)))),
          V.inf(tb));
  em.rule(FpRuleId::MUL_S4, 0,
          V.or_(V.and_(V.zero(xb), V.fin(yb)), V.and_(V.zero(yb), V.fin(xb))),
          V.zero(tb));
  em.rule(FpRuleId::MUL_S5, 0, V.inf(tb),
          V.or_(V.inf(xb), V.inf(yb), V.and_(V.nor(xb), V.nor(yb))));
  // MUL-S6: a product of at least the smallest subnormal cannot round to
  // zero, in any mode.
  em.rule(FpRuleId::MUL_S6, 0,
          V.or_(V.and_(V.nor(xb), V.nor(yb), V.ge(exy, V.I(V.emin - V.p + 1))),
                V.and_(V.sub(xb), V.nor(yb), V.ge(ey, V.I(0))),
                V.and_(V.nor(xb), V.sub(yb), V.ge(ex, V.I(0)))),
          V.not_(V.zero(tb)));
  em.rule(
      FpRuleId::MUL_S7, 0, V.and_(V.sub(xb), V.sub(yb)),
      V.or_(V.zero(tb), V.sub(tb), V.and_(V.nor(tb), V.ieq(et, V.I(V.emin)))));

  // Tier 1: order.
  em.rule(
      FpRuleId::MUL_O1, 1,
      V.and_(V.not_(V.nan(tb)), V.not_(V.nan(xb)), V.fpleq(one, V.fpabs(y))),
      V.fpleq(V.fpabs(x), V.fpabs(t)));
  em.rule(
      FpRuleId::MUL_O2, 1,
      V.and_(V.not_(V.nan(tb)), V.not_(V.nan(xb)), V.fpleq(V.fpabs(y), one)),
      V.fpleq(V.fpabs(t), V.fpabs(x)));
  em.rule(
      FpRuleId::MUL_O1y, 1,
      V.and_(V.not_(V.nan(tb)), V.not_(V.nan(yb)), V.fpleq(one, V.fpabs(x))),
      V.fpleq(V.fpabs(y), V.fpabs(t)));
  em.rule(
      FpRuleId::MUL_O2y, 1,
      V.and_(V.not_(V.nan(tb)), V.not_(V.nan(yb)), V.fpleq(V.fpabs(x), one)),
      V.fpleq(V.fpabs(t), V.fpabs(y)));

  // Tier 2: bands and overflow.
  const ASTNode normals = V.and_(V.nor(xb), V.nor(yb));
  em.rule(FpRuleId::MUL_B1, 2,
          V.and_(normals, V.le(V.I(V.emin), exy), V.le(exy, V.I(V.emax - 1))),
          V.and_(V.nor(tb), V.le(exy, et), V.le(et, V.add(exy, V.I(1)))));
  em.rule(FpRuleId::MUL_B2, 2, V.and_(normals, V.ieq(exy, V.I(V.emax))),
          V.or_(V.inf(tb), V.and_(V.nor(tb), V.ieq(et, V.I(V.emax)))));
  em.rule(FpRuleId::MUL_B3, 2, V.and_(normals, V.lt(V.I(V.emax), exy)),
          V.overflowSelect(tb, negProduct));
  em.rule(
      FpRuleId::MUL_B4, 2, V.and_(normals, V.lt(exy, V.I(V.emin))),
      V.or_(V.zero(tb), V.sub(tb), V.and_(V.nor(tb), V.ieq(et, V.I(V.emin)))));
  {
    // MUL-B5: one subnormal, one normal, normal result.
    const ASTNode en = V.bm->CreateTerm(ITE, V.W, V.sub(xb), ey, ex);
    em.rule(FpRuleId::MUL_B5, 2,
            V.and_(V.or_(V.and_(V.sub(xb), V.nor(yb)),
                         V.and_(V.sub(yb), V.nor(xb))),
                   V.nor(tb)),
            V.and_(V.le(V.add(en, V.I(V.emin - V.p + 1)), et),
                   V.le(et, V.add(en, V.I(V.emin + 1)))));
  }

  // Within the band, the fractions order: |x| 2^e(y) <= |x||y| < |x| 2^(e(y)+1)
  // and both ends are exact scalings, so the rounded product is at least the
  // first and at most the second. In the lower binade of the band that is
  // F(t) >= F(x); in the upper, F(t) <= F(x); and the same with y.
  {
    const ASTNode inBand = V.and_(normals, V.nor(tb));
    em.rule(FpRuleId::MUL_F1, 2, V.and_(inBand, V.ieq(et, exy)),
            V.and_(V.uge(V.F(tb), V.F(xb)), V.uge(V.F(tb), V.F(yb))));
    em.rule(FpRuleId::MUL_F2, 2, V.and_(inBand, V.ieq(et, V.add(exy, V.I(1)))),
            V.and_(V.ule(V.F(tb), V.F(xb)), V.ule(V.F(tb), V.F(yb))));
  }

  // Tier 3: identities.
  em.rule(FpRuleId::MUL_I1, 3, V.and_(V.bitsEq(yb, V.one()), V.not_(V.nan(xb))),
          V.fpeq(t, x));
  em.rule(FpRuleId::MUL_I1, 3, V.and_(V.bitsEq(xb, V.one()), V.not_(V.nan(yb))),
          V.fpeq(t, y));
  em.rule(FpRuleId::MUL_I2, 3,
          V.and_(V.bitsEq(yb, V.minusOne()), V.not_(V.nan(xb))),
          V.fpeq(t, V.fpneg(x)));
  em.rule(FpRuleId::MUL_I2, 3,
          V.and_(V.bitsEq(xb, V.minusOne()), V.not_(V.nan(yb))),
          V.fpeq(t, V.fpneg(y)));
  // MUL-I3: a normal power of two scales exactly.
  em.rule(FpRuleId::MUL_I3, 3,
          V.and_(V.nor(yb), V.fractionZero(yb), V.nor(xb),
                 V.and_(V.le(V.I(V.emin), exy), V.le(exy, V.I(V.emax)))),
          V.and_(V.nor(tb), V.ieq(et, exy), V.sameFraction(tb, xb),
                 V.iff(V.neg(tb), negProduct)));
  em.rule(FpRuleId::MUL_I3, 3,
          V.and_(V.nor(xb), V.fractionZero(xb), V.nor(yb),
                 V.and_(V.le(V.I(V.emin), exy), V.le(exy, V.I(V.emax)))),
          V.and_(V.nor(tb), V.ieq(et, exy), V.sameFraction(tb, yb),
                 V.iff(V.neg(tb), negProduct)));
  emitMulSignificandBands(V, em);
}

// t = div(rm, x, y)
void emitDiv(const Vocabulary& V, Emitter& em)
{
  const ASTNode &xb = V.ctx.bits[0], &yb = V.ctx.bits[1], &tb = V.ctx.tb;
  const ASTNode &x = V.ctx.view[0], &y = V.ctx.view[1], &t = V.ctx.t;
  const ASTNode T = V.bm->ASTTrue;
  const ASTNode ex = V.e(xb), ey = V.e(yb), et = V.e(tb);
  const ASTNode exy = V.subi(ex, ey);
  const ASTNode one = V.fpConst(V.one());
  const ASTNode negQuotient = V.not_(V.sameSign(xb, yb));

  // Tier 0.
  em.rule(FpRuleId::DIV_S1, 0, T,
          V.iff(V.nan(tb), V.or_(ASTVec{V.nan(xb), V.nan(yb),
                                        V.and_(V.zero(xb), V.zero(yb)),
                                        V.and_(V.inf(xb), V.inf(yb))})));
  em.rule(FpRuleId::DIV_S2, 0, V.not_(V.nan(tb)),
          V.iff(V.neg(tb), negQuotient));
  em.rule(FpRuleId::DIV_S3, 0,
          V.or_(V.and_(V.zero(yb), V.not_(V.nan(xb)), V.not_(V.zero(xb))),
                V.and_(V.inf(xb), V.fin(yb))),
          V.inf(tb));
  em.rule(FpRuleId::DIV_S4, 0,
          V.or_(V.and_(V.inf(yb), V.fin(xb)), V.and_(V.zero(xb), V.nz(yb))),
          V.zero(tb));
  em.rule(FpRuleId::DIV_S5u, 0, V.inf(tb),
          V.or_(V.inf(xb), V.zero(yb), V.and_(V.nz(xb), V.nz(yb))));
  // DIV-S5: a subnormal numerator cannot overflow unless the format is so
  // narrow that maxsub/minsub reaches 2^(emax+1): 2^(eb-1) >= sb.
  if (((uint64_t)1 << (V.eb - 1)) >= V.sb)
    em.rule(FpRuleId::DIV_S5, 0, V.inf(tb),
            V.or_(V.inf(xb), V.zero(yb), V.and_(V.nor(xb), V.nz(yb))));
  em.rule(FpRuleId::DIV_S6, 0, V.zero(tb),
          V.or_(V.zero(xb), V.inf(yb), V.nor(yb)));
  em.rule(FpRuleId::DIV_S7, 0,
          V.and_(V.nor(xb), V.nor(yb),
                 V.or_(V.ge(exy, V.I(V.emin - V.p + 2)),
                       V.and_(V.rmIn({symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN,
                                      symbolic_fp::ROUND_NEAREST_TIES_TO_AWAY}),
                              V.ge(exy, V.I(V.emin - V.p + 1))))),
          V.not_(V.zero(tb)));

  // Tier 1.
  em.rule(
      FpRuleId::DIV_O1, 1,
      V.and_(V.not_(V.nan(tb)), V.not_(V.nan(xb)), V.fpleq(one, V.fpabs(y))),
      V.fpleq(V.fpabs(t), V.fpabs(x)));
  em.rule(FpRuleId::DIV_O2, 1,
          V.and_(V.not_(V.nan(tb)), V.not_(V.nan(xb)), V.not_(V.zero(yb)),
                 V.fpleq(V.fpabs(y), one)),
          V.fpleq(V.fpabs(x), V.fpabs(t)));

  // Tier 2.
  const ASTNode normals = V.and_(V.nor(xb), V.nor(yb));
  em.rule(FpRuleId::DIV_B1, 2,
          V.and_(normals, V.le(V.I(V.emin + 1), exy), V.le(exy, V.I(V.emax))),
          V.and_(V.nor(tb), V.le(V.subi(exy, V.I(1)), et), V.le(et, exy)));
  em.rule(FpRuleId::DIV_B2, 2, V.and_(normals, V.ieq(exy, V.I(V.emin))),
          V.or_(V.sub(tb), V.and_(V.nor(tb), V.ieq(et, V.I(V.emin)))));
  em.rule(FpRuleId::DIV_B3, 2, V.and_(normals, V.lt(V.I(V.emax + 1), exy)),
          V.overflowSelect(tb, negQuotient));
  em.rule(FpRuleId::DIV_B3b, 2, V.and_(normals, V.ieq(exy, V.I(V.emax + 1))),
          V.or_(V.inf(tb), V.and_(V.nor(tb), V.ieq(et, V.I(V.emax)))));
  em.rule(
      FpRuleId::DIV_B4, 2, V.and_(normals, V.lt(exy, V.I(V.emin))),
      V.or_(V.zero(tb), V.sub(tb), V.and_(V.nor(tb), V.ieq(et, V.I(V.emin)))));
  em.rule(FpRuleId::DIV_B5, 2, V.and_(V.sub(xb), V.nor(yb), V.nor(tb)),
          V.le(et, V.subi(V.I(V.emin), ey)));
  em.rule(FpRuleId::DIV_B6, 2, V.and_(V.nor(xb), V.sub(yb), V.not_(V.nan(tb))),
          V.or_(V.inf(tb),
                V.and_(V.nor(tb), V.ge(et, V.mini(V.subi(ex, V.I(V.emin)),
                                                  V.I(V.emax))))));

  // Within the band the fractions order the other way: |x| / 2^(e(y)+1) <
  // |x|/|y| <= |x| / 2^e(y), exact scalings both, so in the upper binade of
  // the band F(t) <= F(x) and in the lower F(t) >= F(x).
  {
    const ASTNode s = V.subi(V.e(xb), V.e(yb));
    const ASTNode inBand = V.and_(V.nor(xb), V.nor(yb), V.nor(tb));
    em.rule(FpRuleId::DIV_F1, 2, V.and_(inBand, V.ieq(V.e(tb), s)),
            V.ule(V.F(tb), V.F(xb)));
    em.rule(FpRuleId::DIV_F2, 2,
            V.and_(inBand, V.ieq(V.e(tb), V.subi(s, V.I(1)))),
            V.uge(V.F(tb), V.F(xb)));
  }

  // Tier 3.
  em.rule(FpRuleId::DIV_I1, 3, V.and_(V.bitsEq(yb, V.one()), V.not_(V.nan(xb))),
          V.fpeq(t, x));
  em.rule(FpRuleId::DIV_I2, 3,
          V.and_(V.bitsEq(yb, V.minusOne()), V.not_(V.nan(xb))),
          V.fpeq(t, V.fpneg(x)));
  em.rule(FpRuleId::DIV_I3, 3, V.and_(V.bm->CreateNode(EQ, xb, yb), V.nz(xb)),
          V.bitsEq(tb, V.one()));
  em.rule(
      FpRuleId::DIV_I4, 3,
      V.and_(V.bm->CreateNode(
                 EQ, xb, V.bm->CreateTerm(BVXOR, V.width, yb, V.minusZero())),
             V.nz(xb)),
      V.bitsEq(tb, V.minusOne()));
  em.rule(FpRuleId::DIV_I5, 3,
          V.and_(V.nor(yb), V.fractionZero(yb), V.nor(xb),
                 V.and_(V.le(V.I(V.emin), exy), V.le(exy, V.I(V.emax)))),
          V.and_(V.nor(tb), V.ieq(et, exy), V.sameFraction(tb, xb),
                 V.iff(V.neg(tb), negQuotient)));
  emitDivSignificandBands(V, em);
}

// t = sqrt(rm, x)
void emitSqrt(const Vocabulary& V, Emitter& em)
{
  const ASTNode &xb = V.ctx.bits[0], &tb = V.ctx.tb;
  const ASTNode &x = V.ctx.view[0], &t = V.ctx.t;
  const ASTNode T = V.bm->ASTTrue;
  const ASTNode ex = V.e(xb), et = V.e(tb);
  const ASTNode one = V.fpConst(V.one());
  const ASTNode pzero = V.fpConst(V.plusZero());

  // Tier 0.
  em.rule(FpRuleId::SQRT_S1, 0, T,
          V.iff(V.nan(tb),
                V.or_(V.nan(xb), V.and_(V.neg(xb), V.not_(V.zero(xb))))));
  em.rule(FpRuleId::SQRT_S2, 0, V.zero(xb), V.bm->CreateNode(EQ, tb, xb));
  em.rule(FpRuleId::SQRT_S3, 0, V.not_(V.nan(tb)),
          V.iff(V.neg(tb), V.and_(V.neg(xb), V.zero(xb))));
  em.rule(FpRuleId::SQRT_S4, 0, T, V.iff(V.inf(tb), V.bitsEq(xb, V.plusInf())));
  em.rule(FpRuleId::SQRT_S6, 0, V.and_(V.nz(xb), V.pos(xb)), V.nz(tb));
  // SQRT-S7: the root of a positive finite is normal wherever
  // sqrt(minsub) >= minnormal, i.e. 2^(eb-1) >= sb + 1 -- every IEEE format.
  if (((uint64_t)1 << (V.eb - 1)) >= V.sb + 1)
    em.rule(FpRuleId::SQRT_S7, 0, V.and_(V.nz(xb), V.pos(xb)), V.nor(tb));
  em.rule(FpRuleId::SQRT_S8, 0, V.and_(V.nor(xb), V.pos(xb)), V.nor(tb));

  // Tier 1.
  em.rule(FpRuleId::SQRT_O1, 1, V.fpleq(one, x),
          V.and_(V.fpleq(one, t), V.fpleq(t, x)));
  em.rule(FpRuleId::SQRT_O2, 1, V.and_(V.fpleq(pzero, x), V.fpleq(x, one)),
          V.and_(V.fpleq(x, t), V.fpleq(t, one)));

  // Tier 2.
  {
    const ASTNode half = V.halfDown(ex);
    em.rule(
        FpRuleId::SQRT_B1, 2, V.and_(V.nor(xb), V.pos(xb), V.nor(tb)),
        V.and_(
            V.le(half, et),
            V.le(et,
                 V.add(half,
                       V.bm->CreateTerm(
                           ITE, V.W,
                           V.and_(V.rmIn({symbolic_fp::ROUND_TOWARD_POSITIVE}),
                                  V.odd(ex)),
                           V.I(1), V.I(0))))));
  }
  em.rule(FpRuleId::SQRT_B2, 2, V.and_(V.sub(xb), V.nor(tb)),
          V.le(V.add(et, et), V.I(V.emin)));

  // Tier 3.
  em.rule(FpRuleId::SQRT_I1, 3, V.bitsEq(xb, V.one()), V.bitsEq(tb, V.one()));
  em.rule(FpRuleId::SQRT_I2, 3,
          V.and_(V.nor(xb), V.fractionZero(xb), V.pos(xb), V.not_(V.odd(ex))),
          V.and_(V.nor(tb), V.fractionZero(tb), V.pos(tb),
                 V.ieq(et, V.halfDown(ex))));
  emitSqrtSignificandBands(V, em);
}

// t = add(rm, x, y), and t = sub(rm, x, y) as add(rm, x, -y): the second
// operand's sign bit is flipped in the bits and negated in the view, and one
// table serves both.
void emitAdd(const Vocabulary& V, Emitter& em, bool subtract)
{
  const ASTNode &xb = V.ctx.bits[0], &tb = V.ctx.tb;
  const ASTNode &x = V.ctx.view[0], &t = V.ctx.t;
  const ASTNode yb =
      subtract ? V.bm->CreateTerm(BVXOR, V.width, V.ctx.bits[1], V.minusZero())
               : V.ctx.bits[1];
  const ASTNode y = subtract ? V.fpneg(V.ctx.view[1]) : V.ctx.view[1];
  const ASTNode T = V.bm->ASTTrue;
  const ASTNode ex = V.e(xb), ey = V.e(yb), et = V.e(tb);
  const ASTNode emaxE = V.maxi(ex, ey);
  const ASTNode same = V.sameSign(xb, yb);
  const ASTNode opposite = V.not_(same);
  using namespace symbolic_fp;
  const ASTNode towardNegative = V.rmIn({ROUND_TOWARD_NEGATIVE});

  // Tier 0: shell and sign.
  em.rule(FpRuleId::ADD_S1, 0, T,
          V.iff(V.nan(tb), V.or_(V.nan(xb), V.nan(yb),
                                 V.and_(V.inf(xb), V.inf(yb), opposite))));
  em.rule(FpRuleId::ADD_S2, 0,
          V.or_(V.and_(V.inf(xb), V.not_(V.nan(yb)),
                       V.not_(V.and_(V.inf(yb), opposite))),
                V.and_(V.inf(yb), V.not_(V.nan(xb)),
                       V.not_(V.and_(V.inf(xb), opposite)))),
          V.ite(V.inf(xb), V.fpeq(t, x), V.fpeq(t, y)));
  em.rule(FpRuleId::ADD_S3, 0, V.and_(V.zero(xb), V.zero(yb), same),
          V.fpeq(t, x));
  em.rule(FpRuleId::ADD_S3b, 0, V.and_(V.zero(xb), V.zero(yb), opposite),
          V.zeroSigned(tb, towardNegative));
  em.rule(FpRuleId::ADD_S4, 0,
          V.or_(V.and_(V.zero(xb), V.nz(yb)), V.and_(V.zero(yb), V.nz(xb))),
          V.ite(V.zero(xb), V.fpeq(t, y), V.fpeq(t, x)));
  em.rule(FpRuleId::ADD_S5, 0, V.and_(V.zero(tb), V.nz(xb), V.nz(yb)),
          V.iff(V.neg(tb), towardNegative));
  em.rule(FpRuleId::ADD_S6, 0, V.and_(V.nz(xb), V.nz(yb), same),
          V.and_(V.not_(V.zero(tb)), V.not_(V.nan(tb)), V.sameSign(tb, xb)));
  {
    const ASTNode xLarger = V.fplt(V.fpabs(y), V.fpabs(x));
    const ASTNode yLarger = V.fplt(V.fpabs(x), V.fpabs(y));
    em.rule(FpRuleId::ADD_S7, 0,
            V.and_(V.nz(xb), V.nz(yb), opposite, V.or_(xLarger, yLarger)),
            V.and_(V.not_(V.zero(tb)),
                   V.ite(xLarger, V.sameSign(tb, xb), V.sameSign(tb, yb))));
  }
  em.rule(FpRuleId::ADD_S8, 0,
          V.and_(V.nz(xb), V.nz(yb), opposite, V.fpeq(V.fpabs(x), V.fpabs(y))),
          V.zeroSigned(tb, towardNegative));
  em.rule(FpRuleId::ADD_S9, 0, V.inf(tb),
          V.or_(V.inf(xb), V.inf(yb),
                V.and_(V.nz(xb), V.nz(yb), same, V.or_(V.nor(xb), V.nor(yb)))));

  // Tier 1: order. Adding a non-negative moves up, a non-positive down.
  {
    const ASTNode noNaN =
        V.and_(V.not_(V.nan(tb)), V.not_(V.nan(xb)), V.not_(V.nan(yb)));
    em.rule(FpRuleId::ADD_M1, 1, V.and_(noNaN, V.or_(V.pos(yb), V.zero(yb))),
            V.fpleq(x, t));
    em.rule(FpRuleId::ADD_M2, 1, V.and_(noNaN, V.or_(V.neg(yb), V.zero(yb))),
            V.fpleq(t, x));
    em.rule(FpRuleId::ADD_M1x, 1, V.and_(noNaN, V.or_(V.pos(xb), V.zero(xb))),
            V.fpleq(y, t));
    em.rule(FpRuleId::ADD_M2x, 1, V.and_(noNaN, V.or_(V.neg(xb), V.zero(xb))),
            V.fpleq(t, y));
  }

  // Tier 2: bands and overflow.
  {
    const ASTNode normals = V.and_(V.nor(xb), V.nor(yb));
    em.rule(FpRuleId::ADD_B1, 2, V.and_(normals, V.nor(tb)),
            V.le(et, V.add(emaxE, V.I(1))));
    em.rule(FpRuleId::ADD_B2, 2, V.and_(normals, same, V.nor(tb)),
            V.ge(et, emaxE));
    em.rule(FpRuleId::ADD_B3, 2, V.and_(normals, opposite, V.nor(tb)),
            V.le(et, emaxE));
    em.rule(FpRuleId::ADD_B4, 2,
            V.and_(normals, opposite,
                   V.or_(V.ge(V.subi(ex, ey), V.I(2)),
                         V.ge(V.subi(ey, ex), V.I(2)))),
            V.and_(V.nor(tb), V.ge(et, V.subi(emaxE, V.I(1)))));
    // ADD-B5, both ways round: the larger normal of a same-sign sum bounds
    // the result below.
    em.rule(FpRuleId::ADD_B5, 2,
            V.and_(V.nor(xb), V.nz(yb), same, V.ge(ex, ey)),
            V.and_(V.or_(V.nor(tb), V.inf(tb)), V.ge(et, ex)));
    em.rule(FpRuleId::ADD_B5, 2,
            V.and_(V.nor(yb), V.nz(xb), same, V.ge(ey, ex)),
            V.and_(V.or_(V.nor(tb), V.inf(tb)), V.ge(et, ey)));
    em.rule(
        FpRuleId::ADD_B6, 2,
        V.and_(normals, same, V.ieq(ex, V.I(V.emax)), V.ieq(ey, V.I(V.emax))),
        V.overflowSelect(tb, V.neg(xb)));
    em.rule(FpRuleId::ADD_B7, 2,
            V.and_(V.fin(xb), V.fin(yb), V.le(emaxE, V.I(V.emax - 1))),
            V.not_(V.inf(tb)));
    em.rule(FpRuleId::ADD_B8, 2, V.and_(V.nz(xb), V.nz(yb), V.not_(V.nan(tb))),
            V.or_(V.inf(tb), V.le(et, V.add(emaxE, V.I(1)))));
  }

  // Tier 3: absorption. A normal absorbs an operand at least p+1 binades
  // below it, exactly under round-to-nearest, and otherwise to a
  // neighbour in the rounding direction.
  const auto absorption = [&](const ASTNode& bb, const ASTNode& bv,
                              const ASTNode& smallBits, const ASTNode& eBig,
                              const ASTNode& eSmall) {
    const ASTNode gap = V.subi(eBig, eSmall);
    const ASTNode wide = V.ge(gap, V.I((int64_t)V.p + 2));
    const ASTNode narrow = V.ge(gap, V.I((int64_t)V.p + 1));
    em.rule(
        FpRuleId::ADD_A1, 3,
        V.and_(V.nor(bb), V.nz(smallBits),
               V.rmIn({ROUND_NEAREST_TIES_TO_EVEN, ROUND_NEAREST_TIES_TO_AWAY}),
               V.or_(wide, V.and_(narrow, V.or_(V.not_(V.fractionZero(bb)),
                                                V.sameSign(bb, smallBits))))),
        V.fpeq(t, bv));
    em.rule(
        FpRuleId::ADD_A2, 3,
        V.and_(V.nor(bb), V.nz(smallBits), V.sameSign(bb, smallBits), narrow),
        V.ite(V.or_(V.and_(V.rmIn({ROUND_TOWARD_POSITIVE}), V.pos(bb)),
                    V.and_(towardNegative, V.neg(bb))),
              V.bitsEq(tb, V.succ(bb)), V.fpeq(t, bv)));
    em.rule(
        FpRuleId::ADD_A3, 3,
        V.and_(V.nor(bb), V.nz(smallBits), V.not_(V.sameSign(bb, smallBits)),
               V.or_(wide,
                     V.and_(narrow, V.or_(V.not_(V.fractionZero(bb)),
                                          V.rmIn({ROUND_TOWARD_ZERO,
                                                  ROUND_TOWARD_POSITIVE,
                                                  ROUND_TOWARD_NEGATIVE}))))),
        V.ite(V.or_(V.rmIn({ROUND_TOWARD_ZERO}),
                    V.and_(towardNegative, V.pos(bb)),
                    V.and_(V.rmIn({ROUND_TOWARD_POSITIVE}), V.neg(bb))),
              V.bitsEq(tb, V.pred(bb)), V.fpeq(t, bv)));
  };
  absorption(xb, x, yb, ex, ey);
  absorption(yb, y, xb, ey, ex);
}

// t = fma(rm, x, y, z): one rounding of x*y + z, never modelled as a
// product followed by a sum.
void emitFma(const Vocabulary& V, Emitter& em)
{
  const ASTNode &xb = V.ctx.bits[0], &yb = V.ctx.bits[1], &zb = V.ctx.bits[2],
                &tb = V.ctx.tb;
  const ASTNode &z = V.ctx.view[2], &t = V.ctx.t;
  const ASTNode T = V.bm->ASTTrue;
  const ASTNode ex = V.e(xb), ey = V.e(yb), ez = V.e(zb), et = V.e(tb);
  const ASTNode exy = V.add(ex, ey);
  const ASTNode negProduct = V.not_(V.sameSign(xb, yb));
  const ASTNode zAgrees = V.iff(V.neg(zb), negProduct);
  using namespace symbolic_fp;

  // Tier 0: shell and sign.
  em.rule(FpRuleId::FMA_S1, 0, T,
          V.iff(V.nan(tb),
                V.or_(ASTVec{V.nan(xb), V.nan(yb), V.nan(zb),
                             V.and_(V.zero(xb), V.inf(yb)),
                             V.and_(V.inf(xb), V.zero(yb)),
                             V.and_(V.or_(V.inf(xb), V.inf(yb)), V.inf(zb),
                                    V.iff(V.neg(zb), V.sameSign(xb, yb)))})));
  em.rule(FpRuleId::FMA_S2, 0,
          V.and_(V.not_(V.nan(tb)), V.or_(V.inf(xb), V.inf(yb))),
          V.and_(V.inf(tb), V.iff(V.neg(tb), negProduct)));
  em.rule(FpRuleId::FMA_S3, 0, V.and_(V.inf(zb), V.fin(xb), V.fin(yb)),
          V.fpeq(t, z));
  em.rule(FpRuleId::FMA_S4, 0,
          V.and_(V.or_(V.zero(xb), V.zero(yb)), V.fin(xb), V.fin(yb), V.nz(zb)),
          V.fpeq(t, z));
  em.rule(
      FpRuleId::FMA_S5, 0,
      V.and_(V.or_(V.zero(xb), V.zero(yb)), V.fin(xb), V.fin(yb), V.zero(zb)),
      V.ite(zAgrees, V.zeroSigned(tb, V.neg(zb)),
            V.zeroSigned(tb, V.rmIn({ROUND_TOWARD_NEGATIVE}))));
  em.rule(FpRuleId::FMA_S6, 0, V.and_(V.nz(xb), V.nz(yb), V.nz(zb), zAgrees),
          V.and_(V.not_(V.zero(tb)), V.not_(V.nan(tb)), V.sameSign(tb, zb)));
  em.rule(FpRuleId::FMA_S7, 0, V.and_(V.nz(xb), V.nz(yb), V.zero(zb)),
          V.iff(V.neg(tb), negProduct));
  em.rule(FpRuleId::FMA_S8, 0,
          V.and_(V.nor(xb), V.nor(yb), V.nz(zb), V.ge(exy, V.add(ez, V.I(1)))),
          V.and_(V.iff(V.neg(tb), negProduct), V.not_(V.zero(tb))));
  em.rule(FpRuleId::FMA_S9, 0,
          V.and_(V.nz(xb), V.nz(yb), V.nor(zb), V.ge(ez, V.add(exy, V.I(3)))),
          V.and_(V.sameSign(tb, zb),
                 V.or_(V.inf(tb), V.ge(et, V.subi(ez, V.I(1))))));

  // Tier 1: order against the addend.
  {
    const ASTNode noNaN = V.and_(V.not_(V.nan(tb)), V.not_(V.nan(zb)),
                                 V.not_(V.nan(xb)), V.not_(V.nan(yb)));
    em.rule(FpRuleId::FMA_M1, 1, V.and_(noNaN, V.sameSign(xb, yb)),
            V.fpleq(z, t));
    em.rule(FpRuleId::FMA_M2, 1, V.and_(noNaN, negProduct), V.fpleq(t, z));
  }

  // Tier 2: bands.
  em.rule(FpRuleId::FMA_B1, 2,
          V.and_(V.nor(xb), V.nor(yb), V.nz(zb), V.nor(tb)),
          V.le(et, V.add(V.maxi(V.add(exy, V.I(1)), ez), V.I(1))));
  em.rule(FpRuleId::FMA_B2, 2,
          V.and_(V.and_(V.nor(xb), V.nor(yb), V.nor(zb), V.nor(tb)),
                 V.and_(zAgrees, V.le(exy, V.I(V.emax)))),
          V.ge(et, V.maxi(exy, ez)));
  em.rule(FpRuleId::FMA_B3, 2,
          V.and_(V.nor(xb), V.nor(yb), V.fin(zb),
                 V.le(V.maxi(V.add(exy, V.I(1)), ez), V.I(V.emax - 1))),
          V.not_(V.inf(tb)));
}

// t = rem(x, y): exact, no rounding mode.
void emitRem(const Vocabulary& V, Emitter& em)
{
  const ASTNode &xb = V.ctx.bits[0], &yb = V.ctx.bits[1], &tb = V.ctx.tb;
  const ASTNode &x = V.ctx.view[0], &y = V.ctx.view[1], &t = V.ctx.t;
  const ASTNode T = V.bm->ASTTrue;
  const ASTNode ex = V.e(xb), ey = V.e(yb), et = V.e(tb);

  // Tier 0: shell and sign.
  em.rule(FpRuleId::REM_S1, 0, T,
          V.iff(V.nan(tb),
                V.or_(ASTVec{V.nan(xb), V.nan(yb), V.inf(xb), V.zero(yb)})));
  em.rule(FpRuleId::REM_S2, 0, V.and_(V.fin(xb), V.inf(yb)), V.fpeq(t, x));
  em.rule(FpRuleId::REM_S3, 0,
          V.and_(V.zero(xb), V.not_(V.nan(yb)), V.not_(V.zero(yb))),
          V.fpeq(t, x));
  em.rule(FpRuleId::REM_S4, 0, V.not_(V.nan(tb)), V.fin(tb));
  em.rule(FpRuleId::REM_S5, 0, V.zero(tb), V.sameSign(tb, xb));

  // Tier 1: order. The remainder is at most the dividend and at most half
  // the divisor in magnitude; the latter compares the doubled magnitude
  // bits, which is exact for every finite value.
  em.rule(FpRuleId::REM_O1, 1, V.not_(V.nan(tb)),
          V.fpleq(V.fpabs(t), V.fpabs(x)));
  em.rule(FpRuleId::REM_O2, 1,
          V.and_(V.not_(V.nan(tb)), V.fin(tb), V.nz(yb), V.fin(xb)),
          V.or_(V.zero(tb), V.ule(V.doubledMagnitude(tb), V.magnitude(yb))));

  // Tier 2: bands.
  em.rule(FpRuleId::REM_O3, 2,
          V.and_(V.nz(xb), V.nor(yb), V.le(ex, V.subi(ey, V.I(2)))),
          V.fpeq(t, x));
  em.rule(FpRuleId::REM_O4, 2, V.and_(V.nor(tb), V.nor(yb)),
          V.le(et, V.subi(ey, V.I(1))));

  // Tier 3: identities.
  em.rule(FpRuleId::REM_I1, 3, V.and_(V.nz(xb), V.fpeq(V.fpabs(x), V.fpabs(y))),
          V.zeroSigned(tb, V.neg(xb)));
}

// t = roundToIntegral(rm, x). Integrality is the trailing-exponent
// predicate at threshold 0, which is what "a multiple of 1" is on the
// packed bits; nothing here needs a candidate.
void emitRti(const Vocabulary& V, Emitter& em)
{
  const ASTNode &xb = V.ctx.bits[0], &tb = V.ctx.tb;
  const ASTNode &x = V.ctx.view[0], &t = V.ctx.t;
  const ASTNode T = V.bm->ASTTrue;
  const ASTNode ex = V.e(xb), et = V.e(tb);
  const ASTNode xIntegral =
      fpRuleTrailingExponentAtLeast(V.bm, xb, V.eb, V.sb, 0);
  const ASTNode tIntegral =
      fpRuleTrailingExponentAtLeast(V.bm, tb, V.eb, V.sb, 0);
  using namespace symbolic_fp;

  // Whether every value of the top binade is an integer, which is when
  // 2^(eb-1) >= sb: then the finite range is closed under rounding to an
  // integer. Otherwise the top binade holds non-integers whose rounding up
  // is beyond the largest finite, and is an infinity of the argument's
  // sign (symfpu roundToIntegral, as patched under cmake/deps-utils).
  const bool integralTop = ((uint64_t)1 << (V.eb - 1)) >= (uint64_t)V.sb;

  // Tier 0: shell and sign. A special or a zero is its own rounding; an
  // infinity comes only from one, or from the top binade where that can
  // overflow; the sign is the argument's.
  em.rule(FpRuleId::RTI_N1, 0, T, V.iff(V.nan(tb), V.nan(xb)));
  if (integralTop)
    em.rule(FpRuleId::RTI_N2, 0, T, V.iff(V.inf(tb), V.inf(xb)));
  else
  {
    em.rule(FpRuleId::RTI_N3, 0, V.inf(xb), V.inf(tb));
    em.rule(FpRuleId::RTI_N4, 0, V.inf(tb),
            V.or_(V.inf(xb), V.and_(V.nor(xb), V.ieq(ex, V.I(V.emax)))));
  }
  em.rule(FpRuleId::RTI_S1, 0, V.or_(V.nan(xb), V.inf(xb), V.zero(xb)),
          V.fpeq(t, x));
  em.rule(FpRuleId::RTI_S2, 0, V.not_(V.nan(tb)), V.sameSign(tb, xb));
  // A zero result needs an argument below one in magnitude.
  em.rule(FpRuleId::RTI_N5, 0, V.zero(tb),
          V.or_(V.zero(xb), V.le(ex, V.I(-1))));

  // Tier 1: order, by mode.
  em.rule(FpRuleId::RTI_O1p, 1,
          V.and_(V.not_(V.nan(tb)), V.rmIn({ROUND_TOWARD_POSITIVE})),
          V.fpleq(x, t));
  em.rule(FpRuleId::RTI_O1n, 1,
          V.and_(V.not_(V.nan(tb)), V.rmIn({ROUND_TOWARD_NEGATIVE})),
          V.fpleq(t, x));
  em.rule(FpRuleId::RTI_O1z, 1,
          V.and_(V.not_(V.nan(tb)), V.rmIn({ROUND_TOWARD_ZERO})),
          V.fpleq(V.fpabs(t), V.fpabs(x)));

  // Tier 2: bands, and the result is an integer.
  em.rule(FpRuleId::RTI_S3, 2, V.nz(tb), tIntegral);
  // At or above one, the result is a normal within one binade above --
  // or, in a format whose top binade can overflow, the infinity.
  {
    const ASTNode normalAbove =
        V.and_(V.nor(tb), V.le(ex, et), V.le(et, V.add(ex, V.I(1))));
    em.rule(FpRuleId::RTI_B1, 2, V.and_(V.nor(xb), V.ge(ex, V.I(0))),
            integralTop ? normalAbove
                        : V.or_(normalAbove,
                                V.and_(V.inf(tb), V.ieq(ex, V.I(V.emax)))));
  }
  // Below a half, the result is the zero of the argument's sign under the
  // nearest and toward-zero modes, and that zero or a unit otherwise.
  em.rule(FpRuleId::RTI_B2, 2, V.and_(V.nz(xb), V.le(ex, V.I(-2))),
          V.ite(V.rmIn({ROUND_NEAREST_TIES_TO_EVEN, ROUND_NEAREST_TIES_TO_AWAY,
                        ROUND_TOWARD_ZERO}),
                V.zeroSigned(tb, V.neg(xb)),
                V.or_(V.zeroSigned(tb, V.neg(xb)), V.bitsEq(tb, V.one()),
                      V.bitsEq(tb, V.minusOne()))));
  // Between a half and one, a zero or a unit of the argument's sign.
  em.rule(FpRuleId::RTI_B3, 2, V.and_(V.nz(xb), V.ieq(ex, V.I(-1))),
          V.or_(V.zeroSigned(tb, V.neg(xb)), V.bitsEq(tb, V.one()),
                V.bitsEq(tb, V.minusOne())));

  // Tier 3: an integer is its own rounding, and nothing else is.
  em.rule(FpRuleId::RTI_S4, 3, V.and_(V.nz(xb), xIntegral), V.fpeq(t, x));
  em.rule(FpRuleId::RTI_I1, 3, V.and_(V.nz(xb), V.not_(xIntegral)),
          V.not_(V.bitsEq(tb, xb)));
}

// fp.to_sbv / fp.to_ubv, in their totalised form: the result is a machine
// integer of `targetWidth` bits, and everything unspecified -- NaN, the
// infinities, and any value whose rounding leaves the target range -- is
// the totalised choice `undefBits`. The sound vocabulary is the operand's
// class and exponent against the target width: rounding is monotone over
// the representable integers, so 2^e <= |x| < 2^(e+1) bounds the rounded
// magnitude by [2^e, 2^(e+1)] wherever both bounds are in range, and the
// rows stop one exponent short of the boundary the rounding mode could
// cross. Host-word range endpoints have width caps; direct zero and
// unspecified results use the full target width.
void emitToBV(const Vocabulary& V, Emitter& em, bool isSigned)
{
  STPMgr* bm = V.bm;
  if (V.ctx.bits.empty() || V.ctx.undefBits.IsNull() ||
      V.ctx.targetWidth < 2)
    return;
  const ASTNode& xb = V.ctx.bits[0];
  const ASTNode& tb = V.ctx.tb;
  const ASTNode& undef = V.ctx.undefBits;
  const unsigned m = V.ctx.targetWidth;

  const ASTNode tUndef = bm->CreateNode(EQ, tb, undef);
  // The whole special-value semantics: NaN and the infinities are the
  // totalised choice, a zero of either sign is the integer zero.
  em.rule(FpRuleId::CVT_S1, 0, V.nan(xb), tUndef);
  em.rule(FpRuleId::CVT_S2, 0, V.inf(xb), tUndef);
  em.rule(FpRuleId::CVT_S3, 0, V.zero(xb),
          bm->CreateNode(EQ, tb, bm->CreateZeroConst(m)));

  // The target width is itself an integer in these comparisons. The FP
  // exponent width alone need not hold it (e.g. (eb,p)=(2,2), m=64).
  const unsigned CW = std::max(V.W, bitLength(m) + 2);
  const auto I = [&](int64_t n) {
    return bm->CreateBVConst(CW, (uint64_t)n & (((uint64_t)1 << CW) - 1));
  };
  const ASTNode eW = CW == V.W
                        ? V.e(xb)
                        : bm->CreateTerm(BVSX, CW, V.e(xb),
                                         bm->CreateBVConst(32, CW));
  const ASTNode finNz = V.and_(V.fin(xb), V.nz(xb));
  // |x| >= 2^m is out of range for either signedness (the unsigned
  // maximum is 2^m - 1, the signed magnitudes at most 2^(m-1)).
  em.rule(FpRuleId::CVT_B1, 2, V.and_(finNz, V.ge(eW, I((int64_t)m))), tUndef);
  if (!isSigned)
  {
    // A negative of magnitude one or more rounds at or below -1: out of
    // the unsigned range under every mode.
    em.rule(FpRuleId::UBV_B2, 2, V.and_(finNz, V.neg(xb), V.ge(eW, I(0))),
            tUndef);
    const ASTNode negativeSmall = V.and_(finNz, V.neg(xb), V.lt(eW, I(0)));
    em.rule(
        FpRuleId::UBV_B5, 2,
        V.and_(negativeSmall,
               V.or_(V.rmIn({symbolic_fp::ROUND_TOWARD_ZERO,
                             symbolic_fp::ROUND_TOWARD_POSITIVE}),
                     V.and_(V.rmIn({symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN,
                                    symbolic_fp::ROUND_NEAREST_TIES_TO_AWAY}),
                            V.le(eW, I(-2))))),
        bm->CreateNode(EQ, tb, bm->CreateZeroConst(m)));
    em.rule(FpRuleId::UBV_B6, 2,
            V.and_(negativeSmall, V.rmIn({symbolic_fp::ROUND_TOWARD_NEGATIVE})),
            tUndef);
  }
  else
  {
    // At e = m-1 only one signed value is representable: -2^(m-1) itself.
    // A positive rounds to at least 2^(m-1) under every mode. A negative
    // is out of range once the integer part of |x| exceeds 2^(m-1): with
    // e(x) = m-1 that part is 2^(m-1) + floor(F / 2^(p-m)), so the test is
    // the top m-1 bits of the fraction field. For p <= m that integer
    // part is F * 2^(m-p), whose zero test is the whole field's zero test;
    // every value of the binade is then an integer. Below that,
    // |x| in (2^(m-1), 2^(m-1)+1) rounds to -2^(m-1) toward zero or
    // upward, past the range toward negative, and to either under the
    // nearest modes, which are left to the value lemmas. (The row once
    // sent every negative of the binade with a nonzero fraction to the
    // unspecified value, which is wrong wherever p > m: -128.125 to 8
    // bits under RNE is -128.)
    using namespace symbolic_fp;
    const ASTNode eTop = V.ieq(eW, I((int64_t)m - 1));
    em.rule(FpRuleId::SBV_B2, 2, V.and_(finNz, V.pos(xb), eTop), tUndef);
    const bool fractionalBinade = V.p > m;
    const ASTNode integerPartZero =
        fractionalBinade
            ? bm->CreateNode(EQ, V.extract(xb, V.fw - 1, V.p - m),
                             bm->CreateZeroConst(m - 1))
            : V.fractionZero(xb);
    em.rule(
        FpRuleId::SBV_B3, 2,
        V.and_(finNz, V.neg(xb), eTop, bm->CreateNode(NOT, integerPartZero)),
        tUndef);
    if (fractionalBinade)
    {
      const ASTNode sliver =
          V.and_(finNz, V.neg(xb), eTop,
                 V.and_(integerPartZero,
                        bm->CreateNode(NOT, V.fractionZero(xb))));
      const ASTNode towardNegative = V.rmIn({ROUND_TOWARD_NEGATIVE});
      if (towardNegative != bm->ASTFalse)
        em.rule(FpRuleId::SBV_B4, 2, V.and_(sliver, towardNegative), tUndef);
      const ASTNode towardTheEdge =
          V.rmIn({ROUND_TOWARD_ZERO, ROUND_TOWARD_POSITIVE});
      if (m <= 64 && towardTheEdge != bm->ASTFalse)
        em.rule(FpRuleId::SBV_B5, 2, V.and_(sliver, towardTheEdge),
                bm->CreateNode(EQ, tb,
                               bm->CreateBVConst(m, (uint64_t)1 << (m - 1))));
    }
    if (m <= 64)
      em.rule(
          FpRuleId::SBV_B6, 2,
          V.and_(finNz, V.neg(xb), eTop, V.fractionZero(xb)),
          bm->CreateNode(EQ, tb, bm->CreateBVConst(m, (uint64_t)1 << (m - 1))));
  }

  // |x| < 1 rounds to a magnitude of at most one, which every target
  // range holds for signed or positive unsigned inputs. UBV-B5/B6 handle
  // the guarded negative cases; the remaining nearest cases use refinement.
  const ASTNode eSmall = V.and_(finNz, V.lt(eW, I(0)));
  if (m <= 64)
  {
    const ASTNode one = bm->CreateOneConst(m);
    if (!isSigned)
      em.rule(FpRuleId::UBV_B3, 2, V.and_(eSmall, V.pos(xb)),
              bm->CreateNode(BVLE, tb, one));
    else
      em.rule(FpRuleId::SBV_B7, 2, eSmall,
              V.and_(bm->CreateNode(BVSLE, tb, one),
                     bm->CreateNode(BVSGE, tb,
                                    bm->CreateBVConst(m, (uint64_t)0 - 1))));
  }

  // The exponent bands: 2^e <= |x| < 2^(e+1) bounds the rounded magnitude
  // by [2^e, 2^(e+1)] wherever the upper bound is still in range -- one
  // exponent short of the boundary, which rounding away from zero could
  // cross.
  if (m <= 64 && m >= 4)
  {
    const int64_t eCap = isSigned ? (int64_t)m - 3 : (int64_t)m - 2;
    if (eCap >= 0)
    {
      const ASTNode inBand =
          V.and_(finNz, V.ge(eW, I(0)), V.le(eW, I(eCap)));
      // 2^e at the target width: the guard bounds e inside [0, m-2], so
      // the low target-width bits of the exponent arithmetic are exact.
      const ASTNode eM =
          m >= CW
              ? bm->CreateTerm(BVZX, m, eW, bm->CreateBVConst(32, m))
              : bm->CreateTerm(BVEXTRACT, m, eW, bm->CreateBVConst(32, m - 1),
                               bm->CreateBVConst(32, 0));
      const ASTNode one = bm->CreateOneConst(m);
      const ASTNode pow = bm->CreateTerm(BVLEFTSHIFT, m, one, eM);
      const ASTNode pow2 = bm->CreateTerm(
          BVLEFTSHIFT, m, one,
          bm->CreateTerm(BVPLUS, m, eM, one));
      if (!isSigned)
        em.rule(FpRuleId::UBV_B4, 2, V.and_(inBand, V.pos(xb)),
                V.and_(bm->CreateNode(BVGE, tb, pow),
                       bm->CreateNode(BVLE, tb, pow2)));
      else
      {
        em.rule(FpRuleId::SBV_B8, 2, V.and_(inBand, V.pos(xb)),
                V.and_(bm->CreateNode(BVSGE, tb, pow),
                       bm->CreateNode(BVSLE, tb, pow2)));
        em.rule(
            FpRuleId::SBV_B9, 2, V.and_(inBand, V.neg(xb)),
            V.and_(
                bm->CreateNode(BVSLE, tb, bm->CreateTerm(BVUMINUS, m, pow)),
                bm->CreateNode(BVSGE, tb, bm->CreateTerm(BVUMINUS, m, pow2))));
      }
    }
  }
}

} // namespace

unsigned emitFpAbstractionRules(const FpRuleContext& context, unsigned tiers,
                                std::vector<ASTNode>& out,
                                std::vector<FpRuleId>* ids)
{
  Vocabulary V(context);
  Emitter em{V, tiers, out, ids};
  switch (context.kind)
  {
    case FP_MUL:
      emitMul(V, em);
      break;
    case FP_DIV:
      emitDiv(V, em);
      break;
    case FP_SQRT:
      emitSqrt(V, em);
      break;
    case FP_ADD:
      emitAdd(V, em, false);
      break;
    case FP_SUB:
      emitAdd(V, em, true);
      break;
    case FP_FMA:
      emitFma(V, em);
      break;
    case FP_REM:
      emitRem(V, em);
      break;
    case FP_ROUNDTOINTEGRAL:
      emitRti(V, em);
      break;
    case FP_TO_SBV:
      emitToBV(V, em, true);
      break;
    case FP_TO_UBV:
      emitToBV(V, em, false);
      break;
    default:
      break;
  }
  return em.count;
}

unsigned emitFpAbstractionCrossRules(const FpRuleContext& fma,
                                     const FpRuleContext* product,
                                     const FpRuleContext* sumWithX,
                                     const FpRuleContext* sumWithY,
                                     std::vector<ASTNode>& out,
                                     std::vector<FpRuleId>* ids)
{
  assert(fma.kind == FP_FMA && fma.bits.size() == 3);
  Vocabulary V(fma);
  Emitter em{V, 0, out, ids};
  const ASTNode &xb = fma.bits[0], &yb = fma.bits[1], &zb = fma.bits[2];
  const ASTNode &tb = fma.tb, &t = fma.t;
  if (product != NULL)
  {
    const ASTNode &pb = product->tb, &p = product->t;
    // fma(x, y, z) rounds x*y + z once and mul(x, y) rounds x*y once; an
    // addend of either sign moves the exact value its way, and rounding
    // is monotone.
    const ASTNode numbers = V.and_(V.not_(V.nan(tb)), V.not_(V.nan(pb)));
    em.rule(FpRuleId::FMA_C1, 0, V.and_(numbers, V.or_(V.pos(zb), V.zero(zb))),
            V.fpleq(p, t));
    em.rule(FpRuleId::FMA_C2, 0, V.and_(numbers, V.or_(V.neg(zb), V.zero(zb))),
            V.fpleq(t, p));
    // A zero addend to a nonzero product leaves the exact value alone, so
    // the one rounding of each is the same rounding: the results are one
    // value, NaN against NaN included.
    em.rule(FpRuleId::FMA_C3, 0,
            V.and_(V.zero(zb), V.not_(V.zero(xb)), V.not_(V.zero(yb))),
            V.fpeq(t, p));
  }
  // x*1 + z is x + z before either is rounded.
  if (sumWithX != NULL)
    em.rule(FpRuleId::FMA_C4, 0, V.bitsEq(yb, V.one()), V.fpeq(t, sumWithX->t));
  if (sumWithY != NULL)
    em.rule(FpRuleId::FMA_C5, 0, V.bitsEq(xb, V.one()), V.fpeq(t, sumWithY->t));
  return em.count;
}

// ---------------------------------------------------------------- concrete

namespace
{
bool bitAt(const ASTNode& c, unsigned i)
{
  return CONSTANTBV::BitVector_bit_test(c.GetBVConst(), i) != 0;
}
uint64_t fieldValue(const ASTNode& c, unsigned lo, unsigned n)
{
  uint64_t v = 0;
  for (unsigned i = 0; i < n && i < 64; i++)
    if (bitAt(c, lo + i))
      v |= (uint64_t)1 << i;
  return v;
}
bool fieldZero(const ASTNode& c, unsigned lo, unsigned n)
{
  for (unsigned i = 0; i < n; i++)
    if (bitAt(c, lo + i))
      return false;
  return true;
}
unsigned fieldTrailingZeros(const ASTNode& c, unsigned lo, unsigned n)
{
  for (unsigned i = 0; i < n; i++)
    if (bitAt(c, lo + i))
      return i;
  return n;
}
} // namespace

FpPackedValue decodeFpPackedValue(const ASTNode& c, unsigned eb, unsigned sb)
{
  assert(c.GetKind() == BVCONST && c.GetValueWidth() == eb + sb);
  const unsigned fw = sb - 1;
  const int64_t bias = ((int64_t)1 << (eb - 1)) - 1;
  const int64_t emin = 1 - bias;
  FpPackedValue v;
  v.negative = bitAt(c, eb + sb - 1);
  const bool eAllOnes = !fieldZero(c, fw, eb) &&
                        fieldValue(c, fw, eb) == (((uint64_t)1 << eb) - 1);
  const bool eZero = fieldZero(c, fw, eb);
  const bool fZero = fieldZero(c, 0, fw);
  if (eAllOnes)
  {
    v.cls = fZero ? FpPackedValue::Inf : FpPackedValue::NaN;
    v.e = bias + 1;
    return v;
  }
  if (eZero)
  {
    v.cls = fZero ? FpPackedValue::Zero : FpPackedValue::Subnormal;
    v.e = emin - 1;
    // M * 2^k with k = emin - fw and M = F.
    v.f = (emin - (int64_t)fw) + (fZero ? 0 : (int64_t)fieldTrailingZeros(c, 0, fw));
    return v;
  }
  v.cls = FpPackedValue::Normal;
  v.e = (int64_t)fieldValue(c, fw, eb) - bias;
  // M = 1.F as an integer: hidden bit at position fw.
  const int64_t k = v.e - (int64_t)fw;
  v.f = k + (fZero ? (int64_t)fw : (int64_t)fieldTrailingZeros(c, 0, fw));
  return v;
}

bool fpPackedLeq(const ASTNode& a, const ASTNode& b, unsigned eb, unsigned sb)
{
  const FpPackedValue va = decodeFpPackedValue(a, eb, sb);
  const FpPackedValue vb = decodeFpPackedValue(b, eb, sb);
  if (va.cls == FpPackedValue::NaN || vb.cls == FpPackedValue::NaN)
    return false;
  if (va.cls == FpPackedValue::Zero && vb.cls == FpPackedValue::Zero)
    return true;
  if (va.negative != vb.negative)
    return va.negative;
  // One sign: the magnitude bits order as an unsigned integer.
  int compare = 0;
  for (int i = (int)(eb + sb) - 2; i >= 0 && compare == 0; --i)
  {
    const bool x = bitAt(a, i), y = bitAt(b, i);
    if (x != y)
      compare = x ? 1 : -1;
  }
  return va.negative ? compare >= 0 : compare <= 0;
}

bool fpPackedSmtEqual(const ASTNode& a, const ASTNode& b, unsigned eb,
                      unsigned sb)
{
  const FpPackedValue va = decodeFpPackedValue(a, eb, sb);
  const FpPackedValue vb = decodeFpPackedValue(b, eb, sb);
  if (va.cls == FpPackedValue::NaN || vb.cls == FpPackedValue::NaN)
    return va.cls == vb.cls;
  return CONSTANTBV::BitVector_equal(a.GetBVConst(), b.GetBVConst()) != 0;
}

ASTNode fpRuleTrailingExponentAtLeast(STPMgr* bm, const ASTNode& bits,
                                      unsigned eb, unsigned sb,
                                      int64_t threshold)
{
  FpRuleContext c;
  c.bm = bm;
  c.eb = eb;
  c.sb = sb;
  c.rm = symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN; // unused
  Vocabulary V(c);
  const unsigned p = sb;
  // Outside the finite trailing-exponent range the answer needs no
  // arithmetic. Besides simplifying the common extremes, this keeps
  // arbitrary int64_t thresholds from wrapping in a narrower encoding.
  if (threshold <= V.emin - ((int64_t)p - 1))
    return V.fin(bits);
  if (threshold > V.emax)
    return V.zero(bits);
  // U bits hold both the exponent arithmetic and a mask over the p-bit
  // integer significand.
  const unsigned U = std::max(V.W, p + 1);
  const auto widen = [&](const ASTNode& n) {
    return n.GetValueWidth() == U
               ? n
               : bm->CreateTerm(BVSX, U, n, bm->CreateBVConst(32, U));
  };
  const auto UI = [&](int64_t n) {
    if (U <= 64)
    {
      const uint64_t mask = U == 64 ? ~(uint64_t)0 : (((uint64_t)1 << U) - 1);
      return bm->CreateBVConst(U, (uint64_t)n & mask);
    }
    // CreateBVConst(width, uint64_t) zero-extends above bit 63. Negative
    // exponents instead need their signed, U-bit two's-complement value.
    return bm->CreateTerm(BVSX, U, bm->CreateBVConst(64, (uint64_t)n),
                           bm->CreateBVConst(32, U));
  };
  // M = hidden . F, as an unsigned U-bit value.
  const ASTNode hidden = bm->CreateTerm(ITE, 1, V.nor(bits), bm->CreateOneConst(1),
                                        bm->CreateZeroConst(1));
  const ASTNode M = bm->CreateTerm(BVCONCAT, p, hidden, V.F(bits));
  const ASTNode Mu = bm->CreateTerm(BVZX, U, M, bm->CreateBVConst(32, U));
  // k: the place value of M's lowest bit.
  const ASTNode k = widen(bm->CreateTerm(
      ITE, V.W, V.nor(bits), V.subi(V.e(bits), V.I((int64_t)p - 1)),
      V.I(V.emin - ((int64_t)p - 1))));
  const ASTNode s = bm->CreateTerm(BVSUB, U, UI(threshold), k);
  const ASTNode mask = bm->CreateTerm(
      BVSUB, U, bm->CreateTerm(BVLEFTSHIFT, U, UI(1), s), UI(1));
  const ASTNode lowBitsZero =
      bm->CreateNode(EQ, bm->CreateTerm(BVAND, U, Mu, mask), UI(0));
  return V.or_(V.zero(bits),
               V.and_(V.nz(bits),
                      V.or_(bm->CreateNode(BVSLE, s, UI(0)),
                            V.and_(bm->CreateNode(BVSLT, s, UI((int64_t)p)),
                                   lowBitsZero))));
}

ASTNode fpAbstractionShapeLemma(const FpRuleContext& context,
                                const std::vector<ASTNode>& operandValues,
                                const ASTNode& surrogateValue, FpRuleId* id)
{
  if (id != nullptr)
    *id = FpRuleId::None;
  const auto identified = [&](FpRuleId schema, const ASTNode& lemma)
  {
    if (id != nullptr)
      *id = schema;
    return lemma;
  };
  // The trailing-exponent shapes are facts about float results; an integer
  // conversion's result has none, and decoding it as packed float bits
  // would be garbage (at Float32 to int32 the widths even coincide).
  if (context.targetWidth != 0)
    return ASTNode();
  STPMgr* bm = context.bm;
  const unsigned eb = context.eb, sb = context.sb;
  const int64_t bias = ((int64_t)1 << (eb - 1)) - 1;
  const int64_t emax = bias;
  std::vector<FpPackedValue> ov;
  for (const ASTNode& c : operandValues)
    ov.push_back(decodeFpPackedValue(c, eb, sb));
  const FpPackedValue tv = decodeFpPackedValue(surrogateValue, eb, sb);
  const auto nonzeroFinite = [](const FpPackedValue& v) {
    return v.cls == FpPackedValue::Normal || v.cls == FpPackedValue::Subnormal;
  };
  Vocabulary V(context);
  const auto fge = [&](const ASTNode& bits, int64_t c) {
    return fpRuleTrailingExponentAtLeast(bm, bits, eb, sb, c);
  };

  switch (context.kind)
  {
    case FP_MUL:
    {
      if (!(nonzeroFinite(ov[0]) && nonzeroFinite(ov[1]) && nonzeroFinite(tv)))
        return ASTNode();
      if (ov[0].e + ov[1].e > emax - 1)
        return ASTNode();
      const int64_t c = ov[0].f + ov[1].f;
      if (tv.f >= c)
        return ASTNode(); // the candidate does not violate it
      const ASTNode guard = V.and_(
          V.and_(V.nz(context.bits[0]), V.nz(context.bits[1])),
          V.and_(fge(context.bits[0], ov[0].f), fge(context.bits[1], ov[1].f)),
          V.le(V.add(V.e(context.bits[0]), V.e(context.bits[1])),
               V.I(emax - 1)));
      return identified(FpRuleId::MUL_X2, V.implies(guard, fge(context.tb, c)));
    }
    case FP_ADD:
    case FP_SUB:
    case FP_REM:
    {
      if (!(nonzeroFinite(ov[0]) && nonzeroFinite(ov[1]) && nonzeroFinite(tv)))
        return ASTNode();
      if (context.kind != FP_REM)
      {
        const bool cancels = context.kind == FP_SUB
                                 ? ov[0].negative == ov[1].negative
                                 : ov[0].negative != ov[1].negative;
        if (!cancels && std::max(ov[0].e, ov[1].e) > emax - 1)
          return ASTNode();
      }
      const int64_t c = std::min(ov[0].f, ov[1].f);
      if (tv.f >= c)
        return ASTNode();
      ASTNode guard =
          V.and_(V.and_(V.nz(context.bits[0]), V.nz(context.bits[1])),
                 V.and_(fge(context.bits[0], c), fge(context.bits[1], c)));
      if (context.kind != FP_REM)
      {
        const ASTNode same = V.sameSign(context.bits[0], context.bits[1]);
        const ASTNode cancels = context.kind == FP_SUB ? same : V.not_(same);
        guard = V.and_(guard, V.or_(cancels, V.le(V.maxi(V.e(context.bits[0]),
                                                         V.e(context.bits[1])),
                                                  V.I(emax - 1))));
      }
      return identified(context.kind == FP_REM ? FpRuleId::REM_X1
                                               : FpRuleId::ADD_X1,
                        V.implies(guard, fge(context.tb, c)));
    }
    case FP_FMA:
    {
      if (!(nonzeroFinite(ov[0]) && nonzeroFinite(ov[1]) &&
            nonzeroFinite(ov[2]) && nonzeroFinite(tv)))
        return ASTNode();
      if (std::max(ov[0].e + ov[1].e + 1, ov[2].e) > emax - 1)
        return ASTNode();
      const int64_t c = std::min(ov[0].f + ov[1].f, ov[2].f);
      if (tv.f >= c)
        return ASTNode();
      const ASTNode guard = V.and_(
          V.and_(V.nz(context.bits[0]), V.nz(context.bits[1]),
                 V.nz(context.bits[2])),
          V.and_(fge(context.bits[0], ov[0].f), fge(context.bits[1], ov[1].f),
                 fge(context.bits[2], ov[2].f)),
          V.le(V.maxi(V.add(V.e(context.bits[0]), V.e(context.bits[1]), V.I(1)),
                      V.e(context.bits[2])),
               V.I(emax - 1)));
      return identified(FpRuleId::FMA_X1, V.implies(guard, fge(context.tb, c)));
    }
    default:
      return ASTNode();
  }
}

// ------------------------------------------------------------- relational

ASTNode fpAbstractionRelationalLemma(const FpRuleContext& a,
                                     const std::vector<ASTNode>& aValues,
                                     const ASTNode& aResult,
                                     const FpRuleContext& b,
                                     const std::vector<ASTNode>& bValues,
                                     const ASTNode& bResult, FpRuleId* id)
{
  if (id != nullptr)
    *id = FpRuleId::None;
  const auto identified = [&](FpRuleId schema, const ASTNode& lemma)
  {
    if (id != nullptr)
      *id = schema;
    return lemma;
  };
  if (a.kind != b.kind || a.eb != b.eb || a.sb != b.sb || a.rm != b.rm)
    return ASTNode();
  if (a.rm == 0 && a.kind != FP_REM && a.rmTerm != b.rmTerm)
    return ASTNode();
  // The monotonicity and congruence facts below compare results as floats;
  // an integer conversion's results are machine integers (and at Float32
  // to int32 the widths coincide, so the decode would not even trap).
  // Conversions take their own relational family or none.
  if (a.targetWidth != 0 || b.targetWidth != 0)
    return ASTNode();
  const unsigned eb = a.eb, sb = a.sb;
  const auto decode = [&](const ASTNode& c) {
    return decodeFpPackedValue(c, eb, sb);
  };
  Vocabulary V(a);
  // Every monotonicity fact is guarded by both results being numbers; a
  // candidate that has either as NaN violates none of them. The initial
  // NaN characterisations already handle congruent tuples in that case.
  const bool someResultNaN = decode(aResult).cls == FpPackedValue::NaN ||
                             decode(bResult).cls == FpPackedValue::NaN;

  if (someResultNaN)
    return ASTNode();

  // The monotonicity fact over operand i of `a` and operand j of `b`, the
  // other operands being shared: with `direction` +1, a smaller operand
  // gives a smaller result; with -1, a larger one. Both orientations of the
  // premise are tried, and the one the candidate violates is returned.
  const auto fact = [&](FpRuleId schema, const ASTNode& guard, unsigned i,
                        unsigned j, int direction) -> ASTNode
  {
    const bool ab = fpPackedLeq(aValues[i], bValues[j], eb, sb);
    const bool ba = fpPackedLeq(bValues[j], aValues[i], eb, sb);
    const bool tab = fpPackedLeq(aResult, bResult, eb, sb);
    const bool tba = fpPackedLeq(bResult, aResult, eb, sb);
    ASTNode premise, conclusion;
    if (ab && !(direction > 0 ? tab : tba))
    {
      premise = V.fpleq(a.view[i], b.view[j]);
      conclusion = direction > 0 ? V.fpleq(a.t, b.t) : V.fpleq(b.t, a.t);
    }
    else if (ba && !(direction > 0 ? tba : tab))
    {
      premise = V.fpleq(b.view[j], a.view[i]);
      conclusion = direction > 0 ? V.fpleq(b.t, a.t) : V.fpleq(a.t, b.t);
    }
    else
      return ASTNode();
    ASTVec antecedent{V.not_(V.nan(a.tb)), V.not_(V.nan(b.tb)), premise};
    if (!guard.IsNull())
      antecedent.push_back(guard);
    return identified(schema, V.implies(V.and_(antecedent), conclusion));
  };
  const auto shared = [&](unsigned i, unsigned j) {
    return a.bits[i] == b.bits[j];
  };

  // Functional consistency first: operands equal under SMT-LIB equality
  // in the candidate -- not merely the same symbols, which the records'
  // keys already merge -- and results that are not. The fact is the
  // congruence of the operation, with the product's factors taken in
  // either order.
  {
    const size_t n = a.bits.size();
    std::vector<unsigned> pairing(n);
    for (unsigned i = 0; i < n; ++i)
      pairing[i] = i;
    bool congruent = true;
    if (n == b.bits.size())
    {
      for (unsigned i = 0; i < n; ++i)
        if (!fpPackedSmtEqual(aValues[i], bValues[i], eb, sb))
          congruent = false;
      if (!congruent && (a.kind == FP_MUL || a.kind == FP_ADD ||
                         a.kind == FP_FMA))
      {
        // The commuted pairing of the two factors.
        std::vector<unsigned> swapped = pairing;
        std::swap(swapped[0], swapped[1]);
        congruent = true;
        for (unsigned i = 0; i < n; ++i)
          if (!fpPackedSmtEqual(aValues[i], bValues[swapped[i]], eb, sb))
            congruent = false;
        if (congruent)
          pairing = swapped;
      }
    }
    else
      congruent = false;
    if (congruent && !fpPackedSmtEqual(aResult, bResult, eb, sb))
    {
      ASTVec antecedent;
      for (unsigned i = 0; i < n; ++i)
        antecedent.push_back(V.fpeq(a.view[i], b.view[pairing[i]]));
      return identified(FpRuleId::REL_C1,
                        V.implies(V.and_(antecedent), V.fpeq(a.t, b.t)));
    }
  }
  // A fact whose direction follows the sign of shared operand i: monotone
  // for a non-negative one, antitone for a negative one; guarded by that
  // sign so it stays universal.
  const auto bySign = [&](FpRuleId schema, unsigned i, unsigned vi,
                          unsigned vj) -> ASTNode
  {
    const bool negative = decode(aValues[i]).negative;
    return fact(schema, negative ? V.neg(a.bits[i]) : V.pos(a.bits[i]), vi, vj,
                negative ? -1 : +1);
  };

  switch (a.kind)
  {
    case FP_SQRT:
    case FP_ROUNDTOINTEGRAL:
      return fact(FpRuleId::REL_U1, ASTNode(), 0, 0, +1);
    case FP_MUL:
    case FP_ADD:
      for (unsigned i = 0; i < 2; ++i)
        for (unsigned j = 0; j < 2; ++j)
          if (shared(i, j))
          {
            // A sum is monotone in its free operand outright; a product
            // in the direction of the shared operand's sign.
            const ASTNode r =
                a.kind == FP_ADD
                    ? fact(FpRuleId::REL_A1, ASTNode(), 1 - i, 1 - j, +1)
                    : bySign(FpRuleId::REL_M1, i, 1 - i, 1 - j);
            if (!r.IsNull())
              return r;
          }
      return ASTNode();
    case FP_SUB:
      if (shared(0, 0))
        return fact(FpRuleId::REL_S1, ASTNode(), 1, 1, -1);
      if (shared(1, 1))
        return fact(FpRuleId::REL_S2, ASTNode(), 0, 0, +1);
      return ASTNode();
    case FP_DIV:
      if (shared(1, 1))
        // One divisor: the quotient follows the dividend, in the direction
        // of the divisor's sign.
        return bySign(FpRuleId::REL_D1, 1, 0, 0);
      if (shared(0, 0))
      {
        // One dividend: the quotient runs against the divisor, for
        // divisors of one sign and neither zero, in the direction of the
        // dividend's sign.
        const FpPackedValue ya = decode(aValues[1]), yb = decode(bValues[1]);
        const bool usable = ya.cls != FpPackedValue::Zero &&
                            yb.cls != FpPackedValue::Zero &&
                            ya.cls != FpPackedValue::NaN &&
                            yb.cls != FpPackedValue::NaN &&
                            ya.negative == yb.negative;
        if (!usable)
          return ASTNode();
        const bool negative = decode(aValues[0]).negative;
        const ASTNode guard =
            V.and_(V.sameSign(a.bits[1], b.bits[1]), V.not_(V.zero(a.bits[1])),
                   V.not_(V.zero(b.bits[1])),
                   negative ? V.neg(a.bits[0]) : V.pos(a.bits[0]));
        return fact(FpRuleId::REL_D2, guard, 1, 1, negative ? +1 : -1);
      }
      return ASTNode();
    case FP_FMA:
      if (shared(2, 2))
        for (unsigned i = 0; i < 2; ++i)
          for (unsigned j = 0; j < 2; ++j)
            if (shared(i, j))
            {
              const ASTNode r = bySign(FpRuleId::REL_F1, i, 1 - i, 1 - j);
              if (!r.IsNull())
                return r;
            }
      if ((shared(0, 0) && shared(1, 1)) || (shared(0, 1) && shared(1, 0)))
        return fact(FpRuleId::REL_F2, ASTNode(), 2, 2, +1);
      return ASTNode();
    default:
      return ASTNode();
  }
}

} // namespace stp
