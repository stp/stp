/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: July, 2026
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

#include "stp/Simplifier/AchievableImage.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Util/CBVOps.h"

namespace stp
{

namespace
{

// The bottom `bits` bits set, at the given width.
CBV mkLowMask(unsigned bits, unsigned width)
{
  assert(bits <= width);
  CBV v = mkZero(width);
  if (bits > 0)
    CONSTANTBV::BitVector_Interval_Fill(v, 0, bits - 1);
  return v;
}

CBV clone(const CBV v)
{
  return CONSTANTBV::BitVector_Clone(v);
}

void destroy(CBV v)
{
  CONSTANTBV::BitVector_Destroy(v);
}

int ucmp(const CBV a, const CBV b)
{
  return CONSTANTBV::BitVector_Lexicompare(a, b);
}

bool isZero(const CBV v)
{
  return CONSTANTBV::BitVector_is_empty(v);
}

// The low `width` bits.
CBV truncate(const CBV v, unsigned width)
{
  assert(width <= bits_(v));
  CBV out = CONSTANTBV::BitVector_Create(width, false);
  CONSTANTBV::BitVector_Interval_Copy(out, v, 0, 0, width);
  return out;
}

// Zero-extend to `width`.
CBV widen(const CBV v, unsigned width)
{
  assert(width >= bits_(v));
  CBV out = mkZero(width);
  CONSTANTBV::BitVector_Interval_Copy(out, v, 0, 0, bits_(v));
  return out;
}

CBV op1(Kind k, const CBV a, unsigned outWidth)
{
  std::vector<CBV> args = {a};
  return NonMemberBVConstEvaluator(k, args, outWidth);
}

CBV op2(Kind k, const CBV a, const CBV b, unsigned outWidth)
{
  std::vector<CBV> args = {a, b};
  return NonMemberBVConstEvaluator(k, args, outWidth);
}

// max(a, t) where t is owned; the result is owned.
CBV umaxTake(const CBV a, CBV t)
{
  if (ucmp(a, t) > 0)
  {
    destroy(t);
    return clone(a);
  }
  return t;
}

} // namespace

AchievableImage::AchievableImage(STPMgr& _bm, unsigned _varWidth)
    : bm(_bm), varWidth(_varWidth), rep(Rep::Exact), lo(mkZero(_varWidth)),
      hi(allOnes(_varWidth)), curWidth(_varWidth)
{
  assert(varWidth > 0);
}

AchievableImage::~AchievableImage()
{
  if (lo != NULL)
    destroy(lo);
  if (hi != NULL)
    destroy(hi);
  for (auto& p : exactBounds)
  {
    destroy(p.first);
    destroy(p.second);
  }
  for (Sample& s : samples)
  {
    destroy(s.witness);
    destroy(s.value);
  }
  for (CBV h : hints)
    destroy(h);
}

namespace
{
// Deterministic integer square root (no libm: the result seeds samples,
// and a last-ulp difference between platforms would change the CNF).
uint64_t isqrt64(uint64_t n)
{
  if (n == 0)
    return 0;
  // The Newton seed is ceil(n/2), written so that it can't overflow:
  // (n + 1) / 2 wraps to zero at n == UINT64_MAX, and the first
  // iteration then divides by it. Every smaller n gets the same seed,
  // so no other input's result moves.
  uint64_t x = n, y = n / 2 + (n & 1);
  while (y < x)
  {
    x = y;
    y = (x + n / x) / 2; // x >= isqrt(n) here, so n / x <= x: no overflow
  }
  return x;
}

// Heuristic preimage of `out` under one step. Used only to generate
// sample seeds -- witnesses are validated forward -- so it may be wrong,
// just not useless. NULL when no sensible backward map exists.
CBV hintBackStep(const GroundStep& step, const CBV out)
{
  const unsigned w = step.inWidth;
  const unsigned W = step.outWidth;

  if (step.samePathAllOperands)
  {
    if (step.kind == BVPLUS) // x + x: halve
    {
      CBV r = clone(out);
      CONSTANTBV::BitVector_Move_Right(r, 1);
      return r;
    }
    if (step.kind == BVMULT && W <= 64) // x * x: integer square root
      return cbvFromU64(W, isqrt64(low64(out)));
    return NULL;
  }

  switch (step.kind)
  {
    case BVPLUS:
      return op2(BVSUB, out, step.constants[0].GetBVConst(), W);
    case BVSUB:
      if (step.pathIndex == 0)
        return op2(BVPLUS, out, step.constants[0].GetBVConst(), W);
      return op2(BVSUB, step.constants[0].GetBVConst(), out, W);
    case BVUMINUS:
      return op1(BVUMINUS, out, W);
    case BVNOT:
      return op1(BVNOT, out, W);
    case BVXOR:
      return op2(BVXOR, out, step.constants[0].GetBVConst(), W);
    case BVDIV:
    {
      if (step.pathIndex != 0)
        return NULL;
      const CBV c = step.constants[0].GetBVConst();
      return isZero(c) ? NULL : op2(BVMULT, out, c, W);
    }
    case BVMOD:
    {
      if (step.pathIndex != 0)
        return NULL;
      const CBV c = step.constants[0].GetBVConst();
      return isZero(c) ? clone(out) : op2(BVMOD, out, c, W);
    }
    case BVRIGHTSHIFT:
    case BVSRSHIFT:
      if (step.pathIndex != 0)
        return NULL;
      return op2(BVLEFTSHIFT, out, step.constants[0].GetBVConst(), W);
    case BVLEFTSHIFT:
      if (step.pathIndex != 0)
        return NULL;
      return op2(BVRIGHTSHIFT, out, step.constants[0].GetBVConst(), W);
    case BVZX:
    case BVSX:
      return truncate(out, w);
    case BVEXTRACT:
    {
      const unsigned j = step.constants[1].GetUnsignedConst();
      CBV t = widen(out, w);
      if (j == 0)
        return t;
      CBV jc = cbvFromU64(w, j);
      CBV r = op2(BVLEFTSHIFT, t, jc, w);
      destroy(t);
      destroy(jc);
      return r;
    }
    case BVCONCAT:
    {
      if (step.pathIndex == 1) // c ++ x
        return truncate(out, w);
      // x ++ c: drop the constant's low bits.
      const unsigned cw = step.constants[0].GetValueWidth();
      CBV sc = cbvFromU64(W, cw);
      CBV t = op2(BVRIGHTSHIFT, out, sc, W);
      destroy(sc);
      CBV r = truncate(t, w);
      destroy(t);
      return r;
    }
    case BVAND:
      return op2(BVAND, out, step.constants[0].GetBVConst(), W);
    case BVMULT:
    {
      // Solve c*x == out (mod 2^w) exactly: with c = 2^s * o (o odd),
      // solutions exist iff 2^s divides out, and then
      // x = (out >> s) * inverse(o). The inverse comes from Newton
      // iteration (i' = i*(2 - o*i)), which doubles correct low bits
      // each round starting from i = o (correct mod 8 for odd o).
      const CBV c = step.constants[0].GetBVConst();
      if (isZero(c))
        return NULL;
      const unsigned s = (unsigned)CONSTANTBV::Set_Min(c);
      if (s > 0)
      {
        CBV lowMask = mkLowMask(s, W);
        CBV masked = op2(BVAND, out, lowMask, W);
        const bool divides = isZero(masked);
        destroy(lowMask);
        destroy(masked);
        if (!divides) // no exact preimage; fall back to the quotient
          return op2(BVDIV, out, c, W);
      }
      CBV sc = cbvFromU64(W, s);
      CBV odd = op2(BVRIGHTSHIFT, c, sc, W);
      CBV shifted = op2(BVRIGHTSHIFT, out, sc, W);
      destroy(sc);
      CBV inv = clone(odd);
      CBV two = cbvFromU64(W, 2);
      for (unsigned bits = 3; bits < W; bits *= 2)
      {
        CBV oi = op2(BVMULT, odd, inv, W);
        CBV corr = op2(BVSUB, two, oi, W);
        destroy(oi);
        CBV next = op2(BVMULT, inv, corr, W);
        destroy(corr);
        destroy(inv);
        inv = next;
      }
      destroy(two);
      destroy(odd);
      CBV r = op2(BVMULT, shifted, inv, W);
      destroy(shifted);
      destroy(inv);
      return r;
    }
    case SBVDIV:
    {
      const CBV c = step.constants[0].GetBVConst();
      if (step.pathIndex != 0 || isZero(c))
        return NULL;
      return op2(BVMULT, out, c, W); // signed multiply == unsigned mod 2^w
    }
    case SBVREM:
    case SBVMOD:
      return step.pathIndex == 0 ? clone(out) : NULL;
    default:
      return NULL; // BVOR, variable-position divides
  }
}
}

void AchievableImage::addHintChain(const std::vector<GroundStep>& steps,
                                   const ASTNode& k)
{
  assert(k.isConstant());
  CBV h = clone(k.GetBVConst());
  hints.push_back(clone(h));
  for (size_t i = steps.size(); i-- > 0;)
  {
    CBV next = hintBackStep(steps[i], h);
    destroy(h);
    if (next == NULL)
      return;
    h = next;
    hints.push_back(clone(h));
  }
  destroy(h);
}

bool AchievableImage::handledKind(Kind k)
{
  switch (k)
  {
    case BVPLUS:
    case BVSUB:
    case BVUMINUS:
    case BVNOT:
    case BVXOR:
    case BVMULT:
    case BVDIV:
    case BVMOD:
    case SBVDIV:
    case SBVREM:
    case SBVMOD:
    case BVLEFTSHIFT:
    case BVRIGHTSHIFT:
    case BVSRSHIFT:
    case BVZX:
    case BVSX:
    case BVEXTRACT:
    case BVCONCAT:
    case BVAND:
    case BVOR:
      return true;
    default:
      return false;
  }
}

bool AchievableImage::predicateKind(Kind k)
{
  switch (k)
  {
    case EQ:
    case BVGT:
    case BVGE:
    case BVLT:
    case BVLE:
    case BVSGT:
    case BVSGE:
    case BVSLT:
    case BVSLE:
      return true;
    default:
      return false;
  }
}

void AchievableImage::setExact(CBV newLo, CBV newHi, unsigned newWidth)
{
  assert(ucmp(newLo, newHi) <= 0);
  // The old bounds move into exactBounds; they are the input interval
  // the just-applied step needs when a value is inverted back through it.
  exactBounds.push_back(std::make_pair(lo, hi));
  lo = newLo;
  hi = newHi;
  curWidth = newWidth;
}

bool AchievableImage::isFull() const
{
  return rep == Rep::Exact && isZero(lo) && CONSTANTBV::BitVector_is_full(hi);
}

bool AchievableImage::apply(const GroundStep& step)
{
  if (!handledKind(step.kind))
    return false;
  assert(step.inWidth == curWidth);

  allSteps.push_back(step);

  if (rep == Rep::Samples)
  {
    applyToSamples(step);
    return true;
  }

  if (applyExact(step))
    return true;

  degradeToSamples(step);
  return true;
}

// Flow the exact interval [lo, hi] through `step` where possible.
// Returns false when the result isn't a contiguous unsigned interval
// (or proving so isn't worth the code) -- the caller degrades to
// samples, which is always available. Everything is computed with the
// solver's own constant evaluator so the transfer can't disagree with
// the bit-blasted semantics.
bool AchievableImage::applyExact(const GroundStep& step)
{
  const unsigned w = curWidth;
  const unsigned W = step.outWidth;

  // Both operands are the path (x*x, x+x): the images are scattered
  // (squares) or strided (doubling) -- always go through samples.
  if (step.samePathAllOperands)
    return false;

  switch (step.kind)
  {
    case BVPLUS:
    {
      const CBV c = step.constants[0].GetBVConst();
      CBV nl = op2(BVPLUS, lo, c, w);
      CBV nh = op2(BVPLUS, hi, c, w);
      // An endpoint wrapped iff adding made it smaller. Exact when both
      // or neither wrapped: the interval stays contiguous.
      const bool wrapL = ucmp(nl, lo) < 0;
      const bool wrapH = ucmp(nh, hi) < 0;
      if (wrapL != wrapH)
      {
        destroy(nl);
        destroy(nh);
        return false;
      }
      setExact(nl, nh, W);
      return true;
    }

    case BVSUB:
    {
      const CBV c = step.constants[0].GetBVConst();
      CBV nl, nh;
      bool borrowL, borrowH;
      if (step.pathIndex == 0) // x - c
      {
        nl = op2(BVSUB, lo, c, w);
        nh = op2(BVSUB, hi, c, w);
        borrowL = ucmp(lo, c) < 0;
        borrowH = ucmp(hi, c) < 0;
      }
      else // c - x: reverses the interval
      {
        nl = op2(BVSUB, c, hi, w);
        nh = op2(BVSUB, c, lo, w);
        borrowL = ucmp(c, hi) < 0;
        borrowH = ucmp(c, lo) < 0;
      }
      if (borrowL != borrowH)
      {
        destroy(nl);
        destroy(nh);
        return false;
      }
      setExact(nl, nh, W);
      return true;
    }

    case BVUMINUS:
    {
      if (isZero(hi)) // [0,0]
      {
        setExact(clone(lo), clone(hi), W);
        return true;
      }
      if (!isZero(lo)) // 0 outside; negation reverses [lo,hi] within [1,M]
      {
        CBV nl = op1(BVUMINUS, hi, w);
        CBV nh = op1(BVUMINUS, lo, w);
        setExact(nl, nh, W);
        return true;
      }
      return false; // {0} u [-hi, M]: not contiguous
    }

    case BVNOT:
    {
      CBV nl = op1(BVNOT, hi, w);
      CBV nh = op1(BVNOT, lo, w);
      setExact(nl, nh, W);
      return true;
    }

    case BVXOR:
    {
      // A bijection, so the full domain maps to itself. A proper
      // sub-interval is scattered.
      if (!isFull())
        return false;
      setExact(clone(lo), clone(hi), W);
      return true;
    }

    case BVMULT:
      // An odd-constant multiply of the full domain is a bijection, but
      // RemoveUnconstrained's own BVMULT rule consumes that case before
      // the climb starts, so it would be dead code here. Everything
      // else is a strided set.
      return false;

    case BVDIV:
    {
      if (step.pathIndex != 0)
        return false; // c / x
      const CBV c = step.constants[0].GetBVConst();
      if (isZero(c))
      {
        // x / 0 is all-ones for every x.
        CBV ones = allOnes(w);
        setExact(clone(ones), ones, W);
        return true;
      }
      // Every quotient between the endpoints' quotients is reached.
      CBV nl = op2(BVDIV, lo, c, w);
      CBV nh = op2(BVDIV, hi, c, w);
      setExact(nl, nh, W);
      return true;
    }

    case BVMOD:
    {
      if (step.pathIndex != 0)
        return false; // c mod x
      const CBV c = step.constants[0].GetBVConst();
      if (isZero(c) || ucmp(hi, c) < 0)
      {
        // x mod 0 == x, and below the divisor the remainder is x itself.
        setExact(clone(lo), clone(hi), W);
        return true;
      }
      // With at least c consecutive inputs every remainder is reached.
      CBV one = mkOne(w);
      CBV cm1 = op2(BVSUB, c, one, w);
      CBV d = op2(BVSUB, hi, lo, w);
      const bool fullCycle = ucmp(d, cm1) >= 0;
      destroy(one);
      destroy(d);
      if (!fullCycle)
      {
        destroy(cm1);
        return false;
      }
      setExact(mkZero(w), cm1, W);
      return true;
    }

    case BVRIGHTSHIFT:
    {
      if (step.pathIndex != 0)
        return false; // c >> x
      // Monotone, and every quotient by 2^k is reached (the evaluator
      // handles amounts >= width, giving [0,0]).
      const CBV c = step.constants[0].GetBVConst();
      CBV nl = op2(BVRIGHTSHIFT, lo, c, w);
      CBV nh = op2(BVRIGHTSHIFT, hi, c, w);
      setExact(nl, nh, W);
      return true;
    }

    case BVZX:
    {
      CBV nl = op1(BVZX, lo, W);
      CBV nh = op1(BVZX, hi, W);
      setExact(nl, nh, W);
      return true;
    }

    case BVSX:
    {
      // Exact when the interval doesn't cross the sign boundary: both
      // halves extend order-preservingly. Crossing gives two bands.
      const bool negLo = CONSTANTBV::BitVector_bit_test(lo, w - 1);
      const bool negHi = CONSTANTBV::BitVector_bit_test(hi, w - 1);
      if (negLo != negHi)
        return false;
      CBV nl = op1(BVSX, lo, W);
      CBV nh = op1(BVSX, hi, W);
      setExact(nl, nh, W);
      return true;
    }

    case BVEXTRACT:
    {
      // extract[i:j] is a right shift by j followed by truncation to
      // i-j+1 bits; the truncation behaves like mod 2^(i-j+1).
      const unsigned j = step.constants[1].GetUnsignedConst();
      const unsigned len = W;
      CBV jc = cbvFromU64(w, j);
      CBV ta = op2(BVRIGHTSHIFT, lo, jc, w);
      CBV tb = op2(BVRIGHTSHIFT, hi, jc, w);
      destroy(jc);
      CBV mask = mkLowMask(len, w); // 2^len - 1
      bool exact = false;
      CBV nl = NULL, nh = NULL;
      if (ucmp(tb, mask) <= 0) // truncation is the identity
      {
        nl = truncate(ta, len);
        nh = truncate(tb, len);
        exact = true;
      }
      else
      {
        CBV d = op2(BVSUB, tb, ta, w);
        if (ucmp(d, mask) >= 0) // a full cycle: every value reached
        {
          nl = mkZero(len);
          nh = allOnes(len);
          exact = true;
        }
        destroy(d);
      }
      destroy(ta);
      destroy(tb);
      destroy(mask);
      if (!exact)
        return false;
      setExact(nl, nh, W);
      return true;
    }

    case BVCONCAT:
    {
      if (step.pathIndex != 1)
        return false; // x ++ c: a strided set
      // c ++ x: fixed high bits over a contiguous low part.
      const CBV c = step.constants[0].GetBVConst();
      CBV nl = op2(BVCONCAT, c, lo, W);
      CBV nh = op2(BVCONCAT, c, hi, W);
      setExact(nl, nh, W);
      return true;
    }

    case BVAND:
    {
      // x & c where c+1 is a power of two (c a low mask, including
      // all-ones) behaves as x mod 2^k.
      const CBV c = step.constants[0].GetBVConst();
      CBV one = mkOne(w);
      CBV cp1 = op2(BVPLUS, c, one, w);
      CBV inter = op2(BVAND, c, cp1, w);
      const bool lowMask = isZero(inter);
      destroy(one);
      destroy(cp1);
      destroy(inter);
      if (!lowMask)
        return false;
      if (ucmp(hi, c) <= 0) // all inside the mask: identity
      {
        setExact(clone(lo), clone(hi), W);
        return true;
      }
      CBV d = op2(BVSUB, hi, lo, w);
      const bool fullCycle = ucmp(d, c) >= 0; // d >= 2^k - 1
      destroy(d);
      if (!fullCycle)
        return false;
      setExact(mkZero(w), clone(c), W);
      return true;
    }

    default:
      // BVLEFTSHIFT / BVSRSHIFT (strided or sign-banded), BVOR, the
      // signed divides, and anything with the path in an inexact
      // position all go through samples.
      return false;
  }
}

void AchievableImage::addSample(CBV witness, CBV value)
{
  for (const Sample& s : samples)
  {
    if (CONSTANTBV::BitVector_equal(s.value, value))
    {
      destroy(witness);
      destroy(value);
      return;
    }
  }
  if (samples.size() >= MAX_SAMPLES)
  {
    destroy(witness);
    destroy(value);
    return;
  }
  samples.push_back({witness, value});
}

void AchievableImage::applyToSamples(const GroundStep& step)
{
  std::vector<Sample> old;
  old.swap(samples);
  for (Sample& s : old)
  {
    CBV nv = evalStep(step, s.value);
    destroy(s.value);
    addSample(s.witness, nv); // dedupes on value, freeing losers
  }
  curWidth = step.outWidth;
}

// The image is exactly [lo, hi] but `degradingStep` would scatter it.
// Pick a deterministic set of members, invert each back to an x
// witness while the whole prefix is still exact, then push them
// through the step pointwise.
void AchievableImage::degradeToSamples(const GroundStep& degradingStep)
{
  const unsigned w = curWidth;
  std::vector<CBV> seeds; // owned members of [lo, hi]

  // When the whole interval fits in the sample budget, enumerate it --
  // the samples are then the COMPLETE image of the chain, not a
  // heuristic under-approximation.
  {
    CBV d = op2(BVSUB, hi, lo, w);
    // d fits a machine word iff its highest set bit is low enough;
    // Set_Max is negative when d is zero.
    const bool enumerable = CONSTANTBV::Set_Max(d) < 16 &&
                            *(unsigned*)d <= MAX_SAMPLES - 1;
    destroy(d);
    if (enumerable)
    {
      CBV v = clone(lo);
      while (true)
      {
        seeds.push_back(clone(v));
        if (ucmp(v, hi) == 0)
          break;
        CONSTANTBV::BitVector_increment(v);
      }
      destroy(v);
      for (CBV s : seeds)
      {
        CBV witness = invertPrefix(clone(s));
        CBV value = evalStep(degradingStep, s);
        destroy(s);
        addSample(witness, value);
      }
      seeds.clear();
      rep = Rep::Samples;
      destroy(lo);
      destroy(hi);
      lo = hi = NULL;
      curWidth = degradingStep.outWidth;
      return;
    }
  }

  auto addSeed = [&](CBV v) {
    if (seeds.size() >= MAX_SAMPLES || ucmp(v, lo) < 0 || ucmp(v, hi) > 0)
    {
      destroy(v);
      return;
    }
    for (const CBV s : seeds)
      if (CONSTANTBV::BitVector_equal(s, v))
      {
        destroy(v);
        return;
      }
    seeds.push_back(v);
  };

  // Seed order is a priority order (addSeed stops at MAX_SAMPLES): the
  // endpoints always survive; then hints already at this level's width
  // -- with a back-propagated chain these are the closest thing to a
  // known-good witness; then the standard members; width-adapted
  // foreign hints take whatever room is left.
  addSeed(clone(lo));
  addSeed(clone(hi));

  CBV one = mkOne(w);
  for (const CBV h : hints)
  {
    if (bits_(h) != w)
      continue;
    addSeed(clone(h));
    addSeed(op2(BVPLUS, h, one, w));
    addSeed(op2(BVSUB, h, one, w));
  }

  addSeed(op2(BVPLUS, lo, one, w));
  addSeed(op2(BVSUB, hi, one, w));
  { // midpoint
    CBV d = op2(BVSUB, hi, lo, w);
    CONSTANTBV::BitVector_Move_Right(d, 1);
    CBV mid = op2(BVPLUS, lo, d, w);
    destroy(d);
    addSeed(mid);
  }
  addSeed(mkZero(w));
  addSeed(mkOne(w));
  addSeed(allOnes(w));
  { // signed extremes
    CBV sMax = allOnes(w);
    CONSTANTBV::BitVector_Bit_Off(sMax, w - 1);
    addSeed(sMax);
    CBV sMin = mkZero(w);
    CONSTANTBV::BitVector_Bit_On(sMin, w - 1);
    addSeed(sMin);
  }
  // The degrading step's own constants and their neighbours: for a
  // masking or multiplying step these are the values most likely to
  // separate the predicate's polarities (e.g. x & 5 == 4).
  for (const ASTNode& cn : degradingStep.constants)
  {
    if (cn.GetValueWidth() != w)
      continue;
    const CBV c = cn.GetBVConst();
    addSeed(clone(c));
    addSeed(op2(BVPLUS, c, one, w));
    addSeed(op2(BVSUB, c, one, w));
  }

  // Foreign-width hints, width-adapted, in whatever room is left.
  for (const CBV h : hints)
  {
    if (bits_(h) == w)
      continue;
    CBV adapted = (bits_(h) > w) ? truncate(h, w) : widen(h, w);
    addSeed(clone(adapted));
    addSeed(op2(BVPLUS, adapted, one, w));
    addSeed(op2(BVSUB, adapted, one, w));
    destroy(adapted);
  }
  destroy(one);

  for (CBV s : seeds)
  {
    CBV witness = invertPrefix(clone(s));
    CBV value = evalStep(degradingStep, s);
    destroy(s);
    addSample(witness, value);
  }
  seeds.clear();

  rep = Rep::Samples;
  destroy(lo);
  destroy(hi);
  lo = hi = NULL;
  curWidth = degradingStep.outWidth;
}

// Walk a value at the top of the exact prefix back down to an x value
// that produces it. Only ever called with members of the recorded
// exact images, where each step's inverse is a closed form.
CBV AchievableImage::invertPrefix(CBV value)
{
  for (size_t i = exactBounds.size(); i-- > 0;)
  {
    CBV next = invertStep(allSteps[i], exactBounds[i].first,
                          exactBounds[i].second, value);
    destroy(value);
    value = next;
  }
  assert(bits_(value) == varWidth);
  return value;
}

CBV AchievableImage::invertStep(const GroundStep& step, const CBV inLo,
                                const CBV inHi, const CBV value)
{
  const unsigned w = step.inWidth;

  switch (step.kind)
  {
    case BVPLUS:
      return op2(BVSUB, value, step.constants[0].GetBVConst(), w);

    case BVSUB:
      if (step.pathIndex == 0) // x - c
        return op2(BVPLUS, value, step.constants[0].GetBVConst(), w);
      return op2(BVSUB, step.constants[0].GetBVConst(), value, w); // c - x

    case BVUMINUS:
      return op1(BVUMINUS, value, w);

    case BVNOT:
      return op1(BVNOT, value, w);

    case BVXOR: // only exact over the full domain: xor is self-inverse
      return op2(BVXOR, value, step.constants[0].GetBVConst(), w);

    case BVDIV:
    {
      const CBV c = step.constants[0].GetBVConst();
      if (isZero(c))
        return clone(inLo); // every input gives all-ones
      // The smallest input with this quotient, clamped into the interval.
      return umaxTake(inLo, op2(BVMULT, value, c, w));
    }

    case BVMOD:
    {
      const CBV c = step.constants[0].GetBVConst();
      if (isZero(c) || ucmp(inHi, c) < 0)
        return clone(value); // was the identity
      // Full cycle: the unique u in [inLo, inLo + c - 1] with
      // u ≡ value (mod c).
      CBV r = op2(BVMOD, inLo, c, w);
      CBV d;
      if (ucmp(value, r) >= 0)
        d = op2(BVSUB, value, r, w);
      else
      {
        CBV t = op2(BVSUB, c, r, w);
        d = op2(BVPLUS, t, value, w);
        destroy(t);
      }
      destroy(r);
      CBV u = op2(BVPLUS, inLo, d, w);
      destroy(d);
      return u;
    }

    case BVRIGHTSHIFT:
    {
      // Smallest input with this quotient (shifts past the width give
      // the [0,0] image, where value<<k is 0 and inLo wins the max).
      const CBV c = step.constants[0].GetBVConst();
      return umaxTake(inLo, op2(BVLEFTSHIFT, value, c, w));
    }

    case BVZX:
    case BVSX:
      return truncate(value, w);

    case BVEXTRACT:
    {
      const unsigned j = step.constants[1].GetUnsignedConst();
      const unsigned len = step.outWidth;
      CBV jc = cbvFromU64(w, j);
      CBV ta = op2(BVRIGHTSHIFT, inLo, jc, w);
      CBV tb = op2(BVRIGHTSHIFT, inHi, jc, w);
      CBV mask = mkLowMask(len, w);
      CBV ut; // the shifted value to hit, at width w
      if (ucmp(tb, mask) <= 0) // truncation was the identity
        ut = widen(value, w);
      else
      {
        // Full cycle mod 2^len: width-len subtraction wraps at exactly
        // the modulus.
        CBV r = truncate(ta, len);
        CBV d = op2(BVSUB, value, r, len);
        destroy(r);
        CBV dw = widen(d, w);
        destroy(d);
        ut = op2(BVPLUS, ta, dw, w);
        destroy(dw);
      }
      CBV u = umaxTake(inLo, op2(BVLEFTSHIFT, ut, jc, w));
      destroy(ut);
      destroy(ta);
      destroy(tb);
      destroy(mask);
      destroy(jc);
      return u;
    }

    case BVCONCAT: // c ++ x
      assert(step.pathIndex == 1);
      return truncate(value, w);

    case BVAND:
    {
      // Low mask: as mod 2^k with modulus c+1.
      const CBV c = step.constants[0].GetBVConst();
      if (ucmp(inHi, c) <= 0)
        return clone(value); // was the identity
      CBV r = op2(BVAND, inLo, c, w);
      CBV d;
      if (ucmp(value, r) >= 0)
        d = op2(BVSUB, value, r, w);
      else
      {
        // (c+1 - r) + value == (c - r) + value + 1, all below 2^k.
        CBV t = op2(BVSUB, c, r, w);
        CBV t2 = op2(BVPLUS, t, value, w);
        destroy(t);
        CBV one = mkOne(w);
        d = op2(BVPLUS, t2, one, w);
        destroy(t2);
        destroy(one);
      }
      destroy(r);
      CBV u = op2(BVPLUS, inLo, d, w);
      destroy(d);
      return u;
    }

    default:
      assert(false && "inverting a step that never stays exact");
      return clone(inLo);
  }
}

CBV AchievableImage::evalStep(const GroundStep& step, const CBV in)
{
  std::vector<CBV> args;
  if (step.samePathAllOperands)
  {
    assert(step.constants.empty());
    args.push_back(in);
    args.push_back(in);
  }
  else if (step.kind == BVSX || step.kind == BVZX)
  {
    // The evaluator takes the new width from outWidth.
    args.push_back(in);
  }
  else
  {
    const size_t arity = step.constants.size() + 1;
    size_t ci = 0;
    for (size_t i = 0; i < arity; i++)
    {
      if (i == step.pathIndex)
        args.push_back(in);
      else
        args.push_back(step.constants[ci++].GetBVConst());
    }
  }
  return NonMemberBVConstEvaluator(step.kind, args, step.outWidth);
}

bool AchievableImage::evalPredicate(Kind pred, bool pathIsFirstOperand,
                                    const CBV member, const CBV k)
{
  if (pathIsFirstOperand)
    return NonMemberBVConstPredicateEvaluator(pred, member, k);
  return NonMemberBVConstPredicateEvaluator(pred, k, member);
}

bool AchievableImage::validate(const CBV xWitness, Kind pred,
                               bool pathIsFirstOperand, const CBV k,
                               bool expected)
{
  CBV v = clone(xWitness);
  for (const GroundStep& s : allSteps)
  {
    CBV nv = evalStep(s, v);
    destroy(v);
    v = nv;
  }
  const bool result = evalPredicate(pred, pathIsFirstOperand, v, k);
  destroy(v);
  return result == expected;
}

AchievableImage::Decision AchievableImage::decide(Kind pred,
                                                  bool pathIsFirstOperand,
                                                  const ASTNode& kNode)
{
  Decision decision;
  if (!predicateKind(pred))
    return decision;
  assert(kNode.isConstant() && kNode.GetValueWidth() == curWidth);
  const CBV k = kNode.GetBVConst();

  CBV xTrue = NULL, xFalse = NULL;

  if (rep == Rep::Exact)
  {
    CBV tMember = NULL, fMember = NULL; // owned members of [lo, hi]
    if (pred == EQ)
    {
      const bool trueOK = ucmp(lo, k) <= 0 && ucmp(k, hi) <= 0;
      const bool falseOK = ucmp(lo, hi) != 0;
      if (!trueOK || !falseOK)
        return decision;
      tMember = clone(k);
      fMember = (ucmp(k, lo) == 0) ? clone(hi) : clone(lo);
    }
    else
    {
      const bool isSigned =
          (pred == BVSGT || pred == BVSGE || pred == BVSLT || pred == BVSLE);
      // The smallest and largest members in the comparison's order.
      // Unsigned: the endpoints. Signed: when the interval crosses the
      // sign boundary, 2^(w-1)-1 and 2^(w-1) are both members and are
      // the signed extremes; otherwise both endpoints sit on one side,
      // where signed and unsigned order agree.
      CBV mn, mx;
      const bool crossing =
          !CONSTANTBV::BitVector_bit_test(lo, curWidth - 1) &&
          CONSTANTBV::BitVector_bit_test(hi, curWidth - 1);
      if (isSigned && crossing)
      {
        mx = allOnes(curWidth);
        CONSTANTBV::BitVector_Bit_Off(mx, curWidth - 1);
        mn = mkZero(curWidth);
        CONSTANTBV::BitVector_Bit_On(mn, curWidth - 1);
      }
      else
      {
        mn = clone(lo);
        mx = clone(hi);
      }
      // All eight comparisons are monotone per operand, so the best
      // member for each polarity is an extreme.
      const bool greater =
          (pred == BVGT || pred == BVGE || pred == BVSGT || pred == BVSGE);
      const bool trueAtMax = (greater == pathIsFirstOperand);
      tMember = trueAtMax ? mx : mn;
      fMember = trueAtMax ? mn : mx;
      const bool trueOK = evalPredicate(pred, pathIsFirstOperand, tMember, k);
      const bool falseOK =
          !evalPredicate(pred, pathIsFirstOperand, fMember, k);
      if (!trueOK || !falseOK)
      {
        destroy(mn);
        destroy(mx);
        return decision;
      }
    }
    xTrue = invertPrefix(tMember);
    xFalse = invertPrefix(fMember);
  }
  else
  {
    for (const Sample& s : samples)
    {
      const bool t = evalPredicate(pred, pathIsFirstOperand, s.value, k);
      if (t && xTrue == NULL)
        xTrue = clone(s.witness);
      if (!t && xFalse == NULL)
        xFalse = clone(s.witness);
    }
    if (xTrue == NULL || xFalse == NULL)
    {
      if (xTrue != NULL)
        destroy(xTrue);
      if (xFalse != NULL)
        destroy(xFalse);
      return decision;
    }
  }

  // The image only searches; this check is what makes the rewrite
  // sound. A failure here is a transfer/inversion bug.
  const bool okTrue = validate(xTrue, pred, pathIsFirstOperand, k, true);
  const bool okFalse = validate(xFalse, pred, pathIsFirstOperand, k, false);
  assert(okTrue && okFalse);
  if (!okTrue || !okFalse)
  {
    destroy(xTrue);
    destroy(xFalse);
    return decision;
  }

  decision.collapse = true;
  decision.witnessTrue = bm.CreateBVConst(xTrue, varWidth);   // takes ownership
  decision.witnessFalse = bm.CreateBVConst(xFalse, varWidth); // takes ownership
  return decision;
}
}
