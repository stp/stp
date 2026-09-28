/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: Aug, 2026
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

#include "stp/ToSat/BVLemmaCatalogue.h"

#include "stp/AST/ASTKind.h"
#include "stp/STPManager/STPManager.h"

#include <cassert>
#include <limits>

namespace stp
{

// ---------------------------------------------------------------------------
// The facts, as values.
//
// Written over unsigned arithmetic on the bit vectors rather than over the
// circuits below, so that the test which checks the two against each other
// is checking two things and not one.
// ---------------------------------------------------------------------------

namespace
{

bool allZero(const std::vector<bool>& v)
{
  for (bool b : v)
    if (b)
      return false;
  return true;
}

bool allOnes(const std::vector<bool>& v)
{
  for (bool b : v)
    if (!b)
      return false;
  return true;
}

bool ule(const std::vector<bool>& a, const std::vector<bool>& b)
{
  for (int i = (int)a.size() - 1; i >= 0; --i)
    if (a[i] != b[i])
      return b[i];
  return true;
}

std::vector<bool> notOf(const std::vector<bool>& v)
{
  std::vector<bool> r(v.size());
  for (unsigned i = 0; i < v.size(); ++i)
    r[i] = !v[i];
  return r;
}

// Two's complement negation: the bitwise complement plus one.
std::vector<bool> negOf(const std::vector<bool>& v)
{
  std::vector<bool> r = notOf(v);
  bool carry = true;
  for (unsigned i = 0; i < r.size() && carry; ++i)
  {
    const bool sum = r[i] ^ carry;
    carry = r[i] && carry;
    r[i] = sum;
  }
  return r;
}

std::vector<bool> decOf(const std::vector<bool>& v)
{
  // v - 1, which is v + ~0.
  std::vector<bool> r(v.size());
  bool borrow = true;
  for (unsigned i = 0; i < v.size(); ++i)
  {
    r[i] = v[i] ^ borrow;
    borrow = !v[i] && borrow;
  }
  return r;
}

std::vector<bool> andOf(const std::vector<bool>& a, const std::vector<bool>& b)
{
  std::vector<bool> r(a.size());
  for (unsigned i = 0; i < a.size(); ++i)
    r[i] = a[i] && b[i];
  return r;
}

std::vector<bool> orOf(const std::vector<bool>& a, const std::vector<bool>& b)
{
  std::vector<bool> r(a.size());
  for (unsigned i = 0; i < a.size(); ++i)
    r[i] = a[i] || b[i];
  return r;
}

std::vector<bool> xorOf(const std::vector<bool>& a, const std::vector<bool>& b)
{
  std::vector<bool> r(a.size());
  for (unsigned i = 0; i < a.size(); ++i)
    r[i] = a[i] != b[i];
  return r;
}

std::vector<bool> addOf(const std::vector<bool>& a, const std::vector<bool>& b)
{
  std::vector<bool> r(a.size());
  bool carry = false;
  for (unsigned i = 0; i < a.size(); ++i)
  {
    r[i] = (a[i] != b[i]) != carry;
    carry = (a[i] && b[i]) || (a[i] && carry) || (b[i] && carry);
  }
  return r;
}

std::vector<bool> subOf(const std::vector<bool>& a, const std::vector<bool>& b)
{
  return addOf(a, negOf(b));
}

// The unsigned value of a shift amount, saturated at the value width. Once
// the represented amount reaches that width both SMT-LIB logical shifts are
// all zero, so there is no reason to risk overflowing a host integer while
// reading the remaining high bits.
unsigned saturatedShiftAmount(const std::vector<bool>& amount, unsigned width)
{
  unsigned by = 0;
  for (unsigned i = 0; i < amount.size(); ++i)
    if (amount[i])
    {
      if (i >= std::numeric_limits<unsigned>::digits)
        return width;
      const unsigned add = 1u << i;
      if (add >= width || by >= width - add)
        return width;
      by += add;
    }
  return by;
}

// Logical shifts by the value `amount` holds. A shift at or past the width
// clears the vector, matching both SMT-LIB operations and the barrel shifters
// the circuit uses.
std::vector<bool> shrOf(const std::vector<bool>& v,
                        const std::vector<bool>& amount)
{
  const unsigned W = (unsigned)v.size();
  const unsigned by = saturatedShiftAmount(amount, W);

  std::vector<bool> r(W, false);
  for (unsigned i = 0; i + by < W; ++i)
    r[i] = v[i + by];
  return r;
}

std::vector<bool> shlOf(const std::vector<bool>& v,
                        const std::vector<bool>& amount)
{
  const unsigned W = (unsigned)v.size();
  const unsigned by = saturatedShiftAmount(amount, W);

  std::vector<bool> r(W, false);
  for (unsigned i = by; i < W; ++i)
    r[i] = v[i - by];
  return r;
}

// `s <=u x <u 2s`, with doubling interpreted in the integers. If the top
// bit of s is set, 2s lies beyond the bit-vector range and the upper half of
// the premise is automatically true. The premise also excludes s = 0.
bool fitsExactlyOnce(const std::vector<bool>& x,
                     const std::vector<bool>& s)
{
  const unsigned W = (unsigned)x.size();
  std::vector<bool> one(W, false);
  one[0] = true;
  return ule(s, x) && (s[W - 1] || !ule(shlOf(s, one), x));
}

} // namespace

bool divLemmaHolds(DivLemma lemma, const std::vector<bool>& x,
                   const std::vector<bool>& s, const std::vector<bool>& t)
{
  assert(x.size() == s.size());
  assert(x.size() == t.size());

  const unsigned W = (unsigned)x.size();
  const std::vector<bool> zero(W, false);
  std::vector<bool> one(W, false);
  one[0] = true;

  switch (lemma)
  {
    case DivLemma::DividendZero:
      return !(allZero(x) && !allZero(s)) || allZero(t);

    case DivLemma::DivisorEqualsDividend:
      return !(s == x && !allZero(s)) || t == one;

    case DivLemma::DivisorAllOnes:
      return !(allOnes(s) && !allOnes(x)) || allZero(t);

    case DivLemma::QuotientBelowNegatedDivisor:
    {
      std::vector<bool> sOr1 = s;
      sOr1[0] = true;
      return ule(t, negOf(sOr1));
    }

    case DivLemma::DividendAboveNegatedAnd:
      return ule(negOf(andOf(negOf(s), negOf(t))), x);

    case DivLemma::DivisorAboveShiftedDividend:
      return ule(shrOf(x, t), s);

    case DivLemma::DivisorLessOneAboveShiftedDividend:
      return ule(shrOf(x, t), decOf(s));

    case DivLemma::DividendAboveShiftedDoubleQuotient:
      // x >=u ((t << 1) >> (t << s))
      return ule(shrOf(shlOf(t, one), shlOf(t, s)), x);

    case DivLemma::QuotientNotNegatedAnd:
      // t != -(s & ~x)
      return t != negOf(andOf(s, notOf(x)));

    case DivLemma::MaskedDividendAboveDivisorAndQuotient:
      // (x & -t) >=u (s & t)
      return ule(andOf(s, t), andOf(x, negOf(t)));

    case DivLemma::DividendAboveDoubledShiftedDivisor:
      // x >=u ((s >> (s << t)) << 1)
      return ule(shlOf(shrOf(s, shlOf(s, t)), one), x);

    case DivLemma::QuotientAboveDoubledShiftedDividend:
      // t >=u ((x >> s) << 1)
      return ule(shlOf(shrOf(x, s), one), t);

    case DivLemma::DividendAboveOrAndDoubledDivisor:
      // x >=u ((x | t) & (s << 1))
      return ule(andOf(orOf(x, t), shlOf(s, one)), x);

    case DivLemma::DividendAboveOrAndDoubledQuotient:
      // x >=u ((x | s) & (t << 1))
      return ule(andOf(orOf(x, s), shlOf(t, one)), x);

    case DivLemma::ShiftedDividendNotOr:
      // (x >> t) != (s | t)
      return shrOf(x, t) != orOf(s, t);

    case DivLemma::DividendAboveQuotientXorShifted:
      // x >=u (t xor (t >> (s >> 1)))
      return ule(xorOf(t, shrOf(t, shrOf(s, one))), x);

    case DivLemma::DividendAboveDivisorXorShifted:
      // x >=u (s xor (s >> (t >> 1)))
      return ule(xorOf(s, shrOf(s, shrOf(t, one))), x);

    case DivLemma::DividendNotTwiceQuotientPlusOr:
      // x != t + t + (x | s)
      return x != addOf(t, addOf(t, orOf(x, s)));

    case DivLemma::QuotientIsOne:
      // s <=u x <u 2s -> t = 1
      return !fitsExactlyOnce(x, s) || t == one;

    case DivLemma::DivisorOrQuotientNotMaskedDividend:
      // (s | t) != (x & ~1)
      return orOf(s, t) != andOf(x, notOf(one));

    case DivLemma::DivisorOrOneNotDividendWithoutQuotient:
      // (s | 1) != (x & ~t)
    {
      std::vector<bool> sOrOne = s;
      sOrOne[0] = true;
      return sOrOne != andOf(x, notOf(t));
    }

    case DivLemma::DivisorNotNegatedSelfShiftedByHalfQuotient:
      // s != ~(s >> (t >> 1))
      return s != notOf(shrOf(s, shrOf(t, one)));

    case DivLemma::DividendNotNegatedAndDoubledQuotient:
      // x != ~(x & (t << 1))
      return x != notOf(andOf(x, shlOf(t, one)));

    case DivLemma::QuotientAboveDoubledDividendShiftedByDivisor:
      // t >=u ((x << 1) >> s)
      return ule(shrOf(shlOf(x, one), s), t);

    case DivLemma::DividendAboveDivisorShiftedByNegatedOr:
      // x >=u (s << ~(x | t))
      return ule(shlOf(s, notOf(orOf(x, t))), x);

    case DivLemma::DividendAboveQuotientShiftedByNegatedOr:
      // x >=u (t << ~(x | s))
      return ule(shlOf(t, notOf(orOf(x, s))), x);

    case DivLemma::DividendAboveDivisorShiftedByNegatedXor:
      // x >=u (s << ~(x xor t))
      return ule(shlOf(s, notOf(xorOf(x, t))), x);

    case DivLemma::DividendAboveQuotientShiftedByNegatedXor:
      // x >=u (t << ~(x xor s))
      return ule(shlOf(t, notOf(xorOf(x, s))), x);

    case DivLemma::DividendNotQuotientPlusDivisorOrSum:
      // x != t + (s | (x + s))
      return x != addOf(t, orOf(s, addOf(x, s)));

    case DivLemma::DividendNotQuotientPlusOnePlusShiftedOne:
      // x != t + (1 + (1 << x))
      return x != addOf(t, addOf(one, shlOf(one, x)));

    case DivLemma::DivisorAboveSumShiftedByQuotient:
      // s >=u ((x + t) >> t)
      return ule(shrOf(addOf(x, t), t), s);

    case DivLemma::DivisorXorOrAboveQuotientXorOne:
      // (s xor (x | t)) >=u (t xor 1)
      return ule(xorOf(t, one), xorOf(s, orOf(x, t)));

    case DivLemma::QuotientAboveDividendShiftedByDivisorLessOne:
      // t >=u (x >> (s - 1))
      return ule(shrOf(x, decOf(s)), t);

    case DivLemma::DividendNotOneLessShiftedDividend:
      // x != 1 - (x << (x - t))
      return x != subOf(one, shlOf(x, subOf(x, t)));
  }
  return true;
}

bool remLemmaHolds(RemLemma lemma, const std::vector<bool>& x,
                   const std::vector<bool>& s, const std::vector<bool>& t)
{
  assert(x.size() == s.size());
  assert(x.size() == t.size());

  const unsigned W = (unsigned)x.size();
  const std::vector<bool> zero(W, false);
  std::vector<bool> one(W, false);
  one[0] = true;

  switch (lemma)
  {
    case RemLemma::DividendZero:
      // x = 0 -> t = 0
      return !allZero(x) || allZero(t);

    case RemLemma::DivisorEqualsDividend:
      // s = x -> t = 0
      return s != x || allZero(t);

    case RemLemma::DividendBelowDivisor:
      // x <u s -> t = x
      return ule(s, x) || t == x;

    case RemLemma::RemainderIsDifference:
      // s <=u x <u 2s -> t = x - s
      return !fitsExactlyOnce(x, s) || t == addOf(x, negOf(s));

    case RemLemma::DividendWithinDivisorOrRemainder:
      // x = x & (s | t | -s)
      return x == andOf(x, orOf(s, orOf(t, negOf(s))));

    case RemLemma::DividendAboveRemainderOrAnd:
      // x >=u (t | (x & s))
      return ule(orOf(t, andOf(x, s)), x);

    case RemLemma::RemainderOutsideOperandsNotOne:
      // 1 != (t & ~(x | s))
      return one != andOf(t, notOf(orOf(x, s)));

    case RemLemma::RemainderNotOrOfComplements:
      // t != (~x | -s)
      return t != orOf(notOf(x), negOf(s));

    case RemLemma::RemainderInOperandsAboveLowBit:
      // (t & (x | s)) >=u (t & 1)
      return ule(andOf(t, one), andOf(t, orOf(x, s)));

    case RemLemma::DividendNotOrOfNegations:
      // x != (-x | -(~t))
      return x != orOf(negOf(x), negOf(notOf(t)));

    case RemLemma::DifferenceAboveRemainder:
      // (x + -s) >=u t
      return ule(t, addOf(x, negOf(s)));

    case RemLemma::XorAboveRemainder:
      // ((-s) xor (x | s)) >=u t
      return ule(t, xorOf(negOf(s), orOf(x, s)));
  }
  return true;
}

bool mulLemmaHolds(MulLemma lemma, const std::vector<bool>& x,
                   const std::vector<bool>& s, const std::vector<bool>& t)
{
  assert(x.size() == s.size());
  assert(x.size() == t.size());

  const unsigned W = (unsigned)x.size();
  std::vector<bool> one(W, false);
  one[0] = true;

  switch (lemma)
  {
    case MulLemma::FactorUnchangedByMaskedShift:
      // s = s << (x & (1 >> t))
      return s == shlOf(s, andOf(x, shrOf(one, t)));

    case MulLemma::FactorNotNegatedProductOrLowBit:
      // s != ~(t | (1 & (x | s)))
      return s != notOf(orOf(t, andOf(one, orOf(x, s))));

    case MulLemma::FactorAndProductNotOr:
      // (x & t) != (s | ~t)
      return andOf(x, t) != orOf(s, notOf(t));

    case MulLemma::ProductNotOddFactorShiftedByShiftedProduct:
    {
      // t != ((s | 1) << (t << x))
      std::vector<bool> sOrOne = s;
      sOrOne[0] = true;
      return t != shlOf(sOrOne, shlOf(t, x));
    }

    case MulLemma::ProductAboveMaskedShiftedFactors:
      // t >=u (1 & ((x & s) >> 1))
      return ule(andOf(one, shrOf(andOf(x, s), one)), t);

    case MulLemma::FactorNotOneXorFactorShiftedByXor:
      // x != (1 xor (x << (s xor t)))
      return x != xorOf(one, shlOf(x, xorOf(s, t)));

    case MulLemma::ProductNotOneOrNegatedXor:
      // t != (1 | ~(x xor s))
      return t != orOf(one, notOf(xorOf(x, s)));

    case MulLemma::ProductNotHighOnesOrXor:
      // t != (~1 | (x xor s))
      return t != orOf(notOf(one), xorOf(x, s));

    case MulLemma::FactorNotShiftedFactorLessOne:
      // x != (x << (s + t)) - 1
      return x != subOf(shlOf(x, addOf(s, t)), one);

    case MulLemma::FactorNotOneLessShiftedFactor:
      // x != 1 - (x << (s - t))
      return x != subOf(one, shlOf(x, subOf(s, t)));

    case MulLemma::FactorNotOnePlusShiftedFactor:
      // s != 1 + (s << (t - x))
      return s != addOf(one, shlOf(s, subOf(t, x)));

    case MulLemma::FactorNotOneLessShiftedFactorReversed:
      // s != 1 - (s << (t - x))
      return s != subOf(one, shlOf(s, subOf(t, x)));

    case MulLemma::FactorNotOnePlusShiftedFactorReversed:
      // s != 1 + (s << (x - t))
      return s != addOf(one, shlOf(s, subOf(x, t)));

    case MulLemma::ProductNotOneOrSum:
      // t != (1 | (x + s))
      return t != orOf(one, addOf(x, s));

    case MulLemma::FactorNotNegatedShiftedFactor:
      // x != ~(x << (s + t))
      return x != notOf(shlOf(x, addOf(s, t)));
  }
  return true;
}

bool addLemmaHolds(AddLemma lemma, const std::vector<bool>& x,
                   const std::vector<bool>& s, const std::vector<bool>& t)
{
  assert(!x.empty());
  assert(x.size() == s.size());
  assert(x.size() == t.size());

  const unsigned W = (unsigned)x.size();
  const std::vector<bool> zero(W, false);
  const std::vector<bool> ones(W, true);
  std::vector<bool> one(W, false);
  one[0] = true;

  switch (lemma)
  {
    case AddLemma::AddZero:
      // s = 0 -> t = x
      return !allZero(s) || t == x;

    case AddLemma::AddSame:
      // x = s -> t[0] = 0
      return x != s || !t[0];

    case AddLemma::AddInv:
      // s = ~x -> t = ~0
      return s != notOf(x) || t == ones;

    case AddLemma::AddOverflow:
      // msb(x) = msb(s) = 1 -> t <u (x & s)
      return !(x[W - 1] && s[W - 1]) || !ule(andOf(x, s), t);

    case AddLemma::AddNoOverflow:
      // msb(x) = msb(s) = 0 -> t >=u (x | s)
      return x[W - 1] || s[W - 1] || ule(orOf(x, s), t);

    case AddLemma::AddOr:
      // x & s = 0 -> t = x | s
      return !allZero(andOf(x, s)) || t == orOf(x, s);

    case AddLemma::LowBitsNotAllSet:
      // 0 = x & s & t & 1
      return zero == andOf(x, andOf(s, andOf(t, one)));

    case AddLemma::LowBitNeedsOtherOrSum:
      // (1 & (s | t)) >=u (x & 1)
      return ule(andOf(x, one), andOf(one, orOf(s, t)));


    case AddLemma::SumLowBitNeedsAnOperand:
      // (1 & (x | s)) >=u (t & 1)
      return ule(andOf(t, one), andOf(one, orOf(x, s)));

    case AddLemma::SumOrNegatedAndNotOne:
      // 1 != (t | ~(x & s))
      return one != orOf(t, notOf(andOf(x, s)));

    case AddLemma::SumNotNegatedSumOrAnd:
      // t != ~(t | (x & s))
      return t != notOf(orOf(t, andOf(x, s)));

    case AddLemma::OperandsOrNegatedSumNotOne:
      // 1 != (x | s | ~t)
      return one != orOf(x, orOf(s, notOf(t)));
  }
  return true;
}


// ---------------------------------------------------------------------------
// The catalogues.
//
// Rank order is the order the refiner offers them in, so a fact's position
// here is the policy decision "try this one before that one". The comment on
// a measured entry is how many times it fired on the qualification corpus.
// ---------------------------------------------------------------------------

namespace
{

const BVLemmaEntry<DivLemma> DIV_LEMMAS[] = {
    {DivLemma::DivisorAboveShiftedDividend, "divisor-above-shifted-dividend",
     BVSchemaGroup::BASE, 1, 0}, // 280 firings
    {DivLemma::QuotientBelowNegatedDivisor, "quotient-below-negated-divisor",
     BVSchemaGroup::BASE, 1, 0}, // 200
    {DivLemma::DividendAboveNegatedAnd, "dividend-above-negated-and",
     BVSchemaGroup::BASE, 1, 0}, // 187
    // STP-specific. Ranked here by the extra candidate cube it excludes at
    // six bits (2.42%), ahead of facts below that add no unique exclusions.
    {DivLemma::QuotientIsOne, "quotient-is-one",
     BVSchemaGroup::QUOTIENT_ONE_QUOT, 1, 0},
    {DivLemma::DividendZero, "dividend-zero", BVSchemaGroup::BASE, 1, 0}, // 171
    {DivLemma::DivisorEqualsDividend, "divisor-equals-dividend",
     BVSchemaGroup::BASE, 1, 0}, // 162
    {DivLemma::DivisorLessOneAboveShiftedDividend,
     "divisor-less-one-above-shifted-dividend", BVSchemaGroup::BASE, 1, 0}, // 161
    {DivLemma::DividendAboveShiftedDoubleQuotient,
     "dividend-above-shifted-double-quotient", BVSchemaGroup::UDIV15, 1, 0}, // 125
    {DivLemma::QuotientNotNegatedAnd, "quotient-not-negated-and",
     BVSchemaGroup::UDIV_OBSERVED, 1, 0}, // 62
    {DivLemma::DivisorAllOnes, "divisor-all-ones", BVSchemaGroup::BASE, 1, 0}, // 59
    {DivLemma::DividendAboveDoubledShiftedDivisor,
     "dividend-above-doubled-shifted-divisor", BVSchemaGroup::UDIV_OBSERVED, 1,
     0}, // 54
    {DivLemma::DividendNotTwiceQuotientPlusOr,
     "dividend-not-twice-quotient-plus-or", BVSchemaGroup::UDIV_OBSERVED, 2,
     0}, // 26
    {DivLemma::QuotientAboveDoubledShiftedDividend,
     "quotient-above-doubled-shifted-dividend", BVSchemaGroup::UDIV_OBSERVED, 1,
     0}, // 14
    {DivLemma::DividendAboveOrAndDoubledDivisor,
     "dividend-above-or-and-doubled-divisor", BVSchemaGroup::UDIV_OBSERVED, 1,
     0}, // 10
    {DivLemma::MaskedDividendAboveDivisorAndQuotient,
     "masked-dividend-above-divisor-and-quotient", BVSchemaGroup::UDIV_OBSERVED,
     1, 0}, // 9
    {DivLemma::DividendAboveQuotientXorShifted,
     "dividend-above-quotient-xor-shifted", BVSchemaGroup::UDIV_OBSERVED, 1,
     0}, // 3
    {DivLemma::ShiftedDividendNotOr, "shifted-dividend-not-or",
     BVSchemaGroup::UDIV_OBSERVED, 1, 0}, // 3
    {DivLemma::DividendAboveOrAndDoubledQuotient,
     "dividend-above-or-and-doubled-quotient", BVSchemaGroup::UDIV_OBSERVED, 1,
     0}, // 2
    {DivLemma::DividendAboveDivisorXorShifted,
     "dividend-above-divisor-xor-shifted", BVSchemaGroup::UDIV_OBSERVED, 1,
     0}, // 2

    // The tail that did not fire on the qualification corpus.
    {DivLemma::DivisorOrQuotientNotMaskedDividend, "divisor-or-quotient-not-masked-dividend",
     BVSchemaGroup::UDIV_TAIL, 1, 0},
    {DivLemma::DivisorOrOneNotDividendWithoutQuotient, "divisor-or-one-not-dividend-without-quotient",
     BVSchemaGroup::UDIV_TAIL, 1, 0},
    {DivLemma::DivisorNotNegatedSelfShiftedByHalfQuotient, "divisor-not-negated-self-shifted-by-half-quotient",
     BVSchemaGroup::UDIV_TAIL, 1, 0},
    {DivLemma::DividendNotNegatedAndDoubledQuotient, "dividend-not-negated-and-doubled-quotient",
     BVSchemaGroup::UDIV_TAIL, 2, 0},
    {DivLemma::QuotientAboveDoubledDividendShiftedByDivisor, "quotient-above-doubled-dividend-shifted-by-divisor",
     BVSchemaGroup::UDIV_TAIL, 1, 0},
    {DivLemma::DividendAboveDivisorShiftedByNegatedOr, "dividend-above-divisor-shifted-by-negated-or",
     BVSchemaGroup::UDIV_TAIL, 1, 0},
    {DivLemma::DividendAboveQuotientShiftedByNegatedOr, "dividend-above-quotient-shifted-by-negated-or",
     BVSchemaGroup::UDIV_TAIL, 1, 0},
    {DivLemma::DividendAboveDivisorShiftedByNegatedXor, "dividend-above-divisor-shifted-by-negated-xor",
     BVSchemaGroup::UDIV_TAIL, 1, 0},
    {DivLemma::DividendAboveQuotientShiftedByNegatedXor, "dividend-above-quotient-shifted-by-negated-xor",
     BVSchemaGroup::UDIV_TAIL, 1, 0},
    {DivLemma::DividendNotQuotientPlusDivisorOrSum, "dividend-not-quotient-plus-divisor-or-sum",
     BVSchemaGroup::UDIV_TAIL, 1, 0},
    {DivLemma::DividendNotQuotientPlusOnePlusShiftedOne, "dividend-not-quotient-plus-one-plus-shifted-one",
     BVSchemaGroup::UDIV_TAIL, 3, 0},
    {DivLemma::DivisorAboveSumShiftedByQuotient, "divisor-above-sum-shifted-by-quotient",
     BVSchemaGroup::UDIV_TAIL, 1, 0},
    {DivLemma::DivisorXorOrAboveQuotientXorOne, "divisor-xor-or-above-quotient-xor-one",
     BVSchemaGroup::UDIV_TAIL, 1, 0},
    {DivLemma::QuotientAboveDividendShiftedByDivisorLessOne, "quotient-above-dividend-shifted-by-divisor-less-one",
     BVSchemaGroup::UDIV_TAIL, 1, 0},
    {DivLemma::DividendNotOneLessShiftedDividend, "dividend-not-one-less-shifted-dividend",
     BVSchemaGroup::UDIV_TAIL, 1, 2}};

const BVLemmaEntry<RemLemma> REM_LEMMAS[] = {
    {RemLemma::DividendZero, "dividend-zero", BVSchemaGroup::UREM, 1, 0},
    {RemLemma::DivisorEqualsDividend, "divisor-equals-dividend",
     BVSchemaGroup::UREM, 1, 0},
    {RemLemma::DividendBelowDivisor, "dividend-below-divisor",
     BVSchemaGroup::UREM, 1, 0},
    // STP-specific, and ranked with the three above because it likewise
    // determines the result throughout its premise rather than only bounding
    // it.
    {RemLemma::RemainderIsDifference, "remainder-is-difference",
     BVSchemaGroup::QUOTIENT_ONE_REM, 1, 0},
    {RemLemma::DividendWithinDivisorOrRemainder,
     "dividend-within-divisor-or-remainder", BVSchemaGroup::UREM, 1, 0},
    {RemLemma::DividendAboveRemainderOrAnd, "dividend-above-remainder-or-and",
     BVSchemaGroup::UREM, 1, 0},
    {RemLemma::RemainderOutsideOperandsNotOne,
     "remainder-outside-operands-not-one", BVSchemaGroup::UREM, 1, 0},
    {RemLemma::RemainderNotOrOfComplements, "remainder-not-or-of-complements",
     BVSchemaGroup::UREM, 1, 0},
    {RemLemma::RemainderInOperandsAboveLowBit,
     "remainder-in-operands-above-low-bit", BVSchemaGroup::UREM, 1, 0},
    {RemLemma::DividendNotOrOfNegations, "dividend-not-or-of-negations",
     BVSchemaGroup::UREM, 3, 0},
    {RemLemma::DifferenceAboveRemainder, "difference-above-remainder",
     BVSchemaGroup::UREM, 1, 0},
    {RemLemma::XorAboveRemainder, "xor-above-remainder", BVSchemaGroup::UREM, 1,
     0}};

const BVLemmaEntry<MulLemma> MUL_LEMMAS[] = {
    {MulLemma::FactorUnchangedByMaskedShift,
     "factor-unchanged-by-masked-shift", BVSchemaGroup::MUL8, 1, 0}, // 75
    {MulLemma::FactorAndProductNotOr, "factor-and-product-not-or",
     BVSchemaGroup::MUL_REF3, 2, 0, true}, // 5
    {MulLemma::ProductNotOddFactorShiftedByShiftedProduct, "product-not-odd-factor-shifted-by-shifted-product",
     BVSchemaGroup::MUL_TAIL, 2, 0}, // 4

    // The tail that did not fire, in catalogue order.
    {MulLemma::FactorNotNegatedProductOrLowBit, "factor-not-negated-product-or-low-bit",
     BVSchemaGroup::MUL_TAIL, 2, 0},
    {MulLemma::ProductAboveMaskedShiftedFactors, "product-above-masked-shifted-factors",
     BVSchemaGroup::MUL_TAIL, 1, 2, true},
    {MulLemma::FactorNotOneXorFactorShiftedByXor, "factor-not-one-xor-factor-shifted-by-xor",
     BVSchemaGroup::MUL_TAIL, 1, 0},
    {MulLemma::ProductNotOneOrNegatedXor, "product-not-one-or-negated-xor",
     BVSchemaGroup::MUL_TAIL, 2, 0, true},
    {MulLemma::ProductNotHighOnesOrXor, "product-not-high-ones-or-xor",
     BVSchemaGroup::MUL_TAIL, 2, 0, true},
    {MulLemma::FactorNotShiftedFactorLessOne, "factor-not-shifted-factor-less-one",
     BVSchemaGroup::MUL_TAIL, 1, 0},
    {MulLemma::FactorNotOneLessShiftedFactor, "factor-not-one-less-shifted-factor",
     BVSchemaGroup::MUL_TAIL, 1, 0},
    {MulLemma::FactorNotOnePlusShiftedFactor, "factor-not-one-plus-shifted-factor",
     BVSchemaGroup::MUL_TAIL, 1, 0},
    {MulLemma::FactorNotOneLessShiftedFactorReversed, "factor-not-one-less-shifted-factor-reversed",
     BVSchemaGroup::MUL_TAIL, 1, 0},
    {MulLemma::FactorNotOnePlusShiftedFactorReversed, "factor-not-one-plus-shifted-factor-reversed",
     BVSchemaGroup::MUL_TAIL, 1, 0},
    {MulLemma::ProductNotOneOrSum, "product-not-one-or-sum", BVSchemaGroup::MUL_TAIL, 2,
     0, true},
    {MulLemma::FactorNotNegatedShiftedFactor, "factor-not-negated-shifted-factor",
     BVSchemaGroup::MUL_TAIL, 1, 0}};

const BVLemmaEntry<AddLemma> ADD_LEMMAS[] = {
    {AddLemma::AddZero, "add-zero", BVSchemaGroup::ADD, 1, 0},
    {AddLemma::AddSame, "add-same", BVSchemaGroup::ADD, 1, 0, true},
    {AddLemma::AddInv, "add-inverse", BVSchemaGroup::ADD, 1, 0, true},
    {AddLemma::AddOverflow, "add-overflow", BVSchemaGroup::ADD, 1, 0, true},
    {AddLemma::AddNoOverflow, "add-no-overflow", BVSchemaGroup::ADD, 1, 0, true},
    {AddLemma::AddOr, "add-or", BVSchemaGroup::ADD, 1, 0, true},
    {AddLemma::LowBitsNotAllSet, "add-low-bits-not-all-set", BVSchemaGroup::ADD, 1, 0, true},
    {AddLemma::LowBitNeedsOtherOrSum, "add-low-bit-needs-other-or-sum", BVSchemaGroup::ADD, 1, 0},
    {AddLemma::SumLowBitNeedsAnOperand, "add-sum-low-bit-needs-an-operand", BVSchemaGroup::ADD, 1, 0, true},
    {AddLemma::SumOrNegatedAndNotOne, "add-sum-or-negated-and-not-one", BVSchemaGroup::ADD, 3, 0, true},
    {AddLemma::SumNotNegatedSumOrAnd, "add-sum-not-negated-sum-or-and", BVSchemaGroup::ADD, 2, 0, true},
    {AddLemma::OperandsOrNegatedSumNotOne, "add-operands-or-negated-sum-not-one", BVSchemaGroup::ADD, 3, 0, true}};

static_assert(sizeof(DIV_LEMMAS) / sizeof(DIV_LEMMAS[0]) ==
                  BV_DIV_LEMMA_COUNT,
              "the published UDIV catalogue size is out of step");
static_assert(sizeof(REM_LEMMAS) / sizeof(REM_LEMMAS[0]) ==
                  BV_REM_LEMMA_COUNT,
              "the published UREM catalogue size is out of step");
static_assert(sizeof(MUL_LEMMAS) / sizeof(MUL_LEMMAS[0]) ==
                  BV_MUL_LEMMA_COUNT,
              "the published MUL catalogue size is out of step");
static_assert(sizeof(ADD_LEMMAS) / sizeof(ADD_LEMMAS[0]) ==
                  BV_ADD_LEMMA_COUNT,
              "the published ADD catalogue size is out of step");

template <typename Lemma, unsigned N>
const BVLemmaEntry<Lemma>& entryOf(const BVLemmaEntry<Lemma> (&table)[N],
                                   Lemma lemma)
{
  for (unsigned i = 0; i < N; ++i)
    if (table[i].lemma == lemma)
      return table[i];
  FatalError("BV abstraction: a lemma is missing from its catalogue");
  return table[0];
}

} // namespace

const BVLemmaEntry<DivLemma>* divLemmaTable(unsigned& count)
{
  count = sizeof(DIV_LEMMAS) / sizeof(DIV_LEMMAS[0]);
  return DIV_LEMMAS;
}

const BVLemmaEntry<RemLemma>* remLemmaTable(unsigned& count)
{
  count = sizeof(REM_LEMMAS) / sizeof(REM_LEMMAS[0]);
  return REM_LEMMAS;
}

const BVLemmaEntry<MulLemma>* mulLemmaTable(unsigned& count)
{
  count = sizeof(MUL_LEMMAS) / sizeof(MUL_LEMMAS[0]);
  return MUL_LEMMAS;
}

const BVLemmaEntry<AddLemma>* addLemmaTable(unsigned& count)
{
  count = sizeof(ADD_LEMMAS) / sizeof(ADD_LEMMAS[0]);
  return ADD_LEMMAS;
}

template <typename Lemma, unsigned N>
const BVLemmaEntry<Lemma>& atRank(const BVLemmaEntry<Lemma> (&table)[N],
                                  unsigned index)
{
  if (index >= N)
    FatalError("BV abstraction: a schema rank is outside its catalogue");
  return table[index];
}

const BVLemmaEntry<DivLemma>& divLemmaAt(unsigned i)
{
  return atRank(DIV_LEMMAS, i);
}
const BVLemmaEntry<RemLemma>& remLemmaAt(unsigned i)
{
  return atRank(REM_LEMMAS, i);
}
const BVLemmaEntry<MulLemma>& mulLemmaAt(unsigned i)
{
  return atRank(MUL_LEMMAS, i);
}
const BVLemmaEntry<AddLemma>& addLemmaAt(unsigned i)
{
  return atRank(ADD_LEMMAS, i);
}

const BVLemmaEntry<DivLemma>& divLemmaEntry(DivLemma l)
{
  return entryOf(DIV_LEMMAS, l);
}
const BVLemmaEntry<RemLemma>& remLemmaEntry(RemLemma l)
{
  return entryOf(REM_LEMMAS, l);
}
const BVLemmaEntry<MulLemma>& mulLemmaEntry(MulLemma l)
{
  return entryOf(MUL_LEMMAS, l);
}
const BVLemmaEntry<AddLemma>& addLemmaEntry(AddLemma l)
{
  return entryOf(ADD_LEMMAS, l);
}

} // namespace stp
