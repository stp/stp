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

// The circuits for the abstraction lemma catalogue.
//
// These are BitBlaster members and nothing in BBTerm reaches them: no query
// is lowered through this file. They are here rather than in BitBlaster.cpp
// so that the file every query path is read from does not also carry the
// refinement catalogue -- five hundred lines of facts about division that
// exist only for --bv-term-abstraction.
//
// They stay *members* rather than moving to a collaborator class because a
// collaborator would need sixteen of the bit-blaster's private primitives --
// the adders, the comparators, the barrel shifters, the node manager itself
// -- made public to reach them. Widening a core class's contract by sixteen
// members to relocate five is the worse trade; splitting the translation
// unit gets the bulk out for nothing.
//
// What each fact *is* lives in BVLemmaCatalogue: the enumerator, the value
// predicate, the name, the owning option family, the rank. This file only
// says how to build it, and the exhaustive circuit-versus-predicate test is
// what keeps the two saying the same thing.

#include "stp/ToSat/BitBlaster.h"

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/ToSat/BBNodeManagerAIG.h"
#include "stp/ToSat/BVLemmaCatalogue.h"

#include <cassert>
#include <limits>

namespace stp
{

// `s <=u x <u 2s`, with doubling interpreted in the integers. A divisor
// whose top bit is set doubles past the vector width, making the upper test
// automatic. A zero divisor cannot satisfy both halves of the premise.
BBNode BitBlaster::BBFitsExactlyOnce(const BBNodeVec& x,
                                     const BBNodeVec& s)
{
  const unsigned width = (unsigned)x.size();
  BBNodeVec twice = s;
  BBLShift(twice, 1);
  return nf->CreateNode(
      AND, BBBVLE(s, x, false),
      nf->CreateNode(OR, s[width - 1],
                     nf->CreateNode(NOT, BBBVLE(twice, x, false))));
}

BBNode BitBlaster::BBDivLemma(DivLemma lemma, const BBNodeVec& x,
                              const BBNodeVec& s, const BBNodeVec& t,
                              BBNodeSet& support)
{
  const unsigned width = (unsigned)x.size();
  assert(s.size() == width);
  assert(t.size() == width);
  assert(divLemmaApplicable(lemma, width));

  const BBNodeVec zero = BBfill(width, BBFalse);
  const BBNodeVec ones = BBfill(width, BBTrue);
  BBNodeVec one = zero;
  one[0] = BBTrue;

  switch (lemma)
  {
    case DivLemma::DividendZero:
      // x = 0 and s != 0 -> t = 0
      return nf->CreateNode(OR, nf->CreateNode(NOT, BBEQ(x, zero)),
                            BBEQ(s, zero), BBEQ(t, zero));

    case DivLemma::DivisorEqualsDividend:
      // s = x and s != 0 -> t = 1
      return nf->CreateNode(OR, nf->CreateNode(NOT, BBEQ(s, x)),
                            BBEQ(s, zero), BBEQ(t, one));

    case DivLemma::DivisorAllOnes:
      // s = ~0 and x != ~0 -> t = 0
      return nf->CreateNode(OR, nf->CreateNode(NOT, BBEQ(s, ones)),
                            BBEQ(x, ones), BBEQ(t, zero));

    case DivLemma::QuotientBelowNegatedDivisor:
    {
      // t <=u -(s | 1). Setting the bottom bit is all `s | 1` does.
      BBNodeVec sOr1 = s;
      sOr1[0] = BBTrue;
      return BBBVLE(t, BBUminus(sOr1), false);
    }

    case DivLemma::DividendAboveNegatedAnd:
    {
      // x >=u -((-s) & (-t))
      const BBNodeVec negS = BBUminus(s);
      const BBNodeVec negT = BBUminus(t);
      BBNodeVec conj(width);
      for (unsigned i = 0; i < width; i++)
        conj[i] = nf->CreateNode(AND, negS[i], negT[i]);
      return BBBVLE(BBUminus(conj), x, false);
    }

    case DivLemma::DivisorAboveShiftedDividend:
      // s >=u (x >> t)
      return BBBVLE(BBShiftRightByVariable(x, t, width), s, false);

    case DivLemma::DivisorLessOneAboveShiftedDividend:
    {
      // (s - 1) >=u (x >> t)
      BBNodeVec sMinusOne = s;
      BBSub(sMinusOne, one, support);
      return BBBVLE(BBShiftRightByVariable(x, t, width), sMinusOne, false);
    }

    case DivLemma::DividendAboveShiftedDoubleQuotient:
    {
      // x >=u ((t << 1) >> (t << s))
      BBNodeVec tTwice = t;
      BBLShift(tTwice, 1);
      const BBNodeVec amount = BBShiftLeftByVariable(t, s);
      return BBBVLE(BBShiftRightByVariable(tTwice, amount, width), x, false);
    }

    case DivLemma::QuotientNotNegatedAnd:
      // t != -(s & ~x)
      return nf->CreateNode(
          NOT, BBEQ(t, BBUminus(BBAnd(s, BBNeg(x)))));

    case DivLemma::MaskedDividendAboveDivisorAndQuotient:
      // (x & -t) >=u (s & t)
      return BBBVLE(BBAnd(s, t), BBAnd(x, BBUminus(t)), false);

    case DivLemma::DividendAboveDoubledShiftedDivisor:
    {
      // x >=u ((s >> (s << t)) << 1)
      BBNodeVec shifted = BBShiftRightByVariable(
          s, BBShiftLeftByVariable(s, t), width);
      BBLShift(shifted, 1);
      return BBBVLE(shifted, x, false);
    }

    case DivLemma::QuotientAboveDoubledShiftedDividend:
    {
      // t >=u ((x >> s) << 1)
      BBNodeVec shifted = BBShiftRightByVariable(x, s, width);
      BBLShift(shifted, 1);
      return BBBVLE(shifted, t, false);
    }

    case DivLemma::DividendAboveOrAndDoubledDivisor:
    {
      // x >=u ((x | t) & (s << 1))
      BBNodeVec twiceS = s;
      BBLShift(twiceS, 1);
      return BBBVLE(BBAnd(BBOr(x, t), twiceS), x, false);
    }

    case DivLemma::DividendAboveOrAndDoubledQuotient:
    {
      // x >=u ((x | s) & (t << 1))
      BBNodeVec twiceT = t;
      BBLShift(twiceT, 1);
      return BBBVLE(BBAnd(BBOr(x, s), twiceT), x, false);
    }

    case DivLemma::ShiftedDividendNotOr:
      // (x >> t) != (s | t)
      return nf->CreateNode(
          NOT, BBEQ(BBShiftRightByVariable(x, t, width), BBOr(s, t)));

    case DivLemma::DividendAboveQuotientXorShifted:
    {
      // x >=u (t xor (t >> (s >> 1)))
      BBNodeVec halfS = s;
      BBRShift(halfS, 1);
      return BBBVLE(
          BBXor(t, BBShiftRightByVariable(t, halfS, width)), x, false);
    }

    case DivLemma::DividendAboveDivisorXorShifted:
    {
      // x >=u (s xor (s >> (t >> 1)))
      BBNodeVec halfT = t;
      BBRShift(halfT, 1);
      return BBBVLE(
          BBXor(s, BBShiftRightByVariable(s, halfT, width)), x, false);
    }

    case DivLemma::DividendNotTwiceQuotientPlusOr:
      // x != t + t + (x | s)
      return nf->CreateNode(
          NOT, BBEQ(x, BBAdd(t, BBAdd(t, BBOr(x, s)))));

    case DivLemma::QuotientIsOne:
      // s <=u x <u 2s -> t = 1
      return nf->CreateNode(OR, nf->CreateNode(NOT, BBFitsExactlyOnce(x, s)),
                            BBEQ(t, one));

    case DivLemma::DivisorOrQuotientNotMaskedDividend:
      // (s | t) != (x & ~1)
      return nf->CreateNode(
          NOT, BBEQ(BBOr(s, t), BBAnd(x, BBNeg(one))));

    case DivLemma::DivisorOrOneNotDividendWithoutQuotient:
    {
      // (s | 1) != (x & ~t)
      BBNodeVec sOrOne = s;
      sOrOne[0] = BBTrue;
      return nf->CreateNode(NOT, BBEQ(sOrOne, BBAnd(x, BBNeg(t))));
    }

    case DivLemma::DivisorNotNegatedSelfShiftedByHalfQuotient:
    {
      // s != ~(s >> (t >> 1))
      BBNodeVec halfT = t;
      BBRShift(halfT, 1);
      return nf->CreateNode(
          NOT,
          BBEQ(s, BBNeg(BBShiftRightByVariable(s, halfT, width))));
    }

    case DivLemma::DividendNotNegatedAndDoubledQuotient:
    {
      // x != ~(x & (t << 1))
      BBNodeVec twiceT = t;
      BBLShift(twiceT, 1);
      return nf->CreateNode(NOT, BBEQ(x, BBNeg(BBAnd(x, twiceT))));
    }

    case DivLemma::QuotientAboveDoubledDividendShiftedByDivisor:
    {
      // t >=u ((x << 1) >> s)
      BBNodeVec twiceX = x;
      BBLShift(twiceX, 1);
      return BBBVLE(BBShiftRightByVariable(twiceX, s, width), t, false);
    }

    case DivLemma::DividendAboveDivisorShiftedByNegatedOr:
      // x >=u (s << ~(x | t))
      return BBBVLE(
          BBShiftLeftByVariable(s, BBNeg(BBOr(x, t))), x, false);

    case DivLemma::DividendAboveQuotientShiftedByNegatedOr:
      // x >=u (t << ~(x | s))
      return BBBVLE(
          BBShiftLeftByVariable(t, BBNeg(BBOr(x, s))), x, false);

    case DivLemma::DividendAboveDivisorShiftedByNegatedXor:
      // x >=u (s << ~(x xor t))
      return BBBVLE(
          BBShiftLeftByVariable(s, BBNeg(BBXor(x, t))), x, false);

    case DivLemma::DividendAboveQuotientShiftedByNegatedXor:
      // x >=u (t << ~(x xor s))
      return BBBVLE(
          BBShiftLeftByVariable(t, BBNeg(BBXor(x, s))), x, false);

    case DivLemma::DividendNotQuotientPlusDivisorOrSum:
      // x != t + (s | (x + s))
      return nf->CreateNode(
          NOT, BBEQ(x, BBAdd(t, BBOr(s, BBAdd(x, s)))));

    case DivLemma::DividendNotQuotientPlusOnePlusShiftedOne:
      // x != t + (1 + (1 << x))
      return nf->CreateNode(
          NOT,
          BBEQ(x, BBAdd(t, BBAdd(one, BBShiftLeftByVariable(one, x)))));

    case DivLemma::DivisorAboveSumShiftedByQuotient:
      // s >=u ((x + t) >> t)
      return BBBVLE(
          BBShiftRightByVariable(BBAdd(x, t), t, width), s, false);

    case DivLemma::DivisorXorOrAboveQuotientXorOne:
      // (s xor (x | t)) >=u (t xor 1)
      return BBBVLE(BBXor(t, one), BBXor(s, BBOr(x, t)), false);

    case DivLemma::QuotientAboveDividendShiftedByDivisorLessOne:
    {
      // t >=u (x >> (s - 1))
      BBNodeVec sMinusOne = s;
      BBSub(sMinusOne, one, support);
      return BBBVLE(
          BBShiftRightByVariable(x, sMinusOne, width), t, false);
    }

    case DivLemma::DividendNotOneLessShiftedDividend:
    {
      // x != 1 - (x << (x - t))
      BBNodeVec xMinusT = x;
      BBSub(xMinusT, t, support);
      const BBNodeVec shifted = BBShiftLeftByVariable(x, xMinusT);
      BBNodeVec difference = one;
      BBSub(difference, shifted, support);
      return nf->CreateNode(NOT, BBEQ(x, difference));
    }
  }

  FatalError("BBDivLemma: unknown lemma");
  return BBFalse;
}

BBNode BitBlaster::BBRemLemma(RemLemma lemma, const BBNodeVec& x,
                              const BBNodeVec& s, const BBNodeVec& t,
                              BBNodeSet& support)
{
  const unsigned width = (unsigned)x.size();
  assert(s.size() == width);
  assert(t.size() == width);
  assert(remLemmaApplicable(lemma, width));

  const BBNodeVec zero = BBfill(width, BBFalse);
  BBNodeVec one = zero;
  one[0] = BBTrue;

  switch (lemma)
  {
    case RemLemma::DividendZero:
      // x = 0 -> t = 0
      return nf->CreateNode(OR, nf->CreateNode(NOT, BBEQ(x, zero)),
                            BBEQ(t, zero));

    case RemLemma::DivisorEqualsDividend:
      // s = x -> t = 0
      return nf->CreateNode(OR, nf->CreateNode(NOT, BBEQ(s, x)),
                            BBEQ(t, zero));

    case RemLemma::DividendBelowDivisor:
      // x <u s -> t = x
      return nf->CreateNode(OR, BBBVLE(s, x, false), BBEQ(t, x));

    case RemLemma::RemainderIsDifference:
    {
      // s <=u x <u 2s -> t = x - s
      BBNodeVec difference = x;
      BBSub(difference, s, support);
      return nf->CreateNode(OR, nf->CreateNode(NOT, BBFitsExactlyOnce(x, s)),
                            BBEQ(t, difference));
    }

    case RemLemma::DividendWithinDivisorOrRemainder:
      // x = x & (s | t | -s)
      return BBEQ(x, BBAnd(x, BBOr(s, BBOr(t, BBUminus(s)))));

    case RemLemma::DividendAboveRemainderOrAnd:
      // x >=u (t | (x & s))
      return BBBVLE(BBOr(t, BBAnd(x, s)), x, false);

    case RemLemma::RemainderOutsideOperandsNotOne:
      // 1 != (t & ~(x | s))
      return nf->CreateNode(
          NOT, BBEQ(one, BBAnd(t, BBNeg(BBOr(x, s)))));

    case RemLemma::RemainderNotOrOfComplements:
      // t != (~x | -s)
      return nf->CreateNode(
          NOT, BBEQ(t, BBOr(BBNeg(x), BBUminus(s))));

    case RemLemma::RemainderInOperandsAboveLowBit:
      // (t & (x | s)) >=u (t & 1)
      return BBBVLE(BBAnd(t, one), BBAnd(t, BBOr(x, s)), false);

    case RemLemma::DividendNotOrOfNegations:
      // x != (-x | -(~t))
      return nf->CreateNode(
          NOT, BBEQ(x, BBOr(BBUminus(x), BBUminus(BBNeg(t)))));

    case RemLemma::DifferenceAboveRemainder:
      // (x + -s) >=u t
      return BBBVLE(t, BBAdd(x, BBUminus(s)), false);

    case RemLemma::XorAboveRemainder:
      // ((-s) xor (x | s)) >=u t
      return BBBVLE(t, BBXor(BBUminus(s), BBOr(x, s)), false);
  }

  FatalError("BBRemLemma: unknown lemma");
  return BBFalse;
}

BBNode BitBlaster::BBMulLemma(MulLemma lemma, const BBNodeVec& x,
                              const BBNodeVec& s, const BBNodeVec& t,
                              BBNodeSet& support)
{
  const unsigned width = (unsigned)x.size();
  assert(s.size() == width);
  assert(t.size() == width);
  assert(mulLemmaApplicable(lemma, width));

  BBNodeVec one = BBfill(width, BBFalse);
  one[0] = BBTrue;

  switch (lemma)
  {
    case MulLemma::FactorUnchangedByMaskedShift:
    {
      // The published form is s = s << (x & (1 >> t)). The shift is
      // nonzero exactly when t is zero and x is odd, and s = s << 1 has only
      // the all-zero solution. This compact equivalent avoids two barrel
      // shifters while the value predicate retains the published spelling.
      const BBNodeVec zero = BBfill(width, BBFalse);
      return nf->CreateNode(OR, nf->CreateNode(NOT, BBEQ(t, zero)),
                            nf->CreateNode(NOT, x[0]), BBEQ(s, zero));
    }

    case MulLemma::FactorNotNegatedProductOrLowBit:
      // s != ~(t | (1 & (x | s)))
      return nf->CreateNode(
          NOT,
          BBEQ(s, BBNeg(BBOr(t, BBAnd(one, BBOr(x, s))))));

    case MulLemma::FactorAndProductNotOr:
      // (x & t) != (s | ~t)
      return nf->CreateNode(
          NOT, BBEQ(BBAnd(x, t), BBOr(s, BBNeg(t))));

    case MulLemma::ProductNotOddFactorShiftedByShiftedProduct:
    {
      // t != ((s | 1) << (t << x))
      BBNodeVec sOrOne = s;
      sOrOne[0] = BBTrue;
      return nf->CreateNode(
          NOT,
          BBEQ(t, BBShiftLeftByVariable(
                      sOrOne, BBShiftLeftByVariable(t, x))));
    }

    case MulLemma::ProductAboveMaskedShiftedFactors:
    {
      // t >=u (1 & ((x & s) >> 1))
      BBNodeVec half = BBAnd(x, s);
      BBRShift(half, 1);
      return BBBVLE(BBAnd(one, half), t, false);
    }

    case MulLemma::FactorNotOneXorFactorShiftedByXor:
      // x != (1 xor (x << (s xor t)))
      return nf->CreateNode(
          NOT,
          BBEQ(x, BBXor(one, BBShiftLeftByVariable(x, BBXor(s, t)))));

    case MulLemma::ProductNotOneOrNegatedXor:
      // t != (1 | ~(x xor s))
      return nf->CreateNode(
          NOT, BBEQ(t, BBOr(one, BBNeg(BBXor(x, s)))));

    case MulLemma::ProductNotHighOnesOrXor:
      // t != (~1 | (x xor s))
      return nf->CreateNode(
          NOT, BBEQ(t, BBOr(BBNeg(one), BBXor(x, s))));

    case MulLemma::FactorNotShiftedFactorLessOne:
    {
      // x != (x << (s + t)) - 1
      BBNodeVec rhs = BBShiftLeftByVariable(x, BBAdd(s, t));
      BBSub(rhs, one, support);
      return nf->CreateNode(NOT, BBEQ(x, rhs));
    }

    case MulLemma::FactorNotOneLessShiftedFactor:
    {
      // x != 1 - (x << (s - t))
      BBNodeVec amount = s;
      BBSub(amount, t, support);
      BBNodeVec rhs = one;
      BBSub(rhs, BBShiftLeftByVariable(x, amount), support);
      return nf->CreateNode(NOT, BBEQ(x, rhs));
    }

    case MulLemma::FactorNotOnePlusShiftedFactor:
    {
      // s != 1 + (s << (t - x))
      BBNodeVec amount = t;
      BBSub(amount, x, support);
      return nf->CreateNode(
          NOT, BBEQ(s, BBAdd(one, BBShiftLeftByVariable(s, amount))));
    }

    case MulLemma::FactorNotOneLessShiftedFactorReversed:
    {
      // s != 1 - (s << (t - x))
      BBNodeVec amount = t;
      BBSub(amount, x, support);
      BBNodeVec rhs = one;
      BBSub(rhs, BBShiftLeftByVariable(s, amount), support);
      return nf->CreateNode(NOT, BBEQ(s, rhs));
    }

    case MulLemma::FactorNotOnePlusShiftedFactorReversed:
    {
      // s != 1 + (s << (x - t))
      BBNodeVec amount = x;
      BBSub(amount, t, support);
      return nf->CreateNode(
          NOT, BBEQ(s, BBAdd(one, BBShiftLeftByVariable(s, amount))));
    }

    case MulLemma::ProductNotOneOrSum:
      // t != (1 | (x + s))
      return nf->CreateNode(NOT, BBEQ(t, BBOr(one, BBAdd(x, s))));

    case MulLemma::FactorNotNegatedShiftedFactor:
      // x != ~(x << (s + t))
      return nf->CreateNode(
          NOT, BBEQ(x, BBNeg(BBShiftLeftByVariable(x, BBAdd(s, t)))));
  }

  FatalError("BBMulLemma: unknown lemma");
  return BBFalse;
}

BBNode BitBlaster::BBAddLemma(AddLemma lemma, const BBNodeVec& x,
                              const BBNodeVec& s, const BBNodeVec& t,
                              BBNodeSet& /*support*/)
{
  const unsigned width = (unsigned)x.size();
  assert(width > 0);
  assert(s.size() == width);
  assert(t.size() == width);
  assert(addLemmaApplicable(lemma, width));

  const BBNodeVec zero = BBfill(width, BBFalse);
  const BBNodeVec ones = BBfill(width, BBTrue);
  BBNodeVec one = zero;
  one[0] = BBTrue;

  switch (lemma)
  {
    case AddLemma::AddZero:
      // s = 0 -> t = x
      return nf->CreateNode(OR, nf->CreateNode(NOT, BBEQ(s, zero)),
                            BBEQ(t, x));

    case AddLemma::AddSame:
      // x = s -> t[0] = 0
      return nf->CreateNode(OR, nf->CreateNode(NOT, BBEQ(x, s)),
                            nf->CreateNode(NOT, t[0]));

    case AddLemma::AddInv:
      // s = ~x -> t = ~0
      return nf->CreateNode(OR, nf->CreateNode(NOT, BBEQ(s, BBNeg(x))),
                            BBEQ(t, ones));

    case AddLemma::AddOverflow:
      // msb(x) = msb(s) = 1 -> t <u (x & s)
      return nf->CreateNode(
          OR, nf->CreateNode(NOT, x[width - 1]),
          nf->CreateNode(NOT, s[width - 1]),
          nf->CreateNode(NOT, BBBVLE(BBAnd(x, s), t, false)));

    case AddLemma::AddNoOverflow:
      // msb(x) = msb(s) = 0 -> t >=u (x | s)
      return nf->CreateNode(OR, x[width - 1], s[width - 1],
                            BBBVLE(BBOr(x, s), t, false));

    case AddLemma::AddOr:
      // x & s = 0 -> t = x | s
      return nf->CreateNode(
          OR, nf->CreateNode(NOT, BBEQ(BBAnd(x, s), zero)),
          BBEQ(t, BBOr(x, s)));

    case AddLemma::LowBitsNotAllSet:
      // 0 = x & s & t & 1
      return BBEQ(zero, BBAnd(x, BBAnd(s, BBAnd(t, one))));

    case AddLemma::LowBitNeedsOtherOrSum:
      // (1 & (s | t)) >=u (x & 1)
      return BBBVLE(BBAnd(x, one), BBAnd(one, BBOr(s, t)), false);


    case AddLemma::SumLowBitNeedsAnOperand:
      // (1 & (x | s)) >=u (t & 1)
      return BBBVLE(BBAnd(t, one), BBAnd(one, BBOr(x, s)), false);

    case AddLemma::SumOrNegatedAndNotOne:
      // 1 != (t | ~(x & s))
      return nf->CreateNode(
          NOT, BBEQ(one, BBOr(t, BBNeg(BBAnd(x, s)))));

    case AddLemma::SumNotNegatedSumOrAnd:
      // t != ~(t | (x & s))
      return nf->CreateNode(
          NOT, BBEQ(t, BBNeg(BBOr(t, BBAnd(x, s)))));

    case AddLemma::OperandsOrNegatedSumNotOne:
      // 1 != (x | s | ~t)
      return nf->CreateNode(
          NOT, BBEQ(one, BBOr(x, BBOr(s, BBNeg(t)))));
  }

  FatalError("BBAddLemma: unknown lemma");
  return BBFalse;
}

} // namespace stp
