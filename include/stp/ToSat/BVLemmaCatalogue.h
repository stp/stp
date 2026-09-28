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

#ifndef BVLEMMACATALOGUE_H
#define BVLEMMACATALOGUE_H

// The arithmetic facts BV term abstraction refines with, as data.
//
// A fact has five faces: an enumerator, a predicate over values, a circuit
// over SAT variables, a name, and the option family that owns it -- plus a
// position in the order the refiner offers them. Four of those, and the
// order, used to be four `switch`es and an array spread over three
// translation units, with nothing but a test keeping them in step, and with
// the ranked array the one place a compiler could not notice an omission.
// They are one table each here.
//
// What is deliberately *not* here is the predicate and the circuit. The
// predicate stays one switch per operation below, because a switch over a
// scoped enum with no default is a compile error when a fact is added and a
// table of function pointers is not. The circuit stays with the bit-blaster,
// because it is written in BBNodeVec.

#include "stp/STPManager/UserDefinedFlags.h"
#include "stp/Util/Attributes.h"

#include <vector>

namespace stp
{

// The facts about division that STP had no way to state before this: each
// is an inequality or an implication over the dividend, the divisor and the
// quotient, rather than a value for the quotient.
//
// They are not STP's. They come from:
//
//   Aina Niemetz, Mathias Preiner, Yoni Zohar.
//   Scalable Bit-Blasting with Abstractions.
//   CAV 2024, LNCS 14681, pp. 178-200. doi:10.1007/978-3-031-65627-9_9
//
// and are reimplemented here against STP's own bit-blaster rather than
// copied from anywhere.
//
// Each enumerator says what its fact is; the label in brackets beside it is
// the paper's name for the same fact, so a reader can go and check. The name
// carries the meaning and the bracket carries the provenance -- a bare
// number does neither, and a bare number that has drifted out of step with
// the paper is worse than none, which is what these were.
//
// The four with no premise are not facts anyone would derive by thinking
// about division -- `x >=u -((-s) & (-t))` is the output of the syntax-guided
// synthesis that paper describes -- which is the argument for taking a
// published set rather than inventing one.
//
// The table in the refiner keeps the measured entries in firing order and the
// unranked tail after them. Completeness is useful for controlled ablations,
// not evidence that every fact should eventually be enabled by default.
enum class DivLemma
{
  // x = 0 and s != 0 -> t = 0  (UDIV4)
  DividendZero,
  // s = x and s != 0 -> t = 1  (UDIV2)
  DivisorEqualsDividend,
  // s = ~0 and x != ~0 -> t = 0  (UDIV6)
  DivisorAllOnes,
  // t <=u -(s | 1)  (UDIV8)
  QuotientBelowNegatedDivisor,
  // x >=u -((-s) & (-t))  (UDIV7)
  DividendAboveNegatedAnd,
  // s >=u (x >> t)  (UDIV13)
  DivisorAboveShiftedDividend,
  // (s - 1) >=u (x >> t)  (UDIV35)
  DivisorLessOneAboveShiftedDividend,
  // x >=u ((t << 1) >> (t << s))  (UDIV15)
  DividendAboveShiftedDoubleQuotient,

  // t != -(s & ~x)  (UDIV9)
  QuotientNotNegatedAnd,
  // (x & -t) >=u (s & t)  (UDIV12)
  MaskedDividendAboveDivisorAndQuotient,
  // x >=u ((s >> (s << t)) << 1)  (UDIV14)
  DividendAboveDoubledShiftedDivisor,
  // t >=u ((x >> s) << 1)  (UDIV16)
  QuotientAboveDoubledShiftedDividend,
  // x >=u ((x | t) & (s << 1))  (UDIV17)
  DividendAboveOrAndDoubledDivisor,
  // x >=u ((x | s) & (t << 1))  (UDIV18)
  DividendAboveOrAndDoubledQuotient,
  // (x >> t) != (s | t)  (UDIV19)
  ShiftedDividendNotOr,
  // x >=u (t xor (t >> (s >> 1)))  (UDIV25)
  DividendAboveQuotientXorShifted,
  // x >=u (s xor (s >> (t >> 1)))  (UDIV26)
  DividendAboveDivisorXorShifted,
  // x != t + t + (x | s)  (UDIV32)
  DividendNotTwiceQuotientPlusOr,

  // s <=u x <u 2s -> t = 1. This STP-specific exact-band fact shares its
  // premise with RemainderIsDifference and is ranked with the fixed UDIV
  // registry rather than maintained as a one-off schema.
  // s <=u x <u 2s -> t = 1
  QuotientIsOne,

  // The tail that did not fire on the qualification corpus. The enumerators
  // keep the catalogue's own numbering, which is the only handle these have;
  // divLemmaName() gives each a description of its formula.
  // (s | t) != (x & ~1)  (UDIV10)
  DivisorOrQuotientNotMaskedDividend,
  // (s | 1) != (x & ~t)  (UDIV11)
  DivisorOrOneNotDividendWithoutQuotient,
  // s != ~(s >> (t >> 1))  (UDIV20)
  DivisorNotNegatedSelfShiftedByHalfQuotient,
  // x != ~(x & (t << 1))  (UDIV21)
  DividendNotNegatedAndDoubledQuotient,
  // t >=u ((x << 1) >> s)  (UDIV22)
  QuotientAboveDoubledDividendShiftedByDivisor,
  // x >=u (s << ~(x | t))  (UDIV23)
  DividendAboveDivisorShiftedByNegatedOr,
  // x >=u (t << ~(x | s))  (UDIV24)
  DividendAboveQuotientShiftedByNegatedOr,
  // x >=u (s << ~(x xor t))  (UDIV27)
  DividendAboveDivisorShiftedByNegatedXor,
  // x >=u (t << ~(x xor s))  (UDIV28)
  DividendAboveQuotientShiftedByNegatedXor,
  // x != t + (s | (x + s))  (UDIV29)
  DividendNotQuotientPlusDivisorOrSum,
  // x != t + (1 + (1 << x))  (UDIV30)
  DividendNotQuotientPlusOnePlusShiftedOne,
  // s >=u ((x + t) >> t)  (UDIV31)
  DivisorAboveSumShiftedByQuotient,
  // (s xor (x | t)) >=u (t xor 1)  (UDIV33)
  DivisorXorOrAboveQuotientXorOne,
  // t >=u (x >> (s - 1))  (UDIV34)
  QuotientAboveDividendShiftedByDivisorLessOne,
  // x != 1 - (x << (x - t))  (UDIV36)
  DividendNotOneLessShiftedDividend
};

// The remainder facts, in the order the refiner offers them.
enum class RemLemma
{
  // x = 0 -> t = 0  (UREM3)
  DividendZero,
  // s = x -> t = 0  (UREM5)
  DivisorEqualsDividend,
  // x <u s -> t = x  (UREM6)
  DividendBelowDivisor,
  // s <=u x <u 2s -> t = x - s. The remainder half of QuotientIsOne, ranked
  // with the three above because it likewise determines the result throughout
  // its premise rather than only bounding it.
  // s <=u x <u 2s -> t = x - s
  RemainderIsDifference,
  // x = x & (s | t | -s)  (UREM8)
  DividendWithinDivisorOrRemainder,
  // x >=u (t | (x & s))  (UREM9)
  DividendAboveRemainderOrAnd,
  // 1 != (t & ~(x | s))  (UREM10)
  RemainderOutsideOperandsNotOne,
  // t != (~x | -s)  (UREM11)
  RemainderNotOrOfComplements,
  // (t & (x | s)) >=u (t & 1)  (UREM12)
  RemainderInOperandsAboveLowBit,
  // x != (-x | -(~t))  (UREM13)
  DividendNotOrOfNegations,
  // (x + -s) >=u t  (UREM14)
  DifferenceAboveRemainder,
  // ((-s) xor (x | s)) >=u t  (UREM15)
  XorAboveRemainder
};

// The unconditional multiplication facts not already represented by STP's
// power-of-two, low-bit, trailing-zero and odd-inverse schemas. Each has two
// readings because multiplication is commutative but most synthesised
// expressions are not syntactically so.
enum class MulLemma
{
  // s = s << (x & (1 >> t))  (MUL8). Its only nontrivial reading is that an
  // odd x and a zero product force s to zero. The value predicate keeps this
  // spelling and the bit-blaster encodes the compact equivalent implication.
  FactorUnchangedByMaskedShift,
  // s != ~(t | (1 & (x | s)))  (MUL5)
  FactorNotNegatedProductOrLowBit,
  // (x & t) != (s | ~t)  (MUL6)
  FactorAndProductNotOr,
  // t != ((s | 1) << (t << x))  (MUL7)
  ProductNotOddFactorShiftedByShiftedProduct,
  // t >=u (1 & ((x & s) >> 1))  (MUL9)
  ProductAboveMaskedShiftedFactors,
  // x != (1 xor (x << (s xor t)))  (MUL10)
  FactorNotOneXorFactorShiftedByXor,
  // t != (1 | ~(x xor s))  (MUL11)
  ProductNotOneOrNegatedXor,
  // t != (~1 | (x xor s))  (MUL12)
  ProductNotHighOnesOrXor,
  // x != (x << (s + t)) - 1  (MUL13)
  FactorNotShiftedFactorLessOne,
  // x != 1 - (x << (s - t))  (MUL14)
  FactorNotOneLessShiftedFactor,
  // s != 1 + (s << (t - x))  (MUL15)
  FactorNotOnePlusShiftedFactor,
  // s != 1 - (s << (t - x))  (MUL16)
  FactorNotOneLessShiftedFactorReversed,
  // s != 1 + (s << (x - t))  (MUL17)
  FactorNotOnePlusShiftedFactorReversed,
  // t != (1 | (x + s))  (MUL18)
  ProductNotOneOrSum,
  // x != ~(x << (s + t))  (MUL19)
  FactorNotNegatedShiftedFactor
};

enum class AddLemma
{
  // s = 0 -> t = x  (ADD_ZERO)
  AddZero,
  // x = s -> t[0] = 0  (ADD_SAME)
  AddSame,
  // s = ~x -> t = ~0  (ADD_INV)
  AddInv,
  // msb(x) = msb(s) = 1 -> t <u (x & s)  (ADD_OVFL)
  AddOverflow,
  // msb(x) = msb(s) = 0 -> t >=u (x | s)  (ADD_NOOVFL)
  AddNoOverflow,
  // x & s = 0 -> t = x | s  (ADD_OR)
  AddOr,
  // 0 = x & s & t & 1  (ADD_REF6)
  LowBitsNotAllSet,
  // (1 & (s | t)) >=u (x & 1)  (ADD_REF7)
  LowBitNeedsOtherOrSum,
  // (1 & (x | s)) >=u (t & 1)  (ADD_REF9)
  SumLowBitNeedsAnOperand,
  // 1 != (t | ~(x & s))  (ADD_REF10)
  SumOrNegatedAndNotOne,
  // t != ~(t | (x & s))  (ADD_REF11)
  SumNotNegatedSumOrAnd,
  // 1 != (x | s | ~t)  (ADD_REF12)
  OperandsOrNegatedSumNotOne
};

// One row of a catalogue: everything about a fact except how to evaluate it
// and how to build it.
//
// `minWidth` and `excludedWidth` are the fact's domain. Several of these
// were synthesised rather than derived, and a synthesised fact is not
// automatically a theorem at every width -- `t >=u (1 & ((x & s) >> 1))`
// holds everywhere except at two bits, where both operands can carry bit one
// and the product still truncates to zero. A caller must not evaluate or
// install one outside its domain, and the tests check that each restriction
// is necessary rather than defensive. Zero excludes nothing.
template <typename Lemma> struct BVLemmaEntry
{
  Lemma lemma;
  const char* name;
  BVSchemaGroup group;
  unsigned minWidth;
  unsigned excludedWidth;
  // Whether this fact says the same thing with its two operands exchanged.
  //
  // Multiplication and addition are commutative but most synthesised
  // expressions are not syntactically so, which is why the chooser offers each
  // row in both readings. For a row that IS syntactically symmetric the second
  // reading is a fact the first already installed: it is evaluated, found to
  // hold, and skipped, on every call, for the life of the record -- fifteen of
  // the twenty-seven multiplication and addition rows.
  //
  // Only meaningful for those two catalogues. Division is not commutative and
  // its chooser offers one reading, so the flag is left false there and read
  // by nobody.
  //
  // The claim is checked rather than trusted:
  // BVAbstractionLemma.every_symmetric_fact_is_marked_and_no_other compares it
  // against the predicate over every triple below seven bits and by sampling
  // up to sixty-four, in both directions -- a row wrongly marked would lose a
  // reading that can fire, and a row wrongly unmarked is the waste this is
  // for. Unset is the safe default: it offers both readings, which is what
  // every row did before.
  bool symmetric = false;

  bool applicable(unsigned width) const
  {
    return width >= minWidth && width != excludedWidth;
  }
};

// The size of each catalogue. A constant rather than only a runtime count
// because the refiner packs one installed-lemma bit per entry into a 64-bit
// field alongside other state, and whether the registry still fits is a
// question a compiler should answer. BVLemmaCatalogue.cpp asserts each
// against its table.
constexpr unsigned BV_DIV_LEMMA_COUNT = 34;
constexpr unsigned BV_REM_LEMMA_COUNT = 12;
constexpr unsigned BV_MUL_LEMMA_COUNT = 15;
constexpr unsigned BV_ADD_LEMMA_COUNT = 12;

// The catalogues, in the order the refiner offers them. Measured entries
// come first, ranked by how often they fired on the qualification corpus;
// the unranked tail keeps its catalogue order, because there is no
// measurement to rank it by and an arbitrary reordering would only look like
// one.
DLL_PUBLIC const BVLemmaEntry<DivLemma>* divLemmaTable(unsigned& count);
DLL_PUBLIC const BVLemmaEntry<RemLemma>* remLemmaTable(unsigned& count);
DLL_PUBLIC const BVLemmaEntry<MulLemma>* mulLemmaTable(unsigned& count);
DLL_PUBLIC const BVLemmaEntry<AddLemma>* addLemmaTable(unsigned& count);

// The i'th row of a catalogue. The refiner carries a rank rather than an
// enumerator, because the rank is what its installed-lemma mask is indexed
// by, so this is the lookup it actually does.
DLL_PUBLIC const BVLemmaEntry<DivLemma>& divLemmaAt(unsigned index);
DLL_PUBLIC const BVLemmaEntry<RemLemma>& remLemmaAt(unsigned index);
DLL_PUBLIC const BVLemmaEntry<MulLemma>& mulLemmaAt(unsigned index);
DLL_PUBLIC const BVLemmaEntry<AddLemma>& addLemmaAt(unsigned index);

// The row for one fact, by name rather than by rank. Linear over a table of
// at most a few dozen; the refiner indexes by rank and never comes here.
DLL_PUBLIC const BVLemmaEntry<DivLemma>& divLemmaEntry(DivLemma lemma);
DLL_PUBLIC const BVLemmaEntry<RemLemma>& remLemmaEntry(RemLemma lemma);
DLL_PUBLIC const BVLemmaEntry<MulLemma>& mulLemmaEntry(MulLemma lemma);
DLL_PUBLIC const BVLemmaEntry<AddLemma>& addLemmaEntry(AddLemma lemma);

inline const char* divLemmaName(DivLemma l) { return divLemmaEntry(l).name; }
inline const char* remLemmaName(RemLemma l) { return remLemmaEntry(l).name; }
inline const char* mulLemmaName(MulLemma l) { return mulLemmaEntry(l).name; }
inline const char* addLemmaName(AddLemma l) { return addLemmaEntry(l).name; }

inline bool divLemmaApplicable(DivLemma l, unsigned w)
{
  return divLemmaEntry(l).applicable(w);
}
inline bool remLemmaApplicable(RemLemma l, unsigned w)
{
  return remLemmaEntry(l).applicable(w);
}
inline bool mulLemmaApplicable(MulLemma l, unsigned w)
{
  return mulLemmaEntry(l).applicable(w);
}
inline bool addLemmaApplicable(AddLemma l, unsigned w)
{
  return addLemmaEntry(l).applicable(w);
}

// Whether one of them holds of these three values. The refiner asks before
// installing -- a lemma the candidate already satisfies rules nothing out --
// and the tests ask to check the circuits say the same thing.
//
// Bit vectors, least significant bit first, all of the same width.
DLL_PUBLIC bool divLemmaHolds(DivLemma lemma, const std::vector<bool>& xBits,
                              const std::vector<bool>& sBits,
                              const std::vector<bool>& tBits);
DLL_PUBLIC bool remLemmaHolds(RemLemma lemma, const std::vector<bool>& xBits,
                              const std::vector<bool>& sBits,
                              const std::vector<bool>& tBits);
DLL_PUBLIC bool mulLemmaHolds(MulLemma lemma, const std::vector<bool>& xBits,
                              const std::vector<bool>& sBits,
                              const std::vector<bool>& tBits);
DLL_PUBLIC bool addLemmaHolds(AddLemma lemma, const std::vector<bool>& xBits,
                              const std::vector<bool>& sBits,
                              const std::vector<bool>& tBits);

} // namespace stp

#endif
