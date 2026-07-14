/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen, Dan Liew
 *
 * BEGIN DATE: November, 2005
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

#include "stp/AST/AST.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/constantBitP/ConstantBitP_TransferFunctions.h"
#include "stp/Simplifier/constantBitP/ConstantBitP_Utility.h"
#include "stp/Simplifier/constantBitP/MultiplicationStats.h"
#include "stp/Simplifier/constantBitP/multiplication/ColumnCounts.h"
#include "stp/Simplifier/constantBitP/multiplication/ColumnStats.h"
#include <cstdint>
#include <set>
#include <stdexcept>
// Multiply.

using namespace stp;

namespace simplifier
{
namespace constantBitP
{
using std::endl;
using std::pair;
using std::set;

const bool debug_multiply = false;
std::ostream& log = std::cerr;

#if 0
// The maximum size of the carry into a column for MULTIPLICATION
    int
    maximumCarryInForMultiplication(int column)
      {
      int result = 0;
      int currIndex = 0;

      while (currIndex < column)
        {
        currIndex++;
        result = (result + currIndex) / 2;
        }

      return result;
      }
#endif

static inline int popcount64(uint64_t v);
static inline uint64_t rightShiftedWord(const uint64_t* m, unsigned words,
                                        unsigned s, unsigned j);
static inline int convolutionAt(const uint64_t* a, const uint64_t* revB,
                                unsigned words, unsigned width, unsigned j);

// The fixed-to-one and unfixed masks of both operands, packed into words so
// a column's pair-category counts are shifted-window popcounts rather than
// a per-column scan. Rebuild after either operand changes.
struct PairMasks
{
  static const unsigned INLINE_WORDS = 8; // up to 512 bits on the stack.
  uint64_t stackBuf[4 * INLINE_WORDS];
  std::vector<uint64_t> heapBuf;
  uint64_t* xOne;
  uint64_t* xUnfixed;
  uint64_t* revYOne; // y, bit-reversed.
  uint64_t* revYUnfixed;
  unsigned words;

  void build(const FixedBits& x, const FixedBits& y)
  {
    const unsigned width = x.getWidth();
    words = (width + 63) / 64;
    uint64_t* buf = stackBuf;
    if (words > INLINE_WORDS)
    {
      heapBuf.assign(4 * words, 0);
      buf = heapBuf.data();
    }
    else
      for (unsigned t = 0; t < 4 * words; t++)
        buf[t] = 0;
    xOne = buf;
    xUnfixed = buf + words;
    revYOne = buf + 2 * words;
    revYUnfixed = buf + 3 * words;

    widthCached = width;
    for (unsigned i = 0; i < width; i++)
    {
      if (!x.isFixed(i))
        xUnfixed[i >> 6] |= (uint64_t)1 << (i & 63);
      else if (x.getValue(i))
        xOne[i >> 6] |= (uint64_t)1 << (i & 63);

      const unsigned r = width - 1 - i;
      if (!y.isFixed(i))
        revYUnfixed[r >> 6] |= (uint64_t)1 << (r & 63);
      else if (y.getValue(i))
        revYOne[r >> 6] |= (uint64_t)1 << (r & 63);
    }
  }

  // Bit i of x was just fixed: leave the unfixed set, join the ones if set.
  void xFixed(unsigned i, bool value)
  {
    xUnfixed[i >> 6] &= ~((uint64_t)1 << (i & 63));
    if (value)
      xOne[i >> 6] |= (uint64_t)1 << (i & 63);
  }

  void yFixed(unsigned i, bool value)
  {
    const unsigned r = widthCached - 1 - i;
    revYUnfixed[r >> 6] &= ~((uint64_t)1 << (r & 63));
    if (value)
      revYOne[r >> 6] |= (uint64_t)1 << (r & 63);
  }

  unsigned widthCached;
};

Result fixIfCanForMultiplication(vector<FixedBits*>& children,
                                 const unsigned index,
                                 const int aspirationalSum, PairMasks* pm)
{
  assert(index < children[0]->getWidth());

  FixedBits& x = *children[0];
  FixedBits& y = *children[1];

  // The counts ColumnStats(x, y, index) walks the column for, but from the
  // packed masks: a pair contributes "ones" when both operands are fixed
  // to one, "one fixed" when one is fixed to one and the other unfixed,
  // and "unfixed" when both are unfixed. (Pairs with a fixed zero are the
  // remainder, and aren't needed here.) Short columns are cheaper to scan
  // directly.
  const unsigned width = x.getWidth();
  int columnOnes, columnUnfixed, columnOneFixed;
  if (pm == NULL || index < 16)
  {
    ColumnStats cs(x, y, index);
    columnOnes = cs.columnOnes;
    columnUnfixed = cs.columnUnfixed;
    columnOneFixed = cs.columnOneFixed;
  }
  else
  {
    columnOnes = convolutionAt(pm->xOne, pm->revYOne, pm->words, width, index);
    columnUnfixed =
        convolutionAt(pm->xUnfixed, pm->revYUnfixed, pm->words, width, index);
    columnOneFixed =
        convolutionAt(pm->xOne, pm->revYUnfixed, pm->words, width, index) +
        convolutionAt(pm->xUnfixed, pm->revYOne, pm->words, width, index);
  }

  Result result = NO_CHANGE;

  // only one of the conditionals can run.
  bool run = false;

  // We need every value that is unfixed to be set to one.
  if (aspirationalSum == columnOnes + columnOneFixed + columnUnfixed &&
      ((columnOneFixed + columnUnfixed) > 0))
  {
    for (unsigned i = 0; i <= index; i++)
    {
      // If y is unfixed, and it's not anded with zero.
      if (!y.isFixed(i) && !(x.isFixed(index - i) && !x.getValue(index - i)))
      {
        y.setFixed(i, true);
        y.setValue(i, true);
        if (pm)
          pm->yFixed(i, true);
        result = CHANGED;
      }

      if (!x.isFixed(index - i) && !(y.isFixed(i) && !y.getValue(i)))
      {
        x.setFixed(index - i, true);
        x.setValue(index - i, true);
        if (pm)
          pm->xFixed(index - i, true);
        result = CHANGED;
      }
    }
    assert(result == CHANGED);
    run = true;
  }

  // We have all the ones that we need already. (thanks). Set everything we can
  // to zero.
  if (aspirationalSum == columnOnes &&
      (columnUnfixed > 0 || columnOneFixed > 0))
  {
    assert(!run);
    for (unsigned i = 0; i <= index; i++)
    {
      if (!y.isFixed(i) && x.isFixed(index - i) &&
          x.getValue(index - i)) // one fixed.

      {
        y.setFixed(i, true);
        y.setValue(i, false);
        if (pm)
          pm->yFixed(i, false);
        result = CHANGED;
      }

      if (!x.isFixed(index - i) && y.isFixed(i) &&
          y.getValue(i)) // one fixed other way.
      {
        x.setFixed(index - i, true);
        x.setValue(index - i, false);
        if (pm)
          pm->xFixed(index - i, false);
        result = CHANGED;
      }
    }
  }
  if (debug_multiply && result == CONFLICT)
    log << "CONFLICT" << endl;

  return result;
}

static inline int popcount64(uint64_t v)
{
#ifdef _MSC_VER
  return (int)__popcnt64(v);
#else
  return __builtin_popcountll(v);
#endif
}

// Word `j` of (m >> s), for a `words`-long array.
static inline uint64_t rightShiftedWord(const uint64_t* m, unsigned words,
                                        unsigned s, unsigned j)
{
  const unsigned word = j + (s >> 6);
  const unsigned bit = s & 63;
  if (word >= words)
    return 0;
  uint64_t r = m[word] >> bit;
  if (bit != 0 && word + 1 < words)
    r |= m[word + 1] << (64 - bit);
  return r;
}

// The number of pairs i + k == j with a[i] and revB[width-1-k] both set,
// i.e. the boolean convolution of a and (un-reversed) b at column j.
static inline int convolutionAt(const uint64_t* a, const uint64_t* revB,
                                unsigned words, unsigned width, unsigned j)
{
  int count = 0;
  const unsigned s = width - 1 - j;
  for (unsigned t = 0; t < words; t++)
  {
    const uint64_t aw = a[t];
    if (aw != 0)
      count += popcount64(aw & rightShiftedWord(revB, words, s, t));
  }
  return count;
}

// Uses the zeroes / ones present adjust the column counts:
//   columnH[j] -= #{i <= j : y[i] fixed to zero}
//              +  #{i <= j : x[i] fixed to zero and y[j-i] not fixed to zero}
//   columnL[j] += #{i + k == j : x[i] and y[k] both fixed to one}
// The counts come from running prefix sums and two boolean convolutions
// evaluated as shifted-window popcounts over packed words.
Result adjustColumns(const FixedBits& x, const FixedBits& y, int* columnL,
                     int* columnH)
{
  const unsigned bitWidth = x.getWidth();
  const unsigned words = (bitWidth + 63) / 64;

  const unsigned INLINE_WORDS = 8; // up to 512 bits on the stack.
  uint64_t stackBuf[4 * INLINE_WORDS];
  std::vector<uint64_t> heapBuf;
  uint64_t* buf = stackBuf;
  if (words > INLINE_WORDS)
  {
    heapBuf.resize(4 * words);
    buf = heapBuf.data();
  }
  uint64_t* xFF = buf;                // x fixed to zero.
  uint64_t* xOne = buf + words;       // x fixed to one.
  uint64_t* revYFF = buf + 2 * words; // y fixed to zero, bit-reversed.
  uint64_t* revYOne = buf + 3 * words;
  for (unsigned t = 0; t < 4 * words; t++)
    buf[t] = 0;

  for (unsigned i = 0; i < bitWidth; i++)
  {
    if (x.isFixed(i))
    {
      if (x.getValue(i))
        xOne[i >> 6] |= (uint64_t)1 << (i & 63);
      else
        xFF[i >> 6] |= (uint64_t)1 << (i & 63);
    }
    if (y.isFixed(i))
    {
      const unsigned r = bitWidth - 1 - i;
      if (y.getValue(i))
        revYOne[r >> 6] |= (uint64_t)1 << (r & 63);
      else
        revYFF[r >> 6] |= (uint64_t)1 << (r & 63);
    }
  }

  bool anyXFF = false, anyYFF = false, anyXOne = false, anyYOne = false;
  for (unsigned t = 0; t < words; t++)
  {
    anyXFF |= xFF[t] != 0;
    anyXOne |= xOne[t] != 0;
    anyYFF |= revYFF[t] != 0;
    anyYOne |= revYOne[t] != 0;
  }
  const bool ffPairsPossible = anyXFF && anyYFF;
  const bool onePairsPossible = anyXOne && anyYOne;
  if (!anyXFF && !anyYFF && !onePairsPossible)
    return NO_CHANGE; // nothing fixed that could adjust any count.

  int xZeroes = 0, yZeroes = 0;
  for (unsigned j = 0; j < bitWidth; j++)
  {
    // Running prefix counts of the fixed-to-zero bits at or below j.
    const unsigned r = bitWidth - 1 - j;
    if ((revYFF[r >> 6] >> (r & 63)) & 1)
      yZeroes++;
    if ((xFF[j >> 6] >> (j & 63)) & 1)
      xZeroes++;

    int decrement = yZeroes + xZeroes;
    if (ffPairsPossible)
      decrement -= convolutionAt(xFF, revYFF, words, bitWidth, j);
    if (decrement != 0)
      columnH[j] -= decrement;
    if (onePairsPossible)
    {
      const int onePairs = convolutionAt(xOne, revYOne, words, bitWidth, j);
      if (onePairs != 0)
        columnL[j] += onePairs;
    }
  }
  return NO_CHANGE;
}

Result setToZero(FixedBits& y, unsigned from, unsigned to)
{
  Result r = NO_CHANGE;
  assert(from <= to);
  assert(to <= y.getWidth());

  /***NB < to ***/
  for (unsigned i = from; i < to; i++)
  {
    if (y[i] == '*')
    {
      y.setFixed(i, true);
      y.setValue(i, false);
      r = CHANGED;
    }
    else if (y[i] == '1')
      return CONFLICT;
  }
  return r;
}

// Finds the leading one in each of the two inputs.
// If this position is i & j, then in the output
// there can be no ones higher than i+j+1.
Result useLeadingZeroesToFix_OLD(FixedBits& x, FixedBits& y, FixedBits& output)
{
  // Count the leading zeroes on x & y.
  // Output should have about that many..
  int xTop = x.topmostPossibleLeadingOne();
  int yTop = y.topmostPossibleLeadingOne();

  int maxOutputOneFromInputs = xTop + yTop + 1;

  for (int i = output.getWidth() - 1; i > maxOutputOneFromInputs; i--)
    if (!output.isFixed(i))
    {
      output.setFixed(i, true);
      output.setValue(i, false);
    }
    else
    {
      if (output.getValue(i))
        return CONFLICT;
    }

  return NOT_IMPLEMENTED;
}

Result useLeadingZeroesToFix(FixedBits& x, FixedBits& y, FixedBits& output)
{
// To check that the new implementation subsumes the old.
#ifndef NDEBUG
  FixedBits x_p = x;
  FixedBits y_p = y;
  FixedBits o_p = output;
  useLeadingZeroesToFix_OLD(x_p, y_p, o_p);
#endif

  const int bitWidth = x.getWidth();
  CBV x_c = CONSTANTBV::BitVector_Create(2 * bitWidth, true);
  CBV y_c = CONSTANTBV::BitVector_Create(2 * bitWidth, true);

  for (int i = 0; i < bitWidth; i++)
  {
    if (x[i] == '1' || x[i] == '*')
      CONSTANTBV::BitVector_Bit_On(x_c, i);

    if (y[i] == '1' || y[i] == '*')
      CONSTANTBV::BitVector_Bit_On(y_c, i);
  }

  stp::CBV result = CONSTANTBV::BitVector_Create(2 * bitWidth + 1, true);
  CONSTANTBV::ErrCode ec = CONSTANTBV::BitVector_Multiply(result, x_c, y_c);
  assert(ec == CONSTANTBV::ErrCode_Ok);

  for (int j = (2 * bitWidth) - 1; j >= 0; j--)
  {
    if (CONSTANTBV::BitVector_bit_test(result, j))
      break;
    if (j < bitWidth)
    {
      if (!output.isFixed(j))
      {
        output.setFixed(j, true);
        output.setValue(j, false);
      }
      else
      {
        if (output.getValue(j))
        {
          CONSTANTBV::BitVector_Destroy(x_c);
          CONSTANTBV::BitVector_Destroy(y_c);
          CONSTANTBV::BitVector_Destroy(result);
          return CONFLICT;
        }
      }
    }
  }

#ifndef NDEBUG
  // Assert the new implementation fixes more than the old.
  assert(FixedBits::in(x, x_p));
  assert(FixedBits::in(y, y_p));
  assert(FixedBits::in(output, o_p));
#endif

  CONSTANTBV::BitVector_Destroy(x_c);
  CONSTANTBV::BitVector_Destroy(y_c);
  CONSTANTBV::BitVector_Destroy(result);

  return NOT_IMPLEMENTED;
}

Result trailingOneReasoning_OLD(FixedBits& x, FixedBits& y, FixedBits& output);

// Remove from x any trailing "boths", that don't have support in y and output.
Result trailingOneReasoning(FixedBits& x, FixedBits& y, FixedBits& output)
{
  Result r = NO_CHANGE;

  const int bitwidth = output.getWidth();

  const int y_min = y.minimum_trailingOne();
  const int y_max = y.maximum_trailingOne();

  const int output_max = output.maximum_trailingOne();

  for (int i = 0; i < bitwidth; i++)
  {
    if (x[i] == '0')
      continue;

    if (x[i] == '1')
      break;

    for (int j = y_min; j <= std::min(y_max, output_max); j++)
    {
      if (j + i >= bitwidth || (y[j] != '0' && output[i + j] != '0'))
        return r;
    }

    x.setFixed(i, true);
    x.setValue(i, false);
    r = CHANGED;
  }

#ifndef NDEBUG
  // Check that the old implementation is subsumed. On copies, because it
  // fixes bits when it fires, and nothing should mutate inside assert().
  FixedBits x_c(x), y_c(y), o_c(output);
  assert(trailingOneReasoning_OLD(x_c, y_c, o_c) == NO_CHANGE);
#endif
  return r;
}

// Remove from x any trailing "boths", that don't have support in y and output.
Result trailingOneReasoning_OLD(FixedBits& x, FixedBits& y, FixedBits& output)
{
  Result r = NO_CHANGE;

  const int bitwidth = output.getWidth();

  const int x_min = x.minimum_trailingOne();
  const int x_max = x.maximum_trailingOne();

  const int y_min = y.minimum_trailingOne();
  const int y_max = y.maximum_trailingOne();

  int output_max = output.maximum_trailingOne();

  bool done = false;
  for (int i = x_min; i <= std::min(x_max, bitwidth - 1); i++)
  {
    if (x[i] == '1')
      break;

    if (x[i] == '0')
      continue;

    assert(!done);
    for (int j = y_min; j <= std::min(y_max, output_max); j++)
    {
      if (j + i >= bitwidth || (y[j] != '0' && output[i + j] != '0'))
      {
        done = true;
        break;
      }
    }
    if (!done)
    {
      x.setFixed(i, true);
      x.setValue(i, false);
      r = CHANGED;
    }
    else
      break;
  }
  return r;
}

// if x has n trailing zeroes, and y has m trailing zeroes, then the output has
// n+m trailing zeroes.
// if the output has n trailing zeroes and x has p trailing zeroes, then y has
// n-p trailing zeroes.
Result useTrailingZeroesToFix(FixedBits& x, FixedBits& y, FixedBits& output)
{
  const int bitwidth = output.getWidth();

  Result r0 = trailingOneReasoning(x, y, output);
  Result r1 = trailingOneReasoning(y, x, output);

  // Calculate the minimum number of trailing zeroes in the operands,
  // the result has a >= number.
  int min =
      x.minimum_numberOfTrailingZeroes() + y.minimum_numberOfTrailingZeroes();
  min = std::min(min, bitwidth);

  Result r2 = setToZero(output, 0, min);
  if (r2 == CONFLICT)
    return CONFLICT;

  if (r0 == CHANGED || r1 == CHANGED || r2 == CHANGED)
    return CHANGED;

  return NO_CHANGE;
}

Result useInversesToSolve(FixedBits& x, FixedBits& y, FixedBits& output,
                          stp::STPMgr* bm)
{
  // Position of the first unfixed value +1.
  int xBottom = x.leastUnfixed();
  int yBottom = y.leastUnfixed();
  int outputBottom = output.leastUnfixed();

  int invertCount = std::min(std::max(xBottom, yBottom), outputBottom);

  if (invertCount == 0)
    return NO_CHANGE;

  FixedBits* toInvert;
  FixedBits* toSet;

  if (xBottom > yBottom)
  {
    toInvert = &x;
    toSet = &y;
  }
  else
  {
    toInvert = &y;
    toSet = &x;
  }

  invertCount--; // position of the least fixed.

  const unsigned int width = invertCount + 1;
  stp::CBV toInvertCBV = toInvert->GetBVConst(invertCount, 0);

  // cerr << "value to invert:" << *toInvertCBV << " ";

  Result status = NOT_IMPLEMENTED;

  if (CONSTANTBV::BitVector_bit_test(toInvertCBV, 0))
  {

    if (debug_multiply)
      cerr << "Value to Invert:" << *toInvertCBV << endl;

    SubstitutionMap sm (bm);
    Simplifier simplifier(bm, &sm );

    stp::CBV inverse =
        simplifier.MultiplicativeInverse(bm->CreateBVConst(toInvertCBV, width))
            .GetBVConst();
    stp::CBV toMultiplyBy = output.GetBVConst(invertCount, 0);

    stp::CBV toSetEqualTo = CONSTANTBV::BitVector_Create(2 * (width), true);

    CONSTANTBV::ErrCode ec =
        CONSTANTBV::BitVector_Multiply(toSetEqualTo, inverse, toMultiplyBy);
    if (ec != CONSTANTBV::ErrCode_Ok)
    {
      assert(false);
      throw 2314231;
    }

    if (false && debug_multiply)
    {
      cerr << x << "*" << y << "=" << output << endl;
      cerr << "Invert bit count" << invertCount << endl;
      cerr << "To set" << *toSet;
      cerr << "To set equal to:" << *toSetEqualTo << endl;
    }

    // Write in the value.
    for (int i = 0; i <= invertCount; i++)
    {
      bool expected = CONSTANTBV::BitVector_bit_test(toSetEqualTo, i);

      if (toSet->isFixed(i) && (toSet->getValue(i) ^ expected))
      {
        status = CONFLICT;
      }
      else if (!toSet->isFixed(i))
      {
        toSet->setFixed(i, true);
        toSet->setValue(i, expected);
      }
    }

    // Don't delete the "inverse" because it's reference counted by the ASTNode.

    CONSTANTBV::BitVector_Destroy(toSetEqualTo);
    CONSTANTBV::BitVector_Destroy(toMultiplyBy);

    // cerr << "result" << *toSet;
  }
  else
    CONSTANTBV::BitVector_Destroy(toInvertCBV);

  // cerr << endl;
  return status;
}

// Use trailing fixed to fix.
// Create two constants and multiply them out fixing the result.
Result useTrailingFixedToFix(FixedBits& x, FixedBits& y, FixedBits& output)
{
  int xBottom = x.leastUnfixed();
  int yBottom = y.leastUnfixed();

  int minV = std::min(xBottom, yBottom);

  if (minV == 0)
    return NO_CHANGE; // nothing determined.

  // It gives the position of the first non-fixed. We want the last fixed.
  minV--;

  // The multiply doesn't like to overflow. So we widen the output.
  stp::CBV xCBV = x.GetBVConst(minV, 0);
  stp::CBV yCBV = y.GetBVConst(minV, 0);
  stp::CBV result = CONSTANTBV::BitVector_Create(2 * (minV + 1), true);

  CONSTANTBV::ErrCode ec = CONSTANTBV::BitVector_Multiply(result, xCBV, yCBV);
  if (ec != CONSTANTBV::ErrCode_Ok)
  {
    assert(false);
    throw 2314231;
  }

  Result status = NOT_IMPLEMENTED;
  for (int i = 0; i <= minV; i++)
  {
    bool expected = CONSTANTBV::BitVector_bit_test(result, i);

    if (output.isFixed(i) && (output.getValue(i) ^ expected))
      status = CONFLICT;
    else if (!output.isFixed(i))
    {
      output.setFixed(i, true);
      output.setValue(i, expected);
    }
  }

  CONSTANTBV::BitVector_Destroy(xCBV);
  CONSTANTBV::BitVector_Destroy(yCBV);
  CONSTANTBV::BitVector_Destroy(result);

  return status;
}

void printColumns(signed* sumL, signed* sumH, int bitWidth)
{
  for (int i = 0; i < bitWidth; i++)
  {
    log << sumL[bitWidth - 1 - i] << " ";
  }
  log << endl;
  for (int i = 0; i < bitWidth; i++)
  {
    log << sumH[bitWidth - 1 - i] << " ";
  }
  log << endl;
}

Result bvMultiplyBothWays(vector<FixedBits*>& children, FixedBits& output,
                          stp::STPMgr* bm, MultiplicationStats* ms)
{
  FixedBits& x = *children[0];
  FixedBits& y = *children[1];

  assert(x.getWidth() == y.getWidth());
  assert(x.getWidth() == output.getWidth());

  const unsigned bitWidth = x.getWidth();

  if (debug_multiply)
    cerr << "======================" << endl;

  if (debug_multiply)
  {
    cerr << "Initial Fixing";
    cerr << x << "*";
    cerr << y << "=";
    cerr << output << endl;
  }

  Result r = useTrailingZeroesToFix(x, y, output);
  if (CONFLICT == r)
    return r;

  // On the heap: bitWidth is unbounded, and this used to alloca inside the
  // loop, which only returns the stack space when the function exits. The
  // ColumnCounts constructor re-initialises the arrays each iteration.
  std::vector<signed> columnH_store(bitWidth); // max. no of true partial products.
  std::vector<signed> columnL_store(bitWidth); // minimum ""  ""
  std::vector<signed> sumH_store(bitWidth);
  std::vector<signed> sumL_store(bitWidth);

  bool changed = true;
  while (changed)
  {
    changed = false;
    signed* columnH = columnH_store.data();
    signed* columnL = columnL_store.data();
    signed* sumH = sumH_store.data();
    signed* sumL = sumL_store.data();
    ColumnCounts cc(columnH, columnL, sumH, sumL, bitWidth, output);

    // Use the number of zeroes and ones in a column to update the possible
    // counts.
    adjustColumns(x, y, columnL, columnH);

    cc.rebuildSums();
    Result r = cc.fixedPoint();

    if (r == CONFLICT)
      return CONFLICT;

    r = NO_CHANGE;

    // If any of the sums have a cardinality of 1. Set the result.
    for (unsigned column = 0; column < bitWidth; column++)
    {
      if (cc.sumL[column] == cc.sumH[column])
      {
        //(1) If the output has a known value. Set the output.
        bool newValue = !(sumH[column] % 2 == 0);
        if (!output.isFixed(column))
        {
          output.setFixed(column, true);
          output.setValue(column, newValue);
          r = CHANGED;
        }
        else if (output.getValue(column) != newValue)
          return CONFLICT;
      }
    }

    if (CHANGED == r)
      changed = true;

    // The packed column stats only pay off past one word; at 64 bits and
    // below the direct scan is cheaper, so bvmul at common widths keeps
    // the original path while the division machinery (double width)
    // benefits.
    PairMasks pm;
    bool masksValid = false; // built lazily: many passes trigger no column.
    const bool usePacked = bitWidth > 64;
    for (unsigned column = 0; column < bitWidth; column++)
    {
      if (cc.columnL[column] == cc.columnH[column])
      {
        if (usePacked && !masksValid)
        {
          pm.build(x, y);
          masksValid = true;
        }

        //(2) Knowledge of the sum may fix the operands.
        Result tempResult = fixIfCanForMultiplication(
            children, column, cc.columnH[column], usePacked ? &pm : NULL);

        if (CONFLICT == tempResult)
          return CONFLICT;

        if (CHANGED == tempResult)
          r = CHANGED; // the masks were updated incrementally.
      }
    }

    if (debug_multiply)
    {
      cerr << "At end";
      cerr << "x:" << x << endl;
      cerr << "y:" << y << endl;
      cerr << "output:" << output << endl;
    }

    assert(CONFLICT != r);

    if (CHANGED == r)
      changed = true;

    if (ms != NULL)
    {
      *ms = MultiplicationStats(bitWidth, cc.columnL, cc.columnH, cc.sumL,
                                cc.sumH);
      ms->x = *children[0];
      ms->y = *children[1];
      ms->r = output;
    }

    if (changed)
    {
      useTrailingZeroesToFix(x, y, output);
      //  if (r == NO_CHANGE)
      //    changed= false;
    }
  }

  if (children[0]->isTotallyFixed() && children[1]->isTotallyFixed())
  {
    assert(output.isTotallyFixed());
  }

// The below assertions are for performance only. It's not maximally precise
// anyway!!!

#ifndef NDEBUG
  if (r != CONFLICT)
  {
    FixedBits x_c(x), y_c(y), o_c(output);

    // These are subsumed by the consistency over the columns..
    useTrailingFixedToFix(x_c, y_c, o_c);
    useLeadingZeroesToFix(x_c, y_c, o_c);
    useInversesToSolve(x_c, y_c, o_c, bm);

    // This one should have been called to fixed point!
    useTrailingZeroesToFix(x_c, y_c, o_c);

    if (!FixedBits::equals(x_c, x) || !FixedBits::equals(y_c, y) ||
        !FixedBits::equals(o_c, output))
    {
      cerr << x << y << output << endl;
      cerr << x_c << y_c << o_c << endl;
      assert(false);
    }
  }
#endif

  return NOT_IMPLEMENTED;
}
}
}
