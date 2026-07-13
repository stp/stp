/***********
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
**********************/

// Tests for the interval transfer functions in UnsignedIntervalAnalysis.
// Each test builds a node, supplies intervals for its children, and checks
// the interval that dispatchToTransferFunctions() computes for the node.

#include "stp/STPManager/STPManager.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/Simplifier/UnsignedIntervalAnalysis.h"
#include "stp/Simplifier/UnsignedInterval.h"
#include <gtest/gtest.h>
#include <vector>

namespace
{

// BitVector_Boot must run before anything allocates constant bitvectors.
struct Boot
{
  Boot() { CONSTANTBV::BitVector_Boot(); }
};

struct Context
{
  Boot boot;
  stp::STPMgr mgr;
  SimplifyingNodeFactory snf;
  stp::UnsignedIntervalAnalysis analysis;

  Context() : snf(*(mgr.hashingNodeFactory), mgr), analysis(mgr)
  {
    mgr.defaultNodeFactory = &snf;
  }
};

stp::CBV makeCBV(unsigned width, unsigned value)
{
  stp::CBV r = CONSTANTBV::BitVector_Create(width, true);
  for (unsigned i = 0; i < width && i < 8 * sizeof(unsigned); i++)
    if ((value >> i) & 1)
      CONSTANTBV::BitVector_Bit_On(r, i);
  return r;
}

stp::UnsignedInterval* makeInterval(unsigned width, unsigned min, unsigned max)
{
  return new stp::UnsignedInterval(makeCBV(width, min), makeCBV(width, max));
}

void expectInterval(const stp::UnsignedInterval* result, unsigned width,
                    unsigned min, unsigned max)
{
  ASSERT_NE(result, nullptr);
  stp::CBV expectedMin = makeCBV(width, min);
  stp::CBV expectedMax = makeCBV(width, max);
  EXPECT_EQ(CONSTANTBV::BitVector_Lexicompare(result->minV, expectedMin), 0)
      << "minimum differs";
  EXPECT_EQ(CONSTANTBV::BitVector_Lexicompare(result->maxV, expectedMax), 0)
      << "maximum differs";
  CONSTANTBV::BitVector_Destroy(expectedMin);
  CONSTANTBV::BitVector_Destroy(expectedMax);
}

void cleanup(std::vector<const stp::UnsignedInterval*>& children,
             stp::UnsignedInterval* result)
{
  for (const auto* c : children)
    delete c;
  delete result;
}

// The hashing node factory builds the node without simplifying it, so the
// tests exercise exactly the kind they name.
stp::ASTNode makeTerm(Context& c, stp::Kind kind, unsigned w,
                      const stp::ASTNode& op0, const stp::ASTNode& op1)
{
  stp::ASTVec children;
  children.push_back(op0);
  children.push_back(op1);
  return c.mgr.hashingNodeFactory->CreateTerm(kind, w, children);
}

const unsigned width = 8;

// [10,20] / [2,4] is [10/4, 20/2] = [2,10].
TEST(UnsignedIntervalPropagators, UdivBoundsWithNonZeroDivisor)
{
  Context c;
  stp::ASTNode x = c.mgr.CreateSymbol("x", 0, width);
  stp::ASTNode y = c.mgr.CreateSymbol("y", 0, width);
  stp::ASTNode n = makeTerm(c, stp::BVDIV, width, x, y);

  std::vector<const stp::UnsignedInterval*> children = {
      makeInterval(width, 10, 20), makeInterval(width, 2, 4)};
  stp::UnsignedInterval* result =
      c.analysis.dispatchToTransferFunctions(n, children);

  expectInterval(result, width, 2, 10);
  cleanup(children, result);
}

// Dividing by the constant zero gives all ones.
TEST(UnsignedIntervalPropagators, UdivByConstantZero)
{
  Context c;
  stp::ASTNode x = c.mgr.CreateSymbol("x", 0, width);
  stp::ASTNode y = c.mgr.CreateSymbol("y", 0, width);
  stp::ASTNode n = makeTerm(c, stp::BVDIV, width, x, y);

  std::vector<const stp::UnsignedInterval*> children = {
      makeInterval(width, 10, 20), makeInterval(width, 0, 0)};
  stp::UnsignedInterval* result =
      c.analysis.dispatchToTransferFunctions(n, children);

  expectInterval(result, width, 255, 255);
  cleanup(children, result);
}

// [10,20] / [0,5]: division by zero gives all ones, so only the upper bound
// is lost. The lower bound 10/5 = 2 still holds.
TEST(UnsignedIntervalPropagators, UdivWhenDivisorMightBeZero)
{
  Context c;
  stp::ASTNode x = c.mgr.CreateSymbol("x", 0, width);
  stp::ASTNode y = c.mgr.CreateSymbol("y", 0, width);
  stp::ASTNode n = makeTerm(c, stp::BVDIV, width, x, y);

  std::vector<const stp::UnsignedInterval*> children = {
      makeInterval(width, 10, 20), makeInterval(width, 0, 5)};
  stp::UnsignedInterval* result =
      c.analysis.dispatchToTransferFunctions(n, children);

  expectInterval(result, width, 2, 255);
  cleanup(children, result);
}

// x mod [3,7] is less than the divisor's maximum.
TEST(UnsignedIntervalPropagators, UremBoundsWithNonZeroDivisor)
{
  Context c;
  stp::ASTNode x = c.mgr.CreateSymbol("x", 0, width);
  stp::ASTNode y = c.mgr.CreateSymbol("y", 0, width);
  stp::ASTNode n = makeTerm(c, stp::BVMOD, width, x, y);

  std::vector<const stp::UnsignedInterval*> children = {
      nullptr, makeInterval(width, 3, 7)};
  stp::UnsignedInterval* result =
      c.analysis.dispatchToTransferFunctions(n, children);

  expectInterval(result, width, 0, 6);
  cleanup(children, result);
}

// x mod 0 = x, so remainder by the constant zero is the identity.
TEST(UnsignedIntervalPropagators, UremByConstantZeroIsIdentity)
{
  Context c;
  stp::ASTNode x = c.mgr.CreateSymbol("x", 0, width);
  stp::ASTNode y = c.mgr.CreateSymbol("y", 0, width);
  stp::ASTNode n = makeTerm(c, stp::BVMOD, width, x, y);

  std::vector<const stp::UnsignedInterval*> children = {
      makeInterval(width, 5, 10), makeInterval(width, 0, 0)};
  stp::UnsignedInterval* result =
      c.analysis.dispatchToTransferFunctions(n, children);

  expectInterval(result, width, 5, 10);
  cleanup(children, result);
}

// [1,3] mod [10,20]: the dividend is always below the divisor, so the
// remainder is the dividend. Both bounds carry over, not just the maximum.
TEST(UnsignedIntervalPropagators, UremIsIdentityWhenDividendBelowDivisor)
{
  Context c;
  stp::ASTNode x = c.mgr.CreateSymbol("x", 0, width);
  stp::ASTNode y = c.mgr.CreateSymbol("y", 0, width);
  stp::ASTNode n = makeTerm(c, stp::BVMOD, width, x, y);

  std::vector<const stp::UnsignedInterval*> children = {
      makeInterval(width, 1, 3), makeInterval(width, 10, 20)};
  stp::UnsignedInterval* result =
      c.analysis.dispatchToTransferFunctions(n, children);

  expectInterval(result, width, 1, 3);
  cleanup(children, result);
}

// [0,5] mod [0,3]: if the divisor is zero the result is the dividend (<= 5),
// otherwise it is below the divisor (<= 2). So the result is at most 5.
TEST(UnsignedIntervalPropagators, UremWhenDivisorMightBeZero)
{
  Context c;
  stp::ASTNode x = c.mgr.CreateSymbol("x", 0, width);
  stp::ASTNode y = c.mgr.CreateSymbol("y", 0, width);
  stp::ASTNode n = makeTerm(c, stp::BVMOD, width, x, y);

  std::vector<const stp::UnsignedInterval*> children = {
      makeInterval(width, 0, 5), makeInterval(width, 0, 3)};
  stp::UnsignedInterval* result =
      c.analysis.dispatchToTransferFunctions(n, children);

  expectInterval(result, width, 0, 5);
  cleanup(children, result);
}

stp::ASTNode makeExtract(Context& c, const stp::ASTNode& child, unsigned high,
                         unsigned low)
{
  stp::ASTVec children;
  children.push_back(child);
  children.push_back(c.mgr.CreateBVConst(32, high));
  children.push_back(c.mgr.CreateBVConst(32, low));
  return c.mgr.hashingNodeFactory->CreateTerm(stp::BVEXTRACT, high - low + 1,
                                              children);
}

// Extracting [5:2] from a value that is at most 0x30 gives at most 0x30 >> 2.
TEST(UnsignedIntervalPropagators, ExtractUpperBound)
{
  Context c;
  stp::ASTNode x = c.mgr.CreateSymbol("x", 0, width);
  stp::ASTNode n = makeExtract(c, x, 5, 2);

  std::vector<const stp::UnsignedInterval*> children = {
      makeInterval(width, 0, 0x30), makeInterval(32, 5, 5),
      makeInterval(32, 2, 2)};
  stp::UnsignedInterval* result =
      c.analysis.dispatchToTransferFunctions(n, children);

  expectInterval(result, 4, 0, 12);
  cleanup(children, result);
}

// When no bits are discarded from the top, the minimum shifts down too.
TEST(UnsignedIntervalPropagators, ExtractBothBounds)
{
  Context c;
  stp::ASTNode x = c.mgr.CreateSymbol("x", 0, width);
  stp::ASTNode n = makeExtract(c, x, 5, 2);

  std::vector<const stp::UnsignedInterval*> children = {
      makeInterval(width, 0x10, 0x30), makeInterval(32, 5, 5),
      makeInterval(32, 2, 2)};
  stp::UnsignedInterval* result =
      c.analysis.dispatchToTransferFunctions(n, children);

  expectInterval(result, 4, 4, 12);
  cleanup(children, result);
}

// Extracting [3:0] from [0x00, 0xF0] wraps through the extract's width
// several times, so every result is reachable and nothing is known.
TEST(UnsignedIntervalPropagators, ExtractGivesNothingWhenTopBitsTruncated)
{
  Context c;
  stp::ASTNode x = c.mgr.CreateSymbol("x", 0, width);
  stp::ASTNode n = makeExtract(c, x, 3, 0);

  std::vector<const stp::UnsignedInterval*> children = {
      makeInterval(width, 0, 0xF0), makeInterval(32, 3, 3),
      makeInterval(32, 0, 0)};
  stp::UnsignedInterval* result =
      c.analysis.dispatchToTransferFunctions(n, children);

  EXPECT_EQ(result, nullptr);
  cleanup(children, result);
}

// [8,15] | [0,7]: OR is at least each operand, so at least 8. Neither
// operand has a bit above bit 3, so the result is at most 15.
TEST(UnsignedIntervalPropagators, BvorBounds)
{
  Context c;
  stp::ASTNode x = c.mgr.CreateSymbol("x", 0, width);
  stp::ASTNode y = c.mgr.CreateSymbol("y", 0, width);
  stp::ASTNode n = makeTerm(c, stp::BVOR, width, x, y);

  std::vector<const stp::UnsignedInterval*> children = {
      makeInterval(width, 8, 15), makeInterval(width, 0, 7)};
  stp::UnsignedInterval* result =
      c.analysis.dispatchToTransferFunctions(n, children);

  expectInterval(result, width, 8, 15);
  cleanup(children, result);
}

// OR with an unknown operand still keeps the other operand's minimum.
TEST(UnsignedIntervalPropagators, BvorMinimumWithUnknownChild)
{
  Context c;
  stp::ASTNode x = c.mgr.CreateSymbol("x", 0, width);
  stp::ASTNode y = c.mgr.CreateSymbol("y", 0, width);
  stp::ASTNode n = makeTerm(c, stp::BVOR, width, x, y);

  std::vector<const stp::UnsignedInterval*> children = {
      nullptr, makeInterval(width, 4, 7)};
  stp::UnsignedInterval* result =
      c.analysis.dispatchToTransferFunctions(n, children);

  expectInterval(result, width, 4, 255);
  cleanup(children, result);
}

// Extracting [2:0] from [0x44, 0x46]: the values agree above bit 2, so the
// low bits run from the minimum's to the maximum's without wrapping, even
// though set bits are discarded from the top.
TEST(UnsignedIntervalPropagators, ExtractExactWhenHighBitsAgree)
{
  Context c;
  stp::ASTNode x = c.mgr.CreateSymbol("x", 0, width);
  stp::ASTNode n = makeExtract(c, x, 2, 0);

  std::vector<const stp::UnsignedInterval*> children = {
      makeInterval(width, 0x44, 0x46), makeInterval(32, 2, 2),
      makeInterval(32, 0, 0)};
  stp::UnsignedInterval* result =
      c.analysis.dispatchToTransferFunctions(n, children);

  expectInterval(result, 3, 4, 6);
  cleanup(children, result);
}

// [1,3] << [1,2]: no set bit can be shifted out, so the bounds shift too.
TEST(UnsignedIntervalPropagators, LeftShiftBounds)
{
  Context c;
  stp::ASTNode x = c.mgr.CreateSymbol("x", 0, width);
  stp::ASTNode y = c.mgr.CreateSymbol("y", 0, width);
  stp::ASTNode n = makeTerm(c, stp::BVLEFTSHIFT, width, x, y);

  std::vector<const stp::UnsignedInterval*> children = {
      makeInterval(width, 1, 3), makeInterval(width, 1, 2)};
  stp::UnsignedInterval* result =
      c.analysis.dispatchToTransferFunctions(n, children);

  expectInterval(result, width, 2, 12);
  cleanup(children, result);
}

// Shifting an unknown value left by at least the width gives zero.
TEST(UnsignedIntervalPropagators, LeftShiftByWidthOrMoreIsZero)
{
  Context c;
  stp::ASTNode x = c.mgr.CreateSymbol("x", 0, width);
  stp::ASTNode y = c.mgr.CreateSymbol("y", 0, width);
  stp::ASTNode n = makeTerm(c, stp::BVLEFTSHIFT, width, x, y);

  std::vector<const stp::UnsignedInterval*> children = {
      nullptr, makeInterval(width, 8, 255)};
  stp::UnsignedInterval* result =
      c.analysis.dispatchToTransferFunctions(n, children);

  expectInterval(result, width, 0, 0);
  cleanup(children, result);
}

// [0x10,0x30] >>s [1,2]: the sign bit is clear, so it behaves like a
// logical shift: [0x10 >> 2, 0x30 >> 1].
TEST(UnsignedIntervalPropagators, SignedRightShiftOfNonNegative)
{
  Context c;
  stp::ASTNode x = c.mgr.CreateSymbol("x", 0, width);
  stp::ASTNode y = c.mgr.CreateSymbol("y", 0, width);
  stp::ASTNode n = makeTerm(c, stp::BVSRSHIFT, width, x, y);

  std::vector<const stp::UnsignedInterval*> children = {
      makeInterval(width, 0x10, 0x30), makeInterval(width, 1, 2)};
  stp::UnsignedInterval* result =
      c.analysis.dispatchToTransferFunctions(n, children);

  expectInterval(result, width, 4, 24);
  cleanup(children, result);
}

// [0x80,0xF0] >>s 1: the sign bit is set, so ones are shifted in.
TEST(UnsignedIntervalPropagators, SignedRightShiftOfNegative)
{
  Context c;
  stp::ASTNode x = c.mgr.CreateSymbol("x", 0, width);
  stp::ASTNode y = c.mgr.CreateSymbol("y", 0, width);
  stp::ASTNode n = makeTerm(c, stp::BVSRSHIFT, width, x, y);

  std::vector<const stp::UnsignedInterval*> children = {
      makeInterval(width, 0x80, 0xF0), makeInterval(width, 1, 1)};
  stp::UnsignedInterval* result =
      c.analysis.dispatchToTransferFunctions(n, children);

  expectInterval(result, width, 0xC0, 0xF8);
  cleanup(children, result);
}

// [0x70,0x90] >>s 4 crosses the sign boundary: the minimum comes from the
// non-negative end, the maximum from the negative end.
TEST(UnsignedIntervalPropagators, SignedRightShiftCrossingSign)
{
  Context c;
  stp::ASTNode x = c.mgr.CreateSymbol("x", 0, width);
  stp::ASTNode y = c.mgr.CreateSymbol("y", 0, width);
  stp::ASTNode n = makeTerm(c, stp::BVSRSHIFT, width, x, y);

  std::vector<const stp::UnsignedInterval*> children = {
      makeInterval(width, 0x70, 0x90), makeInterval(width, 4, 4)};
  stp::UnsignedInterval* result =
      c.analysis.dispatchToTransferFunctions(n, children);

  expectInterval(result, width, 0x07, 0xF9);
  cleanup(children, result);
}

// [0,5] ^ [0,3]: neither operand has a bit above bit 2, so the XOR is at
// most 7.
TEST(UnsignedIntervalPropagators, BvxorUpperBound)
{
  Context c;
  stp::ASTNode x = c.mgr.CreateSymbol("x", 0, width);
  stp::ASTNode y = c.mgr.CreateSymbol("y", 0, width);
  stp::ASTNode n = makeTerm(c, stp::BVXOR, width, x, y);

  std::vector<const stp::UnsignedInterval*> children = {
      makeInterval(width, 0, 5), makeInterval(width, 0, 3)};
  stp::UnsignedInterval* result =
      c.analysis.dispatchToTransferFunctions(n, children);

  expectInterval(result, width, 0, 7);
  cleanup(children, result);
}

} // namespace
