/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: August 2026
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

// A constant's source sort is part of its identity, so a floating-point or
// rounding-mode constant interns apart from the plain bitvector constant
// holding the same bits. STP's older code could assume the converse of
// "same node implies same value" -- that distinct constant nodes denote
// distinct values -- and that assumption is now wrong.
//
// The unsound direction is the one that proves *distinctness*: an array
// index rule that skips a write because the two index constants are
// different nodes reads the wrong cell. Every such site has to compare bits
// through constantsSameBits. These tests build the collision explicitly and
// then drive each decision site over it, so that a site which reverts to
// node identity fails here rather than in a fuzz campaign.

#include "stp/AST/AST.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/FloatBlaster/rounding_modes.h"

#include <gtest/gtest.h>

using namespace stp;

namespace
{

struct Fixture
{
  STPMgr mgr;
  SimplifyingNodeFactory snf;
  SubstitutionMap sm;
  Simplifier simp;

  Fixture() : snf(*(mgr.hashingNodeFactory), mgr), sm(&mgr), simp(&mgr, &sm)
  {
    mgr.defaultNodeFactory = &snf;
  }

  NodeFactory& nf() { return snf; }

  // 0x3F800000 is 1.0f, and is also just a 32-bit number someone may write.
  // The two intern apart, because a constant's source sort is part of its
  // identity.
  ASTNode plain() { return mgr.CreateBVConst(32, 0x3F800000u); }
  ASTNode typed() { return mgr.CreateFPConst(plain(), 8, 24); }
};

} // namespace

TEST(ConstantIdentity, the_collision_exists_at_all)
{
  Fixture f;
  const ASTNode typed = f.typed();
  const ASTNode plain = f.plain();

  // If these ever become the same node the rest of the file is vacuous, so
  // assert the premise rather than assume it.
  EXPECT_NE(typed, plain);
  EXPECT_EQ(BVCONST, typed.GetKind());
  EXPECT_EQ(BVCONST, plain.GetKind());
  EXPECT_EQ(typed.GetValueWidth(), plain.GetValueWidth());
  EXPECT_TRUE(constantsSameBits(typed, plain));
}

TEST(ConstantIdentity, rounding_mode_constants_collide_with_plain_ones)
{
  Fixture f;
  // The modes are one-hot, so RNE is 5-bit 1 -- a bit pattern any bitvector
  // problem may also hold.
  const ASTNode rne =
      f.mgr.CreateRMConst(symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);
  const ASTNode bits =
      f.mgr.CreateBVConst(5, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);

  EXPECT_NE(rne, bits);
  EXPECT_TRUE(constantsSameBits(rne, bits));
}

// Equality of two constants is decided on bits, not on node identity.
TEST(ConstantIdentity, equality_folds_on_bits)
{
  Fixture f;
  EXPECT_EQ(f.mgr.ASTTrue, f.nf().CreateNode(EQ, f.typed(), f.plain()));

  // And a genuine difference still folds the other way.
  const ASTNode other = f.mgr.CreateBVConst(32, 0x3F800001u);
  EXPECT_EQ(f.mgr.ASTFalse, f.nf().CreateNode(EQ, f.typed(), other));
}

// Read-over-write may only skip a write when the two indexes are *values*
// that differ. Skipping on node identity reads straight past the cell that
// was written and answers with whatever is underneath.
TEST(ConstantIdentity, read_over_write_does_not_skip_a_matching_cell)
{
  Fixture f;
  const ASTNode typed = f.typed();
  const ASTNode plain = f.plain();
  const ASTNode a = f.mgr.CreateSourceSymbol(
      "a", SourceSort::array(SourceSort::bitVector(32),
                             SourceSort::bitVector(8)));
  const ASTNode stored = f.mgr.CreateBVConst(8, 0x2A);
  const ASTNode other_value = f.mgr.CreateBVConst(8, 0x2B);

  // Write at the typed constant, read at the plain one: same cell.
  const ASTNode write =
      f.nf().CreateArrayTerm(WRITE, 32, 8, {a, typed, stored});
  EXPECT_EQ(stored, f.nf().CreateTerm(READ, 8, write, plain));

  // ... and the other way round.
  const ASTNode write2 =
      f.nf().CreateArrayTerm(WRITE, 32, 8, {a, plain, stored});
  EXPECT_EQ(stored, f.nf().CreateTerm(READ, 8, write2, typed));

  // A write at a genuinely different index is still skipped, so the rule
  // has not simply been disabled: the read sees the cell underneath.
  const ASTNode different = f.mgr.CreateBVConst(32, 0x3F800001u);
  const ASTNode inner =
      f.nf().CreateArrayTerm(WRITE, 32, 8, {a, typed, stored});
  const ASTNode layered = f.nf().CreateArrayTerm(
      WRITE, 32, 8, {inner, different, other_value});
  EXPECT_EQ(stored, f.nf().CreateTerm(READ, 8, layered, plain));
}

// The simplifier reaches the same decisions through its own path.
TEST(ConstantIdentity, simplifier_equality_folds_on_bits)
{
  Fixture f;
  EXPECT_EQ(f.mgr.ASTTrue, f.simp.CreateSimplifiedEQ(f.typed(), f.plain()));

  const ASTNode other = f.mgr.CreateBVConst(32, 0x3F800001u);
  EXPECT_EQ(f.mgr.ASTFalse, f.simp.CreateSimplifiedEQ(f.typed(), other));
}

// ite(c, x, x) collapses on node identity, and deliberately does not collapse
// two constants that merely share bits.
//
// This is the direction where identity is the *right* test. The two nodes
// have different source sorts, so there is no answer to collapse to: picking
// either branch retypes the expression, and a float and its packed bits are
// not interchangeable at the public boundary. Leaving the ITE alone keeps
// the value right, and the front ends reject a mixed float/bitvector ITE
// before it can be built anyway (ite-mixed-float-bv-rejected.smt2). Recorded
// as a test so that "fixing" it later is a deliberate act.
TEST(ConstantIdentity, ite_collapses_on_identity_not_on_bits)
{
  Fixture f;
  const ASTNode cond =
      f.mgr.CreateSourceSymbol("p", SourceSort::boolean());

  const ASTNode same =
      f.nf().CreateTerm(ITE, 32, cond, f.plain(), f.plain());
  EXPECT_EQ(f.plain(), same);

  const ASTNode mixed =
      f.nf().CreateTerm(ITE, 32, cond, f.typed(), f.plain());
  EXPECT_FALSE(mixed.isConstant());
  EXPECT_EQ(ITE, mixed.GetKind());
}
