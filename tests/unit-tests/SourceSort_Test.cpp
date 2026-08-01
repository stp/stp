#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"

#include <gtest/gtest.h>

using namespace stp;

TEST(SourceSort, distinguishes_equal_width_float_formats)
{
  const SourceSort single = SourceSort::floatingPoint(8, 24);
  const SourceSort other32 = SourceSort::floatingPoint(11, 21);
  EXPECT_EQ(32u, single.packedWidth());
  EXPECT_EQ(32u, other32.packedWidth());
  EXPECT_NE(single, other32);
  EXPECT_NE(single, SourceSort::bitVector(32));
}

TEST(SourceSort, rounding_mode_literal_is_not_its_carrier)
{
  STPMgr mgr;
  const ASTNode rm = mgr.CreateRMConst(1);
  const ASTNode rm_again = mgr.CreateRMConst(1);
  const ASTNode bits = mgr.CreateBVConst(5, 1);

  EXPECT_NE(rm, bits);
  EXPECT_EQ(rm, rm_again);
  EXPECT_EQ(BVCONST, rm.GetKind());
  EXPECT_EQ(BVCONST, bits.GetKind());
  EXPECT_EQ(SourceSort::Kind::RoundingMode, rm.GetSourceSort().kind());
  EXPECT_EQ(SourceSort::Kind::BitVector, bits.GetSourceSort().kind());
  EXPECT_TRUE(constantsSameBits(rm, bits));
}

TEST(SourceSort, derives_array_reads_writes_and_ites)
{
  STPMgr mgr;
  const SourceSort index = SourceSort::floatingPoint(8, 24);
  const SourceSort element = SourceSort::roundingMode();
  const SourceSort array = SourceSort::array(index, element);

  const ASTNode a = mgr.CreateSourceSymbol("a", array);
  const ASTNode b = mgr.CreateSourceSymbol("b", array);
  const ASTNode i = mgr.CreateSourceSymbol("i", index);
  const ASTNode r = mgr.CreateSourceSymbol("r", element);
  const ASTNode c = mgr.CreateSourceSymbol("c", SourceSort::boolean());

  const ASTNode read = mgr.CreateTerm(READ, 5, a, i);
  const ASTNode write = mgr.CreateArrayTerm(WRITE, 32, 5, {a, i, r});
  const ASTNode choice = mgr.CreateArrayTerm(ITE, 32, 5, {c, a, b});

  EXPECT_EQ(element, read.GetSourceSort());
  EXPECT_EQ(array, write.GetSourceSort());
  EXPECT_EQ(array, choice.GetSourceSort());
}

TEST(SourceSort, typed_same_name_symbols_do_not_retype_each_other)
{
  STPMgr mgr;
  const ASTNode rm =
      mgr.CreateSourceSymbol("x", SourceSort::roundingMode());
  const ASTNode bits =
      mgr.CreateSourceSymbol("x", SourceSort::bitVector(5));

  EXPECT_NE(rm, bits);
  EXPECT_EQ(SourceSort::Kind::RoundingMode, rm.GetSourceSort().kind());
  EXPECT_EQ(SourceSort::Kind::BitVector, bits.GetSourceSort().kind());
}
