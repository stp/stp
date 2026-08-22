#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"

#include <gtest/gtest.h>

using namespace stp;

TEST(SourceSort, prints_canonical_smtlib_spelling)
{
  EXPECT_EQ("Unknown", sourceSortToSMTLib(SourceSort::unknown()));
  EXPECT_EQ("Bool", sourceSortToSMTLib(SourceSort::boolean()));
  EXPECT_EQ("(_ BitVec 17)",
            sourceSortToSMTLib(SourceSort::bitVector(17)));
  EXPECT_EQ("(_ FloatingPoint 8 24)",
            sourceSortToSMTLib(SourceSort::floatingPoint(8, 24)));
  EXPECT_EQ("RoundingMode",
            sourceSortToSMTLib(SourceSort::roundingMode()));
  EXPECT_EQ("(Array (_ FloatingPoint 8 24) RoundingMode)",
            sourceSortToSMTLib(SourceSort::array(
                SourceSort::floatingPoint(8, 24),
                SourceSort::roundingMode())));
}

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

TEST(SourceSort, array_equality_rejects_equal_width_different_source_sorts)
{
  STPMgr mgr;
  mgr.UserFlags.enable_array_equality = true;

  const ASTNode fp_indexed = mgr.CreateSourceSymbol(
      "fp_indexed",
      SourceSort::array(SourceSort::floatingPoint(8, 24),
                        SourceSort::bitVector(8)));
  const ASTNode bv_indexed = mgr.CreateSourceSymbol(
      "bv_indexed",
      SourceSort::array(SourceSort::bitVector(32),
                        SourceSort::bitVector(8)));

  // The carrier widths agree, but these are different SMT source sorts.
  EXPECT_DEATH(
      mgr.hashingNodeFactory->CreateNode(EQ, ASTVec{fp_indexed, bv_indexed}),
      "identical source sorts");
  EXPECT_DEATH(
      mgr.hashingNodeFactory->CreateNode(ARRAY_EQ,
                                         ASTVec{fp_indexed, bv_indexed}),
      "identical source sorts");
}

// A sort declared by (declare-sort S 0) has an identity of its own, and this
// is what that means. Registered as its bare carrier the sort WAS that
// bit-vector, so any two declared sorts were one sort and each was the same
// sort as a genuine bit-vector of the same width -- which is how a query could
// equate elements of two unrelated sorts, or add one to itself, and be
// answered rather than rejected.
//
// The identity is an id in the first field and the carrier width in the
// second, so operator==, hash() and Hasher were left untouched and are correct
// by construction. These rows exist because nothing else in the tree would
// notice an edit that stopped comparing the id: dropping it from operator==
// makes any two declared sorts one sort again, and every other test in the
// suite stays green. Verified by making that edit and watching this fail.
//
// Two related regressions are NOT caught here, and are not oversights. An
// operator== that ignored the kind cannot make a declared sort equal its
// carrier, because the two use the fields differently -- a bit-vector's width
// sits in the first field and leaves the second at zero, while a declared sort
// has an id there and a non-zero width beside it, and a declared sort of width
// zero is refused. And a hash() that ignored the kind only collides, which is
// legal, since equality is what separates them.
TEST(SourceSort, UninterpretedSortsHaveTheirOwnIdentity)
{
  const SourceSort first = registerUninterpretedSort("S", 16);
  const SourceSort second = registerUninterpretedSort("T", 16);

  EXPECT_EQ(SourceSort::Kind::Uninterpreted, first.kind());
  EXPECT_TRUE(first.isScalar());

  // Two sorts, not one, even sharing a carrier width -- and told apart by the
  // hash as well as by equality, or the intern pool would collapse them.
  EXPECT_NE(first, second);
  EXPECT_NE(first.hash(), second.hash());

  // Neither is the bit-vector that carries it, in either direction.
  EXPECT_NE(first, SourceSort::bitVector(16));
  EXPECT_NE(SourceSort::bitVector(16), first);
  EXPECT_NE(second, SourceSort::bitVector(16));

  // The same registration twice is two sorts: a name can be declared again in
  // another frame and the two are unrelated, which is why the name is not the
  // identity.
  EXPECT_NE(registerUninterpretedSort("S", 16),
            registerUninterpretedSort("S", 16));

  // Equal to itself, by value, so a copy still finds its own nodes.
  const SourceSort copy = first;
  EXPECT_EQ(first, copy);
  EXPECT_EQ(first.hash(), copy.hash());

  // The carrier width is what the sort packs into, and is independent of the
  // identity: two sorts at different widths differ, and so do two widths of
  // one name.
  EXPECT_EQ(16u, first.packedWidth());
  EXPECT_EQ(4u, registerUninterpretedSort("N", 4).packedWidth());
  EXPECT_NE(registerUninterpretedSort("W", 8), registerUninterpretedSort("W", 16));

  // The spelling is the declared name, not the carrier.
  EXPECT_EQ("S", sourceSortToSMTLib(first));
  EXPECT_EQ("T", sourceSortToSMTLib(second));

  // A name that is not a simple SMT-LIB symbol is quoted, or a model naming it
  // cannot be read back.
  EXPECT_EQ("|my sort|", sourceSortToSMTLib(registerUninterpretedSort("my sort", 16)));
}

// A symbol of a declared sort takes the carrier's width, exactly as a rounding
// mode does, and keeps its own sort. Missing that arm left the width at zero,
// which the legacy width checks read as a Boolean.
TEST(SourceSort, UninterpretedSymbolsCarryTheirSortAndWidth)
{
  STPMgr mgr;
  const SourceSort sort = registerUninterpretedSort("Elem", 12);
  const ASTNode e = mgr.CreateSourceSymbol("e", sort);

  EXPECT_EQ(sort, e.GetSourceSort());
  EXPECT_EQ(12u, e.GetValueWidth());
  EXPECT_EQ(BITVECTOR_TYPE, e.GetType());

  // Two sorts of the same width are two sorts here too: the symbol table keys
  // on the source sort, so the same name at each is two nodes.
  const SourceSort other = registerUninterpretedSort("Other", 12);
  const ASTNode same_name = mgr.CreateSourceSymbol("e", other);
  EXPECT_NE(e, same_name);
  EXPECT_EQ(other, same_name.GetSourceSort());
}
