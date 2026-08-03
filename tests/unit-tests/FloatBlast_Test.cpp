/********************************************************************
 * Tests for the floating-point source-to-carrier lowering boundary.
 ********************************************************************/

#include "stp/AST/AST.h"
#include "stp/FloatBlaster/FloatBlast.h"
#include "stp/FloatBlaster/FpTotalise.h"
#include "stp/FloatBlaster/rounding_modes.h"
#include "stp/STPManager/STPManager.h"

#include <gtest/gtest.h>
#include <set>

using namespace stp;

namespace
{

bool containsFloatingPointKind(const ASTNode& n, ASTNodeSet& visited)
{
  if (!visited.insert(n).second)
    return false;

  if (is_FP_kind(n.GetKind()))
    return true;

  for (size_t i = 0; i < n.Degree(); ++i)
  {
    if (containsFloatingPointKind(n[i], visited))
      return true;
  }
  return false;
}

bool containsFloatingPointKind(const ASTNode& n)
{
  ASTNodeSet visited;
  return containsFloatingPointKind(n, visited);
}

size_t countKind(const ASTNode& n, Kind kind, ASTNodeSet& visited)
{
  if (!visited.insert(n).second)
    return 0;

  size_t count = n.GetKind() == kind ? 1 : 0;
  for (size_t i = 0; i < n.Degree(); ++i)
    count += countKind(n[i], kind, visited);
  return count;
}

size_t countKind(const ASTNode& n, Kind kind)
{
  ASTNodeSet visited;
  return countKind(n, kind, visited);
}

ASTNode rne(STPMgr& mgr)
{
  return mgr.CreateRMConst(
      symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);
}

} // namespace

TEST(FloatBlast, shared_chain_stays_unpacked_until_a_carrier_boundary)
{
  STPMgr mgr;
  const SourceSort fp16 = SourceSort::floatingPoint(5, 11);
  const ASTNode x = mgr.CreateSourceSymbol("x", fp16);
  const ASTNode y = mgr.CreateSourceSymbol("y", fp16);
  const ASTNode rounding_mode = rne(mgr);

  // `sum` is deliberately shared by both operands of the multiply. A
  // packed-only traversal builds unpack(sum) twice here even though AST
  // hash-consing may hide the duplicate circuit in the final DAG.
  const ASTNode sum =
      mgr.CreateTerm(FP_ADD, 16, ASTVec{rounding_mode, x, y});
  const ASTNode product =
      mgr.CreateTerm(FP_MUL, 16, ASTVec{rounding_mode, sum, sum});
  const ASTNode predicate = mgr.CreateNode(FP_ISZERO, product);

  FloatBlast lower(&mgr);
  const ASTNode lowered_predicate = lower.topLevel(predicate);

  EXPECT_FALSE(containsFloatingPointKind(lowered_predicate));
  EXPECT_EQ(2u, lower.statistics().unpack_builds);
  EXPECT_EQ(2u, lower.statistics().unpacked_operation_builds);
  EXPECT_EQ(0u, lower.statistics().pack_builds);
  EXPECT_GE(lower.statistics().unpacked_cache_hits, 1u);

  // Asking for the IEEE carrier is a real pack boundary. The same context
  // must reuse product's cached UF and build exactly one encoding for it.
  const ASTNode ieee = mgr.CreateTerm(FP_TO_IEEE_BV, 16, product);
  const ASTNode lowered_ieee = lower.topLevel(ieee);

  EXPECT_FALSE(containsFloatingPointKind(lowered_ieee));
  EXPECT_EQ(16u, lowered_ieee.GetValueWidth());
  EXPECT_EQ(2u, lower.statistics().unpack_builds);
  EXPECT_EQ(2u, lower.statistics().unpacked_operation_builds);
  EXPECT_EQ(1u, lower.statistics().pack_builds);
}

TEST(FloatBlast, format_conversion_feeds_the_next_operation_unpacked)
{
  STPMgr mgr;
  const ASTNode half =
      mgr.CreateSourceSymbol("half", SourceSort::floatingPoint(5, 11));
  const ASTNode rounding_mode = rne(mgr);

  // ((_ to_fp 8 24) RNE half), followed by another FP operation and a
  // Boolean consumer. The conversion creates an FP32 UF directly; it must
  // not encode that UF merely so fp.neg can decode it again.
  const ASTNode converted = mgr.CreateTerm(
      FP_TOFP, 32,
      ASTVec{mgr.CreateBVConst(32, 8), mgr.CreateBVConst(32, 24),
             rounding_mode, half});
  const ASTNode negated = mgr.CreateTerm(FP_NEG, 32, converted);
  const ASTNode predicate = mgr.CreateNode(FP_ISNORMAL, negated);

  FloatBlast lower(&mgr);
  const ASTNode lowered = lower.topLevel(predicate);

  EXPECT_FALSE(containsFloatingPointKind(lowered));
  EXPECT_EQ(1u, lower.statistics().unpack_builds);
  EXPECT_EQ(2u, lower.statistics().unpacked_operation_builds);
  EXPECT_EQ(0u, lower.statistics().pack_builds);
}

TEST(FloatBlast, reinterpret_cache_distinguishes_equal_width_formats)
{
  STPMgr mgr;
  const ASTNode bits =
      mgr.CreateSourceSymbol("bits", SourceSort::bitVector(16));

  // Both formats have a 16-bit carrier, and both reinterpret exactly the same
  // BV node. They nevertheless require different SymFPU decodes: the cache
  // key is the typed source operation, not just its child or packed width.
  const ASTNode binary16 = mgr.CreateTerm(
      FP_TOFP, 16,
      ASTVec{mgr.CreateBVConst(32, 5), mgr.CreateBVConst(32, 11), bits});
  const ASTNode exponent8 = mgr.CreateTerm(
      FP_TOFP, 16,
      ASTVec{mgr.CreateBVConst(32, 8), mgr.CreateBVConst(32, 8), bits});

  const ASTNode binary16_normal = mgr.CreateNode(FP_ISNORMAL, binary16);
  const ASTNode exponent8_normal = mgr.CreateNode(FP_ISNORMAL, exponent8);
  const ASTNode both =
      mgr.CreateNode(AND, binary16_normal, exponent8_normal);

  FloatBlast lower(&mgr);
  const ASTNode lowered = lower.topLevel(both);

  EXPECT_FALSE(containsFloatingPointKind(lowered));
  EXPECT_EQ(2u, lower.statistics().unpack_builds);
  EXPECT_EQ(2u, lower.statistics().unpacked_operation_builds);
  EXPECT_EQ(0u, lower.statistics().pack_builds);
}

TEST(FloatBlast, totalisation_defers_canonical_boundaries_to_lowering)
{
  STPMgr mgr;
  const SourceSort fp16 = SourceSort::floatingPoint(5, 11);
  const ASTNode x = mgr.CreateSourceSymbol("x", fp16);
  const ASTNode y = mgr.CreateSourceSymbol("y", fp16);
  const ASTNode rounding_mode = rne(mgr);

  const ASTNode sum =
      mgr.CreateTerm(FP_ADD, 16, ASTVec{rounding_mode, x, y});
  const ASTNode minimum = mgr.CreateTerm(FP_MIN, 16, ASTVec{sum, x});
  const ASTNode predicate = mgr.CreateNode(FP_ISZERO, minimum);

  FpTotalise totalise(&mgr);
  const ASTNode prepared = totalise.topLevel(predicate);

  // fp.min's unspecified signed-zero choice is indexed by canonical forms of
  // both operands. Totalisation records those as source boundaries rather
  // than eagerly constructing independent SymFPU decode/encode circuits.
  EXPECT_EQ(2u, countKind(prepared, FP_TO_IEEE_BV));
  EXPECT_EQ(prepared, totalise.topLevel(prepared));

  FloatBlast lower(&mgr);
  const ASTNode lowered = lower.topLevel(prepared);

  EXPECT_FALSE(containsFloatingPointKind(lowered));
  EXPECT_EQ(2u, lower.statistics().unpack_builds);
  EXPECT_EQ(2u, lower.statistics().unpacked_operation_builds);
  EXPECT_EQ(2u, lower.statistics().pack_builds);
}

// Every floating-point kind reaches an arm of the lowering table.
//
// There used to be two tables over this signature -- the unpacked one here
// and a packed one in FloatBlaster::BlastNode -- and keeping them in step was
// a manual obligation: a kind added to one and not the other compiles, and
// fails only on the path that reaches the one that was missed. There is one
// table now, so the remaining risk is a kind that reaches no arm at all.
// Both ends of the table fail closed with a FatalError, so an omission
// aborts this test rather than silently answering.
TEST(FloatBlast, every_floating_point_kind_is_lowered)
{
  STPMgr mgr;
  const SourceSort fp32 = SourceSort::floatingPoint(8, 24);
  const ASTNode x = mgr.CreateSourceSymbol("x", fp32);
  const ASTNode y = mgr.CreateSourceSymbol("y", fp32);
  const ASTNode z = mgr.CreateSourceSymbol("z", fp32);
  const ASTNode rm = rne(mgr);
  const ASTNode bits = mgr.CreateSourceSymbol("b", SourceSort::bitVector(32));
  const ASTNode choice =
      mgr.CreateSourceSymbol("c", SourceSort::bitVector(1));
  const ASTNode undef =
      mgr.CreateSourceSymbol("u", SourceSort::bitVector(16));
  const ASTNode eight = mgr.CreateBVConst(32, 8);
  const ASTNode twentyfour = mgr.CreateBVConst(32, 24);
  const ASTNode sixteen = mgr.CreateBVConst(32, 16);

  // One representative per kind, in the arity the blaster is entitled to
  // assume -- the partial operations after FpTotalise has added their
  // unspecified-value child.
  std::vector<std::pair<Kind, ASTNode>> cases;
  auto term = [&](Kind k, unsigned w, const ASTVec& kids) {
    cases.push_back({k, mgr.CreateTerm(k, w, kids)});
  };
  auto form = [&](Kind k, const ASTVec& kids) {
    cases.push_back({k, mgr.CreateNode(k, kids)});
  };

  term(FP_ABS, 32, {x});
  term(FP_NEG, 32, {x});
  term(FP_ADD, 32, {rm, x, y});
  term(FP_SUB, 32, {rm, x, y});
  term(FP_MUL, 32, {rm, x, y});
  term(FP_DIV, 32, {rm, x, y});
  term(FP_FMA, 32, {rm, x, y, z});
  term(FP_SQRT, 32, {rm, x});
  term(FP_REM, 32, {x, y});
  term(FP_ROUNDTOINTEGRAL, 32, {rm, x});
  term(FP_MIN, 32, {x, y, choice});
  term(FP_MAX, 32, {x, y, choice});
  term(FP_TOFP, 32, {eight, twentyfour, bits});
  term(FP_TOFP, 32, {eight, twentyfour, rm, x});
  term(FP_TOFP_SIGNED, 32, {eight, twentyfour, rm, bits});
  term(FP_TOFP_UNSIGNED, 32, {eight, twentyfour, rm, bits});
  term(FP_TO_UBV, 16, {sixteen, rm, x, undef});
  term(FP_TO_SBV, 16, {sixteen, rm, x, undef});
  term(FP_TO_IEEE_BV, 32, {x});
  form(FP_LEQ, {x, y});
  form(FP_LT, {x, y});
  form(FP_GEQ, {x, y});
  form(FP_GT, {x, y});
  form(FP_EQ, {x, y});
  form(FP_SMT_EQ, {x, y});
  form(FP_ISNORMAL, {x});
  form(FP_ISSUBNORMAL, {x});
  form(FP_ISZERO, {x});
  form(FP_ISINFINITE, {x});
  form(FP_ISNAN, {x});
  form(FP_ISNEGATIVE, {x});
  form(FP_ISPOSITIVE, {x});

  // Every FP kind in the tree is represented, so adding one without adding
  // an arm for it fails here rather than at the first input that uses it.
  // FP_SMT_EQ is the last kind in ASTKind.kinds; a new one is appended after
  // it, so the scan has to reach it.
  std::set<int> covered;
  for (const auto& c : cases)
    covered.insert(static_cast<int>(c.first));
  for (int k = 0; k <= static_cast<int>(FP_SMT_EQ); k++)
  {
    if (!is_FP_kind(static_cast<Kind>(k)))
      continue;
    EXPECT_EQ(1u, covered.count(k)) << "no representative for "
                                    << _kind_names[k];
  }

  for (const auto& c : cases)
  {
    FloatBlast lower(&mgr);
    const ASTNode lowered = lower.topLevel(c.second);
    EXPECT_FALSE(containsFloatingPointKind(lowered))
        << _kind_names[c.first] << " was not lowered";
  }
}
