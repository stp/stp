/********************************************************************
 * Tests for the floating-point source-to-carrier lowering boundary.
 ********************************************************************/

#include "stp/AST/AST.h"
#include "stp/FloatBlaster/FloatBlast.h"
#include "stp/FloatBlaster/FpTotalise.h"
#include "stp/FloatBlaster/rounding_modes.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/ToSat/BBNodeManagerAIG.h"
#include "stp/ToSat/BitBlaster.h"

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
  // fp.gt/fp.lt over leaves deliberately survive lowering when the native
  // comparison is on (see native_comparison_survives_for_leaf_operands).
  // This sweep checks that every kind has a SymFPU arm, so turn it off.
  mgr.UserFlags.fp_native_cmp = false;
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

// The four ordering comparisons over leaf operands are not expanded to
// SymFPU circuits: the source node passes through lowering unchanged and
// the bit-blaster encodes it natively over the packed bits (BBcompareFP).
// Everything else -- operands that are FP operations, constant pairs, and
// every comparison once the flag is off -- still lowers through SymFPU.
TEST(FloatBlast, native_comparison_survives_for_leaf_operands)
{
  STPMgr mgr;
  ASSERT_TRUE(mgr.UserFlags.fp_native_cmp); // on by default
  const SourceSort fp32 = SourceSort::floatingPoint(8, 24);
  const ASTNode x = mgr.CreateSourceSymbol("x", fp32);
  const ASTNode y = mgr.CreateSourceSymbol("y", fp32);
  const ASTNode one =
      mgr.CreateFPConst(mgr.CreateBVConst(32, 0x3f800000u), 8, 24);
  const ASTNode two =
      mgr.CreateFPConst(mgr.CreateBVConst(32, 0x40000000u), 8, 24);
  const ASTNode sum =
      mgr.CreateTerm(FP_ADD, 32, ASTVec{rne(mgr), x, y});

  auto lowered = [&mgr](const ASTNode& n) {
    FloatBlast lower(&mgr);
    return lower.topLevel(n);
  };

  // Leaf operands: the comparison itself survives, and nothing else does.
  const ASTNode gt_symbols = mgr.CreateNode(FP_GT, x, y);
  EXPECT_EQ(gt_symbols, lowered(gt_symbols));
  const ASTNode gt_constant = mgr.CreateNode(FP_GT, x, one);
  EXPECT_EQ(gt_constant, lowered(gt_constant));
  const ASTNode lt_constant = mgr.CreateNode(FP_LT, x, one);
  EXPECT_EQ(lt_constant, lowered(lt_constant));

  // FP constant folding is deferred solver-wide, so literals usually arrive
  // as to_fp's three-child reinterpret form over constant bits. The gate
  // resolves that form to the interned constant and the comparison survives
  // rebuilt over it.
  const ASTNode one_reinterpreted = mgr.CreateTerm(
      FP_TOFP, 32,
      ASTVec{mgr.CreateBVConst(32, 8), mgr.CreateBVConst(32, 24),
             mgr.CreateBVConst(32, 0x3f800000u)});
  EXPECT_EQ(gt_constant,
            lowered(mgr.CreateNode(FP_GT, x, one_reinterpreted)));

  // An FP-operation operand keeps the whole comparison on the SymFPU path:
  // its value is cached unpacked and the unpacked comparison is cheaper
  // than packing it.
  EXPECT_FALSE(
      containsFloatingPointKind(lowered(mgr.CreateNode(FP_GT, sum, y))));

  // A constant pair must not survive -- constant folding and model
  // evaluation rely on lowering replacing the node (they collapse the
  // SymFPU circuit built over the constants).
  EXPECT_FALSE(
      containsFloatingPointKind(lowered(mgr.CreateNode(FP_GT, one, two))));

  // The non-strict comparisons survive under the same gate.
  const ASTNode geq_symbols = mgr.CreateNode(FP_GEQ, x, y);
  EXPECT_EQ(geq_symbols, lowered(geq_symbols));
  const ASTNode leq_constant = mgr.CreateNode(FP_LEQ, x, one);
  EXPECT_EQ(leq_constant, lowered(leq_constant));
  EXPECT_FALSE(
      containsFloatingPointKind(lowered(mgr.CreateNode(FP_GEQ, sum, y))));

  // Flag off: the old behaviour, everything lowers.
  mgr.UserFlags.fp_native_cmp = false;
  EXPECT_FALSE(containsFloatingPointKind(lowered(gt_symbols)));
}

// The native encoding and SymFPU must agree on every comparison. At the
// smallest supported format, (3, 4), all 128 x 128 packed operand pairs are
// checked for each of the four ordering comparisons: the native verdict
// comes from bit-blasting the comparison over constant operands (the AIG
// collapses to a constant), the reference from SymFPU's
// fold-by-construction constant evaluation. The sweep includes +/-0,
// +/-infinity, NaN and every subnormal pair.
TEST(FloatBlast, native_comparison_agrees_with_symfpu_exhaustively)
{
  STPMgr mgr;
  SubstitutionMap substitutions(&mgr);
  Simplifier simp(&mgr, &substitutions);
  BBNodeManagerAIG aig;
  BitBlaster bb(&aig, &simp, mgr.defaultNodeFactory, &mgr.UserFlags);

  const unsigned eb = 3, sb = 4;
  const unsigned width = eb + sb;
  const unsigned values = 1u << width;

  std::vector<ASTNode> constants;
  constants.reserve(values);
  for (unsigned i = 0; i < values; i++)
    constants.push_back(mgr.CreateFPConst(mgr.CreateBVConst(width, i), eb, sb));

  unsigned checked = 0;
  for (unsigned i = 0; i < values; i++)
  {
    for (unsigned j = 0; j < values; j++)
    {
      for (const Kind kind : {FP_GT, FP_LT, FP_GEQ, FP_LEQ})
      {
        const ASTNode comparison =
            mgr.CreateNode(kind, constants[i], constants[j]);

        const ASTNode reference = NonMemberBVConstEvaluator(&mgr, comparison);
        ASSERT_TRUE(reference == mgr.ASTTrue || reference == mgr.ASTFalse);

        const BBNode native = bb.BBForm(comparison);
        ASSERT_TRUE(native == aig.getTrue() || native == aig.getFalse());

        ASSERT_EQ(reference == mgr.ASTTrue, native == aig.getTrue())
            << _kind_names[kind] << " disagrees on operands " << i << ", "
            << j;
        ++checked;
      }
    }
  }
  EXPECT_EQ(4 * values * values, checked);
}
