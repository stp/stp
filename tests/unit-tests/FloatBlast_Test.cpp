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
#include "stp/UninterpretedFunctions/UFContext.h"

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

bool contains(const ASTNode& haystack, const ASTNode& needle,
              ASTNodeSet& visited)
{
  if (!visited.insert(haystack).second)
    return false;
  if (haystack == needle)
    return true;
  for (size_t i = 0; i < haystack.Degree(); ++i)
    if (contains(haystack[i], needle, visited))
      return true;
  return false;
}

bool contains(const ASTNode& haystack, const ASTNode& needle)
{
  ASTNodeSet visited;
  return contains(haystack, needle, visited);
}

// The one node of `kind` in `n`, or null if `n` holds none or several.
ASTNode soleNodeOfKind(const ASTNode& n, Kind kind, ASTNodeSet& visited,
                       ASTNode& found, bool& unique)
{
  if (!visited.insert(n).second)
    return found;

  if (n.GetKind() == kind)
  {
    if (!found.IsNull() && found != n)
      unique = false;
    found = n;
  }
  for (size_t i = 0; i < n.Degree(); ++i)
    soleNodeOfKind(n[i], kind, visited, found, unique);
  return found;
}

ASTNode soleNodeOfKind(const ASTNode& n, Kind kind)
{
  ASTNodeSet visited;
  ASTNode found;
  bool unique = true;
  const ASTNode answer = soleNodeOfKind(n, kind, visited, found, unique);
  return unique ? answer : ASTNode();
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
  // The FP predicates over leaves deliberately survive lowering when the
  // native encoding is on (see native_comparison_survives_for_leaf_operands).
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
  // FP_SMT_EQ is the end of the contiguous FP block in ASTKind.kinds;
  // append-only non-FP public kinds follow it. A new FP kind extends this
  // bound deliberately, so the scan has to reach it.
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

// The six comparison predicates over packed-view operands are not expanded to
// SymFPU circuits: the source node passes through lowering unchanged and the
// bit-blaster encodes it natively over the packed bits (BBcompareFP,
// BBeqFP).
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

  // ... and so do the two equalities.
  const ASTNode eq_symbols = mgr.CreateNode(FP_EQ, x, y);
  EXPECT_EQ(eq_symbols, lowered(eq_symbols));
  const ASTNode smt_eq_constant = mgr.CreateNode(FP_SMT_EQ, x, one);
  EXPECT_EQ(smt_eq_constant, lowered(smt_eq_constant));
  EXPECT_FALSE(
      containsFloatingPointKind(lowered(mgr.CreateNode(FP_EQ, sum, y))));

  // The classification predicates survive over a symbol operand. Their gate
  // is stricter about constants than the binary one: a unary predicate over
  // a constant is a constant node, which must lower and collapse -- so the
  // to_fp-reinterpret literal that makes a comparison survive does not make
  // a classification survive.
  const ASTNode isnan_symbol = mgr.CreateNode(FP_ISNAN, x);
  EXPECT_EQ(isnan_symbol, lowered(isnan_symbol));
  const ASTNode ispositive_symbol = mgr.CreateNode(FP_ISPOSITIVE, x);
  EXPECT_EQ(ispositive_symbol, lowered(ispositive_symbol));
  EXPECT_FALSE(containsFloatingPointKind(
      lowered(mgr.CreateNode(FP_ISNAN, one_reinterpreted))));
  EXPECT_FALSE(
      containsFloatingPointKind(lowered(mgr.CreateNode(FP_ISNAN, one))));
  EXPECT_FALSE(
      containsFloatingPointKind(lowered(mgr.CreateNode(FP_ISNORMAL, sum))));

  // Flag off: the old behaviour, everything lowers.
  mgr.UserFlags.fp_native_cmp = false;
  EXPECT_FALSE(containsFloatingPointKind(lowered(gt_symbols)));
  EXPECT_FALSE(containsFloatingPointKind(lowered(isnan_symbol)));
}

// A float-sorted ITE is a mux over packed bits, so a predicate over one can
// survive lowering too: the bit-blaster muxes the branches (BBITE) instead
// of SymFPU unpacking both of them and muxing the unpacked records. The
// branches have to pass the same test the top-level operands do.
TEST(FloatBlast, native_comparison_survives_for_ite_operands)
{
  STPMgr mgr;
  ASSERT_TRUE(mgr.UserFlags.fp_native_cmp); // on by default
  const SourceSort fp32 = SourceSort::floatingPoint(8, 24);
  const ASTNode x = mgr.CreateSourceSymbol("x", fp32);
  const ASTNode y = mgr.CreateSourceSymbol("y", fp32);
  const ASTNode z = mgr.CreateSourceSymbol("z", fp32);
  const ASTNode c = mgr.CreateSymbol("c", 0, 0);
  const ASTNode d = mgr.CreateSymbol("d", 0, 0);
  const ASTNode one =
      mgr.CreateFPConst(mgr.CreateBVConst(32, 0x3f800000u), 8, 24);
  const ASTNode sum = mgr.CreateTerm(FP_ADD, 32, ASTVec{rne(mgr), x, y});

  auto lowered = [&mgr](const ASTNode& n) {
    FloatBlast lower(&mgr);
    return lower.topLevel(n);
  };

  // Both branches are symbols: the whole comparison survives unchanged.
  const ASTNode mux = mgr.CreateTerm(ITE, 32, ASTVec{c, x, y});
  const ASTNode gt_mux = mgr.CreateNode(FP_GT, mux, z);
  EXPECT_EQ(gt_mux, lowered(gt_mux));

  // Nested muxes are just more of the same.
  const ASTNode nested = mgr.CreateTerm(
      ITE, 32, ASTVec{d, x, mgr.CreateTerm(ITE, 32, ASTVec{c, y, z})});
  const ASTNode gt_nested = mgr.CreateNode(FP_GT, nested, z);
  EXPECT_EQ(gt_nested, lowered(gt_nested));

  // A to_fp-spelled literal inside a branch resolves to the interned
  // constant, so the comparison survives rebuilt over the resolved mux.
  const ASTNode one_reinterpreted = mgr.CreateTerm(
      FP_TOFP, 32,
      ASTVec{mgr.CreateBVConst(32, 8), mgr.CreateBVConst(32, 24),
             mgr.CreateBVConst(32, 0x3f800000u)});
  const ASTNode gt_resolved = mgr.CreateNode(
      FP_GT, mgr.CreateTerm(ITE, 32, ASTVec{c, x, one}), z);
  EXPECT_EQ(gt_resolved,
            lowered(mgr.CreateNode(
                FP_GT, mgr.CreateTerm(ITE, 32, ASTVec{c, x, one_reinterpreted}),
                z)));

  // An FP operation in either branch keeps the whole comparison on the
  // SymFPU path -- the branch has no packed view that lowering would leave
  // in the formula.
  EXPECT_FALSE(containsFloatingPointKind(lowered(mgr.CreateNode(
      FP_GT, mgr.CreateTerm(ITE, 32, ASTVec{c, x, sum}), z))));
  EXPECT_FALSE(containsFloatingPointKind(lowered(mgr.CreateNode(
      FP_GT, mgr.CreateTerm(ITE, 32, ASTVec{c, sum, x}), z))));

  // The equalities and the classifications share the gate.
  const ASTNode eq_mux = mgr.CreateNode(FP_EQ, mux, z);
  EXPECT_EQ(eq_mux, lowered(eq_mux));
  const ASTNode isnan_mux = mgr.CreateNode(FP_ISNAN, mux);
  EXPECT_EQ(isnan_mux, lowered(isnan_mux));

  // Flag off: the old behaviour, everything lowers.
  mgr.UserFlags.fp_native_cmp = false;
  EXPECT_FALSE(containsFloatingPointKind(lowered(gt_mux)));
  EXPECT_FALSE(containsFloatingPointKind(lowered(isnan_mux)));
}

// A select from a float-element array is the packed element bits already,
// so a predicate over one survives lowering as well. The array and the index
// are lowered like any other children -- what must not happen is the element
// itself being unpacked and re-encoded.
TEST(FloatBlast, native_comparison_survives_for_read_operands)
{
  STPMgr mgr;
  ASSERT_TRUE(mgr.UserFlags.fp_native_cmp); // on by default
  const SourceSort fp32 = SourceSort::floatingPoint(8, 24);
  const SourceSort index = SourceSort::bitVector(4);
  const ASTNode array =
      mgr.CreateSourceSymbol("A", SourceSort::array(index, fp32));
  const ASTNode i = mgr.CreateSourceSymbol("i", index);
  const ASTNode y = mgr.CreateSourceSymbol("y", fp32);
  const ASTNode x = mgr.CreateSourceSymbol("x", fp32);
  const ASTNode sum = mgr.CreateTerm(FP_ADD, 32, ASTVec{rne(mgr), x, y});

  auto lowered = [&mgr](const ASTNode& n) {
    FloatBlast lower(&mgr);
    return lower.topLevel(n);
  };

  const ASTNode read = mgr.CreateTerm(READ, 32, array, i);
  ASSERT_EQ(SourceSort::Kind::FloatingPoint, read.GetSourceSort().kind());

  // Array and index carry no FP work: the whole comparison survives as is.
  const ASTNode gt_read = mgr.CreateNode(FP_GT, read, y);
  EXPECT_EQ(gt_read, lowered(gt_read));

  // The classifications and equalities share the gate.
  const ASTNode isnan_read = mgr.CreateNode(FP_ISNAN, read);
  EXPECT_EQ(isnan_read, lowered(isnan_read));

  // An index containing FP work is lowered like any other child, so the
  // comparison survives REBUILT over a read with the lowered index -- the
  // element bits are still read directly. The index here compares an
  // fp.add, which cannot survive, so nothing floating-point is left in it.
  const ASTNode fp_index = mgr.CreateTerm(
      ITE, 4,
      ASTVec{mgr.CreateNode(FP_GT, sum, y), i, mgr.CreateBVConst(4, 3)});
  const ASTNode gt_fp_index =
      mgr.CreateNode(FP_GT, mgr.CreateTerm(READ, 32, array, fp_index), y);
  const ASTNode gt_fp_index_lowered = lowered(gt_fp_index);
  EXPECT_NE(gt_fp_index, gt_fp_index_lowered);
  EXPECT_EQ(FP_GT, gt_fp_index_lowered.GetKind());
  ASSERT_EQ(READ, gt_fp_index_lowered[0].GetKind());
  EXPECT_EQ(array, gt_fp_index_lowered[0][0]);
  EXPECT_FALSE(containsFloatingPointKind(gt_fp_index_lowered[0][1]));

  // A comparison in the index that CAN survive is left alone there, exactly
  // as it would be anywhere else in the formula.
  const ASTNode native_index = mgr.CreateTerm(
      ITE, 4, ASTVec{mgr.CreateNode(FP_GT, x, y), i, mgr.CreateBVConst(4, 3)});
  const ASTNode gt_native_index =
      mgr.CreateNode(FP_GT, mgr.CreateTerm(READ, 32, array, native_index), y);
  EXPECT_EQ(gt_native_index, lowered(gt_native_index));

  // The other operand still has to pass the gate.
  EXPECT_FALSE(
      containsFloatingPointKind(lowered(mgr.CreateNode(FP_GT, read, sum))));

  // Flag off: the old behaviour, everything lowers.
  mgr.UserFlags.fp_native_cmp = false;
  EXPECT_FALSE(containsFloatingPointKind(lowered(gt_read)));
}

// The native encoding and SymFPU must agree on every predicate. At the
// smallest supported format, (3, 4), all 128 x 128 packed operand pairs are
// checked for each of the six comparison predicates, and all 128 operands
// for each of the seven classifications: the native verdict comes from
// bit-blasting the predicate over constant operands (the AIG collapses to a
// constant), the reference from SymFPU's fold-by-construction constant
// evaluation. The sweep includes +/-0, +/-infinity, every NaN payload and
// every subnormal.
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
      for (const Kind kind : {FP_GT, FP_LT, FP_GEQ, FP_LEQ, FP_EQ, FP_SMT_EQ})
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
  EXPECT_EQ(6 * values * values, checked);

  unsigned classified = 0;
  for (unsigned i = 0; i < values; i++)
  {
    for (const Kind kind : {FP_ISNORMAL, FP_ISSUBNORMAL, FP_ISZERO,
                            FP_ISINFINITE, FP_ISNAN, FP_ISNEGATIVE,
                            FP_ISPOSITIVE})
    {
      const ASTNode classification = mgr.CreateNode(kind, constants[i]);

      const ASTNode reference = NonMemberBVConstEvaluator(&mgr, classification);
      ASSERT_TRUE(reference == mgr.ASTTrue || reference == mgr.ASTFalse);

      const BBNode native = bb.BBForm(classification);
      ASSERT_TRUE(native == aig.getTrue() || native == aig.getFalse());

      ASSERT_EQ(reference == mgr.ASTTrue, native == aig.getTrue())
          << _kind_names[kind] << " disagrees on operand " << i;
      ++classified;
    }
  }
  EXPECT_EQ(7 * values, classified);

  // Muxed operands: the same sweep through a float-sorted ITE. The mux is
  // structural, so what needs checking is that the surviving comparison
  // reads the branch the condition selects -- against every constant, with
  // a NaN in the other branch so a mux that leaked the wrong branch shows
  // up as a comparison that is false when it should not be. (The unit tests
  // build nodes through the hashing factory, so the constant condition does
  // not fold the ITE away before it is blasted.)
  unsigned nanIndex = values;
  for (unsigned i = 0; i < values && nanIndex == values; i++)
    if (NonMemberBVConstEvaluator(&mgr, mgr.CreateNode(FP_ISNAN, constants[i]))
        == mgr.ASTTrue)
      nanIndex = i;
  ASSERT_LT(nanIndex, values);

  unsigned muxed = 0;
  for (const ASTNode& cond : {mgr.ASTTrue, mgr.ASTFalse})
  {
    for (unsigned i = 0; i < values; i++)
    {
      const ASTNode mux = mgr.CreateTerm(
          ITE, width, ASTVec{cond, constants[i], constants[nanIndex]});
      const ASTNode& selected =
          cond == mgr.ASTTrue ? constants[i] : constants[nanIndex];
      for (unsigned j = 0; j < values; j++)
      {
        const ASTNode comparison = mgr.CreateNode(FP_GT, mux, constants[j]);
        const ASTNode reference = NonMemberBVConstEvaluator(
            &mgr, mgr.CreateNode(FP_GT, selected, constants[j]));
        ASSERT_TRUE(reference == mgr.ASTTrue || reference == mgr.ASTFalse);

        const BBNode native = bb.BBForm(comparison);
        ASSERT_TRUE(native == aig.getTrue() || native == aig.getFalse());

        ASSERT_EQ(reference == mgr.ASTTrue, native == aig.getTrue())
            << "muxed fp.gt disagrees on branch " << i << ", operand " << j;
        ++muxed;
      }
    }
  }
  EXPECT_EQ(2 * values * values, muxed);
}

// A UF application is opaque to this pass.
//
// The generic rebuild substitutes lowered children into whatever node it is
// rebuilding, and doing that under an application is wrong twice over: the
// actuals are stated in source sorts and the UF layer both validates and
// compares them there, so a float actual replaced by the bits it lowered to
// no longer denotes the same argument -- and the node factory refuses to
// build the application at all, which took the process down.
//
// It takes a *computed* actual to reach it. A symbol or a constant lowers to
// itself, so the rebuild never fires; the second half of this test is that
// case, which has to keep behaving the same way.
TEST(FloatBlast, uf_application_is_an_opaque_carrier)
{
  STPMgr mgr;
  mgr.UserFlags.enable_uninterpreted_functions = true;
  UFContext* const context = mgr.getUFContext();
  const SourceSort fp16 = SourceSort::floatingPoint(5, 11);
  std::string diagnostic;
  const UFDecl* const f =
      context->declareFunction("f", {fp16}, fp16, &diagnostic);
  ASSERT_NE(nullptr, f) << diagnostic;

  const ASTNode x = mgr.CreateSourceSymbol("x", fp16);
  const ASTNode magnitude = mgr.CreateTerm(FP_ABS, 16, x);
  const ASTNode applied = context->apply(f, {magnitude}, &diagnostic);
  ASSERT_FALSE(applied.IsNull()) << diagnostic;

  // The actual is shared with the enclosing operation, which is what made
  // the defect fire: fp.abs is lowered in its non-UF position first, and the
  // cached lowering is what the rebuild then substituted under f.
  const ASTNode sum = mgr.CreateTerm(
      FP_ADD, 16, ASTVec{rne(mgr), magnitude, applied});

  FloatBlast lower(&mgr);
  const ASTNode lowered = lower.topLevel(sum);

  // The application survives as itself -- same node, same actual, still at
  // the declared float sort -- so the model evaluator can resolve it against
  // the certified interpretation.
  const ASTNode survivor = soleNodeOfKind(lowered, UF_APPLY);
  ASSERT_FALSE(survivor.IsNull());
  EXPECT_EQ(applied, survivor);
  ASSERT_EQ(2u, survivor.Degree());
  EXPECT_EQ(magnitude, survivor[1]);
  EXPECT_EQ(fp16, survivor[1].GetSourceSort());

  // Everything else is bits. The float operation under the application is
  // deliberately among the exceptions: nothing below an application is
  // lowered, so its fp.abs is still there, inside it and nowhere else.
  EXPECT_EQ(1u, countKind(lowered, FP_ABS));
  EXPECT_EQ(0u, countKind(lowered, FP_ADD));

  // Two decodes: x, which the shared fp.abs consumes, and the application's
  // own bits. An application is a carrier like any other leaf, not an
  // operation to build a circuit for.
  EXPECT_EQ(2u, lower.statistics().unpack_builds);
  EXPECT_EQ(2u, lower.statistics().unpacked_operation_builds);

  // A leaf actual takes the same route, and always did: the application is
  // returned untouched because there was nothing to substitute.
  const ASTNode leafApplied = context->apply(f, {x}, &diagnostic);
  ASSERT_FALSE(leafApplied.IsNull()) << diagnostic;
  const ASTNode leafSum = mgr.CreateTerm(
      FP_ADD, 16, ASTVec{rne(mgr), x, leafApplied});

  FloatBlast leafLower(&mgr);
  const ASTNode leafLowered = leafLower.topLevel(leafSum);
  const ASTNode leafSurvivor = soleNodeOfKind(leafLowered, UF_APPLY);
  ASSERT_FALSE(leafSurvivor.IsNull());
  EXPECT_EQ(leafApplied, leafSurvivor);
}

// The same rule, for the codomains that never reach the packed/unpacked
// views at all. A Bool or bit-vector result puts the application on lower()'s
// generic path, where the substitution was equally fatal -- the argument
// sorts are what the factory checks, and they do not depend on the result.
TEST(FloatBlast, uf_application_with_a_non_float_result_is_opaque_too)
{
  STPMgr mgr;
  mgr.UserFlags.enable_uninterpreted_functions = true;
  UFContext* const context = mgr.getUFContext();
  const SourceSort fp16 = SourceSort::floatingPoint(5, 11);
  std::string diagnostic;
  const UFDecl* const p =
      context->declareFunction("p", {fp16}, SourceSort::boolean(), &diagnostic);
  const UFDecl* const w = context->declareFunction(
      "w", {fp16}, SourceSort::bitVector(16), &diagnostic);
  ASSERT_NE(nullptr, p) << diagnostic;
  ASSERT_NE(nullptr, w) << diagnostic;

  const ASTNode x = mgr.CreateSourceSymbol("x", fp16);
  const ASTNode magnitude = mgr.CreateTerm(FP_ABS, 16, x);
  const ASTNode predicate = context->apply(p, {magnitude}, &diagnostic);
  const ASTNode bits = context->apply(w, {magnitude}, &diagnostic);
  ASSERT_FALSE(predicate.IsNull()) << diagnostic;
  ASSERT_FALSE(bits.IsNull()) << diagnostic;

  // The bit-vector result is reinterpreted back into the float layer, so
  // both applications sit under one float-valued term.
  const ASTNode reinterpreted = mgr.CreateTerm(
      FP_TOFP, 16,
      ASTVec{mgr.CreateBVConst(32, 5), mgr.CreateBVConst(32, 11), bits});
  const ASTNode mux = mgr.CreateTerm(
      ITE, 16, ASTVec{predicate, magnitude, reinterpreted});
  const ASTNode sum =
      mgr.CreateTerm(FP_ADD, 16, ASTVec{rne(mgr), magnitude, mux});

  FloatBlast lower(&mgr);
  const ASTNode lowered = lower.topLevel(sum);

  // Both applications survive as the nodes that were built, actuals and all.
  EXPECT_EQ(2u, countKind(lowered, UF_APPLY));
  EXPECT_TRUE(contains(lowered, predicate));
  EXPECT_TRUE(contains(lowered, bits));

  // Their shared fp.abs is the only float operation left, and it is left
  // only because it is under them.
  EXPECT_EQ(1u, countKind(lowered, FP_ABS));
  EXPECT_EQ(0u, countKind(lowered, FP_ADD));
  EXPECT_EQ(0u, countKind(lowered, FP_TOFP));
}
