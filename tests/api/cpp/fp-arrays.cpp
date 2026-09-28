/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: September, 2026
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

// fp-arrays.cpp -- arrays with floating-point and RoundingMode index and
// element sorts: mk_array_sort over mk_fp_sort / mk_rm_sort, declare at such
// array sorts, select and store over them, and reading their values and
// whole-array values back from a model.
//
// The semantic corners pinned here mirror SMT-LIB's (Array X Y) over those
// sorts: array indexes are compared by the index sort's '=', so for a
// float-indexed array every NaN addresses the one NaN cell (whatever its
// payload or sign bit) while +0 and -0 address distinct cells; and a read
// from a RoundingMode-element array always denotes one of the five modes.
//
// A 2.x validity query of a formula is Solver::entails here, and a query of
// `false` (the satisfiability idiom) is check_sat.

#include "api_common.hpp"

#include <cstdint>
#include <string>
#include <vector>

using namespace stp;

namespace
{

// A 2.x checker's configuration: the counterexample self-check on (3.x's
// default is off), so every satisfiable check constructs its model and checks
// each assertion against it.
Options self_checking()
{
  Options o;
  o.set_bool("check-sanity", true);
  return o;
}

// 1.0 in binary32 packs as 0x3F800000, 2.0 as 0x40000000.
Term float32(TermManager& tm, std::uint64_t bits)
{
  return tm.mk_fp_from_bits(tm.mk_fp_sort(8, 24), tm.mk_bv(32, bits));
}

// The packed interchange bits of a float value (formats up to 64 bits).
std::uint64_t packed(const Term& value)
{
  return std::stoull(value.to_fp().bits(), nullptr, 2);
}

// A Boolean value: what a predicate evaluates to under a model.
bool isTruthValue(const Term& t)
{
  return t.is_value() && t.sort().is_bool();
}

// The five rounding modes.
const RoundingMode MODES[5] = {RoundingMode::RNE, RoundingMode::RTP, RoundingMode::RTN,
                               RoundingMode::RTZ, RoundingMode::RNA};

// `read` is one of the five modes.
Term oneOfTheModes(TermManager& tm, const Term& read)
{
  std::vector<Term> one_of;
  for (const RoundingMode mode : MODES)
    one_of.push_back(read == tm.mk_rm(mode));
  return or_(one_of);
}

} // namespace

TEST(fp_arrays, float_element_store_read)
{
  TermManager tm;
  Solver s(tm, self_checking());

  const Sort arrayType = tm.mk_array_sort(tm.mk_bv_sort(2), tm.mk_fp_sort(8, 24));
  const Term a = tm.declare("a", arrayType);

  // A read carries the element's floating-point sort.
  const Term read = a[tm.mk_bv(2, 0)];
  EXPECT_EQ(read.sort().kind(), SortKind::FP);
  EXPECT_EQ(read.sort().fp_exp_size(), 8u);
  EXPECT_EQ(read.sort().fp_sig_size(), 24u);

  // Store 1.0 and read it back: valid, whatever the rest of the array is.
  const Term one = float32(tm, 0x3F800000);
  const Term idx = tm.mk_bv(2, 1);
  const Term stored = store(a, idx, one);
  const Term back = select(stored, idx);
  ASSERT_TRUE(s.entails(back == one).is_valid());
}

TEST(fp_arrays, float_element_arithmetic_and_model)
{
  TermManager tm;
  Solver s(tm, self_checking());

  const Sort arrayType = tm.mk_array_sort(tm.mk_bv_sort(2), tm.mk_fp_sort(8, 24));
  const Term a = tm.declare("a", arrayType);

  const Term idx = tm.mk_bv(2, 3);
  const Term read = a[idx];

  // '=' pins the cell to exactly 1.0 (a non-NaN float has one bit
  // pattern); the addition uses the read as a float like any other, and is
  // consistent with it (1.0 + 1.0 is exactly 2.0 under RNE).
  s.add(read == float32(tm, 0x3F800000));
  const Term sum = fp_add(tm.mk_rm(RoundingMode::RNE), float32(tm, 0x3F800000), read);
  s.add(sum == float32(tm, 0x40000000));
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();

  EXPECT_EQ(packed(m.value(read)), 0x3F800000u);

  // The whole-array value contains that cell, as a float of the element's
  // format at the read's index.
  const ArrayValue av = m.array_value(a);
  ASSERT_EQ(av.size(), 1u);
  EXPECT_EQ(av.entry(0).index.to_uint64(), 3u);
  EXPECT_EQ(packed(av.entry(0).element), 0x3F800000u);
}

// Regression test: evaluating a floating-point operation over a float-element
// array read that the solve never constrained. Model evaluation resolves the
// operation's float operands and rebuilds it, but an out-of-model read used
// to come back as the symbolic READ rather than a constant. Rebuilding over
// it mostly "worked" -- the blaster embeds a read like any term -- until an
// identity fold saw through the rebuild: here idx evaluates to -1.0, so
// idx*idx is exactly 1.0, and rebuilding (fp.mul rm 1.0 rd) folds to rd, the
// bare READ, which went to the float blaster as the whole term:
//   Fatal Error: FloatBlaster::BlastNode: unhandled kind: (READ ...)
// An out-of-model float operand must resolve to a concrete value, as
// bit-vector operands already did. The value itself is unconstrained, so only
// its shape and stability are checked.
//
// Found by fuzzing with murxla driving the 2.x C API; delta-minimized.
TEST(fp_arrays, float_element_read_as_operand_of_evaluated_term)
{
  TermManager tm;
  Solver s(tm, self_checking());

  const Sort fp = tm.mk_fp_sort(5, 11);
  const Term a = tm.declare("a", tm.mk_array_sort(fp, fp));
  const Term rne = tm.mk_rm(RoundingMode::RNE);
  const Term rm = tm.declare("rm", tm.mk_rm_sort());
  // the signed 1-bit #b1 is -1
  const Term idx = to_fp(fp, rm, tm.mk_bv(1, "1", 2));
  const Term rd = a[idx];
  const Term m1 = fp_mul(rm, idx, idx);
  const Term m2 = fp_mul(rne, m1, rd);
  const Term ad = fp_add(rm, m2, rd);
  const Term mn = fp_min(ad, rd);
  const Term f = fp_mul(rm, mn, rd);

  // No assertions: the check is sat, and nothing in the model constrains the
  // array or the operands.
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();

  const Term cv = m.value(f);
  EXPECT_TRUE(cv.is_value());
  // A model value carries the sort of the term it is a value of, so this is
  // a float of the term's format (16 bits packed) rather than a bit-vector.
  EXPECT_EQ(cv.sort().kind(), SortKind::FP);
  EXPECT_EQ(cv.sort().fp_exp_size(), 5u);
  EXPECT_EQ(cv.sort().fp_sig_size(), 11u);

  // The model is a fixed snapshot, so asking again gives the same value.
  const Term again = m.value(f);
  EXPECT_TRUE(again.same_as(cv));
  EXPECT_EQ(packed(again), packed(cv));
}

// Regression test: the same out-of-model float-element array read, but as
// the operand of a floating-point *predicate* rather than of an operation.
// Model evaluation of a predicate resolves its operands and rebuilds it too,
// and had no tolerance at all for an operand that did not come back a
// constant:
//   CounterExample.cpp: ComputeFormulaUsingModel:
//   Assertion `simp.GetKind() == BVCONST' failed.
// A read the solve never constrained must be resolved to a value exactly as
// the operation arm above already does.
//
// Found by fuzzing with murxla driving the 2.x C API; delta-minimized. With
// array extensionality the same defect aborted inside the check, when the
// counterexample check evaluated an fp.geq / SMT '=' over array reads that
// the extensionality rewriting left out of the model.
TEST(fp_arrays, float_element_read_as_operand_of_fp_predicate)
{
  TermManager tm;
  Solver s(tm, self_checking());

  const Sort fp = tm.mk_fp_sort(5, 11);
  const Term a = tm.declare("a", tm.mk_array_sort(fp, fp));
  const Term rm = tm.declare("rm", tm.mk_rm_sort());
  const Term idx = to_fp(fp, rm, tm.mk_bv(1, "1", 2));
  const Term rd = a[idx];
  const Term mzero = tm.mk_fp_neg_zero(fp);
  const Term geq = fp_geq(rd, mzero);
  const Term isNaN = fp_is_nan(rd);

  // No assertions: the check is sat, and nothing constrains the array.
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();

  // A predicate has a truth value under the model -- true or false, never a
  // formula left standing over an unresolved read.
  const Term geqValue = m.value(geq);
  const Term isNaNValue = m.value(isNaN);
  ASSERT_TRUE(isTruthValue(geqValue));
  ASSERT_TRUE(isTruthValue(isNaNValue));

  // The read itself resolves to a float of the element's format...
  const Term cell = m.value(rd);
  ASSERT_TRUE(cell.is_value());
  ASSERT_EQ(cell.sort().kind(), SortKind::FP);
  EXPECT_EQ(cell.sort().fp_exp_size(), 5u);
  EXPECT_EQ(cell.sort().fp_sig_size(), 11u);

  // ...and that is the value the predicates were evaluated over: asking the
  // same questions of the value folds them outright, and the answers must
  // agree. An arbitrary value is fine; an inconsistent one is not.
  EXPECT_EQ(geqValue.to_bool(), m.bool_value(fp_geq(cell, mzero)));
  EXPECT_EQ(isNaNValue.to_bool(), m.bool_value(fp_is_nan(cell)));

  // The model is a fixed snapshot, so asking again agrees.
  EXPECT_EQ(geqValue.to_bool(), m.bool_value(geq));
}

// Every floating-point predicate takes the same route through model
// evaluation, so every one of them meets an out-of-model array read. Walk the
// lot: the binary comparisons, SMT-LIB '=' over floats (what 'distinct'
// negates, and the kind the murxla trace tripped), fp.eq, and the seven
// classification predicates.
TEST(fp_arrays, fp_predicates_over_out_of_model_reads)
{
  TermManager tm;
  Solver s(tm, self_checking());

  const Sort fp = tm.mk_fp_sort(5, 11);
  const Term a = tm.declare("a", tm.mk_array_sort(tm.mk_bv_sort(10), fp));
  const Term x = a[tm.mk_bv(10, "1100001111", 2)];
  const Term y = a[tm.mk_bv(10, "0001101011", 2)];
  const Term mzero = tm.mk_fp_neg_zero(fp);

  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();

  const Term predicates[] = {
      fp_lt(x, mzero),  fp_leq(x, mzero), fp_gt(x, mzero), fp_geq(x, mzero),
      fp_eq(x, y),      x == y,           fp_is_normal(x), fp_is_subnormal(x),
      fp_is_zero(x),    fp_is_inf(x),     fp_is_nan(x),    fp_is_neg(x),
      fp_is_pos(x),
  };

  for (std::size_t i = 0; i < sizeof(predicates) / sizeof(predicates[0]); i++)
  {
    const Term value = m.value(predicates[i]);
    EXPECT_TRUE(isTruthValue(value)) << "predicate " << i << " did not evaluate to a truth value";
  }
}

// The shape murxla reduced the report to, transcribed from its trace: an
// (Array (_ BitVec 10) Float16), a store chain over it, fp.geq of a read
// against -zero, 'distinct' of two reads (SMT-LIB '=' over floats, negated)
// where one index is a folded bvsdiv, and the disjunction of the two -- all
// asserted together and solved. The counterexample self-check is turned on
// (check-sanity), so every assertion is evaluated against the model that
// comes back and STP rejects its own answer if any of them is not satisfied.
//
// The trace's third conjunct, 'distinct' over two array *terms*, is left out:
// this case predates array extensionality, and what is left still drives
// every floating-point predicate in the evaluator over array reads.
TEST(fp_arrays, fp_predicates_over_array_reads_solve_and_self_check)
{
  TermManager tm;
  Solver s(tm, self_checking()); // construct and check the counterexample

  const Sort fp = tm.mk_fp_sort(5, 11);
  const Sort bv10 = tm.mk_bv_sort(10);
  const Term a = tm.declare("a", tm.mk_array_sort(bv10, fp));

  const Term i0 = tm.declare("i0", bv10);
  const Term i1 = tm.declare("i1", bv10);
  const Term c0 = tm.mk_bv(10, "1111101110", 2);
  const Term c1 = tm.mk_bv(10, "0001101011", 2);
  const Term c2 = tm.mk_bv(10, "1100001111", 2);
  const Term mzero = tm.mk_fp_neg_zero(fp);

  const Term read = a[c2];

  // A store chain over the array, at both constant and symbolic indexes.
  Term chain = store(a, i0, mzero);
  chain = store(chain, c0, read);
  chain = store(chain, c1, read);
  chain = store(chain, i0, read);
  chain = store(chain, i1, read);
  chain = store(chain, c1, mzero);
  chain = store(chain, c2, read);

  const Term geq = fp_geq(read, mzero);
  // 'distinct' over floats is the negation of SMT-LIB '=' -- the kind the
  // reported abort came through.
  const Term sdiv = bvsdiv(c1, c0);
  const Term distinct = !(a[i0] == a[sdiv]);

  s.add(geq || distinct);
  s.add(geq);
  // Keep the store chain live: what it reads back at c2 is what was stored.
  s.add(select(chain, c2) == read);

  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();

  // The asserted predicate holds under the model that came back.
  EXPECT_TRUE(m.bool_value(geq));

  // What array extensionality does to the trace's reads -- leave one of the
  // operands of a float 'distinct' out of the model -- is reached here by
  // asking about a cell no assertion mentions. It still has to answer.
  const Term elsewhere = a[tm.mk_bv(10, "0101010101", 2)];
  const Term apart = !(elsewhere == read);
  EXPECT_TRUE(isTruthValue(m.value(apart)));
}

TEST(fp_arrays, float_index_nan_payloads_share_one_cell)
{
  TermManager tm;
  Solver s(tm, self_checking());

  const Sort arrayType = tm.mk_array_sort(tm.mk_fp_sort(8, 24), tm.mk_bv_sort(8));
  const Term a = tm.declare("a", arrayType);

  // Two NaNs with different payloads and signs: the same abstract value,
  // so a store at one is read back at the other.
  const Term nan1 = float32(tm, 0x7F800001);
  const Term nan2 = float32(tm, 0xFFC00F00);
  const Term stored = store(a, nan1, tm.mk_bv(8, 0x2A));
  const Term back = select(stored, nan2);
  ASSERT_TRUE(s.entails(back == tm.mk_bv(8, 0x2A)).is_valid());
}

TEST(fp_arrays, float_index_zeros_are_distinct_cells)
{
  TermManager tm;
  Solver s(tm, self_checking());

  const Sort arrayType = tm.mk_array_sort(tm.mk_fp_sort(8, 24), tm.mk_bv_sort(8));
  const Term a = tm.declare("a", arrayType);

  const Term plus_zero = float32(tm, 0x00000000);
  const Term minus_zero = float32(tm, 0x80000000);

  // Store 1 at +0, then 2 at -0: the second store does not shadow the
  // first, because the cells differ.
  Term stored = store(a, plus_zero, tm.mk_bv(8, 1));
  stored = store(stored, minus_zero, tm.mk_bv(8, 2));

  ASSERT_TRUE(s.entails(select(stored, plus_zero) == tm.mk_bv(8, 1)).is_valid());
  ASSERT_TRUE(s.entails(select(stored, minus_zero) == tm.mk_bv(8, 2)).is_valid());
}

TEST(fp_arrays, float_index_symbolic_congruence)
{
  TermManager tm;
  Solver s(tm, self_checking());

  const Sort arrayType = tm.mk_array_sort(tm.mk_fp_sort(8, 24), tm.mk_bv_sort(8));
  const Term a = tm.declare("a", arrayType);

  const Sort f = tm.mk_fp_sort(8, 24);
  const Term x = tm.declare("x", f);
  const Term y = tm.declare("y", f);

  // Both NaN -- possibly under different bit patterns -- still means one
  // index value, so the reads agree.
  s.add(fp_is_nan(x));
  s.add(fp_is_nan(y));
  ASSERT_TRUE(s.entails(a[x] == a[y]).is_valid());
}

// The solve addresses a floating-point-indexed array through the canonical
// representative of the index. Model evaluation must use that same address:
// a symbolic NaN can have non-canonical carrier bits in the SAT model even
// though every NaN denotes the array sort's single NaN index value.
TEST(fp_arrays, float_index_model_uses_canonical_nan_cell)
{
  TermManager tm;
  Solver s(tm, self_checking()); // construct and check the counterexample

  const Sort fp = tm.mk_fp_sort(5, 11);
  const Term a = tm.declare("a", tm.mk_array_sort(fp, tm.mk_bv_sort(8)));
  const Term x = tm.declare("x", fp);
  const Term read = a[x];
  const Term expected = tm.mk_bv(8, 0x2A);

  s.add(fp_is_nan(x));
  s.add(read == expected);
  ASSERT_TRUE(s.check_sat().is_sat());

  EXPECT_EQ(s.model().uint64_value(read), 0x2Au);
}

// A read over a store, both at NaN indexes: one cell, so the read is the
// stored value. Carrier reads nested below the encoded root still retain the
// array's source sort, and the engine's model evaluator once expanded this
// read-over-write forever, redispatching its canonical child as though it were
// a fresh source access and canonicalising it again; it must treat the whole
// encoded DAG as target language while evaluating it.
TEST(fp_arrays, float_index_model_read_over_write_is_lowered_once)
{
  TermManager tm;
  Solver s(tm, self_checking());

  const Sort fp = tm.mk_fp_sort(5, 11);
  const Term a = tm.declare("a", tm.mk_array_sort(fp, tm.mk_bv_sort(8)));
  const Term x = tm.declare("x", fp);
  const Term y = tm.declare("y", fp);
  const Term expected = tm.mk_bv(8, 0x2A);
  const Term stored = store(a, x, expected);
  const Term read = select(stored, y);

  s.add(fp_is_nan(x));
  s.add(fp_is_nan(y));
  ASSERT_TRUE(s.check_sat().is_sat());

  EXPECT_EQ(s.model().uint64_value(read), 0x2Au);
}

TEST(fp_arrays, float_index_constant_model_cell)
{
  TermManager tm;
  Solver s(tm, self_checking());

  const Sort fp = tm.mk_fp_sort(5, 11);
  const Term a = tm.declare("a", tm.mk_array_sort(fp, tm.mk_bv_sort(8)));
  const Term index = tm.mk_fp_from_bits(fp, tm.mk_bv(16, 0x3C00));
  const Term read = a[index];
  const Term expected = tm.mk_bv(8, 0x2A);

  s.add(read == expected);
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.model().uint64_value(read), 0x2Au);
}

TEST(fp_arrays, float_index_float_element_combined)
{
  TermManager tm;
  Solver s(tm, self_checking());

  const Sort f = tm.mk_fp_sort(5, 11);
  const Sort arrayType = tm.mk_array_sort(f, f);
  const Term a = tm.declare("a", arrayType);

  // '=' on the float indexes (all NaNs one cell) and '=' on the float
  // elements (the read returns the stored float) in one query.
  const Term nan1 = tm.mk_fp_from_bits(f, tm.mk_bv(16, 0x7C01));
  const Term nan2 = tm.mk_fp_from_bits(f, tm.mk_bv(16, 0xFE00));
  const Term v = tm.declare("v", f);

  const Term stored = store(a, nan1, v);
  const Term back = select(stored, nan2);
  ASSERT_TRUE(s.entails(back == v).is_valid());
}

TEST(fp_arrays, roundingmode_element_reads_are_modes)
{
  TermManager tm;
  Solver s(tm, self_checking());

  const Sort arrayType = tm.mk_array_sort(tm.mk_bv_sort(2), tm.mk_rm_sort());
  const Term a = tm.declare("a", arrayType);
  const Term i = tm.declare("i", tm.mk_bv_sort(2));

  // Whatever the array and index are, the read denotes one of the five
  // modes -- the 27 junk patterns of the 5-bit carrier are not values of
  // the sort.
  const Term read = a[i];
  ASSERT_TRUE(s.entails(oneOfTheModes(tm, read)).is_valid());
}

TEST(fp_arrays, roundingmode_element_store_read_use)
{
  TermManager tm;
  Solver s(tm, self_checking());

  const Sort arrayType = tm.mk_array_sort(tm.mk_bv_sort(2), tm.mk_rm_sort());
  const Term a = tm.declare("a", arrayType);

  const Term idx = tm.mk_bv(2, 1);
  const Term stored = store(a, idx, tm.mk_rm(RoundingMode::RTZ));
  const Term back = select(stored, idx);
  ASSERT_TRUE(s.entails(back == tm.mk_rm(RoundingMode::RTZ)).is_valid());

  // The read is a rounding mode like any other: it can steer an operation.
  // Under any mode, 1.0 + 1.0 is exactly 2.0.
  const Term sum = fp_add(back, float32(tm, 0x3F800000), float32(tm, 0x3F800000));
  ASSERT_TRUE(s.entails(sum == float32(tm, 0x40000000)).is_valid());
}

TEST(fp_arrays, roundingmode_element_model_value)
{
  TermManager tm;
  Solver s(tm, self_checking());

  const Sort arrayType = tm.mk_array_sort(tm.mk_bv_sort(2), tm.mk_rm_sort());
  const Term a = tm.declare("a", arrayType);

  const Term read = a[tm.mk_bv(2, 2)];
  s.add(read == tm.mk_rm(RoundingMode::RTZ));
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();

  // The model value is a mode, as for a RoundingMode symbol. 3.x: it reads as
  // the RoundingMode enumerator (rm_value), not as the carrier's bits.
  EXPECT_EQ(m.rm_value(read), RoundingMode::RTZ);
  EXPECT_TRUE(m.value(read).same_as(tm.mk_rm(RoundingMode::RTZ)));
}

TEST(fp_arrays, unobserved_roundingmode_element_defaults_to_rne)
{
  TermManager tm;
  Solver s(tm, self_checking());

  const Sort arrayType = tm.mk_array_sort(tm.mk_bv_sort(2), tm.mk_rm_sort());
  const Term a = tm.declare("a", arrayType);
  const Term read = a[tm.mk_bv(2, 0)];

  // These two results distinguish the illegal 0b11111 carrier value from all
  // five rounding modes: it underflows upward like RTP but rounds 1/3 downward
  // like RTN/RTZ. Model completion chooses RNE, so both the reported mode and
  // every operation evaluated through it must have RNE's behaviour.
  const Term tiny = float32(tm, 0x0D800000); // 2^-100
  const Term underflow = fp_mul(read, tiny, tiny);
  const Term third = fp_div(read, float32(tm, 0x3F800000), float32(tm, 0x40400000));

  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();

  // Read the operations first so they cannot merely inherit a mode cached by
  // the direct read below.
  EXPECT_EQ(packed(m.value(underflow)), 0x00000000u);
  EXPECT_EQ(packed(m.value(third)), 0x3EAAAAABu);
  EXPECT_EQ(m.rm_value(read), RoundingMode::RNE);
}

// Regression test: evaluating a floating-point operation whose rounding mode
// is an array read that the solve never constrained. The solve is fine;
// reading the term's value back used to abort. Model evaluation re-totalised
// the term before blasting it, and the totalising pass pinned the
// rounding-mode-element read to the five legal encodings by conjoining a
// constraint onto its input -- sound for an asserted formula, but here the
// input is a *term*, and the wrap handed the blaster an AND it cannot blast:
//   Fatal Error: FloatBlaster::BlastNode: unhandled kind: (AND ...)
// The pinning must apply to formulas only. The value itself is unconstrained
// (the model says nothing about the read, and an out-of-model read resolves
// arbitrarily), so only its shape is checked.
//
// Found by fuzzing with murxla driving the 2.x C API; delta-minimized.
TEST(fp_arrays, roundingmode_element_read_as_mode_of_evaluated_term)
{
  TermManager tm;
  Solver s(tm, self_checking());

  const Sort rm = tm.mk_rm_sort();
  const Term a = tm.declare("a", tm.mk_array_sort(rm, rm));
  const Term idx = tm.declare("x0", rm);
  const Term rd = a[idx];
  const Term b = tm.declare("b", tm.mk_bv_sort(8));
  const Term f = fp_neg(to_fp_unsigned(tm.mk_fp_sort(8, 24), rd, b));

  // No assertions: the check is sat, and the model leaves both the array and
  // the term's operands entirely unconstrained.
  ASSERT_TRUE(s.check_sat().is_sat());

  // The read-back must produce a value of the term's sort -- some float of
  // the term's format that it can take under a legal rounding mode -- not
  // abort.
  const Term cv = s.model().value(f);
  EXPECT_TRUE(cv.is_value());
  EXPECT_EQ(cv.sort().kind(), SortKind::FP);
  EXPECT_EQ(cv.sort().fp_exp_size(), 8u);
  EXPECT_EQ(cv.sort().fp_sig_size(), 24u);
}

TEST(fp_arrays, roundingmode_index)
{
  TermManager tm;
  Solver s(tm, self_checking());

  const Sort arrayType = tm.mk_array_sort(tm.mk_rm_sort(), tm.mk_bv_sort(8));
  const Term a = tm.declare("a", arrayType);

  const Term stored = store(a, tm.mk_rm(RoundingMode::RNE), tm.mk_bv(8, 0x11));

  // The RNE cell holds what was stored there...
  ASSERT_TRUE(
      s.entails(select(stored, tm.mk_rm(RoundingMode::RNE)) == tm.mk_bv(8, 0x11)).is_valid());
  // ...while the RTZ cell is untouched by that store, so nothing forces its
  // value.
  ASSERT_TRUE(
      s.entails(select(stored, tm.mk_rm(RoundingMode::RTZ)) == tm.mk_bv(8, 0x11)).is_invalid());

  // A RoundingMode symbol serves as an index too.
  const Term r = tm.declare("r", tm.mk_rm_sort());
  const Term read = select(stored, r);
  s.add(r == tm.mk_rm(RoundingMode::RNE));
  ASSERT_TRUE(s.entails(read == tm.mk_bv(8, 0x11)).is_valid());
}

// Model evaluation must compare array indexes by their carrier value, not by
// the source-sort decoration on the constant node. The SAT model supplies a
// plain five-bit value for r, whereas the store index is the source-sorted
// RNE constant. Those denote the same RoundingMode even though they are not
// the same interned node.
TEST(fp_arrays, roundingmode_index_read_over_write_model)
{
  TermManager tm;
  Solver s(tm, self_checking());

  const Sort arrayType = tm.mk_array_sort(tm.mk_rm_sort(), tm.mk_bv_sort(8));
  const Term a = tm.declare("a", arrayType);
  const Term stored = store(a, tm.mk_rm(RoundingMode::RNE), tm.mk_bv(8, 0x11));
  const Term r = tm.declare("r", tm.mk_rm_sort());
  const Term read = select(stored, r);

  // Pin r to RNE without asserting r = RNE directly: direct substitution can
  // hide the typed/plain constant boundary exercised by model evaluation.
  for (const RoundingMode mode :
       {RoundingMode::RNA, RoundingMode::RTP, RoundingMode::RTN, RoundingMode::RTZ})
    s.add(!(r == tm.mk_rm(mode)));

  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.model().uint64_value(read), 0x11u);
}

TEST(fp_arrays, type_round_trip)
{
  TermManager tm;
  Solver s(tm, self_checking());

  const Sort arrayType = tm.mk_array_sort(tm.mk_fp_sort(8, 24), tm.mk_rm_sort());
  const Term a = tm.declare("a", arrayType);
  EXPECT_EQ(a.sort().kind(), SortKind::ARRAY);

  // A term's sort is the declared index and element sorts, not their
  // bit-vector carriers: a fresh symbol of the returned sort behaves like the
  // original -- its reads take float indexes and denote rounding modes.
  const Sort again = a.sort();
  EXPECT_TRUE(again == arrayType);
  EXPECT_TRUE(again.array_index() == tm.mk_fp_sort(8, 24));
  EXPECT_TRUE(again.array_element().is_rm());
  const Term b = tm.declare("b", again);

  const Term read = b[float32(tm, 0x3F800000)];
  ASSERT_TRUE(s.entails(oneOfTheModes(tm, read)).is_valid());
}
