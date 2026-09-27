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

// api3-fp-model-eval-predicates.cpp -- floating-point predicates and value
// operations evaluated under a model.
//
// Regression tests for floating-point predicate evaluation in the model. STP's
// model-formula evaluator, ComputeFormulaUsingModel
// (lib/AbsRefineCounterExample/CounterExample.cpp), is walked while a
// counterexample is built and checked (option check-sanity). It must be able
// to evaluate every floating-point predicate kind. A rewrite of that file
// dropped the cases for all thirteen of them (FP_EQ, FP_SMT_EQ, the four
// ordered comparisons, and the seven classification predicates), so a
// satisfiable check whose model reached one aborted with
//   FP_<X> Fatal Error: ComputeFormulaUsingModel: the kind has not been implemented
// instead of solving.
//
// A predicate only reaches the model evaluator when its node survives
// bit-blasting. A bare (fp.isZero x) is discharged in the SAT circuit and never
// gets there; a predicate over an fp.fp-reinterpreted value, kept inside an
// ite, is not, and the counterexample check then walks it. These build exactly
// that shape. Found by fuzzing with murxla; the second test is its minimized
// query, the first exercises the whole predicate family.
//
// 3.x: check-sanity is off by default (2.x switched it on for every checker),
// so every solver here sets it to put the engine's check on the path. The
// same terms are then evaluated through the API's own Model, which evaluates
// any term of the manager: the asserted formula must hold there too, and the
// predicate under test must come back as a truth value.

#include "api3_common.hpp"

using namespace stp;

namespace
{

// A solver whose checks construct and check the counterexample, as every 2.x
// checker did.
void check_sanity(Solver& s)
{
  s.options().set_bool("check-sanity", true);
}

// A Float32 reinterpreted from 32 bit-vector bits (fp.fp). Its node is a
// reinterpret, not a leaf, so predicates over it survive to model evaluation.
Term float32FromBits(TermManager& tm, const char* name)
{
  return to_fp_from_bits(tm.mk_fp_sort(8, 24), tm.declare(name, tm.mk_bv_sort(32)));
}

// The thirteen floating-point predicate kinds, as the API builds them
// (eq over floats is SMT-LIB '='; fp_eq is IEEE equality).
Term predicate(int which, const Term& a, const Term& b)
{
  switch (which)
  {
    case 0: return fp_eq(a, b);
    case 1: return eq(a, b);
    case 2: return fp_leq(a, b);
    case 3: return fp_lt(a, b);
    case 4: return fp_geq(a, b);
    case 5: return fp_gt(a, b);
    case 6: return fp_is_nan(a);
    case 7: return fp_is_zero(a);
    case 8: return fp_is_normal(a);
    case 9: return fp_is_subnormal(a);
    case 10: return fp_is_inf(a);
    case 11: return fp_is_pos(a);
    default: return fp_is_neg(a);
  }
}
const int NUM_PREDICATES = 13;

} // namespace

// Each predicate kind, reached at model-evaluation time. The predicate under
// test is put in a boolean position (the condition of the ite the outer
// fp.isZero is taken over), so the counterexample walk reaches it. Before the
// fix each one aborted; here every kind solves. The check is satisfiable for
// every kind -- taking the ite's then-branch makes the selected value +zero,
// which is a zero -- independent of the predicate's own truth value.
TEST(fp_model_eval_predicates, every_predicate_kind_is_evaluated)
{
  for (int which = 0; which < NUM_PREDICATES; which++)
  {
    TermManager tm;
    Solver s(tm);
    check_sanity(s);
    const Sort fp = tm.mk_fp_sort(8, 24);

    const Term f = float32FromBits(tm, "f");
    const Term g = float32FromBits(tm, "g");
    const Term inner = predicate(which, f, g);
    const Term other = bvult(tm.declare("k", tm.mk_bv_sort(8)), tm.mk_bv(8, 42));
    const Term cond = !(other == inner); // not (iff other inner)
    const Term sel = ite(cond, tm.mk_fp_pos_zero(fp), f);
    const Term asserted = fp_is_zero(sel);

    s.add(asserted);

    ASSERT_TRUE(s.check_sat().is_sat()) << "predicate kind index " << which;
    const Model m = s.model();
    EXPECT_TRUE(m.bool_value(asserted)) << "predicate kind index " << which;
    const Term value = m.value(inner);
    EXPECT_TRUE(value.is_value() && value.sort().is_bool()) << "predicate kind index " << which;
    EXPECT_EQ(m.bool_value(cond), m.bool_value(other) != value.to_bool())
        << "predicate kind index " << which;
  }
}

// The fuzzer's minimized query itself: fp.isZero over an ite whose condition
// pairs a bit-vector comparison with fp.eq of an fp.fp value with itself. It
// is satisfiable.
TEST(fp_model_eval_predicates, fuzzed_iszero_over_ite_with_fp_eq_is_sat)
{
  TermManager tm;
  Solver s(tm);
  check_sanity(s);
  const Sort fp = tm.mk_fp_sort(8, 24);

  const Term f = float32FromBits(tm, "f");
  const Term bv = bvuge(tm.declare("x", tm.mk_bv_sort(23)), tm.declare("y", tm.mk_bv_sort(23)));
  const Term cond = !(bv == fp_eq(f, f));
  const Term sel = ite(cond, fp_max(tm.mk_fp_pos_zero(fp), tm.mk_fp_pos_zero(fp)), f);
  const Term asserted = fp_is_zero(sel);

  s.add(asserted);

  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  EXPECT_TRUE(m.bool_value(asserted));
  EXPECT_EQ(m.bool_value(cond), m.bool_value(bv) != m.bool_value(fp_eq(f, f)));
}

// Regression: an FP *value* operation (a conversion, fp.sqrt, fp.max) reached
// during model evaluation must keep its operand format. The engine's
// TermToConstTermUsingModel strips formats; when the evaluator re-blasts such
// an op via NonMemberBVConstEvaluator -> BlastNode, the operand format has to
// be restored or SymFPU's decode asserts (packed width vs format's packed
// width, symbolic_fp.cpp). The op reaches the evaluator the same way the
// predicates do: kept live under a predicate so its node survives
// bit-blasting. This is the fuzzer's minimized query: fp.to_sbv feeds
// fp.to_fp_unsigned into fp.max under fp.isPositive; it is satisfiable.
TEST(fp_model_eval_predicates, fp_value_op_reached_in_model_keeps_format)
{
  TermManager tm;
  Solver s(tm);
  check_sanity(s);
  const Sort fp = tm.mk_fp_sort(8, 24);
  const Term rna = tm.mk_rm(RoundingMode::RNA);
  const Term x4 = tm.declare("x4", fp);
  const Term x5 = tm.declare("x5", tm.mk_rm_sort());
  const Term x0 = tm.declare("x0", tm.mk_bv_sort(23));
  const Term x2 = tm.declare("x2", tm.mk_bv_sort(32));
  const Term neg = bvneg(tm.mk_bv(23, "1594224", 10));

  const Term sq = fp_is_subnormal(fp_sqrt(rna, x4));
  const Term t12 = fp_to_sbv(63, x5, x4); // FP -> BV63
  const Term cond = bvslt(neg, x0) == sq;
  const Term rm = ite(cond, rna, x5);
  const Term conv = to_fp_unsigned(fp, rm, t12); // BV63 -> Float32
  const Term pred = fp_is_pos(fp_max(conv, conv));
  const Term t22 = bvsge(x2, x2);

  s.add(t22);
  s.add(implies(t22, pred));

  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  EXPECT_TRUE(m.bool_value(pred));
  // the value operations themselves evaluate at their own formats
  const Term c = m.value(conv);
  EXPECT_TRUE(c.is_value());
  EXPECT_EQ(c.sort().fp_exp_size(), 8u);
  EXPECT_EQ(c.sort().fp_sig_size(), 24u);
  EXPECT_EQ(m.value(t12).sort().bv_size(), 63u);
}
