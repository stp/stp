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

// api3-bv-abstraction-array-candidate-is-bound.cpp -- a BV abstraction's
// refinement must not materialize a candidate before the array-equality
// checker has bound its graph.
//
// The array-equality consistency checker owns the complete array graph for a
// solve, and ConstructCounterExample refuses to materialize a candidate before
// that graph has been bound -- a model assembled ahead of the checker would be
// read back as if the checker had certified it.
//
// A BV abstraction can reach that point first. It replaces an operation with
// free Booleans and is refined from candidate models, so the driver has to pin
// it before anything else reads the candidate; where it did not, a solve whose
// array equality was still pending had a candidate built underneath it:
//
//   Fatal Error: array-equality: a SAT candidate was materialized before the
//   complete array graph was bound
//
// The shape is a reduced fuzzer trace and every part of it is load-bearing.
// The array disequality is not asserted until after the first solve has fixed
// the abstraction records, and it arrives inside an assumption scope, so the
// graph for it is bound on a later round than the one the abstraction was
// installed on. A hand-written sequence does not get there: with the fix
// reverted, half a dozen other guards on this route fire first, and only this
// ordering reaches the one under test.
//
// Both checks answer for the caller's assertions, so the test pins the
// verdicts as well as the absence of the engine failure (which the API would
// report as INTERNAL): the first is unsatisfiable under its assumptions and
// the second, with those assumptions retracted, is satisfiable.

#include "api3_common.hpp"

using namespace stp;

namespace
{

const std::uint32_t WIDE = 88; // the width the abstraction engages on here
const std::uint32_t INDEX = 32;

} // namespace

TEST(bv_abstraction_array_candidate_is_bound, array_disequality_inside_an_assumption_scope)
{
  TermManager tm;
  Options o;
  o.set_str("array-equality", "on");          // decide whole-array equality (extensional arrays)
  o.set_str("uninterpreted-functions", "on"); // uninterpreted functions
  o.set_bool("bv-eq-abstraction", true);
  o.set_bool("bv-term-abstraction", true);
  o.set_uint("bv-abstraction-width", 1);
  o.set_uint("bv-eq-refine-width", 1);
  o.set_str("incremental", "on"); // incremental driver from the first check
  // 2.x checked the counterexample of every satisfiable answer ('d', forced
  // on every checker); 3.x leaves check-sanity off by default.
  o.set_bool("check-sanity", true);
  Solver s(tm, o);

  const Sort wide = tm.mk_bv_sort(WIDE);
  const Sort boolean = tm.mk_bool_sort();
  const Term x = tm.declare("x", wide);
  const Term y = tm.declare("y", wide);
  const Term z = tm.declare("z", wide);
  const Term w = tm.declare("w", wide);
  const Term v = tm.declare("v", wide);

  const Term maxSigned = tm.mk_bv_max_signed(WIDE); // #b0 followed by ones
  const Term minSigned = tm.mk_bv_min_signed(WIDE); // #b1 followed by zeroes
  const Term zero = tm.mk_bv_zero(WIDE);

  // A comparison over abstracted arithmetic: the term abstraction stands in
  // for the remainder, and the comparison is what the refinement pins.
  const Term rem = bvsrem(bvneg(maxSigned), bvneg(minSigned));
  const Term remGtX = bvugt(rem, x);
  const Term quotient = bvudiv(minSigned, minSigned);

  const Term f = tm.declare("f", tm.mk_fun_sort({wide}, wide));
  ASSERT_FALSE(f.is_null());

  const Term p = tm.declare("p", tm.mk_fun_sort({wide, boolean, wide, boolean}, boolean));
  ASSERT_FALSE(p.is_null());

  const Term rm = tm.declare("rm", tm.mk_rm_sort());
  const Term converted = to_fp_unsigned(tm.mk_fp_sort(8, 24), rm, y);
  const Term isNaN = fp_is_nan(converted);

  const Term p0 = p(v, remGtX, y, remGtX);
  ASSERT_FALSE(p0.is_null());

  const Term p1 = p(minSigned, remGtX == p0, y, bvsge(z, w));
  ASSERT_FALSE(p1.is_null());

  const Term fy = f(y);
  ASSERT_FALSE(fy.is_null());

  const Term p2 = p(fy, isNaN, rem, p0);
  ASSERT_FALSE(p2.is_null());

  const Term p3 = p(y, remGtX, tm.declare("u", wide), remGtX);
  ASSERT_FALSE(p3.is_null());

  const Term p4 = p(zero, p3, y, p1);
  ASSERT_FALSE(p4.is_null());

  s.add(and_({p4, p2}));

  // The array only enters after the abstraction records exist.
  const Term array = tm.declare("a", tm.mk_array_sort(tm.mk_bv_sort(INDEX), wide));
  const Term index = tm.declare("i", tm.mk_bv_sort(INDEX));
  const Term storeAtIndex = store(array, index, y);
  const Term storeAtConst =
      store(array, tm.mk_bv(INDEX, "01111011000001100101000100110101", 2), quotient);
  const Term storesDiffer = !(storeAtConst == storeAtIndex);

  const Term p5 = p(x, p0, x, storesDiffer);
  ASSERT_FALSE(p5.is_null());

  s.push();
  s.add(isNaN == p0);
  s.add(p0);
  s.add(p5 == p0);
  EXPECT_EQ(Verdict::UNSAT, s.check_sat().verdict());

  s.pop();
  EXPECT_EQ(Verdict::SAT, s.check_sat().verdict());
}
