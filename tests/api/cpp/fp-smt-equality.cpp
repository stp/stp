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

// fp-smt-equality.cpp -- SMT-LIB '=' over floating-point operands.
//
// eq(a, b) (and a == b) over two floats is SMT-LIB '=', not fp.eq: +0 and -0
// are distinct, and every NaN equals every NaN. fp_eq is the IEEE equality.
//
// Regression tests: the equality over floats used to be built as a generic
// equality. A leaf-vs-leaf equality (x = y) folded to a bit-vector comparison
// and behaved, but once an operand was a composite floating-point term (here
// fp.neg x) the generic equality over floats was not discharged by the
// floating-point solver, and the solve aborted with
//   Fatal Error: TopLevelSTPAux: reached the end without proper conclusion.
// rather than fail an expectation here.

#include "api_common.hpp"

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

} // namespace

// x = -x holds exactly for NaN under SMT '=' (NaN = NaN, and -NaN is NaN), so
// the constraint is satisfiable.
TEST(fp_smt_equality, self_negation_is_sat)
{
  TermManager tm;
  Solver s(tm, self_checking());
  const Term x = tm.declare("x", tm.mk_fp_sort(11, 53));

  s.add(x == fp_neg(x));

  EXPECT_TRUE(s.check_sat().is_sat());
}

// The only witness for x = -x is NaN -- in particular +0 = -0 is false under
// SMT '=' -- so ruling out NaN makes the same constraint unsatisfiable. This
// pins the SMT-LIB '=' semantics, not merely the absence of the abort.
TEST(fp_smt_equality, self_negation_requires_nan)
{
  TermManager tm;
  Solver s(tm, self_checking());
  const Term x = tm.declare("x", tm.mk_fp_sort(11, 53));

  s.add(x == fp_neg(x));
  s.add(!fp_is_nan(x));

  EXPECT_TRUE(s.check_sat().is_unsat());
}
