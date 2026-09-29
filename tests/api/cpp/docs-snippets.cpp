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

// docs-snippets.cpp -- the C++ snippets of docs/api.rst, as they are there
// (keep the two in step), run: the first answers what its comments say, the
// second is satisfiable and its model is read after its check.

#include "api_common.hpp"

#include <sstream>

using namespace stp;

TEST(DocsSnippets, the_cpp_snippets_run_as_documented)
{
  std::ostringstream out;

  TermManager tm;
  Sort bv32 = tm.mk_bv_sort(32);
  Term x = tm.declare("x", bv32), y = tm.declare("y", bv32);

  Solver s(tm);
  s.add(x * 3 == 7);   // literals take the term's sort and must fit
  s.add(bvult(y, 10)); // no <,> on terms: signedness is explicit
  if (s.check_sat().is_sat())
  {
    Model m = s.model();
    out << m.uint64_value(x) << "\n";   // 2863311533
    out << m.value(x * 3) << "\n";      // #x00000007
  }
  EXPECT_EQ(out.str(), "2863311533\n#x00000007\n");

  // Arrays, floating point, uninterpreted functions and Reals use the same shapes:
  Sort arr = tm.mk_array_sort(bv32, tm.mk_bv_sort(8));
  Term a = tm.declare("a", arr), i = tm.declare("i", bv32);
  s.add(a[i] == 42);                                            // select; store(a, i, v) for the update
  s.add(a == store(tm.declare("b", arr), i, tm.mk_bv(8, 42)));  // extensional
  s.add(a != tm.mk_const_array(arr, tm.mk_bv(8, 0)));          // ((as const ...) #x00)

  Sort f32 = tm.mk_fp32_sort();
  Term fx = tm.declare("fx", f32);
  s.add(fp_add(RoundingMode::RNE, fx, 1.0) == tm.mk_fp(f32, RoundingMode::RNE, 3.0));

  Term f = tm.declare("f", tm.mk_fun_sort({bv32}, bv32));
  s.add(f(x) == f(y));

  Term r = tm.declare("r", tm.mk_real_sort());
  s.add(real_lt(r + 1, tm.mk_real("3/2")));

  bool read = false;
  if (s.check_sat().is_sat())
  {
    Model m = s.model();
    FloatValue v = m.fp_value(fx);          // sign, exponent, significand, class
    FunctionValue fv = m.function_value(f); // entries and a default
    RationalValue q = m.real_value(r);      // numerator and denominator
    ASSERT_TRUE(v.to_double().has_value());
    EXPECT_NEAR(*v.to_double(), 2.0, 1e-6); // 2, or the float below it, which rounds up too
    EXPECT_TRUE(fv.apply({m.value(x)}).same_as(fv.apply({m.value(y)})));
    EXPECT_TRUE(m.bool_value(real_lt(tm.mk_real(q.numerator + "/" + q.denominator), tm.mk_real("1/2"))));
    EXPECT_EQ(m.uint64_value(a[i]), 42u);
    read = true;
  }
  EXPECT_TRUE(read);

  // Options are set at construction or on the live solver:
  Options o;
  o.set("max-time", "2s"); // the text form: a duration needs its unit here
  if (has_sat_backend("cadical"))
    o.set_str("sat-backend", "cadical");
  o.set_args({"--fp-abstraction", "--bb.div-v3=false"});
  Solver s2(tm, o);
  s2.options().set_bool("check-sanity", true); // anytime
  const Term assumption = x == 5;
  Result res = s2.check_sat({assumption}, CheckBudget{std::chrono::milliseconds(500), std::nullopt});
  EXPECT_TRUE(res.is_sat()) << res;
}
