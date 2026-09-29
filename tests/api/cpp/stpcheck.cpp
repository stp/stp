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

// stpcheck.cpp -- an 8-bit symbol zero-extended to 32 bits by
// concatenation and incremented never wraps to zero: x + 1 != 0 is entailed.
// 2.x then printed a counterexample, which was empty; an entailment that
// holds has no counterexample, and the solver has no model to give.

#include "api_common.hpp"

using namespace stp;

namespace
{

TEST(extend_adder_notexpr, one)
{
  TermManager tm;
  Solver s(tm);
  // 2.x flags 'n' (print the verdict: the Entailment) and 'd'
  s.options().set_bool(Option::CHECK_SANITY, true);

  // 8-bit variable 'x'
  const Term x = tm.declare("x", tm.mk_bv_sort(8));

  // 32 bit constant value 1
  const Term one = tm.mk_bv(32, 1);

  // 24 bit constant value 0
  const Term bit24_zero = tm.mk_bv(24, 0);
  // 32 bit constant value 0
  const Term bit32_zero = tm.mk_bv(32, 0);

  // Extending 8-bit variable to 32-bit value
  const Term zero_concat_x = concat(bit24_zero, x);
  const Term xp1 = bvadd(zero_concat_x, one);

  // Instead of the concatenation, sign_extend(24, x) was also tried
  // const Term signextend_x = sign_extend(24, x);
  // const Term xp1 = bvadd(signextend_x, one);

  // x+1=0
  Term eq = xp1 == bit32_zero;

  // x+1!=0
  eq = !eq;

  const Entailment query = s.entails(eq);
  ASSERT_TRUE(query.is_valid());
  EXPECT_EQ(query.str(), "valid");
  // 3.x: a valid entailment leaves no model, so no counterexample to print
  API_EXPECT_ERROR(ErrorCode::NO_MODEL, s.model());
}

} // namespace
