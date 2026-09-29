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

// mdempsky.cpp -- three queries over the sums A + B and A + B + 42, each
// in its own push/pop: the growing conjunctions are not entailed, the last
// one because it is contradictory (A + B + 42 both above and below 5).

#include "api_common.hpp"

#include <iostream>

using namespace stp;

namespace
{

TEST(mdempsky, one)
{
  TermManager tm;
  Solver s(tm);
  s.options().set_bool(Option::CHECK_SANITY, true); // every 2.x checker had 'd' on

  const Term A = tm.declare("A", tm.mk_bv_sort(32));
  const Term B = tm.declare("B", tm.mk_bv_sort(32));

  const Term AplusB = bvadd(A, B);
  const Term AplusBplus42 = bvadd(AplusB, tm.mk_bv(32, 42));

  const Term myexpr = bvugt(AplusB, tm.mk_bv(32, 100));
  const Term myexpr2 = bvugt(AplusBplus42, tm.mk_bv(32, 5));
  const Term both_of_them = myexpr && myexpr2;
  const Term myexpr3 = bvult(AplusBplus42, tm.mk_bv(32, 5));
  const Term all_of_them = both_of_them && myexpr3;

  s.push();
  EXPECT_TRUE(s.entails(myexpr).is_invalid());
  s.pop();

  s.push();
  EXPECT_TRUE(s.entails(both_of_them).is_invalid());
  s.pop();

  s.push();
  const Entailment ret = s.entails(all_of_them);
  std::cout << "ret: " << ret << "\n";
  EXPECT_TRUE(ret.is_invalid()); // (2.x printed 0 here: invalid)
  s.pop();
}

} // namespace
