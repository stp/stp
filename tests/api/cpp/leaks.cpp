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

// leaks.cpp -- managers, solvers and terms created and destroyed over and
// over.
//
// The 2.x suite was written to be run under valgrind and checked nothing
// itself. A leak is still valgrind's to find, but these cases also check what
// the 3.x lifetimes promise: a manager lives while anything that came from it
// lives, destruction order is free, and every manager has its own name table.

#include "api_common.hpp"

#include <cstdint>
#include <optional>
#include <string>
#include <vector>

using namespace stp;

namespace
{

// The options of a 2.x checker: vc_createValidityChecker set 'd', so every
// 2.x case ran with the counterexample self-check on, and every solver here
// runs with check-sanity.
Options checkerOptions()
{
  Options o;
  o.set_bool("check-sanity", true);
  return o;
}

} // namespace

TEST(Leaks, leak)
{
  for (int i = 0; i < 10; i++)
  {
    TermManager tm;
    // 2.x set 'n', 'd' and 'p'. 'n' printed the verdict, which 3.x returns as
    // a value; 'd' and 'p' are check-sanity and print-counterex.
    Options o = checkerOptions();
    o.set_bool("print-counterex", true);
    Solver s(tm, o);

    // A fresh manager's name table is empty: the previous iteration's
    // symbols went with its manager.
    EXPECT_TRUE(tm.symbols().empty());

    // create 50 expressions
    const Sort bv32 = tm.mk_bv_sort(32);
    std::vector<Term> a;
    for (int k = 1; k <= 50; k++)
      a.push_back(tm.declare("a" + std::to_string(k), bv32));
    ASSERT_EQ(tm.symbols().size(), 50u);

    // Release every handle. A declaration is the manager's: the name still
    // finds its symbol until the manager goes.
    a.clear();
    EXPECT_EQ(tm.symbols().size(), 50u);
    ASSERT_TRUE(tm.symbol("a50").has_value());
    EXPECT_TRUE(tm.symbol("a50")->sort() == bv32);
  }
}

TEST(Leaks, boolean)
{
  std::optional<TermManager> tm(std::in_place);
  std::optional<Solver> s(std::in_place, *tm, checkerOptions());

  const Term x = tm->declare("x", tm->mk_bool_sort());
  const Term y = tm->declare("y", tm->mk_bool_sort());

  const Term x_and_y = x && y;
  const Term not_x_and_y = !x_and_y;

  const Term not_x = !x;
  const Term not_y = !y;
  const Term not_x_or_not_y = not_x || not_y;

  const Term equiv = not_x_and_y == not_x_or_not_y;

  // De Morgan (2.x printed the verdict: 1, valid)
  EXPECT_TRUE(s->entails(equiv).is_valid());

  // 2.x deleted every expression before vc_Destroy. In 3.x the order is
  // free: the solver and the manager handle go first, the terms keep the
  // manager alive, and a new solver over it decides the same question.
  s.reset();
  tm.reset();
  EXPECT_EQ(equiv.manager().symbols().size(), 2u);
  Solver again(equiv.manager(), checkerOptions());
  EXPECT_TRUE(again.entails(equiv).is_valid());
}

TEST(Leaks, sqaures)
{
  // Do some simple arithmetic by creating an expression involving constants
  // and then simplifying it. Since we create and destroy a fresh manager and
  // solver each time, we shouldn't leak any memory.
  for (std::uint64_t i = 1; i <= 100; i++)
  {
    TermManager tm;
    Solver s(tm, checkerOptions());
    const Term arg = tm.mk_bv(64, i);
    const Term product = bvmul(arg, arg);
    const Term simp = tm.simplify(product);
    const std::uint64_t j = simp.to_uint64();
    EXPECT_EQ(j, i * i);
  }
}
