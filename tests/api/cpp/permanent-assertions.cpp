/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: October, 2026
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

#include "api_common.hpp"
#include <algorithm>

// The API's permanent assertions are the incremental driver's level zero,
// not a pushed level of their own. A permanent defining equality must stay
// available when later assumptions mention the symbols it eliminated, and
// the answers must survive push, pop, a second solver on the same manager
// and reset_assertions.
TEST(PermanentAssertions, DefinitionsUnderAssumptionsAndLifecycle)
{
  stp::Options options;
  options.set("incremental", "on");
  stp::TermManager tm;
  stp::Solver solver(tm, options);
  solver.parse_smt2("(declare-const x (_ BitVec 3))"
                    "(declare-const y (_ BitVec 3))"
                    "(declare-const s Bool)"
                    "(assert (= y (bvadd x #b001)))"
                    "(assert (= s (bvult x #b100)))");
  auto s = solver.parse_term("s");
  for (unsigned x = 0; x != 8; ++x)
    for (unsigned y = 0; y != 8; ++y)
      for (int sign = -1; sign <= 1; ++sign)
      {
        auto a = solver.parse_term("(= x (_ bv" + std::to_string(x) + " 3))");
        auto b = solver.parse_term("(= y (_ bv" + std::to_string(y) + " 3))");
        std::vector<stp::Term> assumptions{a, b};
        if (sign)
          assumptions.push_back(sign > 0 ? s : !s);
        const bool expected =
            y == ((x + 1) % 8) && (!sign || (sign > 0) == (x < 4));
        auto answer = solver.check_sat(assumptions);
        ASSERT_EQ(answer.is_sat(), expected);
        ASSERT_EQ(answer.is_unsat(), !expected);
        if (!expected)
        {
          auto failed = solver.unsat_assumptions();
          for (const auto& f : failed)
            ASSERT_TRUE(std::any_of(assumptions.begin(), assumptions.end(),
                                    [&](const stp::Term& a)
                                    { return a.id() == f.id(); }));
          ASSERT_TRUE(solver.check_sat(failed).is_unsat());
        }
      }
  ASSERT_TRUE(solver.check_sat({s}).is_sat());
  solver.push();
  solver.assert_formula(!s);
  ASSERT_TRUE(solver.check_sat({s}).is_unsat());
  solver.pop();
  ASSERT_TRUE(solver.check_sat({s}).is_sat());
  stp::Solver other(tm, options);
  other.assert_formula(!s);
  ASSERT_TRUE(other.check_sat({s}).is_unsat());
  ASSERT_TRUE(solver.check_sat({s}).is_sat());
  solver.assert_formula(!s);
  ASSERT_TRUE(solver.check_sat({s}).is_unsat());
  solver.reset_assertions();
  ASSERT_TRUE(solver.check_sat({s}).is_sat());
}
