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

// api3-array-equality-retired-after-pop.cpp -- the array-equality checker's
// solve-local state is retired by the next incremental round, including a
// round that only applies an uninterpreted function.
//
// Everything the array-equality consistency checker works on is solve-local:
// the abstraction records, the frozen array graph, and the scalar names its
// refinement lemmas are encoded over. That state deliberately outlives the
// solve that built it, because the model surfaces read the certified array
// contents after the check has returned, so retiring it is the next round's
// job and nobody else's -- a pop keeps the model of the check inside the
// bracket (push, pop and assert do not invalidate it) and so clears nothing.
//
// The incremental driver retired it on the route it takes for an ordinary
// stack. The exact-stack route, which owns the whole active stack whenever a
// conjunct has an array equality or applies an uninterpreted function, began
// a round of its own only in the first of those two cases. So a check that
// merely applied a function inherited whatever the last equality left behind,
// and STP ran the previous round's checker over this round's assignment.
//
// What that cost depends on whether the names survived into the new round's
// solver, and both endings are below, one per test. The array equality is
// popped before the second check in each: that is what makes the second round
// an ordinary one as far as arrays are concerned, and it is the point the
// stale graph should have been dropped at.

#include "api3_common.hpp"

using namespace stp;

namespace
{

// Two arrays of the same sort, and a solver with the options the 2.x
// checker's flags map to. incremental = on (the 2.x 'i' flag) engages the
// incremental driver from the first check rather than from the first push,
// which is what puts both checks below on the persistent exact-stack route;
// it is what a client that solves incrementally sets.
struct Session
{
  TermManager tm;
  Solver solver{tm, options()};
  Term left, right;

  Session()
  {
    const Sort array = tm.mk_array_sort(tm.mk_bv_sort(8), tm.mk_bv_sort(8));
    left = tm.declare("a", array);
    right = tm.declare("b", array);
  }

  static Options options()
  {
    Options o;
    o.set_str("array-equality", "on");          // whole-array equality by lemmas on demand
    o.set_str("uninterpreted-functions", "on"); // uninterpreted functions
    o.set_str("incremental", "on");             // incremental from the first check
    // 2.x checked the counterexample of every satisfiable answer ('d', forced
    // on every checker); 3.x leaves check-sanity off by default.
    o.set_bool("check-sanity", true);
    return o;
  }

  Result check() { return solver.check_sat(); }
};

} // namespace

// The equality is the only thing on the stack when it is checked, and the
// function application arrives after the pop. Its argument is a rounding
// mode, so the round that decides it is not the round that encoded the
// witness index and the read abstractions, and the stale graph asks the new
// assignment for scalar names that are not in it at all.
TEST(array_equality_retired_after_pop, application_asserted_after_the_pop)
{
  Session s;

  s.solver.push();
  s.solver.add(s.left == s.right);
  EXPECT_TRUE(s.check().is_sat());
  s.solver.pop();

  const Term f = s.tm.declare("f", s.tm.mk_fun_sort({s.tm.mk_rm_sort()}, s.tm.mk_bv_sort(8)));
  const Term application = f(s.tm.mk_rm(RoundingMode::RTP));
  const Term x = s.tm.declare("x", s.tm.mk_bv_sort(8));
  s.solver.add(bvule(application, x));

  EXPECT_TRUE(s.check().is_sat());
  EXPECT_EQ(1u, s.solver.statistics().uint64("incremental.engaged"));
}

// The function application is already at the base level when the equality is
// pushed over it, so the second round re-solves a stack the first round did
// encode and the stale names do have values -- the ones this round's solver
// chose for a formula the graph says nothing about. The checker reads them as
// two arrays disagreeing at the witness index and demands a refinement lemma
// which a round with no active equality has no lane to encode.
TEST(array_equality_retired_after_pop, application_asserted_before_the_push)
{
  Session s;

  const Term f = s.tm.declare("f", s.tm.mk_fun_sort({s.tm.mk_bv_sort(8)}, s.tm.mk_bv_sort(8)));
  const Term application = f(s.tm.mk_bv(8, 3));
  s.solver.add(bvsle(s.tm.mk_bv(8, 1), application));

  s.solver.push();
  s.solver.add(s.left == s.right);
  EXPECT_TRUE(s.check().is_sat());
  s.solver.pop();

  EXPECT_TRUE(s.check().is_sat());
  EXPECT_EQ(1u, s.solver.statistics().uint64("incremental.engaged"));
}
