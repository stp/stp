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

// api3-bv-abstraction-nary-plus.cpp -- an addition of three or more operands,
// and the statistics that say what the abstraction did with it.
//
// BVPLUS is n-ary, and Flatten folds every chain of additions into one such
// node, so an addition written a + b + c arrives at the bit-blaster as a
// single node of degree three however it was built. The term abstraction
// takes two operands, so before this it declined every one of them: which
// additions got abstracted was decided by the arity the front end happened to
// produce rather than by the width floor that is meant to decide it. They are
// lowered to genuine two-operand nodes first now, as BVMULT already was.
//
// The counters are the other half: a caller that turns an abstraction on and
// sees nothing abstracted cannot tell an option that reached no eligible
// operation from an option that is broken, so the candidate count -- what the
// abstraction was offered -- is kept alongside what it took, and both are
// readable through Solver::statistics().

#include "api3_common.hpp"

#include <cstdint>

using namespace stp;

namespace
{

// Every solver here that checks satisfiability runs with the engine's model
// self-check (check-sanity) on, as every 2.x checker did. It evaluates the
// model after the search and moves none of the counters read below.
Options nary_options(bool abstraction)
{
  Options o;
  o.set_bool("check-sanity", true);
  o.set_bool("bv-term-abstraction", abstraction);
  o.set_bool("bv-term-abstraction-plus", abstraction);
  o.set_bool("bv-eq-abstraction", abstraction);
  // Every operand qualifies, so the arity is the only thing under test here.
  o.set_uint("bv-abstraction-width", 1);
  return o;
}

// A satisfiable query that preprocessing cannot settle: the product pins both
// factors, so nothing is unconstrained and the bit-blaster actually runs. The
// sum is an operand of that product rather than equated to a constant, which
// is what keeps a substitution from removing it before bit-blasting.
struct CheckerOverANAryAddition
{
  explicit CheckerOverANAryAddition(bool abstraction) : s(tm, nary_options(abstraction))
  {
    const Sort bv = tm.mk_bv_sort(32);
    const Term a = tm.declare("a", bv);
    const Term b = tm.declare("b", bv);
    const Term c = tm.declare("c", bv);
    const Term sum = bvadd({a, b, c});

    s.add(bvmul(sum, a) == tm.mk_bv(32, 3037 * 3041));
    s.add(bvugt(a, 1));
    s.add(bvugt(b, 1));
    s.add(bvugt(c, 1));
  }

  std::uint64_t counter(const char* name) const
  {
    return s.statistics().uint64(name);
  }

  TermManager tm;
  Solver s;
};

// What a solver that has done nothing reports.
void expect_nothing_counted(const Solver& s)
{
  const Statistics st = s.statistics();
  EXPECT_EQ(0u, st.uint64("checks.bitblasted"));
  EXPECT_EQ(0u, st.uint64("bv.candidates.plus"));
  EXPECT_EQ(0u, st.uint64("bv.abstracted.plus"));
  EXPECT_EQ(0u, st.uint64("bv.refinement_rounds"));
  EXPECT_EQ(0u, st.uint64("uf.applications_lowered"));
}

} // namespace

// The addition reaches the abstraction, which is what the lowering above is
// for: three operands become the two two-operand additions that the
// abstraction takes. Nothing here is about the width -- the floor is 1, so a
// declined abstraction can only be the arity.
TEST(bv_abstraction_nary_plus, AnNAryAdditionIsAbstracted)
{
  CheckerOverANAryAddition c(true);
  (void)c.s.check_sat();

  EXPECT_GT(c.counter("checks.bitblasted"), 0u);
  EXPECT_EQ(2u, c.counter("bv.candidates.plus"));
  EXPECT_EQ(2u, c.counter("bv.abstracted.plus"));
}

// With the abstraction off the same query offers the same two additions and
// none of them is taken. The candidate count is what makes a zero readable:
// it has to mean "no addition wide enough was here", not "the option that
// lowers them was off", or a caller cannot tell the two apart -- so it counts
// what the lowering would have produced even when the lowering does not run.
TEST(bv_abstraction_nary_plus, CandidatesAreCountedWithTheAbstractionOff)
{
  CheckerOverANAryAddition c(false);
  (void)c.s.check_sat();

  EXPECT_GT(c.counter("checks.bitblasted"), 0u);
  EXPECT_EQ(2u, c.counter("bv.candidates.plus"));
  EXPECT_EQ(0u, c.counter("bv.abstracted.plus"));
}

// The abstraction is a way of searching, not a different question: the
// lowering reassociates the addition, and reassociating is sound modulo 2^n,
// so the verdict is the one the exact encoding gives.
TEST(bv_abstraction_nary_plus, TheVerdictIsTheOneTheExactEncodingGives)
{
  CheckerOverANAryAddition off(false);
  const Verdict exact = off.s.check_sat().verdict();

  CheckerOverANAryAddition on(true);
  const Verdict abstracted = on.s.check_sat().verdict();

  EXPECT_EQ(exact, abstracted);
}

// A fresh solver has done nothing, and the statistics say so rather than
// carrying whatever the last one in this process reached. (The tests above
// have counted by now, each in a manager of its own.)
TEST(bv_abstraction_nary_plus, AFreshCheckerHasCountedNothing)
{
  TermManager tm;
  Solver s(tm);
  expect_nothing_counted(s);

  // A manager can serve any number of solvers, and a fresh one is fresh too
  // when another has already checked over the same manager.
  CheckerOverANAryAddition used(true);
  (void)used.s.check_sat();
  ASSERT_GT(used.counter("checks.bitblasted"), 0u);
  Solver fresh(used.tm);
  expect_nothing_counted(fresh);
  // and the one that checked keeps its own counts
  EXPECT_GT(used.counter("checks.bitblasted"), 0u);
}

// The persistent driver bit-blasts through a BitBlaster of its own, so a
// denominator taken only from the batch pipeline reads zero for a session
// that never uses it -- and an engagement rate over a zero denominator is
// worse than no rate at all.
TEST(bv_abstraction_nary_plus, TheIncrementalRouteCountsItsBitBlasting)
{
  TermManager tm;
  Options o;
  o.set_bool("check-sanity", true);
  o.set_str("incremental", "on");
  o.set_bool("bv-term-abstraction", true);
  o.set_uint("bv-abstraction-width", 1);
  Solver s(tm, o);

  const Sort bv = tm.mk_bv_sort(32);
  const Term a = tm.declare("a", bv);
  const Term b = tm.declare("b", bv);
  const Term c = tm.declare("c", bv);
  const Term sum = bvadd({a, b, c});
  s.add(bvmul(sum, a) == tm.mk_bv(32, 3037 * 3041));
  s.add(bvugt(a, 1));
  (void)s.check_sat();

  EXPECT_GT(s.statistics().uint64("checks.bitblasted"), 0u);
}
