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

// api3-incremental-scoped-preprocessing.cpp -- offering the whole active
// stack to the exact-stack preprocessor on every check, from an embedder that
// pushes and pops per query (incremental-scoped-preprocessing).
//
// The per-level incremental route encodes each level as it arrives and never
// simplifies across the stack, so what reaches the SAT solver is a formula
// nobody has been over. That is not a small thing: on one floating-point
// query the batch pipeline spends 13ms between the simplifier, constant-bit
// propagation, unconstrained removal, pure literals and strength reduction,
// and then searches for 10.1s, where the per-level route skips all five and
// the same search costs 31.1s.
//
// STP already had the route that supplies it -- the whole stack preprocessed
// into one assumption-scoped block -- but it was reachable only on an
// explicitly forced first engagement and only for a plain bit-vector stack.
// A caller whose queries carry array reads or floating point, which is every
// symbolic-execution embedder, could not get at it at all.
//
// What is pinned here is that the entry reaches its engine field and that
// turning it on does not change an answer. Whether it makes a given query
// faster is a stopwatch question, and the answer is "sometimes": see the
// field's own documentation (UserDefinedFlags) for the measurements.

#include "api3_engine.hpp"

#include <cstdint>

using namespace stp::api;

namespace
{
const char* const kScoped = "incremental-scoped-preprocessing";

const stp::UserDefinedFlags& flags(Solver& s)
{
  return api3::engine_flags(s);
}

// Options with the engine's model self-check on (check-sanity), as every 2.x
// checker had it: a sat answer whose model does not satisfy the stack is an
// INTERNAL error rather than a silent pass.
Options checked()
{
  Options o;
  o.set_bool("check-sanity", true);
  return o;
}

// A push/assert/check/pop session, which is the shape an embedder that
// treats every query as independent produces -- and the shape the per-level
// route serves worst.
Verdict solve_scoped(TermManager& tm, Solver& s, std::uint64_t scale)
{
  const Sort bv = tm.mk_bv_sort(32);
  const Term a = tm.declare("a", bv);
  const Term b = tm.declare("b", bv);

  s.push();
  s.add(bvmul(a, b) == tm.mk_bv(32, scale));
  s.add(bvugt(a, 1));
  s.add(bvugt(b, 1));
  const Result r = s.check_sat();
  s.pop();
  return r.verdict();
}
} // namespace

TEST(incremental_scoped_preprocessing, ItIsOffByDefault)
{
  TermManager tm;
  Solver s(tm);
  EXPECT_FALSE(s.options().get_bool(kScoped));
  EXPECT_FALSE(flags(s).incremental_scoped_preprocessing);
}

TEST(incremental_scoped_preprocessing, TheFlagReachesTheField)
{
  TermManager tm;
  Solver s(tm);
  s.options().set_bool(kScoped, true);
  EXPECT_TRUE(flags(s).incremental_scoped_preprocessing);
  s.options().set_bool(kScoped, false);
  EXPECT_FALSE(flags(s).incremental_scoped_preprocessing);
}

// Enough checks that the driver engages -- it takes over on the third for a
// solver with no logic to declare -- and the same answers either way. The
// route preprocesses into a block and adopts it only when the DAG at least
// halves, so which checks take it is its own business; what must not vary is
// what they answer.
TEST(incremental_scoped_preprocessing, TheAnswersDoNotChange)
{
  const std::uint64_t scales[6] = {3037 * 3041, 15, 1024, 7919 * 3, 65535, 42};

  for (int i = 0; i < 6; ++i)
  {
    TermManager off_tm, on_tm;
    Solver off(off_tm, checked());
    Solver on(on_tm, checked());
    on.options().set_bool(kScoped, true);

    // Run the whole sequence on each, so the driver is engaged by the time
    // the interesting checks arrive rather than being asked cold.
    Verdict expected = Verdict::UNKNOWN, got = Verdict::UNKNOWN;
    for (int j = 0; j <= i; ++j)
    {
      expected = solve_scoped(off_tm, off, scales[j]);
      got = solve_scoped(on_tm, on, scales[j]);
    }
    EXPECT_EQ(expected, got) << "scale=" << scales[i];
    // and the checks from the third on did reach the driver
    EXPECT_EQ(i >= 2, api3::engine_solver(on).hasIncrementalSolver()) << "scale=" << scales[i];
  }
}
