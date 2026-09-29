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

// incremental-auto-engage.cpp -- the check at which a pushing session
// hands over to the incremental driver (incremental-auto-engage-at).
//
// The C API used to hard-code "engage the incremental driver from the third
// query" as a literal, consulting nothing. --incremental-auto-engage-at was
// documented as the override for that ordinal and could not reach that path
// at all, so it was inert for every embedder, and the two frontends' copies
// of one policy were free to drift apart. Every door now calls
// IncrementalSolver::automaticEngagementReady, and the registry entry
// incremental-auto-engage-at is how a client sets it.
//
// The driver is only constructed when a check actually engages it, so asking
// the solver's engine whether one exists (api_test::engine_solver(s)) is an
// honest probe for "did this session engage?".

#include "api_engine.hpp"

#include <cstdint>

using namespace stp::api;

namespace
{
const char* const kEngageAt = "incremental-auto-engage-at";

bool engaged(Solver& s)
{
  return api_test::engine_solver(s).hasIncrementalSolver();
}

// Options with the engine's model self-check on (check-sanity), as every 2.x
// checker had it. It does not bear on engagement: which check hands over is
// decided by incremental-auto-engage-at alone.
Options checked()
{
  Options o;
  o.set_bool("check-sanity", true);
  return o;
}

// asks whether the assertions entail (a = 0), so each call is one real check
Entailment one_query(TermManager& tm, Solver& s)
{
  const Term a = tm.declare("a", tm.mk_bv_sort(8));
  return s.entails(a == 0);
}
} // namespace

// Default policy: two batch warm-ups, so a two-check session never engages.
TEST(incremental_auto_engage, DefaultKeepsTheFirstTwoQueriesOnBatch)
{
  TermManager tm;
  Solver s(tm, checked());
  EXPECT_EQ(-1, s.options().get_int(kEngageAt)); // the engine's default
  s.push();
  ASSERT_TRUE(one_query(tm, s).is_invalid());
  EXPECT_FALSE(engaged(s));
  ASSERT_TRUE(one_query(tm, s).is_invalid());
  EXPECT_FALSE(engaged(s));
  // the third is the default ordinal
  ASSERT_TRUE(one_query(tm, s).is_invalid());
  EXPECT_TRUE(engaged(s));
  s.pop();
}

// The override reaches this path. Before it did, a threshold of 1 behaved
// exactly like the default above and this session stayed on batch.
TEST(incremental_auto_engage, ThresholdOfOneEngagesOnTheFirstQuery)
{
  TermManager tm;
  Solver s(tm, checked());
  s.options().set_int(kEngageAt, 1);
  s.push();
  ASSERT_TRUE(one_query(tm, s).is_invalid());
  EXPECT_TRUE(engaged(s));
  s.pop();
}

// Zero disables automatic engagement, at any depth.
TEST(incremental_auto_engage, ZeroNeverEngages)
{
  TermManager tm;
  Solver s(tm, checked());
  s.options().set_int(kEngageAt, 0);
  s.push();
  for (int i = 0; i < 6; i++)
    ASSERT_TRUE(one_query(tm, s).is_invalid());
  EXPECT_FALSE(engaged(s));
  s.pop();
}

// Engaging early must not change what the session answers. Same bracket,
// driver from the first check against batch throughout, including the model.
TEST(incremental_auto_engage, EarlyEngagementDoesNotChangeAnswersOrModels)
{
  const std::int64_t thresholds[2] = {0, 1};
  Validity verdicts[2][3];
  std::uint64_t models[2];
  for (int t = 0; t < 2; t++)
  {
    TermManager tm;
    Solver s(tm, checked());
    s.options().set_int(kEngageAt, thresholds[t]);
    const Sort bv8 = tm.mk_bv_sort(8);
    const Term x = tm.declare("x", bv8);
    const Term y = tm.declare("y", bv8);
    s.add(bvugt(x, 3));

    s.push();
    s.add(bvult(x, 9));
    verdicts[t][0] = s.entails(x == 200).validity();
    verdicts[t][1] = s.entails(bvult(x, y)).validity();
    s.pop();

    const Entailment last = s.entails(x == 0);
    verdicts[t][2] = last.validity();
    // the last query was invalid, so the model of its counterexample is there
    ASSERT_TRUE(last.is_invalid());
    models[t] = s.model().uint64_value(x);
    EXPECT_EQ(thresholds[t] == 1, engaged(s));
  }
  for (int q = 0; q < 3; q++)
    EXPECT_EQ(verdicts[0][q], verdicts[1][q]) << "query " << q;
  // both models must satisfy the live base constraint x > 3
  EXPECT_GT(models[0], 3u);
  EXPECT_GT(models[1], 3u);
}
