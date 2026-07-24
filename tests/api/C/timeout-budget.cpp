/***********
AUTHORS: Andrew Teylu

BEGIN DATE: July, 2026

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
**********************/

/*
 * The budgets taken by vc_query_with_timeout() mean the same thing whichever
 * SAT solver is underneath: -1 is the only negative value accepted and means
 * "no limit", and 0 is a budget of zero rather than an absent one.
 */

#include "stp/c_interface.h"
#include <chrono>
#include <gtest/gtest.h>
#include <string>
#include <vector>

namespace
{

// Return codes of vc_query_with_timeout().
const int QUERY_INVALID = 0;
const int QUERY_VALID = 1;
const int QUERY_ERROR = 2;
const int QUERY_TIMEOUT = 3;

const int NO_LIMIT = -1;

struct Backend
{
  const char* name;
  bool (*select)(VC);

  // TRUE if the backend can abandon a search that is already running. The
  // others only notice a time budget between calls into the SAT solver, so
  // asking one of them to give up part way through a hard query would mean
  // waiting for that query to finish.
  bool interruptible;
};

std::vector<Backend> backends()
{
  std::vector<Backend> result;

  result.push_back({"minisat", vc_useMinisat, false});
  result.push_back({"simplifying-minisat", vc_useSimplifyingMinisat, false});

#ifdef USE_CRYPTOMINISAT
  result.push_back({"cryptominisat", vc_useCryptominisat, true});
#endif
#ifdef USE_RISS
  result.push_back({"riss", vc_useRiss, false});
#endif
#ifdef USE_CADICAL
  result.push_back({"cadical", vc_useCadical, true});
#endif

  return result;
}

/*
 * Factoring a semiprime: hard enough that the SAT solver will not answer
 * while a test is watching, so any answer we do get came from a budget
 * running out rather than from the search finishing.
 *
 * Both factors are held below 2^32 so that the 64-bit multiply cannot wrap.
 * Without that the constraint is satisfied modulo 2^64 by almost any 'a',
 * and the instance is trivial rather than a factoring problem.
 */
void assert_hard_instance(VC vc)
{
  const int width = 96;

  // 486579698794948075013401 == 703873773913 * 691288291777, both prime.
  // Two 40-bit factors: unlimited, this runs for minutes rather than the
  // seconds a semiprime with 32-bit factors takes.
  Expr a = vc_varExpr(vc, "a", vc_bvType(vc, width));
  Expr b = vc_varExpr(vc, "b", vc_bvType(vc, width));
  Expr one = vc_bvConstExprFromDecStr(vc, width, "1");
  Expr limit = vc_bvConstExprFromDecStr(vc, width, "1099511627776"); // 2^40
  Expr product =
      vc_bvConstExprFromDecStr(vc, width, "486579698794948075013401");

  vc_assertFormula(vc, vc_eqExpr(vc, vc_bvMultExpr(vc, width, a, b), product));
  vc_assertFormula(vc, vc_bvGtExpr(vc, a, one));
  vc_assertFormula(vc, vc_bvGtExpr(vc, b, one));
  vc_assertFormula(vc, vc_bvLtExpr(vc, a, limit));
  vc_assertFormula(vc, vc_bvLtExpr(vc, b, limit));
  vc_assertFormula(vc, vc_bvLeExpr(vc, a, b));
}

double seconds_since(const std::chrono::steady_clock::time_point& start)
{
  const std::chrono::duration<double> elapsed =
      std::chrono::steady_clock::now() - start;

  return elapsed.count();
}

} // namespace

/*
 * -1 is the only negative budget with a meaning. Anything else is a mistake
 * on the caller's part and is reported rather than being run as unlimited.
 */
TEST(timeout_budget, negative_budgets_are_rejected)
{
  VC vc = vc_createValidityChecker();

  EXPECT_EQ(vc_query_with_timeout(vc, vc_falseExpr(vc), -2, NO_LIMIT),
            QUERY_ERROR);
  EXPECT_EQ(vc_query_with_timeout(vc, vc_falseExpr(vc), NO_LIMIT, -2),
            QUERY_ERROR);
  EXPECT_EQ(vc_query_with_timeout(vc, vc_falseExpr(vc), -100, -100),
            QUERY_ERROR);

  vc_Destroy(vc);
}

// A budget of zero is a budget, not the absence of one.
TEST(timeout_budget, zero_time_budget_gives_up_immediately)
{
  for (const Backend& backend : backends())
  {
    SCOPED_TRACE(backend.name);

    VC vc = vc_createValidityChecker();
    ASSERT_TRUE(backend.select(vc));
    assert_hard_instance(vc);

    const std::chrono::steady_clock::time_point start =
        std::chrono::steady_clock::now();

    EXPECT_EQ(vc_query_with_timeout(vc, vc_falseExpr(vc), NO_LIMIT, 0),
              QUERY_TIMEOUT);
    EXPECT_LT(seconds_since(start), 30.0);

    vc_Destroy(vc);
  }
}

TEST(timeout_budget, zero_conflict_budget_gives_up_immediately)
{
  for (const Backend& backend : backends())
  {
    SCOPED_TRACE(backend.name);

    VC vc = vc_createValidityChecker();
    ASSERT_TRUE(backend.select(vc));
    assert_hard_instance(vc);

    EXPECT_EQ(vc_query_with_timeout(vc, vc_falseExpr(vc), 0, NO_LIMIT),
              QUERY_TIMEOUT);

    vc_Destroy(vc);
  }
}

/*
 * The budget is for the query rather than for each call into the SAT solver,
 * of which a query makes one per refinement iteration. Allow generously more
 * than the budget before failing: the point is that the query stops in some
 * multiple of the budget that does not grow with the number of iterations.
 */
TEST(timeout_budget, time_budget_covers_the_whole_query)
{
  for (const Backend& backend : backends())
  {
    if (!backend.interruptible)
    {
      continue;
    }

    SCOPED_TRACE(backend.name);

    VC vc = vc_createValidityChecker();
    ASSERT_TRUE(backend.select(vc));
    assert_hard_instance(vc);

    const std::chrono::steady_clock::time_point start =
        std::chrono::steady_clock::now();

    EXPECT_EQ(vc_query_with_timeout(vc, vc_falseExpr(vc), NO_LIMIT, 2),
              QUERY_TIMEOUT);
    EXPECT_LT(seconds_since(start), 30.0);

    vc_Destroy(vc);
  }
}

/*
 * An unlimited query must still reach the SAT solver and come back with an
 * answer. The trivial case below is decided before the solver is called, so
 * it would not notice a backend that mistook "no budget configured" for a
 * budget of zero.
 */
TEST(timeout_budget, no_limit_reaches_the_solver)
{
  for (const Backend& backend : backends())
  {
    SCOPED_TRACE(backend.name);

    VC vc = vc_createValidityChecker();
    ASSERT_TRUE(backend.select(vc));

    // 60491 == 251 * 241, factored in milliseconds, but still an answer
    // that has to come out of the SAT solver: give this same instance a
    // budget of zero conflicts and every backend reports a timeout.
    const int width = 32;
    Expr a = vc_varExpr(vc, "a", vc_bvType(vc, width));
    Expr b = vc_varExpr(vc, "b", vc_bvType(vc, width));
    Expr one = vc_bvConstExprFromLL(vc, width, 1);
    Expr limit = vc_bvConstExprFromLL(vc, width, 1ULL << 16);
    Expr product = vc_bvConstExprFromLL(vc, width, 60491ULL);

    vc_assertFormula(vc,
                     vc_eqExpr(vc, vc_bvMultExpr(vc, width, a, b), product));
    vc_assertFormula(vc, vc_bvGtExpr(vc, a, one));
    vc_assertFormula(vc, vc_bvGtExpr(vc, b, one));
    vc_assertFormula(vc, vc_bvLtExpr(vc, a, limit));
    vc_assertFormula(vc, vc_bvLtExpr(vc, b, limit));
    vc_assertFormula(vc, vc_bvLeExpr(vc, a, b));

    // The assertions are satisfiable, so the query of FALSE is invalid.
    EXPECT_EQ(vc_query_with_timeout(vc, vc_falseExpr(vc), NO_LIMIT, NO_LIMIT),
              QUERY_INVALID);

    vc_Destroy(vc);
  }
}

// An unlimited query is unaffected by any of the above.
TEST(timeout_budget, no_limit_still_answers)
{
  for (const Backend& backend : backends())
  {
    SCOPED_TRACE(backend.name);

    VC vc = vc_createValidityChecker();
    ASSERT_TRUE(backend.select(vc));

    Expr a = vc_varExpr(vc, "a", vc_bvType(vc, 32));
    Expr value = vc_bvConstExprFromInt(vc, 32, 42);
    vc_assertFormula(vc, vc_eqExpr(vc, a, value));

    EXPECT_EQ(vc_query_with_timeout(vc, vc_eqExpr(vc, a, value), NO_LIMIT,
                                    NO_LIMIT),
              QUERY_VALID);

    vc_Destroy(vc);
  }
}

TEST(timeout_budget, vc_query_is_unlimited)
{
  VC vc = vc_createValidityChecker();

  Expr a = vc_varExpr(vc, "a", vc_bvType(vc, 32));
  Expr value = vc_bvConstExprFromInt(vc, 32, 42);
  vc_assertFormula(vc, vc_eqExpr(vc, a, value));

  EXPECT_EQ(vc_query(vc, vc_eqExpr(vc, a, value)), QUERY_VALID);
  EXPECT_EQ(vc_query(vc, vc_falseExpr(vc)), QUERY_INVALID);

  vc_Destroy(vc);
}

// Every backend that is compiled in can be selected and reports itself.
TEST(timeout_budget, backends_are_selectable)
{
  for (const Backend& backend : backends())
  {
    SCOPED_TRACE(backend.name);

    VC vc = vc_createValidityChecker();
    EXPECT_TRUE(backend.select(vc));
    vc_Destroy(vc);
  }
}

#ifdef USE_CADICAL
TEST(timeout_budget, cadical_is_selectable)
{
  VC vc = vc_createValidityChecker();

  EXPECT_TRUE(vc_supportsCadical(vc));
  EXPECT_TRUE(vc_useCadical(vc));
  EXPECT_TRUE(vc_isUsingCadical(vc));

  EXPECT_TRUE(vc_useMinisat(vc));
  EXPECT_FALSE(vc_isUsingCadical(vc));

  vc_Destroy(vc);
}
#else
TEST(timeout_budget, cadical_is_absent)
{
  VC vc = vc_createValidityChecker();

  EXPECT_FALSE(vc_supportsCadical(vc));
  EXPECT_FALSE(vc_useCadical(vc));
  EXPECT_FALSE(vc_isUsingCadical(vc));

  vc_Destroy(vc);
}
#endif
