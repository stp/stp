/***********
AUTHORS: Trevor Hansen

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
 * Driving CaDiCaL through the public C API: both ways of selecting it, and
 * then actually solving with it.
 */

#include "stp/c_interface.h"
#include <gtest/gtest.h>
#include <iostream>

namespace
{

// Return codes of vc_query().
const int QUERY_INVALID = 0;
const int QUERY_VALID = 1;

#ifdef USE_CADICAL
const bool cadical_available = true;
#else
const bool cadical_available = false;
#endif

#ifdef USE_MINISAT
const bool minisat_available = true;
#else
const bool minisat_available = false;
#endif

} // namespace

// Whether STP can offer CaDiCaL is a build-time property, and the API has to
// report it honestly either way.
TEST(cadical, support_is_reported)
{
  VC vc = vc_createValidityChecker();

  EXPECT_EQ(vc_supportsCadical(vc), cadical_available);

  vc_Destroy(vc);
}

/*
 * vc_useCadical() succeeds exactly when the build has CaDiCaL. Note that a
 * build with CaDiCaL also *defaults* to it, so the selection is only visible
 * as a change if we move off it first.
 */
TEST(cadical, selected_by_use_cadical)
{
  VC vc = vc_createValidityChecker();

  if (!minisat_available)
  {
    // Moving the selection somewhere visible first needs a second backend.
    vc_Destroy(vc);
    GTEST_SKIP() << "needs the MiniSat backend to move the selection off "
                    "CaDiCaL first";
  }

  ASSERT_TRUE(vc_useMinisat(vc));
  ASSERT_TRUE(vc_isUsingMinisat(vc));

  EXPECT_EQ(vc_useCadical(vc), cadical_available);
  EXPECT_EQ(vc_isUsingCadical(vc), cadical_available);

  vc_Destroy(vc);
}

// The same choice through vc_setInterfaceFlags(), which is how a caller that
// already selects its solver from the ifaceflag_t enum reaches CaDiCaL.
TEST(cadical, selected_by_interface_flag)
{
  VC vc = vc_createValidityChecker();

  if (minisat_available)
  {
    // Move the selection somewhere visible first, so setting the flag is
    // observable as a change and not just the default reasserting itself.
    ASSERT_TRUE(vc_useMinisat(vc));
  }

  vc_setInterfaceFlags(vc, CADICAL, 0);

  // vc_isUsingCadical() answers for the build as well as the selection, so it
  // only turns true where CaDiCaL exists. Either way the flag has moved the
  // selection off MiniSat, which is what the enum entry is for.
  EXPECT_EQ(vc_isUsingCadical(vc), cadical_available);
  EXPECT_FALSE(vc_isUsingMinisat(vc));
  EXPECT_FALSE(vc_isUsingSimplifyingMinisat(vc));
  EXPECT_FALSE(vc_isUsingCryptominisat(vc));

  vc_Destroy(vc);
}

/*
 * The numbers themselves, not just the names. Value 4 was RISS, and removing
 * the Riss backend left the slot empty rather than closing it up, so MSP and
 * CADICAL are still 5 and 6 for a caller compiled against an older header.
 */
TEST(cadical, interface_flag_values_are_unchanged)
{
  EXPECT_EQ(static_cast<int>(EXPRDELETE), 0);
  EXPECT_EQ(static_cast<int>(MS), 1);
  EXPECT_EQ(static_cast<int>(SMS), 2);
  EXPECT_EQ(static_cast<int>(CMS4), 3);
  EXPECT_EQ(static_cast<int>(MSP), 5);
  EXPECT_EQ(static_cast<int>(CADICAL), 6);
}

/*
 * CADICAL was appended to ifaceflag_t rather than inserted, so the flags that
 * existed before it still mean what they did. A caller compiled against an
 * older header passes the same integers.
 */
TEST(cadical, other_interface_flags_still_select_their_own_solver)
{
  VC vc = vc_createValidityChecker();

  // vc_isUsingMinisat answers for the build as well as the selection, so in
  // a build without the MiniSat backend it stays false; the flag has still
  // moved the selection off CaDiCaL, which is the part that must not shift.
  vc_setInterfaceFlags(vc, MS, 0);
  EXPECT_EQ(vc_isUsingMinisat(vc), minisat_available);
  EXPECT_FALSE(vc_isUsingCadical(vc));

  vc_setInterfaceFlags(vc, SMS, 0);
  EXPECT_EQ(vc_isUsingSimplifyingMinisat(vc), minisat_available);
  EXPECT_FALSE(vc_isUsingCadical(vc));

  vc_setInterfaceFlags(vc, MSP, 0);
  EXPECT_EQ(vc_isUsingMinisat(vc), minisat_available);
  EXPECT_FALSE(vc_isUsingCadical(vc));

  vc_Destroy(vc);
}

// A valid query and an invalid one, answered by CaDiCaL.
TEST(cadical, solves_valid_and_invalid_queries)
{
  if (!cadical_available)
  {
    std::cout << "[  SKIPPED ] built without CaDiCaL" << std::endl;
    return;
  }

  VC vc = vc_createValidityChecker();
  ASSERT_TRUE(vc_useCadical(vc));

  const int width = 16;
  Expr x = vc_varExpr(vc, "x", vc_bvType(vc, width));
  Expr ten = vc_bvConstExprFromInt(vc, width, 10);

  // (x > 10) => (x > 5) holds for every x.
  EXPECT_EQ(vc_query(vc, vc_impliesExpr(vc, vc_bvGtExpr(vc, x, ten),
                                        vc_bvGtExpr(vc, x, vc_bvConstExprFromInt(
                                                               vc, width, 5)))),
            QUERY_VALID);

  // The converse does not.
  EXPECT_EQ(vc_query(vc, vc_impliesExpr(
                             vc, vc_bvGtExpr(vc, x, vc_bvConstExprFromInt(
                                                        vc, width, 5)),
                             vc_bvGtExpr(vc, x, ten))),
            QUERY_INVALID);

  vc_Destroy(vc);
}

/*
 * A counterexample produced while CaDiCaL is the backend, read back through
 * the API and checked against the constraints it is supposed to satisfy.
 */
TEST(cadical, produces_a_usable_counterexample)
{
  if (!cadical_available)
  {
    std::cout << "[  SKIPPED ] built without CaDiCaL" << std::endl;
    return;
  }

  VC vc = vc_createValidityChecker();
  ASSERT_TRUE(vc_useCadical(vc));
  vc_setFlag(vc, 'c'); // construct counterexamples

  const int width = 32;
  Expr a = vc_varExpr(vc, "a", vc_bvType(vc, width));
  Expr b = vc_varExpr(vc, "b", vc_bvType(vc, width));
  Expr thousand = vc_bvConstExprFromInt(vc, width, 1000);
  Expr hundred = vc_bvConstExprFromInt(vc, width, 100);

  // a + b == 1000 with both operands in (100, 1000): satisfiable, so the query
  // is invalid. Bounding both below 1000 keeps the addition from wrapping, so
  // the values read back have to add up exactly.
  vc_assertFormula(vc,
                   vc_eqExpr(vc, vc_bvPlusExpr(vc, width, a, b), thousand));
  vc_assertFormula(vc, vc_bvGtExpr(vc, a, hundred));
  vc_assertFormula(vc, vc_bvGtExpr(vc, b, hundred));
  vc_assertFormula(vc, vc_bvLtExpr(vc, a, thousand));
  vc_assertFormula(vc, vc_bvLtExpr(vc, b, thousand));

  ASSERT_EQ(vc_query(vc, vc_falseExpr(vc)), QUERY_INVALID);

  const unsigned long a_value = getBVUnsigned(vc_getCounterExample(vc, a));
  const unsigned long b_value = getBVUnsigned(vc_getCounterExample(vc, b));

  EXPECT_EQ(a_value + b_value, 1000u);
  EXPECT_GT(a_value, 100u);
  EXPECT_GT(b_value, 100u);

  vc_Destroy(vc);
}

/*
 * An unsatisfiable set of assertions: the query STP is asked is "false", which
 * is valid exactly when the assertions cannot be satisfied.
 */
TEST(cadical, reports_unsatisfiable_assertions)
{
  if (!cadical_available)
  {
    std::cout << "[  SKIPPED ] built without CaDiCaL" << std::endl;
    return;
  }

  VC vc = vc_createValidityChecker();
  ASSERT_TRUE(vc_useCadical(vc));

  const int width = 8;
  Expr x = vc_varExpr(vc, "x", vc_bvType(vc, width));
  Expr five = vc_bvConstExprFromInt(vc, width, 5);

  vc_assertFormula(vc, vc_bvGtExpr(vc, x, five));
  vc_assertFormula(vc, vc_bvLtExpr(vc, x, five));

  EXPECT_EQ(vc_query(vc, vc_falseExpr(vc)), QUERY_VALID);

  vc_Destroy(vc);
}
