/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: Aug, 2026
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

// How much effort the CNF generator spends, reachable from the C API.
//
// --cnf-generation-effort has been a command-line option for as long as the
// generator has had levels, and an embedder could not ask for any of them.
// That is not a cosmetic gap: the level is a genuine trade rather than a
// quality dial, and which end of it a query wants depends on the query.
// A floating-point square root over a wide significand builds an enormous
// circuit that the SAT solver then disposes of at once -- one such query
// spent 983ms of its 1.28s in cut enumeration and none at all in search --
// while a query whose search is the expensive part wants the other end.
//
// An embedder that cannot reach the level is stuck with whichever end its
// workload happens to disagree with.
#include "stp/STPManager/STP.h"
#include "stp/c_interface.h"
#include <gtest/gtest.h>

namespace
{
// The flags the checker is actually carrying, which is what a setter has to
// be shown to reach: an enumerator the switch does not handle would fall
// through and change nothing.
const stp::UserDefinedFlags& flags(VC vc)
{
  return ((stp::STP*)vc)->bm->UserFlags;
}

int errors = 0;
void countError(const char*)
{
  errors++;
}
} // namespace

TEST(cnf_effort_flag, TheDefaultIsAuto)
{
  VC vc = vc_createValidityChecker();
  EXPECT_EQ(stp::UserDefinedFlags::CNF_EFFORT_AUTO, flags(vc).cnf_effort);
  // AUTO is not a level of its own at conversion time: it resolves to VERY_LOW
  // or MEDIUM from the size of the AIG. The threshold has to be reachable, or
  // the decision cannot be exercised or adjusted.
  EXPECT_GT(flags(vc).cnf_auto_threshold, 0u);
  vc_Destroy(vc);
}

// Where the crossover falls is a property of the workload, so a caller that
// has measured its own has to be able to say so without a command line.
TEST(cnf_effort_flag, TheAutoThresholdIsReachableThroughTheCAPI)
{
  VC vc = vc_createValidityChecker();
  const unsigned before = flags(vc).cnf_auto_threshold;

  vc_setInterfaceFlags(vc, CNF_AUTO_THRESHOLD, 32000);
  EXPECT_EQ(32000u, flags(vc).cnf_auto_threshold);

  // Zero is meaningful -- every AIG is at or above it, so AUTO becomes
  // very-low everywhere -- and must not be mistaken for "unset".
  vc_setInterfaceFlags(vc, CNF_AUTO_THRESHOLD, 0);
  EXPECT_EQ(0u, flags(vc).cnf_auto_threshold);

  // Negative would wrap to a threshold no AIG could reach, silently disabling
  // the decision. Refused, and the field left as it was.
  vc_setInterfaceFlags(vc, CNF_AUTO_THRESHOLD, -1);
  EXPECT_EQ(0u, flags(vc).cnf_auto_threshold);

  vc_setInterfaceFlags(vc, CNF_AUTO_THRESHOLD, (int)before);
  EXPECT_EQ(before, flags(vc).cnf_auto_threshold);
  vc_Destroy(vc);
}

// Every level the command line names, by the ordinal the header documents.
TEST(cnf_effort_flag, EveryLevelIsReachable)
{
  VC vc = vc_createValidityChecker();

  vc_setInterfaceFlags(vc, CNF_GENERATION_EFFORT, 0);
  EXPECT_EQ(stp::UserDefinedFlags::CNF_EFFORT_VERY_LOW, flags(vc).cnf_effort);
  vc_setInterfaceFlags(vc, CNF_GENERATION_EFFORT, 1);
  EXPECT_EQ(stp::UserDefinedFlags::CNF_EFFORT_LOW, flags(vc).cnf_effort);
  vc_setInterfaceFlags(vc, CNF_GENERATION_EFFORT, 2);
  EXPECT_EQ(stp::UserDefinedFlags::CNF_EFFORT_MEDIUM, flags(vc).cnf_effort);
  vc_setInterfaceFlags(vc, CNF_GENERATION_EFFORT, 3);
  EXPECT_EQ(stp::UserDefinedFlags::CNF_EFFORT_HIGH, flags(vc).cnf_effort);
  vc_setInterfaceFlags(vc, CNF_GENERATION_EFFORT, 4);
  EXPECT_EQ(stp::UserDefinedFlags::CNF_EFFORT_VERY_HIGH, flags(vc).cnf_effort);

  // Auto is a level like the others here, and the only one that matters to a
  // caller that has already set another: it is the default, so without it
  // there is no way back to where the checker started.
  vc_setInterfaceFlags(vc, CNF_GENERATION_EFFORT, 5);
  EXPECT_EQ(stp::UserDefinedFlags::CNF_EFFORT_AUTO, flags(vc).cnf_effort);

  // The rungs that name a backend rather than an effort. They are on the same
  // ordinal scale by construction -- a new rung goes on the end -- so an
  // embedder reaches them the same way.
  vc_setInterfaceFlags(vc, CNF_GENERATION_EFFORT, 6);
  EXPECT_EQ(stp::UserDefinedFlags::CNF_EFFORT_NEW_VERY_LOW,
            flags(vc).cnf_effort);
  vc_setInterfaceFlags(vc, CNF_GENERATION_EFFORT, 7);
  EXPECT_EQ(stp::UserDefinedFlags::CNF_EFFORT_NEW_LOW, flags(vc).cnf_effort);
  vc_setInterfaceFlags(vc, CNF_GENERATION_EFFORT, 8);
  EXPECT_EQ(stp::UserDefinedFlags::CNF_EFFORT_NEW_MEDIUM, flags(vc).cnf_effort);
  vc_setInterfaceFlags(vc, CNF_GENERATION_EFFORT, 9);
  EXPECT_EQ(stp::UserDefinedFlags::CNF_EFFORT_GIA_LOW, flags(vc).cnf_effort);
  vc_setInterfaceFlags(vc, CNF_GENERATION_EFFORT, 10);
  EXPECT_EQ(stp::UserDefinedFlags::CNF_EFFORT_GIA_HIGH, flags(vc).cnf_effort);
  vc_setInterfaceFlags(vc, CNF_GENERATION_EFFORT, 11);
  EXPECT_EQ(stp::UserDefinedFlags::CNF_EFFORT_GIA_VERY_HIGH,
            flags(vc).cnf_effort);

  vc_Destroy(vc);
}

// Out of range is refused and leaves the level alone. The field is an enum,
// so an accepted value past the end would be one no switch in the generator
// handles -- it would fall to whichever arm happens to be first and the
// caller would never learn that what they asked for did not happen.
TEST(cnf_effort_flag, OutOfRangeIsRefusedAndLeavesTheLevelAlone)
{
  vc_registerErrorHandler(countError);
  errors = 0;

  VC vc = vc_createValidityChecker();
  vc_setInterfaceFlags(vc, CNF_GENERATION_EFFORT, 3);
  EXPECT_EQ(stp::UserDefinedFlags::CNF_EFFORT_HIGH, flags(vc).cnf_effort);

  // One past the last enumerator.
  vc_setInterfaceFlags(vc, CNF_GENERATION_EFFORT, 12);
  EXPECT_EQ(stp::UserDefinedFlags::CNF_EFFORT_HIGH, flags(vc).cnf_effort);
  vc_setInterfaceFlags(vc, CNF_GENERATION_EFFORT, -1);
  EXPECT_EQ(stp::UserDefinedFlags::CNF_EFFORT_HIGH, flags(vc).cnf_effort);
  EXPECT_EQ(2, errors);

  vc_Destroy(vc);
  vc_registerErrorHandler(nullptr);
}

// The level reaches the solve, and every one of them answers the same
// question the same way. A level that changed a verdict would be a bug in
// the generator, not a setting -- and since six of the twelve pick a whole
// bit-blasting backend rather than an effort, this is where a backend that
// encoded the query wrongly would be caught.
TEST(cnf_effort_flag, EveryLevelDecidesTheSameQuery)
{
  for (int effort = 0; effort <= 11; ++effort)
  {
    VC vc = vc_createValidityChecker();
    vc_setInterfaceFlags(vc, CNF_GENERATION_EFFORT, effort);

    Type bv = vc_bvType(vc, 32);
    Expr a = vc_varExpr(vc, "a", bv);
    Expr b = vc_varExpr(vc, "b", bv);
    vc_assertFormula(vc, vc_eqExpr(vc, vc_bvMultExpr(vc, 32, a, b),
                                   vc_bvConstExprFromInt(vc, 32, 3037 * 3041)));
    vc_assertFormula(vc, vc_bvGtExpr(vc, a, vc_bvConstExprFromInt(vc, 32, 1)));
    vc_assertFormula(vc, vc_bvGtExpr(vc, b, vc_bvConstExprFromInt(vc, 32, 1)));

    EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc))) << "effort=" << effort;
    vc_Destroy(vc);
  }
}
