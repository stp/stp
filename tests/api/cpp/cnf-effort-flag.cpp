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

// cnf-effort-flag.cpp -- how much effort the CNF generator spends,
// reachable through the option registry: cnf-generation-effort and the
// cnf-auto-threshold its `auto` level decides by.
//
// --cnf-generation-effort has been a command-line option for as long as the
// generator has had levels, and an embedder could not ask for any of them.
// That is not a cosmetic gap: the level is a genuine trade rather than a
// quality dial, and which end of it a query wants depends on the query. A
// floating-point square root over a wide significand builds an enormous
// circuit that the SAT solver then disposes of at once -- one such query
// spent 983ms of its 1.28s in cut enumeration and none at all in search --
// while a query whose search is the expensive part wants the other end.
//
// An embedder that cannot reach the level is stuck with whichever end its
// workload happens to disagree with. The registry names the levels (2.x
// numbered them), and api_test::engine_flags(s) reads back the level the solver's
// next check would convert with.

#include "api_engine.hpp"

#include <algorithm>
#include <string>
#include <vector>

using namespace stp::api;

namespace
{
const char* const kEffort = "cnf-generation-effort";
const char* const kThreshold = "cnf-auto-threshold";

// The flags the solver is actually carrying, which is what a setter has to
// be shown to reach: a level the applier did not handle would fall through
// and change nothing.
const stp::UserDefinedFlags& flags(Solver& s)
{
  return api_test::engine_flags(s);
}

struct Level
{
  const char* name;
  stp::UserDefinedFlags::CNFEffort effort;
};

// Every level the command line names, in the order 2.x numbered them (0 to
// 12): the efforts, then auto, then the rungs that name a backend rather than
// an effort. A new rung goes on the end.
const Level kLevels[] = {
    {"very-low", stp::UserDefinedFlags::CNF_EFFORT_VERY_LOW},
    {"low", stp::UserDefinedFlags::CNF_EFFORT_LOW},
    {"medium", stp::UserDefinedFlags::CNF_EFFORT_MEDIUM},
    {"high", stp::UserDefinedFlags::CNF_EFFORT_HIGH},
    {"very-high", stp::UserDefinedFlags::CNF_EFFORT_VERY_HIGH},
    {"auto", stp::UserDefinedFlags::CNF_EFFORT_AUTO},
    {"new-very-low", stp::UserDefinedFlags::CNF_EFFORT_NEW_VERY_LOW},
    {"new-low", stp::UserDefinedFlags::CNF_EFFORT_NEW_LOW},
    {"new-medium", stp::UserDefinedFlags::CNF_EFFORT_NEW_MEDIUM},
    {"gia-low", stp::UserDefinedFlags::CNF_EFFORT_GIA_LOW},
    {"gia-high", stp::UserDefinedFlags::CNF_EFFORT_GIA_HIGH},
    {"gia-very-high", stp::UserDefinedFlags::CNF_EFFORT_GIA_VERY_HIGH},
    {"new-high", stp::UserDefinedFlags::CNF_EFFORT_NEW_HIGH},
};
} // namespace

TEST(cnf_effort_flag, TheDefaultIsAuto)
{
  TermManager tm;
  Solver s(tm);
  EXPECT_EQ(stp::UserDefinedFlags::CNF_EFFORT_AUTO, flags(s).cnf_effort);
  EXPECT_EQ("auto", s.options().get_str(kEffort));
  // AUTO is not a level of its own at conversion time: it resolves to VERY_LOW
  // or MEDIUM from the size of the AIG. The threshold has to be reachable, or
  // the decision cannot be exercised or adjusted.
  EXPECT_GT(flags(s).cnf_auto_threshold, 0u);
  EXPECT_EQ(flags(s).cnf_auto_threshold, s.options().get_uint(kThreshold));
}

// Where the crossover falls is a property of the workload, so a caller that
// has measured its own has to be able to say so without a command line.
TEST(cnf_effort_flag, TheAutoThresholdIsReachableThroughTheCAPI)
{
  TermManager tm;
  Solver s(tm);
  const unsigned before = flags(s).cnf_auto_threshold;

  s.options().set_uint(kThreshold, 32000);
  EXPECT_EQ(32000u, flags(s).cnf_auto_threshold);

  // Zero is meaningful -- every AIG is at or above it, so AUTO becomes
  // very-low everywhere -- and must not be mistaken for "unset".
  s.options().set_uint(kThreshold, 0);
  EXPECT_EQ(0u, flags(s).cnf_auto_threshold);

  // Negative would wrap to a threshold no AIG could reach, silently disabling
  // the decision. Refused, and the option and the field left as they were.
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, s.options().set_int(kThreshold, -1));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, s.options().set(kThreshold, "-1"));
  EXPECT_EQ(0u, s.options().get_uint(kThreshold));
  EXPECT_EQ(0u, flags(s).cnf_auto_threshold);

  s.options().set_uint(kThreshold, before);
  EXPECT_EQ(before, flags(s).cnf_auto_threshold);
}

// Every level the command line names reaches the field, by the name the
// registry gives it.
TEST(cnf_effort_flag, EveryLevelIsReachable)
{
  TermManager tm;
  Solver s(tm);

  for (const Level& level : kLevels)
  {
    if (level.effort == stp::UserDefinedFlags::CNF_EFFORT_AUTO)
      continue;
    s.options().set_str(kEffort, level.name);
    EXPECT_EQ(level.effort, flags(s).cnf_effort) << level.name;
    EXPECT_EQ(level.name, s.options().get_str(kEffort));
  }

  // Auto is a level like the others here, and the only one that matters to a
  // caller that has already set another: it is the default, so without it
  // there is no way back to where the solver started.
  s.options().set_str(kEffort, "auto");
  EXPECT_EQ(stp::UserDefinedFlags::CNF_EFFORT_AUTO, flags(s).cnf_effort);
  s.options().set_str(kEffort, "gia-low");
  s.options().reset(kEffort);
  EXPECT_EQ(stp::UserDefinedFlags::CNF_EFFORT_AUTO, flags(s).cnf_effort);

  // The registry names exactly these levels, so a rung added to it without a
  // mapping here fails this test rather than going untested.
  std::vector<std::string> named;
  for (const Level& level : kLevels)
    named.emplace_back(level.name);
  std::vector<std::string> registry = s.options().info(kEffort).values;
  std::sort(named.begin(), named.end());
  std::sort(registry.begin(), registry.end());
  EXPECT_EQ(named, registry);
}

// Anything else is refused and leaves the level alone. The field is an enum,
// so an accepted value past the end would be one no switch in the generator
// handles -- it would fall to whichever arm happens to be first and the
// caller would never learn that what they asked for did not happen.
TEST(cnf_effort_flag, OutOfRangeIsRefusedAndLeavesTheLevelAlone)
{
  TermManager tm;
  Solver s(tm);
  s.options().set_str(kEffort, "high");
  EXPECT_EQ(stp::UserDefinedFlags::CNF_EFFORT_HIGH, flags(s).cnf_effort);

  // One past 2.x's last ordinal, and a negative one. 3.x takes no ordinal at
  // all: 3, 2.x's number for "high", names nothing either.
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, s.options().set(kEffort, "13"));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, s.options().set(kEffort, "-1"));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, s.options().set(kEffort, "3"));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, s.options().set_str(kEffort, "extreme"));
  EXPECT_EQ("high", s.options().get_str(kEffort));
  EXPECT_EQ(stp::UserDefinedFlags::CNF_EFFORT_HIGH, flags(s).cnf_effort);
}

// The level reaches the solve, and every one of them answers the same
// question the same way. A level that changed a verdict would be a bug in
// the generator, not a setting -- and since seven of the thirteen pick a whole
// bit-blasting backend rather than an effort, this is where a backend that
// encoded the query wrongly would be caught. The model self-check
// (check-sanity, on for every 2.x checker) holds each level's model against
// the assertions too.
TEST(cnf_effort_flag, EveryLevelDecidesTheSameQuery)
{
  for (const Level& level : kLevels)
  {
    TermManager tm;
    Solver s(tm);
    s.options().set_bool("check-sanity", true);
    s.options().set_str(kEffort, level.name);

    const Sort bv = tm.mk_bv_sort(32);
    const Term a = tm.declare("a", bv);
    const Term b = tm.declare("b", bv);
    s.add(bvmul(a, b) == tm.mk_bv(32, 3037 * 3041));
    s.add(bvugt(a, 1));
    s.add(bvugt(b, 1));

    EXPECT_TRUE(s.check_sat().is_sat()) << "effort=" << level.name;
  }
}
