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

namespace
{
std::uint64_t maximum(const std::string& diagnostics, const std::string& key)
{
  const std::string marker = "\"" + key + "\":";
  std::uint64_t value = 0;
  for (std::size_t at = 0;
       (at = diagnostics.find(marker, at)) != std::string::npos;)
  {
    at += marker.size();
    value = std::max<std::uint64_t>(value, std::stoull(diagnostics.substr(at)));
  }
  return value;
}

stp::Options options(const std::string& backend)
{
  stp::Options o;
  o.set("sat-backend", backend);
  o.set("incremental", "on");
  o.set("lra-persistent-state", "true");
  o.set("lra-float-driver", "false");
  o.set("produce-models", "true");
  o.set("print-functionstat", "true");
  return o;
}

class RealSessions : public ::testing::TestWithParam<std::string>
{
};
} // namespace

TEST_P(RealSessions, FirstSearchIncludesAssumptions)
{
  stp::TermManager tm;
  std::string diagnostics;
  stp::Solver solver(tm, options(GetParam()));
  solver.set_diagnostic_sink([&](std::string_view text)
                             { diagnostics += text; });
  solver.parse_smt2(
      "(set-logic QF_LRA)(declare-const x Real)(assert (>= x 0))");
  ASSERT_TRUE(solver.check_sat({solver.parse_term("(< x 0)")}).is_unsat());
  solver.reset_assertions();
  ASSERT_NE(diagnostics.find("Real session: check 1"), std::string::npos);
  // An unrestricted base solve would have produced a complete SAT candidate.
  EXPECT_EQ(0u, maximum(diagnostics, "sat_candidates")) << diagnostics;
  EXPECT_GT(maximum(diagnostics, "persistent_extensions"), 0u) << diagnostics;
}

TEST_P(RealSessions, FirstSearchIncludesPushedAssertions)
{
  stp::TermManager tm;
  std::string diagnostics;
  auto o = options(GetParam());
  o.set("lra-persistent-state", "false");
  o.set("lra-incremental-session", "true");
  stp::Solver solver(tm, o);
  solver.set_diagnostic_sink([&](std::string_view text)
                             { diagnostics += text; });
  solver.parse_smt2(
      "(set-logic QF_LRA)(declare-const x Real)(declare-const flag Bool)"
      "(assert (>= x 0))(assert flag)");
  solver.push();
  // A Boolean contradiction produces no candidate even without arithmetic
  // propagation. Solving the satisfiable base first would produce one.
  solver.assert_formula(solver.parse_term("(not flag)"));
  ASSERT_TRUE(solver.check_sat().is_unsat());
  solver.reset_assertions();
  ASSERT_NE(diagnostics.find("Real session: check 1"), std::string::npos);
  EXPECT_EQ(0u, maximum(diagnostics, "sat_candidates")) << diagnostics;
}

TEST_P(RealSessions, ChecksPushPopModelsAndBudgetRecovery)
{
  stp::TermManager tm;
  std::string diagnostics;
  stp::Solver solver(tm, options(GetParam()));
  solver.set_diagnostic_sink([&](std::string_view text)
                             { diagnostics += text; });
  solver.parse_smt2(
      "(set-logic QF_LRA)(declare-const x Real)(declare-const y Real)"
      "(assert (or (and (= x 0) (= y 1)) (and (= x 1) (= y 0))))");
  const auto base = solver.assertions();
  for (unsigned i = 0; i < 12; ++i)
  {
    const auto region = solver.parse_term(i % 2 ? "(= x 0)" : "(= x 1)");
    ASSERT_TRUE(solver.check_sat({region}).is_sat());
    for (const auto& assertion : base)
      EXPECT_TRUE(solver.value(assertion).to_bool());
    EXPECT_TRUE(solver.value(region).to_bool());
    solver.push();
    solver.assert_formula(solver.parse_term("(> (+ x y) 1)"));
    EXPECT_TRUE(solver.check_sat({region}).is_unsat());
    const auto core = solver.unsat_assumptions();
    for (const auto& term : core)
      EXPECT_EQ(region.id(), term.id());
    solver.pop();
  }
  stp::CheckBudget exhausted;
  exhausted.time = std::chrono::milliseconds(0);
  EXPECT_TRUE(solver.check_sat({}, exhausted).is_unknown());
  EXPECT_TRUE(solver.check_sat({solver.parse_term("(= x 0)")}).is_sat());
  solver.reset_assertions();
  EXPECT_GT(maximum(diagnostics, "persistent_extensions"), 12u) << diagnostics;
  EXPECT_EQ(1u, maximum(diagnostics, "core_rebuilds")) << diagnostics;
  solver.assert_formula(solver.parse_term("(> x 5)"));
  EXPECT_TRUE(solver.check_sat().is_sat());
  EXPECT_TRUE(solver.value(solver.parse_term("(> x 5)")).to_bool());
}

TEST_P(RealSessions, ConflictOmitsIrrelevantAssumptions)
{
  stp::TermManager tm;
  auto o = options(GetParam());
  o.set("print-functionstat", "false");
  stp::Solver solver(tm, o);
  solver.parse_smt2(
      "(set-logic QF_LRA)(declare-const x Real)(declare-const y Real)"
      "(assert (<= x 0))");
  const auto relevant = solver.parse_term("(>= x 1)");
  const auto unrelated = solver.parse_term("(>= y 100)");
  ASSERT_TRUE(solver.check_sat({relevant, unrelated}).is_unsat());
  const auto core = solver.unsat_assumptions();
  ASSERT_EQ(1u, core.size());
  EXPECT_EQ(relevant.id(), core.front().id());
  EXPECT_TRUE(solver.check_sat(core).is_unsat());
  EXPECT_TRUE(solver.check_sat({unrelated}).is_sat());
  solver.assert_formula(solver.parse_term("(>= x 1)"));
  ASSERT_TRUE(solver.check_sat({unrelated}).is_unsat());
  EXPECT_TRUE(solver.unsat_assumptions().empty());
}

TEST_P(RealSessions, ConstantDuplicateAndOppositeAssumptions)
{
  auto o = options(GetParam());
  o.set("print-functionstat", "false");
  stp::TermManager tm;
  stp::Solver solver(tm, o);
  solver.parse_smt2(
      "(set-logic QF_LRA)(declare-const x Real)(declare-const y Real)"
      "(assert (<= x 0))");
  const auto yes = solver.parse_term("true");
  const auto no = solver.parse_term("false");
  const auto x = solver.parse_term("(>= x 1)");
  const auto y = solver.parse_term("(>= y 1)");
  EXPECT_TRUE(solver.check_sat({yes}).is_sat());
  const std::vector<std::vector<stp::Term>> cases{{no, y}, {y, x, x}, {y, !y}};
  for (const auto& assumptions : cases)
  {
    ASSERT_TRUE(solver.check_sat(assumptions).is_unsat());
    const auto failed = solver.unsat_assumptions();
    ASSERT_FALSE(failed.empty());
    for (const auto& term : failed)
      EXPECT_TRUE(std::any_of(assumptions.begin(), assumptions.end(),
                              [&](const stp::Term& original)
                              { return term.id() == original.id(); }));
    EXPECT_TRUE(solver.check_sat(failed).is_unsat());
    EXPECT_TRUE(solver.check_sat({yes, y}).is_sat());
  }
  solver.push();
  solver.assert_formula(x);
  ASSERT_TRUE(solver.check_sat({y}).is_unsat());
  EXPECT_TRUE(solver.unsat_assumptions().empty());
  solver.pop();
  EXPECT_TRUE(solver.check_sat({y}).is_sat());
  solver.reset_assertions();
  EXPECT_TRUE(solver.check_sat({x}).is_sat());
  solver.assert_formula(no);
  ASSERT_TRUE(solver.check_sat({x}).is_unsat());
  EXPECT_TRUE(solver.unsat_assumptions().empty());
}

TEST_P(RealSessions, SwitchingSolversPreservesAssertionsModelsAndCores)
{
  auto o = options(GetParam());
  o.set("print-functionstat", "false");
  stp::TermManager tm;
  stp::Solver first(tm, o);
  first.parse_smt2(
      "(set-logic QF_LRA)(declare-const x Real)(declare-const y Real)"
      "(assert (= y 1))(assert (< x y))");
  const auto low = first.parse_term("(< x 0)");
  const auto high = first.parse_term("(> x 4)");
  stp::Solver second(tm, o);
  second.assert_formula(first.parse_term("(>= x 3)"));
  for (unsigned i = 0; i < 4; ++i)
  {
    ASSERT_TRUE(first.check_sat({low}).is_sat());
    EXPECT_TRUE(first.value(low).to_bool());
    ASSERT_TRUE(second.check_sat({high}).is_sat());
    EXPECT_TRUE(second.value(high).to_bool());
    EXPECT_TRUE(first.value(low).to_bool()); // the first model was shelved
    ASSERT_TRUE(first.check_sat({high}).is_unsat());
    EXPECT_TRUE(first.check_sat(first.unsat_assumptions()).is_unsat());
    ASSERT_TRUE(second.check_sat({low}).is_unsat());
    EXPECT_TRUE(second.check_sat(second.unsat_assumptions()).is_unsat());
  }
  EXPECT_TRUE(first.check_sat({low}).is_sat());
  EXPECT_TRUE(second.check_sat({high}).is_sat());
}

TEST_P(RealSessions, ZeroConflictBudgetDoesNotOutliveCheck)
{
  auto o = options(GetParam());
  o.set("print-functionstat", "false");
  stp::TermManager tm;
  stp::Solver solver(tm, o);
  solver.parse_smt2("(set-logic QF_LRA)(declare-const x Real)"
                    "(assert (or (= x 0) (= x 1)))");
  stp::CheckBudget exhausted;
  exhausted.conflicts = 0;
  const auto result = solver.check_sat({}, exhausted);
  EXPECT_TRUE(result.is_unknown()) << result;
  EXPECT_EQ(stp::UnknownReason::CONFLICT_LIMIT, result.reason());
  EXPECT_TRUE(solver.check_sat({solver.parse_term("(= x 1)")}).is_sat());
}

INSTANTIATE_TEST_SUITE_P(AvailableBackends, RealSessions,
                         ::testing::ValuesIn(stp::sat_backends()));
