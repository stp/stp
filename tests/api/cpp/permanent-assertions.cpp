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
#include <cctype>

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

namespace
{
// What a fresh solver, on the batch pipeline, answers for `base` and
// `assumptions` taken together as assertions.
stp::Result fresh_answer(stp::TermManager& tm, const std::vector<stp::Term>& base,
                         const std::vector<stp::Term>& assumptions)
{
  stp::Options options;
  options.set("incremental", "off");
  stp::Solver fresh(tm, options);
  for (const auto& t : base)
    fresh.assert_formula(t);
  for (const auto& t : assumptions)
    fresh.assert_formula(t);
  return fresh.check_sat();
}

// x(i+1) = 11 * x(i) + 7 over 8 bits, the chain the sessions below assert.
unsigned step(unsigned x) { return (11 * x + 7) & 0xff; }

std::string hex(unsigned v)
{
  const char* digits = "0123456789abcdef";
  return std::string("#x") + digits[(v >> 4) & 0xf] + digits[v & 0xf];
}

// A session whose permanent base grows by one definition before every check,
// with pushed content checked and popped in between, answers each check as a
// fresh solver does, and every sat answer's model satisfies the base and the
// assumptions. With `rebuild`, the driver's rebuild limits are as low as they
// go, so the checks also run after the encoding is rebuilt from the base.
void growing_base(bool rebuild)
{
  stp::TermManager tm;
  stp::Options options;
  options.set("incremental", "on");
  options.set("produce-models", "true");
  if (rebuild)
  {
    options.set("incremental-reencode-limit", "1");
    options.set("incremental-semantic-cache-limit", "1");
  }
  stp::Solver solver(tm, options);
  const unsigned n = 30;
  std::string declarations;
  for (unsigned i = 0; i <= n; ++i)
    declarations += "(declare-const x" + std::to_string(i) + " (_ BitVec 8))";
  solver.parse_smt2(declarations);
  std::vector<stp::Term> base;
  unsigned value = 5; // x(i) when x0 = 5
  for (unsigned i = 0; i < n; ++i)
  {
    const std::string x = "x" + std::to_string(i), next = "x" + std::to_string(i + 1);
    auto definition = solver.parse_term("(= " + next + " (bvadd (bvmul " + x + " #x0b) #x07))");
    solver.assert_formula(definition);
    base.push_back(definition);
    value = step(value);
    // Content that is pushed, checked and popped again.
    solver.push();
    solver.assert_formula(solver.parse_term("(bvult " + next + " #x80)"));
    ASSERT_FALSE(solver.check_sat().is_unknown());
    solver.pop();
    // x0 = 5 with x(i+1) at its value is sat; at any other value, unsat.
    const unsigned asked = i % 2 ? value : (value + 1) & 0xff;
    std::vector<stp::Term> assumptions{solver.parse_term("(= x0 #x05)"),
                                       solver.parse_term("(= " + next + " " + hex(asked) + ")")};
    const stp::Result r = solver.check_sat(assumptions);
    const stp::Result expected = fresh_answer(tm, base, assumptions);
    ASSERT_EQ(r.is_sat(), expected.is_sat()) << "check " << i << " rebuild " << rebuild;
    ASSERT_EQ(r.is_unsat(), expected.is_unsat()) << "check " << i << " rebuild " << rebuild;
    ASSERT_EQ(r.is_sat(), asked == value) << "check " << i;
    if (r.is_sat())
    {
      for (const auto& t : base)
        ASSERT_TRUE(solver.value(t).to_bool()) << "check " << i;
      for (const auto& t : assumptions)
        ASSERT_TRUE(solver.value(t).to_bool()) << "check " << i;
    }
  }
}
} // namespace

TEST(PermanentAssertions, AGrowingBaseAnswersAsAFreshSolverWithItsModels)
{
  growing_base(false);
}

TEST(PermanentAssertions, AGrowingBaseAnswersAsAFreshSolverAfterRebuilds)
{
  growing_base(true);
}

TEST(PermanentAssertions, ThePermanentAssertionsAreTheDriversLevelZero)
{
  // Permanent definitions are the incremental driver's level zero: it
  // substitutes them at the base level, where they accumulate as the base
  // grows, and assumes nothing for them at a check beyond the assumption
  // itself. As a pushed frame of their own they would be pushed
  // substitutions, behind an assumed literal of their own.
  stp::TermManager tm;
  stp::Options options;
  options.set("incremental", "on");
  options.set("print-functionstat", "true");
  stp::Solver solver(tm, options);
  std::string diagnostics;
  solver.set_diagnostic_sink([&](std::string_view text) { diagnostics += text; });
  const unsigned n = 12;
  std::string declarations;
  for (unsigned i = 0; i <= n; ++i)
    declarations += "(declare-const x" + std::to_string(i) + " (_ BitVec 8))";
  solver.parse_smt2(declarations);
  for (unsigned i = 0; i < n; ++i)
  {
    const std::string x = "x" + std::to_string(i), next = "x" + std::to_string(i + 1);
    solver.assert_formula(
        solver.parse_term("(= " + next + " (bvadd (bvmul " + x + " #x0b) #x07))"));
    diagnostics.clear();
    ASSERT_TRUE(solver.check_sat({solver.parse_term("(= x0 #x05)")}).is_sat());
  }
  // The last check's line: "... assumed A literals, ... S base-level and P
  // pushed substitutions ...".
  const std::size_t line = diagnostics.rfind("Incremental: encoded");
  ASSERT_NE(line, std::string::npos) << diagnostics;
  auto number_before = [&](const std::string& words)
  {
    const std::size_t at = diagnostics.find(words, line);
    EXPECT_NE(at, std::string::npos) << words;
    std::size_t start = at;
    while (start > 0 && diagnostics[start - 1] == ' ')
      --start;
    while (start > 0 && std::isdigit(static_cast<unsigned char>(diagnostics[start - 1])))
      --start;
    return std::stoul(diagnostics.substr(start, at - start));
  };
  EXPECT_GE(number_before(" base-level and"), n / 2) << diagnostics.substr(line, 300);
  // The assumption's own substitution is the only pushed one.
  EXPECT_LE(number_before(" pushed substitutions"), 1u) << diagnostics.substr(line, 300);
  EXPECT_LE(number_before(" literals, solver has"), 1u) << diagnostics.substr(line, 300);
}
