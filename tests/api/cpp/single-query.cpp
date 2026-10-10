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

// single-query.cpp -- ParseMode::SINGLE_QUERY: a script as data. The parse
// applies declarations, definitions and assertions, records one check-sat
// without running it, and refuses, by command and line, everything that
// would change the solver's configuration or state or is not one query.

#include "api_common.hpp"

#include <sstream>
#include <string>
#include <vector>

using namespace stp;

namespace
{

// The error a single-query parse of `script` throws, as text, or "" when it
// parses; on an error the solver's assertions must be as they were.
std::string refusal(const std::string& script)
{
  TermManager tm;
  Solver s(tm);
  s.parse_smt2("(declare-const kept (_ BitVec 4))(assert (= kept #x3))");
  const std::size_t before = s.assertions().size();
  const auto error = API_ERROR_OF(s.parse_smt2(script, ParseMode::SINGLE_QUERY));
  if (!error)
    return "";
  EXPECT_EQ(error->code(), ErrorCode::PARSE) << error->what();
  EXPECT_EQ(s.assertions().size(), before) << script;
  EXPECT_TRUE(s.check_sat().is_sat());
  return error->what();
}

void expect_refused(const std::string& script, const std::string& names)
{
  const std::string what = refusal(script);
  EXPECT_NE(what.find(names), std::string::npos)
      << "expected a refusal naming " << names << " for\n"
      << script << "\ngot: " << what;
}

// What a single-query parse of `script` asserts, decided: the answer of
// check_sat on the parsed assertions.
std::string decided(const std::string& script)
{
  TermManager tm;
  Solver s(tm);
  s.parse_smt2(script, ParseMode::SINGLE_QUERY);
  const Result r = s.check_sat();
  return r.is_sat() ? "sat" : r.is_unsat() ? "unsat" : "unknown";
}

const std::string bv1 = "(set-logic QF_BV)(declare-const a (_ BitVec 1))(assert (= a #b0))";

} // namespace

TEST(SingleQuery, AppliesTheQueryAndRecordsItsLogic)
{
  TermManager tm;
  Solver s(tm);
  EXPECT_EQ(s.declared_logic(), "");
  s.parse_smt2("(set-info :smt-lib-version 2.6)(set-option :print-success false)"
               "(set-logic QF_BV)(declare-const x (_ BitVec 8))"
               "(define-fun y () (_ BitVec 8) (bvadd x #x01))(define-sort B () (_ BitVec 8))"
               "(define-const z B #x05)(declare-fun f ((_ BitVec 8)) (_ BitVec 8))"
               "(assert (= y z))(assert (= (f x) x))(check-sat)(exit)",
               ParseMode::SINGLE_QUERY);
  EXPECT_EQ(s.declared_logic(), "QF_BV");
  EXPECT_EQ(s.assertions().size(), 2u);
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.model().uint64_value(*s.symbol("x")), 4u);
  // A failed parse leaves the logic as it was; one that names none clears it.
  EXPECT_FALSE(refusal("(set-logic QF_ABV)(push 1)(check-sat)").empty());
  s.parse_smt2("(set-logic QF_FP)(push 1)", ParseMode::DECLARE_AND_ASSERT);
  EXPECT_EQ(s.declared_logic(), "QF_FP");
  API_EXPECT_ERROR(ErrorCode::PARSE,
                   s.parse_smt2("(set-logic QF_ABV)(pop 1)(check-sat)", ParseMode::SINGLE_QUERY));
  EXPECT_EQ(s.declared_logic(), "QF_FP");
  s.parse_smt2("(declare-const w (_ BitVec 2))(check-sat)", ParseMode::SINGLE_QUERY);
  EXPECT_EQ(s.declared_logic(), "");
}

TEST(SingleQuery, AResetForgetsTheDeclaredLogic)
{
  // The logic a set-logic named stops being in force at a reset: the
  // script's own (reset), Solver::reset() and Solver::reset_assertions().
  {
    TermManager tm;
    Solver s(tm);
    s.parse_smt2("(set-logic QF_BV)(reset)(declare-const r Real)(assert (> r 0.0))",
                 ParseMode::EXECUTE);
    EXPECT_EQ(s.declared_logic(), "");
    s.parse_smt2("(reset)(set-logic QF_ABV)", ParseMode::EXECUTE);
    EXPECT_EQ(s.declared_logic(), "QF_ABV");
  }
  for (const bool everything : {true, false})
  {
    SCOPED_TRACE(everything ? "reset" : "reset_assertions");
    TermManager tm;
    Solver s(tm);
    s.parse_smt2("(set-logic QF_ABV)(declare-const x (_ BitVec 8))(assert (= x #x01))");
    EXPECT_EQ(s.declared_logic(), "QF_ABV");
    if (everything)
      s.reset();
    else
      s.reset_assertions();
    EXPECT_EQ(s.declared_logic(), "");
  }
}

TEST(SingleQuery, ScriptsThatHideCommandsInQuotedRegionsAreRefusedByName)
{
  // Each holds, as STP's lexer reads it (and SMT-LIB's), a command outside
  // one query: a symbol ends at '|' or '"', so "x| |" is x and a quoted
  // symbol, and a region another reader takes for one atom is code here.
  struct Case
  {
    const char* script;
    const char* names;
  };
  const Case cases[] = {
      {"(set-logic QF_ABV)(declare-const m (Array (_ BitVec 4) (_ BitVec 4)))"
       "(declare-const i (_ BitVec 4))(assert (= (select m i) #x1))\n"
       "(set-info :k (x| |))(check-sat)(push 1)(assert (= (select m i) #x2))(set-info :j (| y|))\n"
       "(check-sat)\n",
       "(push) at line 2"},
      {"(set-logic QF_BV)\n(declare-const a (_ BitVec 1))\n(assert (= a #b0))\n"
       "(set-info :k (x| |))(check-sat)(assert (= a #b1))(set-info :j (| y|))\n(check-sat)\n",
       "(assert) at line 4"},
      {"(set-logic QF_BV)\n(declare-const a (_ BitVec 1))\n(assert (= a #b0))\n"
       "(set-info :k (x| |))(check-sat)(push 1)(assert (= a #b1))(set-info :j (| y|))\n(check-sat)\n",
       "(push) at line 4"},
      {"(set-logic QF_BV)\n(set-info :k (x| |))(set-option :bv-term-abstraction true)"
       "(set-info :j (| y|))\n(declare-const x (_ BitVec 8))\n(check-sat)\n",
       "(set-option :bv-term-abstraction) at line 2"},
      {"(set-logic QF_BV)\n(set-info :k (x| |))(set-option :incremental on)(set-info :j (| y|))\n"
       "(declare-const x (_ BitVec 8))\n(check-sat)\n",
       "(set-option :incremental) at line 2"},
      {"(set-logic QF_BV)\n(declare-const a (_ BitVec 8))\n(assert (= a #x0f))\n"
       "(set-info :k (x| |))(set-option :sat-backend minisat)(set-option :random-seed 7)"
       "(set-info :j (| y|))\n(check-sat)\n",
       "(set-option :sat-backend) at line 4"},
      {"(set-logic QF_BV)\n(declare-const a (_ BitVec 1))\n"
       "(set-info :k (x| |))(push 1)(assert (= a #b0))(assert (= a #b1))(check-sat)(pop 1)"
       "(set-info :j (| y|))\n(check-sat)\n",
       "(push) at line 3"},
      {"(set-logic QF_BV)\n(declare-const a (_ BitVec 1))\n(assert (= a #b0))\n"
       "(set-info :k (x\" \"))(check-sat)(assert (= a #b1))(set-info :j (\" y\"))\n(check-sat)\n",
       "(assert) at line 4"},
      {"(set-logic QF_BV)\n(declare-const a (_ BitVec 1))\n(assert (= a #b0))\n(assert (= a #b1))\n"
       "(set-info :k (x| |))(check-sat)(reset-assertions)(set-info :j (| y|))\n(check-sat)\n",
       "(reset-assertions) at line 5"},
      {"(set-logic QF_BV)\n(set-info :k (x| |))(set-option :random-seed 5)(set-info :j (| y|))\n"
       "(declare-const x (_ BitVec 8))\n(check-sat)\n",
       "(set-option :random-seed) at line 2"},
      {"(set-logic QF_BV)\n(set-info :k (x| |))(set-option :stop-after-cnf true)(set-info :j (| y|))\n"
       "(declare-const x (_ BitVec 8))\n(check-sat)\n",
       "(set-option :stop-after-cnf) at line 2"},
      // Where another reader sees a check-sat, here it is inside a quoted
      // symbol, and the check-sat here is inside its comment: no check-sat.
      {"(set-logic QF_BV)\n(declare-const a (_ BitVec 1))\n(assert (= a #b0))\n"
       "(set-info :k (x|))\n(check-sat)\n; |)) (assert (= a #b1))\n",
       "needs a check-sat, and the script has none"},
      {"(set-logic QF_BV)\n(declare-const a (_ BitVec 1))\n(assert (= a #b0))\n"
       "(set-info :k (x|))\n(check-sat)\n; |)) (check-sat) (push 1) (assert (= a #b1))\n(check-sat)\n",
       "(push) at line 6"},
      {"(set-logic QF_BV)\n(declare-const a (_ BitVec 1))\n(assert (= a #b0))\n"
       "(set-info :k (x|))\n(check-sat)\n; |)) (check-sat) (push 1) (assert (= a #b1))\n",
       "(push) at line 6"},
      {"(set-logic QF_BV)\n(declare-const a (_ BitVec 1))\n(declare-const | | (_ BitVec 1))\n"
       "(declare-const | y| (_ BitVec 1))\n(assert (= a #b0))\n"
       "(assert (bvule a| |))(check-sat)(push 1)(assert (= a #b1))(assert (bvule | y| a))\n(check-sat)\n",
       "(push) at line 6"},
      // An output channel would open a file.
      {"(set-logic QF_BV)\n(declare-const a (_ BitVec 1))\n"
       "(set-info :k (x| |))(set-option :regular-output-channel \"never-written\")"
       "(set-info :j (| y|))\n(assert (= a #b0))\n(check-sat)\n",
       "(set-option :regular-output-channel) at line 3: it would open a file"}};
  for (const Case& c : cases)
  {
    SCOPED_TRACE(c.script);
    expect_refused(c.script, c.names);
  }
}

TEST(SingleQuery, ARefusedScriptLeavesTheSolverAsItWas)
{
  TermManager tm;
  Solver s(tm);
  s.parse_smt2("(set-logic QF_BV)(declare-const kept (_ BitVec 4))(assert (= kept #x3))(check-sat)",
               ParseMode::SINGLE_QUERY);
  API_EXPECT_ERROR(ErrorCode::PARSE,
                   s.parse_smt2("(declare-const fresh (_ BitVec 4))(assert (= fresh #x1))"
                                "(assert (= kept #x4))(push 1)(check-sat)",
                                ParseMode::SINGLE_QUERY));
  EXPECT_EQ(s.assertions().size(), 1u);
  EXPECT_FALSE(s.symbol("fresh").has_value());
  EXPECT_EQ(s.declared_logic(), "QF_BV");
  EXPECT_TRUE(s.check_sat().is_sat());
  // As a DECLARE_AND_ASSERT parse that fails part way leaves it.
  API_EXPECT_ERROR(ErrorCode::PARSE,
                   s.parse_smt2("(declare-const other (_ BitVec 4))(assert (= other #x1))"
                                "(assert (= kept #x4))(assert (bvadd))"));
  EXPECT_EQ(s.assertions().size(), 1u);
  EXPECT_FALSE(s.symbol("other").has_value());
  EXPECT_TRUE(s.check_sat().is_sat());
}

TEST(SingleQuery, QuotedSymbolsAndStringsAreData)
{
  // |, ", (, ) and ; inside a quoted symbol or a string are characters, and
  // the assertions around them are applied.
  EXPECT_EQ(decided("(set-info :source |a (b) ; \"c\" d|)(set-info :k \"x | ( ) ; \"\"y\"\"\")"
                    "(set-logic QF_BV)(declare-const |a (b) ; c| (_ BitVec 4))"
                    "(declare-const |x\"y| (_ BitVec 4))"
                    "(assert (= |a (b) ; c| #x1))(assert (= |x\"y| (bvadd |a (b) ; c| #x1)))"
                    "(assert (! (= |x\"y| #x2) :named |n ( ) ;|))(check-sat)"),
            "sat");
  EXPECT_EQ(decided("(set-logic QF_BV)(declare-const |;| (_ BitVec 4))"
                    "(assert (= |;| #x1))(assert (= |;| #x2))(check-sat)"),
            "unsat");
}

TEST(SingleQuery, TheLogicIsNamedOnceBeforeTheQuery)
{
  expect_refused("(set-logic QF_BV)(set-logic QF_BV)(check-sat)",
                 "(set-logic) at line 1: the script names its logic once");
  expect_refused("(declare-const x (_ BitVec 4))\n(set-logic QF_BV)(check-sat)",
                 "(set-logic) at line 2: it follows a declaration");
  expect_refused("(set-logic QF_BV)(assert true)(set-logic QF_ABV)(check-sat)",
                 "(set-logic) at line 1");
  // set-info and set-option may come first.
  EXPECT_EQ(refusal("(set-info :status sat)(set-option :produce-models true)(set-logic QF_BV)"
                    "(check-sat)"),
            "");
  // No set-logic at all: every theory is read, and none is named.
  EXPECT_EQ(decided("(declare-const r (_ FloatingPoint 8 24))(assert (fp.isNaN r))(check-sat)"),
            "sat");
}

TEST(SingleQuery, EveryCommandOutsideOneQueryIsRefusedByName)
{
  const char* const commands[] = {"(push 1)",
                                  "(pop 1)",
                                  "(reset)",
                                  "(reset-assertions)",
                                  "(check-sat-assuming (true))",
                                  "(get-model)",
                                  "(get-value (x))",
                                  "(get-assignment)",
                                  "(get-unsat-core)",
                                  "(get-unsat-assumptions)",
                                  "(get-proof)",
                                  "(get-info :name)",
                                  "(get-option :produce-models)",
                                  "(get-assertions)",
                                  "(echo \"x\")",
                                  "(declare-datatypes ((T 0)) (((c))))",
                                  "(declare-datatype T ((c)))",
                                  "(define-fun-rec g ((y (_ BitVec 4))) (_ BitVec 4) y)",
                                  "(define-funs-rec ((g ((y (_ BitVec 4))) (_ BitVec 4))) (y))",
                                  "(declare-sort-parameter P)"};
  for (const char* command : commands)
  {
    SCOPED_TRACE(command);
    const std::string name = std::string(command).substr(1, std::string(command).find_first_of(" )") - 1);
    // Before the check-sat: not part of a single query.
    expect_refused("(set-logic QF_BV)(declare-const x (_ BitVec 4))\n" + std::string(command) +
                       "\n(check-sat)",
                   "(" + name + ") at line 2: it is not part of a single query");
    // After it: it follows the check-sat.
    expect_refused("(set-logic QF_BV)(declare-const x (_ BitVec 4))(check-sat)\n" +
                       std::string(command),
                   "(" + name + ") at line 2: it follows the check-sat");
  }
}

TEST(SingleQuery, OnlyThePrintingOptionsAreAccepted)
{
  EXPECT_EQ(refusal("(set-option :print-success false)(set-option :print-success true)"
                    "(set-option :produce-models true)(set-option :produce-models false)"
                    "(set-logic QF_BV)(check-sat)"),
            "");
  expect_refused("(set-option :produce-unsat-cores true)(check-sat)",
                 "(set-option :produce-unsat-cores) at line 1: the solver's options are its caller's");
  expect_refused("(set-option :diagnostic-output-channel \"x\")(check-sat)",
                 "(set-option :diagnostic-output-channel) at line 1: it would open a file");
  expect_refused("(set-option :global-declarations true)(check-sat)",
                 "(set-option :global-declarations)");
  expect_refused("(set-option :timeout 5)(check-sat)", "(set-option :timeout)");
  // A value the option cannot take is refused as in any parse.
  EXPECT_FALSE(refusal("(set-option :print-success 7)(check-sat)").empty());
  // The printing options change nothing here: the solver's own still stand.
  TermManager tm;
  Options o;
  o.set("produce-models", "true");
  Solver s(tm, o);
  s.parse_smt2("(set-option :produce-models false)(declare-const x (_ BitVec 4))"
               "(assert (= x #x7))(check-sat)",
               ParseMode::SINGLE_QUERY);
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.model().uint64_value(*s.symbol("x")), 7u);
}

TEST(SingleQuery, ExactlyOneCheckSat)
{
  expect_refused(bv1, "needs a check-sat, and the script has none");
  EXPECT_EQ(refusal(bv1 + "(check-sat)"), "");
  expect_refused(bv1 + "(check-sat)\n(check-sat)",
                 "(check-sat) at line 2: a single query has one check-sat");
  // Recorded, not run: nothing is decided by the parse.
  TermManager tm;
  Solver s(tm);
  s.parse_smt2(bv1 + "(assert (= a #b1))(check-sat)", ParseMode::SINGLE_QUERY);
  EXPECT_EQ(s.statistics().uint64("checks.total"), 0u);
  EXPECT_TRUE(s.check_sat().is_unsat());
}

TEST(SingleQuery, ExitComesOnlyAfterTheCheckSat)
{
  EXPECT_EQ(refusal(bv1 + "(check-sat)(exit)"), "");
  EXPECT_EQ(refusal(bv1 + "(check-sat)(exit)(exit)\n(exit)"), "");
  expect_refused(bv1 + "\n(exit)(check-sat)", "(exit) at line 2: it comes before the check-sat");
  // An exit ends nothing: what follows it is checked as well.
  expect_refused(bv1 + "(check-sat)(exit)\n(assert (= a #b1))", "(assert) at line 2: it follows");
  expect_refused(bv1 + "(check-sat)(exit)\n(push 1)", "(push) at line 2");
}

TEST(SingleQuery, NothingFollowsTheCheckSat)
{
  for (const char* command :
       {"(assert (= a #b1))", "(declare-const b (_ BitVec 1))", "(set-info :status sat)",
        "(set-option :print-success false)", "(define-fun c () (_ BitVec 1) a)",
        "(set-logic QF_BV)"})
  {
    SCOPED_TRACE(command);
    const std::string name = std::string(command).substr(1, std::string(command).find(' ') - 1);
    expect_refused(bv1 + "(check-sat)\n" + command,
                   "(" + name + ") at line 2: it follows the check-sat");
  }
}

TEST(SingleQuery, ANulIsRefusedInEveryMode)
{
  // The lexer reads a text as a C string: a NUL would end the script there,
  // and the assertion behind it would be dropped without a word.
  const std::string script = std::string("(declare-const a (_ BitVec 1))(assert (= a #b0))") +
                             '\0' + "(assert (= a #b1))";
  for (ParseMode mode : {ParseMode::DECLARE_AND_ASSERT, ParseMode::EXECUTE, ParseMode::PARSE_ONLY,
                         ParseMode::SINGLE_QUERY})
  {
    TermManager tm;
    Solver s(tm);
    API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, s.parse_smt2(script, mode));
    EXPECT_TRUE(s.assertions().empty());
  }
  TermManager tm;
  Solver s(tm);
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, s.parse(script, Format::SMTLIB2));
  s.parse_smt2("(declare-const a (_ BitVec 1))");
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, s.parse_term(std::string("a") + '\0' + " junk"));
  // From a stream too, where the lexer would end a quoted symbol at the NUL
  // and read the rest as something else.
  const std::string quoted = std::string("(declare-const |b") + '\0' + "c| (_ BitVec 1))";
  for (const std::string& text : {script, quoted})
    for (ParseMode mode : {ParseMode::DECLARE_AND_ASSERT, ParseMode::EXECUTE,
                           ParseMode::PARSE_ONLY, ParseMode::SINGLE_QUERY})
    {
      TermManager tm2;
      Solver s2(tm2);
      std::istringstream in(text);
      API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, s2.parse(in, Format::SMTLIB2, mode));
      EXPECT_TRUE(s2.assertions().empty());
    }
}
