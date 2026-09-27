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

// api3-errors.cpp -- the error record, the library-level queries, the
// standard-container hooks for Term and Sort, structural equality and the
// thread pinning of this alpha.

#include "api3_common.hpp"

#include <map>
#include <set>
#include <sstream>
#include <thread>
#include <unordered_map>
#include <unordered_set>

using namespace stp;

namespace
{

TEST(Errors, the_record)
{
  TermManager tm;
  const Term u = tm.declare("u", tm.mk_bv_sort(8)), v = tm.declare("v", tm.mk_bv_sort(16));
  try
  {
    (void)bvadd(u, v);
    FAIL() << "no error";
  }
  catch (const RecoverableError& e)
  {
    EXPECT_EQ(e.code(), ErrorCode::SORT_MISMATCH);
    EXPECT_TRUE(e.recoverable());
    EXPECT_EQ(e.function(), "bvadd");
    EXPECT_EQ(e.argument_index(), std::optional<int>(1));
    ASSERT_EQ(e.terms().size(), 2u);
    EXPECT_TRUE(e.terms()[0].same_as(u));
    EXPECT_TRUE(e.terms()[1].same_as(v));
    ASSERT_EQ(e.sorts().size(), 2u);
    EXPECT_TRUE(e.sorts()[0] == v.sort());
    EXPECT_TRUE(e.sorts()[1] == u.sort());
    EXPECT_TRUE(e.option().empty());
    EXPECT_EQ(e.line(), 0);
    EXPECT_EQ(e.column(), 0);
    const std::string what = e.what();
    EXPECT_EQ(what.rfind("invalid call to 'bvadd': ", 0), 0u);
    EXPECT_NE(what.find("(_ BitVec 16)"), std::string::npos);
    EXPECT_NE(what.find("(_ BitVec 8)"), std::string::npos);
    EXPECT_NE(what.find("(argument 1)"), std::string::npos);
    EXPECT_NE(what.find("[SORT_MISMATCH]"), std::string::npos);
    // catchable as the base classes too, and copyable
    const Error& base = e;
    EXPECT_EQ(base.code(), ErrorCode::SORT_MISMATCH);
    const std::exception& std_base = e;
    EXPECT_STREQ(std_base.what(), e.what());
    RecoverableError copy = e;
    EXPECT_EQ(copy.code(), ErrorCode::SORT_MISMATCH);
    EXPECT_EQ(copy.terms().size(), 2u);
  }
  // the error keeps its terms alive
  std::optional<RecoverableError> kept;
  {
    TermManager scoped;
    const Term a = scoped.declare("a", scoped.mk_bv_sort(8));
    kept = API3_ERROR_OF(bvadd(a, scoped.mk_true()));
  }
  ASSERT_TRUE(kept.has_value());
  EXPECT_EQ(kept->terms()[0].symbol(), std::optional<std::string>("a"));
  // an option error names the option
  const std::optional<RecoverableError> oe = API3_ERROR_OF(Options().set("nope", "1"));
  ASSERT_TRUE(oe.has_value());
  EXPECT_EQ(oe->option(), "nope");
  EXPECT_EQ(oe->function(), "Options");
  EXPECT_FALSE(oe->argument_index().has_value());
  EXPECT_TRUE(oe->terms().empty());
  // a parse error carries a position
  Solver s(tm);
  testing::internal::CaptureStdout();
  const std::optional<RecoverableError> pe = API3_ERROR_OF(s.parse_smt2("\n(assert (= u #x0q))"));
  (void)testing::internal::GetCapturedStdout();
  ASSERT_TRUE(pe.has_value());
  EXPECT_EQ(pe->code(), ErrorCode::PARSE);
  EXPECT_EQ(pe->line(), 2);
  // every recoverable code is recoverable by the table
  for (ErrorCode code : {ErrorCode::INVALID_ARGUMENT, ErrorCode::SORT_MISMATCH, ErrorCode::ARITY,
                         ErrorCode::INDEX_OUT_OF_RANGE, ErrorCode::VALUE_OUT_OF_RANGE,
                         ErrorCode::DOES_NOT_FIT, ErrorCode::NOT_A_VALUE, ErrorCode::NO_MODEL,
                         ErrorCode::FOREIGN_MANAGER, ErrorCode::NULL_HANDLE, ErrorCode::UNSUPPORTED,
                         ErrorCode::OPTION_UNKNOWN, ErrorCode::OPTION_VALUE, ErrorCode::OPTION_TIMING,
                         ErrorCode::OPTION_CONFLICT, ErrorCode::OPTION_UNAVAILABLE, ErrorCode::PARSE,
                         ErrorCode::IO, ErrorCode::STATE})
    EXPECT_STRNE(to_string(code), "?");
  EXPECT_STREQ(to_string(ErrorCode::SORT_MISMATCH), "SORT_MISMATCH");
  EXPECT_STREQ(to_string(ErrorCode::RESOURCE), "RESOURCE");
  EXPECT_STREQ(to_string(ErrorCode::INTERNAL), "INTERNAL");
  EXPECT_EQ(static_cast<int>(ErrorCode::RESOURCE), 100);
  EXPECT_EQ(static_cast<int>(ErrorCode::INTERNAL), 101);
}

TEST(Errors, the_recoverable_call_had_no_effect)
{
  TermManager tm;
  Solver s(tm);
  const Term x = tm.declare("x", tm.mk_bv_sort(8));
  s.add(x == 1);
  ASSERT_TRUE(s.check_sat().is_sat());
  const std::size_t symbols = tm.symbols().size();
  // every refused call leaves the manager, the stack, the options and the model alone
  API3_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, s.add(x));
  API3_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, tm.declare("x", tm.mk_bv_sort(9)));
  API3_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, s.pop());
  API3_EXPECT_ERROR(ErrorCode::OPTION_UNKNOWN, s.options().set("nope", "1"));
  API3_EXPECT_ERROR(ErrorCode::OPTION_TIMING, s.options().set_uint("random-seed", 1));
  API3_EXPECT_ERROR(ErrorCode::VALUE_OUT_OF_RANGE, tm.mk_bv(8, 300));
  API3_EXPECT_ERROR(ErrorCode::ARITY, tm.mk_term(Kind::NOT, {}));
  {
    // a second solver over the manager is fine and leaves the first alone
    Solver second(tm);
    second.add(x == 5);
    EXPECT_TRUE(second.check_sat().is_sat());
    EXPECT_EQ(second.model().uint64_value(x), 5u);
  }
  API3_EXPECT_ERROR(ErrorCode::IO, s.parse_file("api3_no_such_file.smt2"));
  API3_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, s.check_sat({x}));
  EXPECT_EQ(tm.symbols().size(), symbols);
  EXPECT_EQ(s.assertions().size(), 1u);
  EXPECT_EQ(s.level(), 0u);
  EXPECT_FALSE(s.options().is_set("random-seed"));
  EXPECT_EQ(s.model().uint64_value(x), 1u);
  EXPECT_EQ(s.statistics().uint64("checks.total"), 1u);
}

TEST(Library, version_and_capabilities)
{
  const Version v = version();
  EXPECT_GE(v.major, 2);
  EXPECT_FALSE(v.string.empty());
  EXPECT_EQ(v.string.rfind(std::to_string(v.major) + "." + std::to_string(v.minor), 0), 0u);
  const std::map<std::string, std::string> caps = capabilities();
  EXPECT_EQ(caps.count("api.version"), 1u);
  EXPECT_EQ(caps.at("api.version").rfind("3.", 0), 0u);
  EXPECT_EQ(caps.at("solvers-per-manager"), "unbounded");
  EXPECT_EQ(caps.at("kind.FP_TO_REAL"), "values-only");
  EXPECT_EQ(caps.at("kind.FP_TO_FP_FROM_REAL"), "values-only");
  EXPECT_EQ(caps.at("real.nonlinear"), "false");
  EXPECT_EQ(caps.at("array.const-equality"), "false");
  EXPECT_EQ(caps.at("cores.assumptions"), "true");
  EXPECT_EQ(caps.at("threads"), "any-thread-one-call-at-a-time");
  EXPECT_EQ(caps.at("lra"), "true");
  EXPECT_TRUE(caps.at("highs") == "true" || caps.at("highs") == "false");
  // the backends of this build are listed with their versions
  const std::vector<std::string> backends = sat_backends();
  EXPECT_FALSE(backends.empty());
  std::string joined;
  for (const std::string& b : backends)
  {
    EXPECT_TRUE(has_sat_backend(b));
    joined += (joined.empty() ? "" : ",") + b;
  }
  EXPECT_EQ(caps.at("sat.backends"), joined);
  EXPECT_FALSE(has_sat_backend("no-such-solver"));
  EXPECT_FALSE(has_sat_backend(""));
  for (const char* b : {"cryptominisat", "cadical"})
  {
    if (has_sat_backend(b))
    {
      EXPECT_EQ(caps.count(std::string("sat.backend.") + b + ".version"), 1u) << b;
    }
  }
  // the process-wide policy for the unsafe codes
  EXPECT_EQ(internal_error_policy(), InternalErrorPolicy::POISON);
  set_internal_error_policy(InternalErrorPolicy::ABORT);
  EXPECT_EQ(internal_error_policy(), InternalErrorPolicy::ABORT);
  set_internal_error_policy(InternalErrorPolicy::POISON);
  EXPECT_EQ(internal_error_policy(), InternalErrorPolicy::POISON);
}

TEST(Library, enum_spellings)
{
  EXPECT_STREQ(to_string(Kind::BV_ADD), "BV_ADD");
  EXPECT_STREQ(smtlib_name(Kind::BV_ADD), "bvadd");
  EXPECT_STREQ(smtlib_name(Kind::FP_RTI), "fp.roundToIntegral");
  EXPECT_STREQ(smtlib_name(Kind::SELECT), "select");
  EXPECT_STREQ(smtlib_name(Kind::BV_EXTRACT), "(_ extract hi lo)");
  EXPECT_STREQ(to_string(Kind::FP_TO_FP_FROM_SBV), "FP_TO_FP_FROM_SBV");
  EXPECT_STREQ(to_string(SortKind::FP), "FloatingPoint");
  EXPECT_STREQ(to_string(SortKind::UNINTERPRETED), "Uninterpreted");
  EXPECT_STREQ(to_string(RoundingMode::RNA), "RNA");
  EXPECT_STREQ(to_string(UnknownReason::TIMEOUT), "timeout");
  EXPECT_STREQ(to_string(UnknownReason::NONE), "none");
  EXPECT_STREQ(to_string(Verdict::SAT), "sat");
  EXPECT_STREQ(to_string(Validity::VALID), "valid");
  EXPECT_STREQ(to_string(Tier::STABLE), "stable");
  EXPECT_STREQ(to_string(Settable::CONSTRUCTION), "construction");
  std::ostringstream os;
  os << Kind::SELECT << " " << RoundingMode::RTN << " " << UnknownReason::INCOMPLETE << " "
     << Verdict::UNKNOWN << " " << Validity::UNKNOWN;
  EXPECT_EQ(os.str(), "SELECT RTN incomplete unknown unknown");
  EXPECT_EQ(static_cast<int>(Kind::NUM_KINDS), 102);
  EXPECT_EQ(static_cast<int>(Kind::VALUE), 0);
  EXPECT_EQ(static_cast<int>(Kind::REAL_GE), 101);
  API3_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, to_string(Kind::NUM_KINDS));
  API3_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, TermManager().mk_term(Kind::NUM_KINDS, {}));
}

TEST(Containers, hash_equal_and_less)
{
  TermManager tm;
  const Sort bv8 = tm.mk_bv_sort(8);
  const Term x = tm.declare("x", bv8), y = tm.declare("y", bv8);
  const Term sum1 = x + y, sum2 = bvadd(x, y), other = y + x;
  EXPECT_TRUE(sum1.same_as(sum2)); // hash-consed
  EXPECT_FALSE(sum1.same_as(x));
  EXPECT_TRUE(std::equal_to<Term>()(sum1, sum2));
  EXPECT_FALSE(std::equal_to<Term>()(sum1, x));
  EXPECT_EQ(std::hash<Term>()(sum1), std::hash<Term>()(sum2));
  EXPECT_EQ(std::hash<Term>()(Term()), 0u);
  std::unordered_set<Term> set{x, y, sum1, sum2, x};
  EXPECT_EQ(set.size(), 3u);
  EXPECT_EQ(set.count(bvadd(x, y)), 1u);
  EXPECT_EQ(set.count(other), other.same_as(sum1) ? 1u : 0u);
  std::unordered_map<Term, int> counts;
  counts[x] += 1;
  counts[tm.declare("x", bv8)] += 1;
  counts[sum1] += 1;
  EXPECT_EQ(counts.size(), 2u);
  EXPECT_EQ(counts[x], 2);
  // ordered containers go by id: the declaration order of the nodes
  std::set<Term> ordered{sum1, y, x};
  ASSERT_EQ(ordered.size(), 3u);
  EXPECT_TRUE(std::less<Term>()(x, y));
  EXPECT_TRUE(Term::Less()(y, sum1));
  EXPECT_FALSE(std::less<Term>()(x, x));
  auto it = ordered.begin();
  EXPECT_TRUE(it->same_as(x));
  ++it;
  EXPECT_TRUE(it->same_as(y));
  ++it;
  EXPECT_TRUE(it->same_as(sum1));
  std::map<Term, std::string> names{{y, "y"}, {x, "x"}};
  EXPECT_EQ(names.begin()->second, "x");
  // null terms and terms of another manager order consistently
  EXPECT_TRUE(std::less<Term>()(Term(), x));
  EXPECT_FALSE(std::less<Term>()(x, Term()));
  EXPECT_FALSE(std::less<Term>()(Term(), Term()));
  TermManager other_tm;
  const Term ox = other_tm.declare("x", other_tm.mk_bv_sort(8));
  EXPECT_FALSE(ox.same_as(x));
  EXPECT_NE(std::less<Term>()(x, ox), std::less<Term>()(ox, x));
  std::unordered_set<Term> mixed{x, ox};
  EXPECT_EQ(mixed.size(), 2u);
  // sorts hash and order too
  std::unordered_map<Sort, int> by_sort;
  by_sort[bv8] = 1;
  by_sort[tm.mk_bv_sort(8)] = 2;
  by_sort[tm.mk_bv_sort(9)] = 3;
  EXPECT_EQ(by_sort.size(), 2u);
  EXPECT_EQ(by_sort[bv8], 2);
  EXPECT_EQ(std::hash<Sort>()(Sort()), 0u);
  // == and != build terms, never booleans
  static_assert(std::is_same<decltype(x == y), Term>::value, "== builds a term");
  static_assert(std::is_same<decltype(x != y), Term>::value, "!= builds a term");
  static_assert(!std::is_convertible<Term, bool>::value, "no truthiness");
  static_assert(!std::is_convertible<Sort, bool>::value, "no truthiness");
  static_assert(!std::is_convertible<Result, bool>::value, "no truthiness");
  EXPECT_EQ((x == y).kind(), Kind::EQUAL);
  EXPECT_EQ((x != y).kind(), Kind::DISTINCT);
}

// A manager and everything created from it may be used from any thread, one
// call at a time (the caller serialises); only interrupt() may overlap a
// running check.
TEST(Threads, a_manager_may_be_used_from_another_thread)
{
  TermManager tm;
  const Sort bv8 = tm.mk_bv_sort(8);
  const Term x = tm.declare("x", bv8);
  Solver s(tm);
  s.add(x == 1);
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  bool ok = false;
  std::string failure;
  std::thread worker([&] {
    try
    {
      const Term y = tm.declare("y", bv8);
      const Term one = tm.mk_bv(8, 1);
      ok = x.is_const() && (x + one).sort() == bv8 && m.uint64_value(x) == 1 &&
           bvult(x, 3).sort().is_bool();
      s.add(y == x + one);
      ok = ok && s.check_sat().is_sat() && s.model().uint64_value(y) == 2;
      s.interrupt();
      ok = ok && s.interrupt_pending();
      s.clear_interrupt();
    }
    catch (const RecoverableError& e)
    {
      failure = e.what();
    }
  });
  worker.join();
  EXPECT_TRUE(failure.empty()) << failure;
  EXPECT_TRUE(ok);
  // and the creating thread goes on where the worker left off
  ASSERT_TRUE(tm.symbol("y").has_value());
  EXPECT_EQ(s.assertions().size(), 2u);
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.model().uint64_value(*tm.symbol("y")), 2u);
  EXPECT_EQ(m.uint64_value(x), 1u);
}

// Declared on one thread, asserted and checked on a second, read on a third:
// every theory's engine state (constant bit-vectors, floats, Reals,
// functions, arrays) is exercised off the creating thread.
TEST(Threads, a_manager_handed_from_thread_to_thread)
{
  TermManager tm;
  Solver s(tm);
  const Sort bv8 = tm.mk_bv_sort(8), f32 = tm.mk_fp32_sort();
  const Term x = tm.declare("x", bv8), fx = tm.declare("fx", f32);
  const Term r = tm.declare("r", tm.mk_real_sort());
  const Term f = tm.declare("f", tm.mk_fun_sort({bv8}, bv8));
  const Term a = tm.declare("a", tm.mk_array_sort(bv8, bv8));
  const Term one_and_a_half = tm.mk_fp(f32, RoundingMode::RNE, 1.5);
  std::string failure;
  std::thread second([&] {
    try
    {
      s.add(x == 5);
      s.add(fx == one_and_a_half);
      s.add(real_lt(r + 1, tm.mk_real("3/2")));
      s.add(f(x) == 7);
      s.add(a[x] == 9);
      if (!s.check_sat().is_sat())
        failure = "the check did not answer sat";
    }
    catch (const RecoverableError& e)
    {
      failure = e.what();
    }
  });
  second.join();
  ASSERT_TRUE(failure.empty()) << failure;
  std::thread third([&] {
    try
    {
      const Model m = s.model();
      if (m.uint64_value(x) != 5)
        failure = "x";
      if (!m.value(fx).same_as(one_and_a_half))
        failure = "fx";
      const RationalValue q = m.real_value(r);
      if (q.to_double() >= 0.5)
        failure = "r";
      if (m.uint64_value(f(x)) != 7)
        failure = "f";
      if (m.uint64_value(a[x]) != 9)
        failure = "a";
    }
    catch (const RecoverableError& e)
    {
      failure = e.what();
    }
  });
  third.join();
  EXPECT_TRUE(failure.empty()) << failure;
  // and back on the creating thread
  EXPECT_EQ(s.model().uint64_value(x), 5u);
  EXPECT_TRUE(s.check_sat().is_sat());
}

// A manager created on another thread works there, alongside one live on the
// main thread (the constant library boots per thread, node ids are
// process-wide).
TEST(Threads, a_manager_created_on_another_thread_works_there)
{
  TermManager tm;
  Solver s(tm);
  s.add(tm.declare("x", tm.mk_bv_sort(8)) == 1);
  ASSERT_TRUE(s.check_sat().is_sat());
  std::optional<std::uint64_t> other_id;
  std::thread creator([&] {
    TermManager theirs;
    const Term t = theirs.declare("t", theirs.mk_bv_sort(4));
    Solver their_solver(theirs);
    their_solver.add(t == 3);
    if (their_solver.check_sat().is_sat() && their_solver.model().uint64_value(t) == 3)
      other_id = theirs.id();
  });
  creator.join();
  ASSERT_TRUE(other_id.has_value());
  EXPECT_NE(*other_id, tm.id());
  EXPECT_EQ(s.model().uint64_value(*tm.symbol("x")), 1u);
}

} // namespace
