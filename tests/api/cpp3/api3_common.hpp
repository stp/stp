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

// api3_common.hpp -- what every 3.x C++ API test shares: a non-simplifying
// manager, an error catcher that hands the RecoverableError back for
// inspection, and a factoring instance hard enough to outlive any budget.
// Names are qualified with stp::api:: (the API's own namespace), so that the
// header also serves a test that includes lib/Api/Internal.h (api3_engine.hpp),
// where stp::Term and the rest are not introduced into stp.

#ifndef STP_TESTS_API3_COMMON_HPP
#define STP_TESTS_API3_COMMON_HPP

#include <stp/stp.hpp>

#include <gtest/gtest.h>

#include <optional>
#include <string>
#include <utility>

namespace api3
{

// A manager that keeps every term as it was built: kind(), children() and
// indices() are only guaranteed without construction-time folding.
inline stp::api::TermManager raw_manager()
{
  stp::api::TermManager::Config cfg;
  cfg.simplify = false;
  return stp::api::TermManager(cfg);
}

// Runs f and returns the RecoverableError it threw, if any.
template <class F> std::optional<stp::api::RecoverableError> catch_error(F&& f)
{
  try
  {
    f();
  }
  catch (const stp::api::RecoverableError& e)
  {
    return e;
  }
  return std::nullopt;
}

// A semiprime with two 40-bit factors at 96 bits: minutes for a SAT solver,
// so any answer inside a test came from a budget, an interrupt or a
// terminator (the 2.x timeout tests use the same instance).
inline void add_hard_factoring(stp::api::TermManager& tm, stp::api::Solver& s)
{
  const stp::api::Sort w = tm.mk_bv_sort(96);
  const stp::api::Term a = tm.declare("hard_a", w), b = tm.declare("hard_b", w);
  const stp::api::Term product = tm.mk_bv(96, "486579698794948075013401", 10);
  const stp::api::Term limit = tm.mk_bv(96, "1099511627776", 10); // 2^40
  s.add(stp::api::bvmul(a, b) == product);
  s.add(stp::api::bvugt(a, 1));
  s.add(stp::api::bvugt(b, 1));
  s.add(stp::api::bvult(a, limit));
  s.add(stp::api::bvult(b, limit));
  s.add(stp::api::bvule(a, b));
}

// The interruptible backend of this build, if any: interrupt() and a
// Terminator reach CaDiCaL and MiniSat mid-search; CryptoMiniSat only
// notices them between its solver calls (capabilities: interrupt.cryptominisat).
inline std::optional<std::string> interruptible_backend()
{
  for (const char* name : {"cadical", "minisat"})
    if (stp::api::has_sat_backend(name))
      return std::string(name);
  return std::nullopt;
}

} // namespace api3

// API3_EXPECT_ERROR(code, statement...): the statement must throw a
// RecoverableError carrying `code`.
#define API3_EXPECT_ERROR(expected_code_, ...)                                 \
  do                                                                           \
  {                                                                            \
    const std::optional<stp::api::RecoverableError> api3_err_ =                     \
        ::api3::catch_error([&] { __VA_ARGS__; });                             \
    ASSERT_TRUE(api3_err_.has_value()) << "no error thrown by: " #__VA_ARGS__; \
    EXPECT_EQ(api3_err_->code(), (expected_code_)) << api3_err_->what();       \
  } while (0)

// API3_ERROR_OF(expression): the error the expression throws, as an optional.
#define API3_ERROR_OF(...) ::api3::catch_error([&] { (void)(__VA_ARGS__); })

#endif
