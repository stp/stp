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

// engine-failure.cpp -- an engine failure under the 3.x API. The
// engine's FatalError throws stp::EngineFatal inside an engine scope (and
// ends the process outside one, as it always did); the API's hubs turn the
// exception into INTERNAL and poison the manager, so that every later call
// on it, its solvers, models and terms is refused with STATE. No public
// entry reaches a FatalError with valid input any more, so the seam is
// exercised through the API's internal header.

#define STP_API_INTERNAL 1
#include "../../../lib/Api/Internal.h"

#include <gtest/gtest.h>

#include <functional>
#include <new>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using namespace stp::api;

namespace
{

TEST(EngineFailure, fatal_error_throws_only_inside_an_engine_scope)
{
  EXPECT_FALSE(stp::FatalErrorThrows());
  {
    detail::EngineScope scope;
    EXPECT_TRUE(stp::FatalErrorThrows());
    EXPECT_THROW(stp::FatalError("simulated engine failure"), stp::EngineFatal);
    {
      detail::EngineScope nested; // nests, and restores what it found
      EXPECT_TRUE(stp::FatalErrorThrows());
    }
    EXPECT_TRUE(stp::FatalErrorThrows());
  }
  EXPECT_FALSE(stp::FatalErrorThrows());

  // the overload that takes a node puts the node in the message, since some
  // callers hand it an empty text
  TermManager tm;
  try
  {
    detail::EngineScope scope;
    stp::FatalError("with a node", detail::node_of(tm.mk_bv(8, 5)), 0);
    FAIL() << "no throw";
  }
  catch (const stp::EngineFatal& e)
  {
    EXPECT_NE(std::string(e.what()).find("with a node"), std::string::npos) << e.what();
  }
}

TEST(EngineFailure, an_engine_failure_is_internal_and_poisons_the_manager)
{
  TermManager tm;
  const Term x = tm.declare("x", tm.mk_bv_sort(8));
  Solver s(tm);
  s.add(x == 1);
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();

  bool caught = false;
  try
  {
    detail::engine_call(tm.impl(), "EngineFailure",
                        [] { stp::FatalError("simulated engine failure"); });
  }
  catch (const Error& e)
  {
    caught = true;
    EXPECT_EQ(e.code(), ErrorCode::INTERNAL);
    EXPECT_NE(std::string(e.what()).find("simulated engine failure"), std::string::npos) << e.what();
    EXPECT_NE(std::string(e.what()).find("poisoned"), std::string::npos) << e.what();
  }
  ASSERT_TRUE(caught);

  // every later call is refused with STATE naming the failure: the manager,
  // a term, the solver, the model
  const std::vector<std::function<void()>> later{
      [&] { (void)tm.mk_bv_sort(16); },
      [&] { (void)tm.declare("y", tm.mk_bv_sort(8)); },
      [&] { (void)(x + 1); },
      [&] { (void)x.str(); },
      [&] { s.add(x == 2); },
      [&] { (void)s.check_sat(); },
      [&] { (void)m.value(x); },
  };
  for (const auto& call : later)
  {
    try
    {
      call();
      FAIL() << "a call on the poisoned manager succeeded";
    }
    catch (const Error& e)
    {
      EXPECT_EQ(e.code(), ErrorCode::STATE) << e.what();
      EXPECT_NE(std::string(e.what()).find("simulated engine failure"), std::string::npos) << e.what();
    }
  }

  // another manager is untouched
  TermManager fresh;
  Solver t(fresh);
  t.add(fresh.declare("z", fresh.mk_bv_sort(4)) == 3);
  EXPECT_TRUE(t.check_sat().is_sat());
}

// Anything else the engine throws unwinds through it as a failure does, and
// is one: INTERNAL, or RESOURCE for std::bad_alloc, with the manager
// poisoned. The API's own refusals raised inside an engine call pass through
// as they are.
TEST(EngineFailure, a_foreign_exception_is_an_engine_failure)
{
  const auto error_of = [](TermManager& tm, const std::function<void()>& engine_work) {
    try
    {
      detail::engine_call(tm.impl(), "EngineFailure", engine_work);
    }
    catch (const Error& e)
    {
      return std::make_pair(std::optional<ErrorCode>(e.code()), std::string(e.what()));
    }
    return std::make_pair(std::optional<ErrorCode>(), std::string("no error"));
  };
  {
    TermManager tm;
    const auto [code, what] =
        error_of(tm, [] { throw std::invalid_argument("simulated foreign failure"); });
    EXPECT_EQ(code, ErrorCode::INTERNAL);
    EXPECT_NE(what.find("simulated foreign failure"), std::string::npos) << what;
    try
    {
      (void)tm.mk_bv_sort(16);
      FAIL() << "a call on the poisoned manager succeeded";
    }
    catch (const Error& e)
    {
      EXPECT_EQ(e.code(), ErrorCode::STATE) << e.what();
    }
  }
  {
    TermManager tm;
    const auto [code, what] = error_of(tm, [] { throw std::bad_alloc(); });
    EXPECT_EQ(code, ErrorCode::RESOURCE) << what;
    EXPECT_THROW((void)tm.mk_bv_sort(16), Error);
  }
  {
    TermManager tm;
    const auto [code, what] = error_of(tm, [&tm] { (void)tm.mk_bv_sort(0); });
    EXPECT_EQ(code, ErrorCode::INVALID_ARGUMENT) << what;
    EXPECT_EQ(tm.mk_bv_sort(16).bv_size(), 16u); // not poisoned
  }
}

} // namespace
