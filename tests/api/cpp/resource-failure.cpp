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

// A RESOURCE error must survive exhaustion of the heap used to report it.
#define STP_API_INTERNAL 1
#include "../../../lib/Api/Internal.h"
#include "../../unit-tests/support/CppAllocationFault.h"

#include <gtest/gtest.h>

using namespace stp::api;

TEST(ResourceFailure, TimedScopesCloseWithoutAllocating)
{
  RunTimes times;
  times.start(RunTimes::Parsing);
  EXPECT_TRUE(times.totals().empty());
  {
    RunTimes::Scope phase(times, RunTimes::SendingToSAT);
    allocation_fault::arm_persistent();
  }
  times.stop(RunTimes::Parsing);
  allocation_fault::disable();
  EXPECT_EQ(times.depth(), 0u);
  const auto totals = times.totals();
  ASSERT_EQ(totals.size(), 2u);
  EXPECT_EQ(totals[0].count, 1);
  EXPECT_EQ(totals[1].count, 1);
}

TEST(ResourceFailure, ReportingAnExhaustedHeapNeedsNoAllocation)
{
  TermManager tm;
  std::optional<UnsafeError> reported;
  bool readable = false;
  bool foreign_exception = false;
  allocation_fault::arm_persistent();
  try
  {
    detail::fail_foreign(tm.impl(), "ResourceFailure", std::bad_alloc());
  }
  catch (const UnsafeError& e)
  {
    // Exercise the complete error record while allocations still fail.
    // Copies of the fallback, as of an ordinary error, allocate nothing.
    reported = e;
    readable = e.code() == ErrorCode::RESOURCE && !e.recoverable() &&
               std::string_view(e.what()).find("[RESOURCE]") != std::string_view::npos &&
               e.function().empty() && !e.argument_index() &&
               e.terms().empty() && e.sorts().empty() && e.option().empty() &&
               e.line() == 0 && e.column() == 0;
  }
  catch (...)
  {
    foreign_exception = true;
  }
  allocation_fault::disable();
  ASSERT_FALSE(foreign_exception);
  ASSERT_TRUE(reported.has_value());
  EXPECT_TRUE(readable);
  EXPECT_TRUE(tm.impl()->poisoned);
  try
  {
    (void)tm.mk_bv_sort(8);
    FAIL() << "the exhausted manager remained usable";
  }
  catch (const Error& e)
  {
    EXPECT_EQ(e.code(), ErrorCode::STATE);
  }
}
