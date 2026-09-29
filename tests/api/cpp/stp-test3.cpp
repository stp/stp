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

// stp-test3.cpp -- an SMT-LIB 2 file parsed into a solver running each MiniSat
// flavour (sat-backend minisat and simplifying-minisat), and an entailment
// decided over its assertions.
//
// Every backend exercised here is a MiniSat. 3.x refuses a solver for a
// backend the build lacks when the solver is built (OPTION_UNAVAILABLE)
// rather than aborting at solve time, so each case checks that refusal and
// is skipped in such a build.

#include "api_common.hpp"

using namespace stp;

namespace
{

// Whether the build has the backend; if not, the refusal is checked and the
// caller skips.
bool available(const char* backend)
{
  if (has_sat_backend(backend))
    return true;
  TermManager tm;
  Options o;
  o.set_str("sat-backend", backend);
  const auto e = API_ERROR_OF(Solver(tm, o));
  EXPECT_TRUE(e.has_value()) << "a solver was built for the missing " << backend;
  if (e.has_value())
  {
    EXPECT_EQ(ErrorCode::OPTION_UNAVAILABLE, e->code()) << e->what();
  }
  return false;
}

void go(const char* backend)
{
  TermManager tm;
  Options o;
  o.set_str("sat-backend", backend);
  o.set_bool("check-sanity", true); // the model self-check every 2.x checker ran
  Solver s(tm, o);

  // INPUT_FILE is a macro that expands to a file path
  s.parse_file(INPUT_FILE, Format::SMTLIB2);

  const Term a = tm.declare("a", tm.mk_bv_sort(8));
  const Term ct_0 = tm.mk_bv(8, 0);

  const Term a_eq_0 = a == ct_0;

  ASSERT_TRUE(s.entails(a_eq_0).is_invalid());
}

} // namespace

TEST(stp_test, SMS)
{
  if (!available("simplifying-minisat"))
    GTEST_SKIP() << "the simplifying MiniSat backend is not in this build";
  go("simplifying-minisat");
}

TEST(stp_test, MS)
{
  if (!available("minisat"))
    GTEST_SKIP() << "the MiniSat backend is not in this build";
  go("minisat");
}

// MSP was 2.x's second spelling of MiniSat.
TEST(stp_test, MSP)
{
  if (!available("minisat"))
    GTEST_SKIP() << "the MiniSat backend is not in this build";
  go("minisat");
}
