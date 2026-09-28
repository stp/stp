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

// libstp2-fidelity.cpp -- 2.x behaviours libstp2 once got wrong.
//
// The 2.x suites in this directory run against libstp2 unchanged; the cases
// here pin what they did not reach, each against what 2.x itself did.

#include "stp/c_interface.h"

#include <gtest/gtest.h>

#include <cstdlib>
#include <string>

namespace
{

std::string text_of(Expr e)
{
  char* s = exprString(e);
  std::string out = s != nullptr ? s : "";
  std::free(s);
  return out;
}

// vc_parseMemExpr hands back the ASSERTs and the QUERY apart, asserting only
// the former. The query here is not valid, so neither it nor FALSE may come
// out valid after the parse.
TEST(libstp2_fidelity, a_parsed_query_that_is_not_valid_stays_so)
{
  VC vc = vc_createValidityChecker();
  Expr query = nullptr, asserts = nullptr;
  ASSERT_EQ(1, vc_parseMemExpr(vc, "x : BITVECTOR(8); ASSERT(x = 0hex01); QUERY x = 0hex02;", &query,
                               &asserts));
  EXPECT_NE(std::string::npos, text_of(asserts).find("0x01")) << text_of(asserts);
  EXPECT_EQ(std::string::npos, text_of(asserts).find("FALSE")) << text_of(asserts);
  EXPECT_EQ(0, vc_query(vc, query));
  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  vc_DeleteExpr(query);
  vc_DeleteExpr(asserts);
  vc_Destroy(vc);
}

} // namespace
