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

// parsefile-using-cinterface.cpp -- parsing a CVC file through the API.
//
// 2.x's vc_parseExpr returned the file's assertions conjoined with its negated
// query as one expression. 3.x's Solver::parse_file asserts the assertions,
// and the query as the assertion of its negation, so that check_sat answers
// the file's question; the file is t.cvc, a KLEE query over byte arrays whose
// QUERY is FALSE (are the assertions satisfiable?).

#include "api_common.hpp"

#include <fstream>
#include <optional>
#include <string>

using namespace stp;

TEST(parsefile, CVC)
{
  TermManager tm;
  // 2.x set 'n', 'd' and 'p'. 'n' printed the verdict, which 3.x returns as a
  // value; 'd' and 'p' are check-sanity and print-counterex.
  Options o;
  o.set_bool("check-sanity", true);
  o.set_bool("print-counterex", true);
  Solver s(tm, o);

  // CVC_FILE is a macro that expands to a file path. A failure would be an
  // exception (2.x counted the handler's calls).
  s.parse_file(CVC_FILE, Format::CVC);

  // vc_printExpr: the parsed problem in the presentation language
  const std::string printed = s.to_string(Format::CVC);
  EXPECT_NE(printed.find("arr665 : ARRAY BITVECTOR(32) OF BITVECTOR(8);"), std::string::npos)
      << printed;
  EXPECT_NE(printed.find("QUERY(FALSE);"), std::string::npos) << printed;

  // The file's sixteen ASSERTs are the solver's assertions, and QUERY FALSE
  // adds nothing; the arrays they read are the manager's symbols.
  EXPECT_EQ(s.assertions().size(), 16u);
  const std::optional<Term> arr665 = tm.symbol("arr665");
  ASSERT_TRUE(arr665.has_value());
  EXPECT_TRUE(arr665->sort() == tm.mk_array_sort(tm.mk_bv_sort(32), tm.mk_bv_sort(8)));

  // The file's question: its assertions are satisfiable (stp --CVC says
  // Invalid.).
  EXPECT_TRUE(s.check_sat().is_sat());
}

// 2.x kept this case disabled: its only refusal of a missing file was a
// FatalError, which ends a running system. 3.x refuses it recoverably, with
// IO, and the solver is as it was.
TEST(parsefile, missing_file)
{
  TermManager tm;
  Options o;
  o.set_bool("check-sanity", true);
  o.set_bool("print-counterex", true);
  Solver s(tm, o);

  const char* nonExistantFile = "./iShOuLdNoTExiSt.cvc";
  std::ifstream file(nonExistantFile, std::ifstream::in);
  ASSERT_FALSE(file.good()); // Check the file does not exist

  const auto e = API_ERROR_OF(s.parse_file(nonExistantFile, Format::CVC));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::IO);
  EXPECT_EQ(e->function(), "Solver::parse_file");
  EXPECT_NE(std::string(e->what()).find("cannot open"), std::string::npos) << e->what();
  EXPECT_TRUE(s.assertions().empty());
  EXPECT_TRUE(s.check_sat().is_sat());
}
