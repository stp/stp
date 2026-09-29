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

// print.cpp -- printing 32-bit constants, one built from a binary
// string and one from an integer: the presentation language (CVC), which
// 2.x's vc_printExpr wrote to stdout, and SMT-LIB 2. The library prints
// nothing itself; the test writes the text out.

#include "api_common.hpp"

#include <cctype>
#include <iostream>
#include <string>

using namespace stp;

namespace
{

// The printed text without the blanks and line breaks the printer ends with.
std::string trimmed(std::string text)
{
  while (!text.empty() && std::isspace(static_cast<unsigned char>(text.back())))
    text.pop_back();
  return text;
}

TEST(print, one)
{
  // 2.x also set 'n', 'd' and 'p' (print the verdict, check and print the
  // counterexample); they govern checks, and this suite runs none.
  TermManager tm;

  Term ct_3 = tm.mk_bv(32, "00000000000000000000000000000011", 2);
  std::string printed = ct_3.to_string(Format::CVC);
  std::cout << printed << "\n";
  EXPECT_EQ(trimmed(printed), "0x00000003");
  EXPECT_EQ(ct_3.str(), "#x00000003");

  ct_3 = tm.mk_bv(32, 5);
  printed = ct_3.to_string(Format::CVC);
  std::cout << printed << "\n";
  EXPECT_EQ(trimmed(printed), "0x00000005");
  EXPECT_EQ(ct_3.str(), "#x00000005");
}

} // namespace
