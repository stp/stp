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

// multi-print.cpp -- printing from two independent managers (2.x: two
// validity checkers), both created up front, the first destroyed before the
// second prints: the second prints exactly as the first did.

#include "api_common.hpp"

#include <cctype>
#include <cstdint>
#include <iostream>
#include <memory>
#include <string>

using namespace stp;

namespace
{

// The printed text without the blanks and line breaks the printer puts around it.
std::string trimmed(std::string text)
{
  while (!text.empty() && std::isspace(static_cast<unsigned char>(text.back())))
    text.pop_back();
  std::size_t start = 0;
  while (start < text.size() && std::isspace(static_cast<unsigned char>(text[start])))
    ++start;
  return text.substr(start);
}

TEST(multiprint, one)
{
  // 2.x set 'n', 'd' and 'p' on each checker (print the verdict, check and
  // print the counterexample); they govern checks, and this suite runs none.
  auto tm = std::make_unique<TermManager>();
  TermManager tm2;
  const std::uint64_t first_id = tm->id();
  EXPECT_NE(tm2.id(), first_id);

  Term ct_3 = tm->mk_bv(32, "00000000000000000000000000000011", 2);
  std::string printed = ct_3.to_string(Format::SMTLIB2);
  std::cout << printed << "\n";
  EXPECT_EQ(trimmed(printed), "#x00000003");

  ct_3 = tm->mk_bv(32, 5);
  printed = ct_3.to_string(Format::SMTLIB2);
  std::cout << printed << "\n";
  EXPECT_EQ(trimmed(printed), "#x00000005");

  // vc_Destroy(vc): the first manager goes once its last handle and term do
  tm.reset();

  ct_3 = tm2.mk_bv(32, "00000000000000000000000000000011", 2);
  EXPECT_TRUE(ct_3.manager() == tm2);
  printed = ct_3.to_string(Format::SMTLIB2);
  std::cout << printed << "\n";
  EXPECT_EQ(trimmed(printed), "#x00000003");

  ct_3 = tm2.mk_bv(32, 5);
  printed = ct_3.to_string(Format::SMTLIB2);
  std::cout << printed << "\n";
  EXPECT_EQ(trimmed(printed), "#x00000005");
}

} // namespace
