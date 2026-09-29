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

// hoangmle.cpp -- printing a bit-vector constant that is wider than 64
// bits and whose width (69) is not a multiple of four: SMT-LIB 2 writes it
// as a binary literal, #b..., with and without shared subterms.

#include "api_common.hpp"

#include <cctype>
#include <cstdint>
#include <iostream>
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

TEST(hoangmle, one)
{
  TermManager tm;
  const std::string bits =
      "001111001110010101010100000000000000000000000000000000000000000000000";
  const Term a = tm.mk_bv(static_cast<std::uint32_t>(bits.size()), bits, 2);
  ASSERT_EQ(a.sort().bv_size(), 69u);
  // the shared and the unshared printer
  const std::string printed = a.to_string(Format::SMTLIB2);
  const std::string unshared = a.to_string(Format::SMTLIB2, false);
  std::cout << printed << "\nMy print:\n" << unshared << "\n";
  EXPECT_EQ(trimmed(printed), "#b" + bits);
  EXPECT_EQ(trimmed(unshared), "#b" + bits);
  EXPECT_EQ(a.str(), "#b" + bits);
  EXPECT_EQ(a.to_bv_string(2), bits);
}

} // namespace
