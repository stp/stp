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

// api3-bit_string.cpp -- a bit-vector constant built from a bit string reads
// back as the same bit string. (2.x's vc_printBVBitStringToBuffer wrote it
// into a buffer the caller freed; to_bv_string returns a std::string.)

#include "api3_common.hpp"

#include <cstdint>
#include <string>

using namespace stp;

namespace
{

TEST(bit_string, one)
{
  // Random input bit string
  const std::string bit_string("0101010101");

  TermManager tm;

  // Create an expression from our original bit string
  const Term e = tm.mk_bv(static_cast<std::uint32_t>(bit_string.size()), bit_string, 2);
  EXPECT_EQ(e.sort().bv_size(), bit_string.size());

  // Convert it back to a bit string
  const std::string result = e.to_bv_string(2);

  // strings should be equal
  EXPECT_EQ(result, bit_string);
}

} // namespace
