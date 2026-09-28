/***********
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
**********************/

/*
 * Tests for BitVector_from_Dec's word-level fast path, cross-checked
 * against BitVector_from_Hex and BitVector_to_Dec, which use unrelated
 * code paths.
 */

#include "extlib-constbv/constantbv.h"
#include <gtest/gtest.h>
#include <string>

using namespace CONSTANTBV;

namespace
{

struct Boot
{
  Boot() { BitVector_Boot(); }
};

// Convert through from_Hex, print with to_Dec, read back with from_Dec:
// the result must match the original vector.
void roundTrip(unsigned width, const std::string& hex)
{
  unsigned int* fromHex = BitVector_Create(width, true);
  ASSERT_EQ(ErrCode_Ok,
            BitVector_from_Hex(fromHex, (unsigned char*)hex.c_str()));

  unsigned char* dec = BitVector_to_Dec(fromHex);
  ASSERT_NE(dec, nullptr);

  unsigned int* fromDec = BitVector_Create(width, true);
  EXPECT_EQ(ErrCode_Ok, BitVector_from_Dec(fromDec, dec))
      << "width " << width << " dec " << dec;
  EXPECT_TRUE(BitVector_equal(fromHex, fromDec))
      << "width " << width << " dec " << dec;

  BitVector_Dispose(dec);
  BitVector_Destroy(fromHex);
  BitVector_Destroy(fromDec);
}

// A deterministic hex string of the full width.
std::string pseudoRandomHex(unsigned width, unsigned seed)
{
  const unsigned digits = (width + 3) / 4;
  std::string s;
  unsigned state = seed * 2654435761u + 1;
  for (unsigned i = 0; i < digits; i++)
  {
    state = state * 1103515245 + 12345;
    unsigned d = (state >> 16) & 0xf;
    if (i == 0 && (width % 4) != 0)
      d &= (1u << (width % 4)) - 1; // keep the leading digit in range
    s += "0123456789abcdef"[d];
  }
  return s;
}

TEST(BitVector_from_Dec, round_trips)
{
  Boot boot;
  for (unsigned width : {1u,  2u,  7u,  8u,   31u,  32u,  33u,
                         64u, 65u, 127u, 128u, 512u, 1056u})
  {
    const unsigned digits = (width + 3) / 4;
    roundTrip(width, std::string(digits, '0'));           // zero
    roundTrip(width, std::string(digits - 1, '0') + "1"); // one
    roundTrip(width, pseudoRandomHex(width, width));
    roundTrip(width, pseudoRandomHex(width, width + 1000));
  }
}

TEST(BitVector_from_Dec, all_ones_and_negative)
{
  Boot boot;
  for (unsigned width : {1u, 8u, 33u, 64u, 1056u})
  {
    // -1 must give the all-ones vector.
    unsigned int* v = BitVector_Create(width, true);
    ASSERT_EQ(ErrCode_Ok, BitVector_from_Dec(v, (unsigned char*)"-1"));
    unsigned int* ones = BitVector_Create(width, false);
    BitVector_Fill(ones);
    EXPECT_TRUE(BitVector_equal(v, ones)) << "width " << width;
    BitVector_Destroy(ones);
    BitVector_Destroy(v);
  }
}

TEST(BitVector_from_Dec, overflow_and_parse_errors)
{
  Boot boot;
  for (unsigned width : {1u, 8u, 32u, 33u, 512u})
  {
    // Print 2^width from a wider vector, then read it back into a
    // width-bit vector: it is one past the maximum.
    unsigned int* wide = BitVector_Create(width + 1, true);
    BitVector_Bit_On(wide, width);
    unsigned char* dec = BitVector_to_Dec(wide);
    ASSERT_NE(dec, nullptr);

    unsigned int* v = BitVector_Create(width, true);
    EXPECT_EQ(ErrCode_Ovfl, BitVector_from_Dec(v, dec)) << "width " << width;

    // The maximum itself must fit: 2^width - 1.
    unsigned int* wideMax = BitVector_Create(width + 1, true);
    for (unsigned i = 0; i < width; i++)
      BitVector_Bit_On(wideMax, i);
    unsigned char* decMax = BitVector_to_Dec(wideMax);
    ASSERT_NE(decMax, nullptr);
    EXPECT_EQ(ErrCode_Ok, BitVector_from_Dec(v, decMax)) << "width " << width;

    BitVector_Dispose(dec);
    BitVector_Dispose(decMax);
    BitVector_Destroy(wide);
    BitVector_Destroy(wideMax);
    BitVector_Destroy(v);
  }

  unsigned int* v = BitVector_Create(64, true);
  EXPECT_EQ(ErrCode_Pars, BitVector_from_Dec(v, (unsigned char*)""));
  EXPECT_EQ(ErrCode_Pars, BitVector_from_Dec(v, (unsigned char*)"+"));
  EXPECT_EQ(ErrCode_Pars, BitVector_from_Dec(v, (unsigned char*)"-"));
  EXPECT_EQ(ErrCode_Pars, BitVector_from_Dec(v, (unsigned char*)"12x3"));
  EXPECT_EQ(ErrCode_Ok, BitVector_from_Dec(v, (unsigned char*)"+42"));
  BitVector_Destroy(v);
}

} // namespace
