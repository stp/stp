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


// MinisatSeed_Test.cpp -- every random-seed value reaches MiniSat as a seed
// its generator can take: nonzero, and small enough that drand's integer
// truncation of seed * 1389796 / (2^31 - 1) fits an int.

#include "stp/Sat/MinisatSeed.h"

#include <gtest/gtest.h>

#include <climits>
#include <cstdint>

TEST(MinisatSeed, every_option_value_is_a_seed_drand_can_take)
{
  const std::uint64_t modulus = 2147483647u;
  for (const std::uint64_t option :
       {std::uint64_t(0), std::uint64_t(1), modulus - 1, modulus, 2 * modulus, 3 * modulus + 5,
        std::uint64_t(3300000000000ull), std::uint64_t(1) << 53, UINT64_MAX - 1, UINT64_MAX})
  {
    SCOPED_TRACE(option);
    const double seed = stp::minisatSeed(option);
    EXPECT_GE(seed, 1.0);
    EXPECT_LE(seed, 2147483646.0);
    EXPECT_EQ(seed, static_cast<double>(static_cast<std::uint64_t>(seed))); // integral
    // drand's first step, which must stay within an int
    EXPECT_LT(seed * 1389796 / 2147483647, static_cast<double>(INT_MAX));
  }
  // distinct small seeds stay distinct
  EXPECT_NE(stp::minisatSeed(1), stp::minisatSeed(2));
}
