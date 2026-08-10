/***********
AUTHORS: Trevor Hansen

BEGIN DATE: August, 2026

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

#include "stp/c_interface.h"
#include <cstdint>
#include <gtest/gtest.h>

// vc_bvConstExprFromInt bounds the value against the largest one the width
// can hold. That bound used to be computed as 0xFF..FF >> (64 - n_bits),
// whose shift distance goes negative once n_bits passes 64 -- undefined, and
// on x86-64 the distance is masked to six bits, so the bound wrapped back to
// something tiny instead of growing. Width 65 admitted only 0 and 1, width 66
// only up to 3, and anything larger aborted the process from inside the API.
// Which widths broke depended on the value, since 70 and 128 happened to land
// on a bound big enough for a small constant.

namespace
{

// Every width worth distinguishing around the machine-word boundaries, plus
// the two that used to abort.
const int widths[] = {1,  2,  7,  8,  31, 32,  33,  63,  64,
                      65, 66, 67, 70, 96, 100, 127, 128, 1000};

} // namespace

TEST(bvconst_width, accepts_small_constant_at_every_width)
{
  for (int width : widths)
  {
    VC vc = vc_createValidityChecker();
    ASSERT_NE(vc, (void*)0);

    // 1 is representable at every width, including width 1.
    Expr e = vc_bvConstExprFromInt(vc, width, 1);
    ASSERT_NE(e, (void*)0) << "width " << width;
    EXPECT_EQ(width, getBVLength(e)) << "width " << width;
    EXPECT_EQ(1u, getBVUnsigned(e)) << "width " << width;

    vc_Destroy(vc);
  }
}

TEST(bvconst_width, value_survives_widths_above_64)
{
  // 65 and 66 are the widths the collapsed bound rejected outright: it made
  // the maximum 1 and 3 respectively, so a constant of 5 could not be built.
  for (int width : widths)
  {
    if (width < 3)
      continue; // 5 genuinely does not fit

    VC vc = vc_createValidityChecker();
    ASSERT_NE(vc, (void*)0);

    Expr e = vc_bvConstExprFromInt(vc, width, 5);
    ASSERT_NE(e, (void*)0) << "width " << width;
    EXPECT_EQ(width, getBVLength(e)) << "width " << width;
    EXPECT_EQ(5u, getBVUnsigned(e)) << "width " << width;

    vc_Destroy(vc);
  }
}

TEST(bvconst_width, widest_value_round_trips)
{
  // The value parameter is `unsigned int`, so UINT32_MAX is the largest input
  // the function can be given: every width from 32 up must accept it, and it
  // must come back unchanged rather than truncated by the width handling.
  for (int width : widths)
  {
    if (width < 32)
      continue;

    VC vc = vc_createValidityChecker();
    ASSERT_NE(vc, (void*)0);

    Expr e = vc_bvConstExprFromInt(vc, width, UINT32_MAX);
    ASSERT_NE(e, (void*)0) << "width " << width;
    EXPECT_EQ(width, getBVLength(e)) << "width " << width;
    EXPECT_EQ(UINT32_MAX, getBVUnsigned(e)) << "width " << width;

    vc_Destroy(vc);
  }
}

TEST(bvconst_width, boundary_values_at_their_exact_width)
{
  // The largest value each width can hold, which is where an off-by-one in
  // the bound shows up. Stops at 32 because `value` is an unsigned int.
  for (int width = 1; width <= 32; width++)
  {
    const uint32_t widest =
        (width >= 32) ? UINT32_MAX : ((UINT32_C(1) << width) - 1);

    VC vc = vc_createValidityChecker();
    ASSERT_NE(vc, (void*)0);

    Expr e = vc_bvConstExprFromInt(vc, width, widest);
    ASSERT_NE(e, (void*)0) << "width " << width;
    EXPECT_EQ(width, getBVLength(e)) << "width " << width;
    EXPECT_EQ(widest, getBVUnsigned(e)) << "width " << width;

    vc_Destroy(vc);
  }
}
