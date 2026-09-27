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

// api3-bvconst-width.cpp -- bit-vector constants at every width around the
// machine-word boundaries.
//
// The constructor bounds the value against the largest one the width can
// hold. 2.x computed that bound as 0xFF..FF >> (64 - n_bits), whose shift
// distance goes negative once n_bits passes 64 -- undefined, and on x86-64
// the distance is masked to six bits, so the bound wrapped back to something
// tiny instead of growing: width 65 admitted only 0 and 1, width 66 only up to
// 3, and anything larger aborted the process from inside the API. Which
// widths broke depended on the value, since 70 and 128 happened to land on a
// bound big enough for a small constant. 3.x's mk_bv(width, value) takes a
// 64-bit value and must accept any value that fits at any width, and refuse
// one that does not with VALUE_OUT_OF_RANGE.

#include "api3_common.hpp"

#include <cstdint>

using namespace stp;

namespace
{

// Every width worth distinguishing around the machine-word boundaries, plus
// the two that used to abort.
const std::uint32_t widths[] = {1,  2,  7,  8,  31, 32,  33,  63,  64,
                                65, 66, 67, 70, 96, 100, 127, 128, 1000};

} // namespace

TEST(bvconst_width, accepts_small_constant_at_every_width)
{
  for (std::uint32_t width : widths)
  {
    TermManager tm;

    // 1 is representable at every width, including width 1.
    const Term e = tm.mk_bv(width, 1);
    ASSERT_FALSE(e.is_null()) << "width " << width;
    EXPECT_EQ(width, e.sort().bv_size()) << "width " << width;
    EXPECT_EQ(1u, e.to_uint64()) << "width " << width;
  }
}

TEST(bvconst_width, value_survives_widths_above_64)
{
  // 65 and 66 are the widths the collapsed bound rejected outright: it made
  // the maximum 1 and 3 respectively, so a constant of 5 could not be built.
  for (std::uint32_t width : widths)
  {
    TermManager tm;
    if (width < 3)
    {
      // 5 genuinely does not fit: 3.x constants are strict
      API3_EXPECT_ERROR(ErrorCode::VALUE_OUT_OF_RANGE, tm.mk_bv(width, 5));
      continue;
    }

    const Term e = tm.mk_bv(width, 5);
    ASSERT_FALSE(e.is_null()) << "width " << width;
    EXPECT_EQ(width, e.sort().bv_size()) << "width " << width;
    EXPECT_EQ(5u, e.to_uint64()) << "width " << width;
  }
}

TEST(bvconst_width, widest_value_round_trips)
{
  // 2.x's value parameter was `unsigned int`, so UINT32_MAX was the largest
  // input the function could be given: every width from 32 up must accept it,
  // and it must come back unchanged rather than truncated by the width
  // handling.
  for (std::uint32_t width : widths)
  {
    if (width < 32)
      continue;

    TermManager tm;
    const Term e = tm.mk_bv(width, UINT32_MAX);
    ASSERT_FALSE(e.is_null()) << "width " << width;
    EXPECT_EQ(width, e.sort().bv_size()) << "width " << width;
    EXPECT_EQ(UINT32_MAX, e.to_uint64()) << "width " << width;
  }
}

TEST(bvconst_width, boundary_values_at_their_exact_width)
{
  // The largest value each width can hold, which is where an off-by-one in
  // the bound shows up. Stops at 32 as the 2.x case did (its value was an
  // unsigned int).
  for (std::uint32_t width = 1; width <= 32; width++)
  {
    const std::uint32_t widest = (width >= 32) ? UINT32_MAX : ((UINT32_C(1) << width) - 1);

    TermManager tm;
    const Term e = tm.mk_bv(width, widest);
    ASSERT_FALSE(e.is_null()) << "width " << width;
    EXPECT_EQ(width, e.sort().bv_size()) << "width " << width;
    EXPECT_EQ(widest, e.to_uint64()) << "width " << width;

    // and the other side of the bound: one past it does not fit
    const std::uint64_t past = static_cast<std::uint64_t>(widest) + 1;
    API3_EXPECT_ERROR(ErrorCode::VALUE_OUT_OF_RANGE, tm.mk_bv(width, past));
  }
}
