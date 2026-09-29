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

// check_sizes.cpp -- the widths a sort reports: a bit-vector's width and
// an array's index and element widths, for Bool, for bit-vectors of 8 to 64
// bits and for arrays over them.
//
// 2.x read them with vc_getValueSize and vc_getIndexSize, which answered 0 for
// a sort without that width. 3.x reads them through the sort itself
// (bv_size(), array_index(), array_element()), and a question the sort cannot
// answer is refused with INVALID_ARGUMENT instead of answered with 0.

#include "api_common.hpp"

#include <cstdint>

using namespace stp;

namespace
{

void check_bool()
{
  TermManager tm;
  const Sort boolType = tm.mk_bool_sort();

  ASSERT_TRUE(boolType.is_bool());
  // 3.x: a Bool has neither a width nor an index; asking is an error, not 0
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, boolType.bv_size());
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, boolType.array_index());
}

void check_bv(std::uint32_t bvSize)
{
  TermManager tm;
  const Sort bvType = tm.mk_bv_sort(bvSize);

  ASSERT_TRUE(bvType.is_bv());
  ASSERT_EQ(bvType.bv_size(), bvSize);
  // 3.x: a bit-vector has no index sort; asking is an error, not 0
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, bvType.array_index());
}

void check_array(std::uint32_t indexSize, std::uint32_t valueSize)
{
  TermManager tm;
  const Sort indexType = tm.mk_bv_sort(indexSize);
  const Sort valueType = tm.mk_bv_sort(valueSize);

  const Sort arrayType = tm.mk_array_sort(indexType, valueType);

  ASSERT_TRUE(arrayType.is_array());
  ASSERT_EQ(arrayType.array_index().bv_size(), indexSize);
  ASSERT_EQ(arrayType.array_element().bv_size(), valueSize);
  // the component sorts are the ones the array was made from
  EXPECT_TRUE(arrayType.array_index() == indexType);
  EXPECT_TRUE(arrayType.array_element() == valueType);
}

} // namespace

TEST(stp_test, bool)
{
  check_bool();
}

TEST(stp_test, bv8)
{
  check_bv(8);
}

TEST(stp_test, bv16)
{
  check_bv(16);
}

TEST(stp_test, bv32)
{
  check_bv(32);
}

TEST(stp_test, bv64)
{
  check_bv(64);
}

TEST(stp_test, arr8_4)
{
  check_array(8, 4);
}

TEST(stp_test, arr16_8)
{
  check_array(16, 8);
}

TEST(stp_test, arr32_16)
{
  check_array(32, 16);
}

TEST(stp_test, arr64_32)
{
  check_array(64, 32);
}

// EOF
