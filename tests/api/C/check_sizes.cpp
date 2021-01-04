/***********
AUTHORS: Andrew V. Jones

BEGIN DATE: January 2021

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
#include <gtest/gtest.h>
#include <stdio.h>

void check_bool()
{
  VC vc;

  vc = vc_createValidityChecker();
  Type boolType = vc_boolType(vc);

  ASSERT_EQ(vc_getValueSize(vc, boolType), 0);
  ASSERT_EQ(vc_getIndexSize(vc, boolType), 0);
}

void check_bv(int bvSize)
{
  VC vc;

  vc = vc_createValidityChecker();
  Type bvType = vc_bvType(vc, bvSize);

  ASSERT_EQ(vc_getValueSize(vc, bvType), bvSize);
  ASSERT_EQ(vc_getIndexSize(vc, bvType), 0);
}

void check_array(int indexSize, int valueSize)
{
  VC vc;

  vc = vc_createValidityChecker();
  Type indexType = vc_bvType(vc, indexSize);
  Type valueType = vc_bvType(vc, valueSize);

  Type arrayType = vc_arrayType(vc, indexType, valueType);

  ASSERT_EQ(vc_getIndexSize(vc, arrayType), indexSize);
  ASSERT_EQ(vc_getValueSize(vc, arrayType), valueSize);
}

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
