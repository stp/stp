/***********
AUTHORS:  Dan Liew

BEGIN DATE: Apr, 2014

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

/* g++ -I/home/vganesh/stp/c_interface simplify.c -L/home/vganesh/stp/lib -lstp
 * -g */

#include "stp/c_interface.h"
#include <cstdint>
#include <gtest/gtest.h>
#include <stdio.h>
#include <stdlib.h>

TEST(getbv, INT64)
{
  ASSERT_EQ(64ul, sizeof(uint64_t) * 8);

  for (uint64_t j = 1; j < UINT64_MAX; j |= (j << 1))
  {
    VC vc = vc_createValidityChecker();
    ASSERT_NE(vc, (void*)0);
    vc_setFlags(vc, 'n');
    vc_setFlags(vc, 'd');
    vc_setFlags(vc, 'p');

    Type bv8 = vc_bvType(vc, 8); // Why do we need this?
    ASSERT_NE(bv8, (void*)0);

    Expr a = vc_bvCreateMemoryArray(vc, "a"); // Why do we need this?
    ASSERT_NE(a, (void*)0);
    Expr index_3 = vc_bvConstExprFromLL(vc, 64, j);
    ASSERT_NE(index_3, (void*)0);

    uint64_t print_index = getBVUnsignedLongLong(index_3);
    ASSERT_EQ(print_index, j);
    vc_DeleteExpr(a);
    vc_DeleteExpr(index_3);
    vc_Destroy(vc);
  }
}

TEST(getbv, INT32)
{
  ASSERT_EQ(32ul, sizeof(int32_t) * 8);

  for (uint32_t j = 1; j < UINT32_MAX; j |= (j << 1))
  {
    VC vc = vc_createValidityChecker();
    ASSERT_NE(vc, (void*)0);
    vc_setFlags(vc, 'n');
    vc_setFlags(vc, 'd');
    vc_setFlags(vc, 'p');

    Type bv8 = vc_bvType(vc, 8);
    ASSERT_NE(bv8, (void*)0);

    Expr a = vc_bvCreateMemoryArray(vc, "a"); // Why do we need this?
    ASSERT_NE(a, (void*)0);

    Expr index_3 = vc_bvConstExprFromInt(vc, 32, j);
    ASSERT_NE(index_3, (void*)0);

    uint32_t print_index = getBVUnsignedLongLong(index_3);
    ASSERT_EQ(print_index, j);
    vc_DeleteExpr(a);
    // vc_DeleteExpr(index_3); - Urgh... STP's C API is inconsistent regarding
    // what we should delete ourselves and what vc_Destroy() will do for us.
    vc_Destroy(vc);
  }
}
