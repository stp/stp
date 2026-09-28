/***********
AUTHORS:   Andrew Teylu

BEGIN DATE: September, 2026

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

// With EXPRDELETE on, the default, the checker owns every Type, every
// vc_bvConstExprFromInt and every vc_fp* handle, and releases them from
// vc_Destroy. Deleting one early is allowed: the checker forgets it, so the
// destroy walk never reads or frees it a second time (#1140).
TEST(PersistDelete, DeletedTypeIsNotRevisitedByDestroy)
{
  VC vc = vc_createValidityChecker();
  Type bv8 = vc_bvType(vc, 8);
  vc_DeleteExpr(bv8);
  vc_Destroy(vc);
}

// Enabling UF afterwards adopts the checker-owned handles into its registry
// by walking the same list, so a deleted one must already be gone from it.
TEST(PersistDelete, DeletedTypeIsNotAdoptedWhenUFIsEnabledLater)
{
  VC vc = vc_createValidityChecker();
  Type bv8 = vc_bvType(vc, 8);
  vc_DeleteExpr(bv8);
  vc_setFlag(vc, 'u');
  vc_Destroy(vc);
}

// The freed wrapper's address may be handed to a later checker-owned
// wrapper; a stale entry must not make vc_Destroy free the new one twice.
TEST(PersistDelete, DeletedSlotDoesNotAliasALaterWrapper)
{
  VC vc = vc_createValidityChecker();
  Type bv8 = vc_bvType(vc, 8);
  vc_DeleteExpr(bv8);
  for (unsigned i = 0; i < 1000; ++i)
    (void)vc_bvConstExprFromInt(vc, 8, i & 0xffu);
  vc_Destroy(vc);
}

// An early delete leaves the checker usable, and caller-owned handles keep
// their own lifetime either way.
TEST(PersistDelete, EarlyDeleteLeavesTheCheckerUsable)
{
  VC vc = vc_createValidityChecker();
  Type bv8 = vc_bvType(vc, 8);
  Expr x = vc_varExpr(vc, "x", bv8);
  vc_DeleteExpr(bv8);
  Expr one = vc_bvConstExprFromInt(vc, 8, 1);
  Expr eq = vc_eqExpr(vc, x, one);
  EXPECT_EQ(0, vc_query(vc, eq)); // x = 1 is not valid
  vc_DeleteExpr(eq);
  vc_DeleteExpr(x);
  vc_Destroy(vc);
}
