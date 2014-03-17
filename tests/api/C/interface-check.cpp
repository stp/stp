// Bug reported by Alvin Cheung. Thanks.

#include <gtest/gtest.h>
#include "c_interface.h"
#include <iostream>
#include <cassert>
#include <stdexcept>

// FIXME: This is a terrible name, all of the tests in this directory are interface tests!
TEST(interface_check,ONE)
{
  ::VC vc = vc_createValidityChecker();
  ::Expr b1 = ::vc_trueExpr(vc);
  ::Expr b2 = ::vc_falseExpr(vc);
  ::Expr andExpr = ::vc_andExpr(vc, b1, b2);

  ASSERT_TRUE(getExprKind(andExpr) ==  ::FALSE );

  ::Expr simplifiedExpr = ::vc_simplify(vc, andExpr);

  ASSERT_TRUE(getExprKind(simplifiedExpr) ==  ::FALSE );
}

