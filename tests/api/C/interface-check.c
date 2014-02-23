// Bug reported by Alvin Cheung. Thanks.

#include "c_interface.h"
#include <iostream>
#include <cassert>
#include <stdexcept>

int main(int argc, char * argv [])
{
  ::VC vc = vc_createValidityChecker();
  ::Expr b1 = ::vc_trueExpr(vc);
  ::Expr b2 = ::vc_falseExpr(vc);
  ::Expr andExpr = ::vc_andExpr(vc, b1, b2);

if (getExprKind(andExpr) !=  ::FALSE )
  throw new std::runtime_error("sa22dfas");

  ::Expr simplifiedExpr = ::vc_simplify(vc, andExpr);

	if (getExprKind(simplifiedExpr) !=  ::FALSE )
	throw new std::runtime_error("sa22dfas");
  return 0;
}

