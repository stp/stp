#include "c_interface.h"
#include <stdio.h>
#include <iostream>

int main() {
    VC vc = vc_createValidityChecker();
    vc_setFlags(vc, 'p');

    Type int_type = vc_bv32Type(vc);
    Expr zero = vc_bv32ConstExprFromInt(vc, 0);
    Expr int_max = vc_bvConstExprFromInt(vc, 32, 0x7fffffff);
    Expr a = vc_varExpr(vc, "a", int_type);
    Expr b = vc_varExpr(vc, "b", int_type);
    vc_assertFormula(vc, vc_sbvGtExpr(vc, b, zero));
    vc_assertFormula(vc, vc_sbvLeExpr(vc, a, vc_sbvDivExpr(vc, 32,int_max, b)));
    std::cout << vc_query(vc, vc_falseExpr(vc)) << std::endl;
}


