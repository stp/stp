#include "c_interface.h"

#include <stdio.h>

int main()
{
    VC vc;
    vc = vc_createValidityChecker();

    Expr x = vc_varExpr(vc, "x", vc_boolType(vc));
    Expr y = vc_varExpr(vc, "y", vc_boolType(vc));

    Expr x_and_y = vc_andExpr(vc, x, y);
    Expr not_x_and_y = vc_notExpr(vc, x_and_y);

    Expr not_x = vc_notExpr(vc, x);
    Expr not_y = vc_notExpr(vc, y);
    Expr not_x_or_not_y = vc_orExpr(vc, not_x, not_y);

    Expr equiv = vc_iffExpr(vc, not_x_and_y, not_x_or_not_y);

    printf("%d\n", vc_query(vc, equiv));

    vc_DeleteExpr(equiv);
    vc_DeleteExpr(not_x_or_not_y);
    vc_DeleteExpr(not_y);
    vc_DeleteExpr(not_x);
    vc_DeleteExpr(not_x_and_y);
    vc_DeleteExpr(x_and_y);
    vc_DeleteExpr(y);
    vc_DeleteExpr(x);
    vc_Destroy(vc);

    return 0;
}
