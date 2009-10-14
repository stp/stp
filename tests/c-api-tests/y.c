#include <stdio.h>
#include "c_interface.h"

int main(int argc, char *argv[]) {
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc,'n');
  vc_setFlags(vc,'d');
  vc_setFlags(vc,'p');
  
  Expr nresp1 = vc_varExpr(vc, "nresp1", vc_bv32Type(vc));
  Expr packet_get_int0 = vc_varExpr(vc, "packet_get_int0", vc_bv32Type(vc));
  Expr exprs[] = {
    // nresp1 == packet_get_int0
    vc_eqExpr(vc, nresp1, packet_get_int0),
    // nresp1 > 0
    vc_bvGtExpr(vc, nresp1, vc_bv32ConstExprFromInt(vc, 0))
  };
  
  Expr res = vc_andExprN(vc, exprs, sizeof(exprs)/sizeof(exprs[0]));
  vc_printExpr(vc, res);
  
  int x = vc_query(vc, res);
  printf("vc_query result = %d\n", x);
  vc_printCounterExample(vc);
  
  Expr cex = vc_getCounterExample(vc, res);
  //vc_printExpr(vc, cex);
  //
  vc_Destroy(vc);
}
