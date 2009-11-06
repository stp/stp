#include "c_interface.h"

int main(int argc, char *argv[]) {
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc,'n');
  vc_setFlags(vc,'d');
  vc_setFlags(vc,'p'); 
 
  Expr nresp1 = vc_varExpr(vc, "nresp1", vc_bv32Type(vc));
  Expr packet_get_int0 = vc_varExpr(vc, "packet_get_int0", vc_bv32Type(vc));
  Expr sz = vc_varExpr(vc, "sz", vc_bv32Type(vc));

  Expr d0,d1,d2;
  Expr exprs[] = {
    // nresp1 == packet_get_int0
    vc_eqExpr(vc, nresp1, packet_get_int0),
    
    // nresp1 > 0
    vc_bvGtExpr(vc, nresp1, vc_bv32ConstExprFromInt(vc, 0)),
    
    // sz == nresp1 * 4
    vc_eqExpr(vc, sz, d0=vc_bv32MultExpr(vc, nresp1, vc_bv32ConstExprFromInt(vc, 4))),
    
    // sz > nresp1 || sz < 0
    vc_orExpr(vc, d1=vc_sbvGeExpr(vc, sz, nresp1), d2=vc_sbvLtExpr(vc, sz, vc_bv32ConstExprFromInt(vc, 0))),
  };
  
  Expr res = vc_andExprN(vc, exprs, sizeof(exprs)/sizeof(exprs[0]));
  //vc_printExpr(vc, res);
  vc_query(vc,res);

  vc_DeleteExpr(nresp1);
  vc_DeleteExpr(packet_get_int0);
  vc_DeleteExpr(sz);

  vc_DeleteExpr(d0);
  vc_DeleteExpr(d1);
  vc_DeleteExpr(d2);

  vc_DeleteExpr(exprs[0]);
  vc_DeleteExpr(exprs[1]);
  vc_DeleteExpr(exprs[2]);
  vc_DeleteExpr(exprs[3]);
  vc_DeleteExpr(res);




  vc_Destroy(vc);
  return 0;
}

