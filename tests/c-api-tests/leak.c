#include "c_interface.h"
#include <stdio.h>
int main(){
    for (int i=0; i < 10;i++){

   
    VC vc;
 	vc = vc_createValidityChecker();
	vc_setFlags(vc,'n');
  	vc_setFlags(vc,'d');
  	vc_setFlags(vc,'p');
    
    // create 50 expression
    Expr a1 = vc_varExpr(vc, "a1", vc_bv32Type(vc));
    Expr a2 = vc_varExpr(vc, "a2", vc_bv32Type(vc));
    Expr a3 = vc_varExpr(vc, "a3", vc_bv32Type(vc));
    Expr a4 = vc_varExpr(vc, "a4", vc_bv32Type(vc));
    Expr a5 = vc_varExpr(vc, "a5", vc_bv32Type(vc));
    Expr a6 = vc_varExpr(vc, "a6", vc_bv32Type(vc));
    Expr a7 = vc_varExpr(vc, "a7", vc_bv32Type(vc));
    Expr a8 = vc_varExpr(vc, "a8", vc_bv32Type(vc));
    Expr a9 = vc_varExpr(vc, "a9", vc_bv32Type(vc));
    Expr a10 = vc_varExpr(vc, "a10", vc_bv32Type(vc));
    Expr a11 = vc_varExpr(vc, "a11", vc_bv32Type(vc));
    Expr a12 = vc_varExpr(vc, "a12", vc_bv32Type(vc));
    Expr a13 = vc_varExpr(vc, "a13", vc_bv32Type(vc));
    Expr a14 = vc_varExpr(vc, "a14", vc_bv32Type(vc));
    Expr a15 = vc_varExpr(vc, "a15", vc_bv32Type(vc));
    Expr a16 = vc_varExpr(vc, "a16", vc_bv32Type(vc));
    Expr a17 = vc_varExpr(vc, "a17", vc_bv32Type(vc));
    Expr a18 = vc_varExpr(vc, "a18", vc_bv32Type(vc));
    Expr a19 = vc_varExpr(vc, "a19", vc_bv32Type(vc));
    Expr a20 = vc_varExpr(vc, "a20", vc_bv32Type(vc));
    Expr a21 = vc_varExpr(vc, "a21", vc_bv32Type(vc));
    Expr a22 = vc_varExpr(vc, "a22", vc_bv32Type(vc));
    Expr a23 = vc_varExpr(vc, "a23", vc_bv32Type(vc));
    Expr a24 = vc_varExpr(vc, "a24", vc_bv32Type(vc));
    Expr a25 = vc_varExpr(vc, "a25", vc_bv32Type(vc));
    Expr a26 = vc_varExpr(vc, "a26", vc_bv32Type(vc));
    Expr a27 = vc_varExpr(vc, "a27", vc_bv32Type(vc));
    Expr a28 = vc_varExpr(vc, "a28", vc_bv32Type(vc));
    Expr a29 = vc_varExpr(vc, "a29", vc_bv32Type(vc));
    Expr a30 = vc_varExpr(vc, "a30", vc_bv32Type(vc));
    Expr a31 = vc_varExpr(vc, "a31", vc_bv32Type(vc));
    Expr a32 = vc_varExpr(vc, "a32", vc_bv32Type(vc));
    Expr a33 = vc_varExpr(vc, "a33", vc_bv32Type(vc));
    Expr a34 = vc_varExpr(vc, "a34", vc_bv32Type(vc));
    Expr a35 = vc_varExpr(vc, "a35", vc_bv32Type(vc));
    Expr a36 = vc_varExpr(vc, "a36", vc_bv32Type(vc));
    Expr a37 = vc_varExpr(vc, "a37", vc_bv32Type(vc));
    Expr a38 = vc_varExpr(vc, "a38", vc_bv32Type(vc));
    Expr a39 = vc_varExpr(vc, "a39", vc_bv32Type(vc));
    Expr a40 = vc_varExpr(vc, "a40", vc_bv32Type(vc));
    Expr a41 = vc_varExpr(vc, "a41", vc_bv32Type(vc));
    Expr a42 = vc_varExpr(vc, "a42", vc_bv32Type(vc));
    Expr a43 = vc_varExpr(vc, "a43", vc_bv32Type(vc));
    Expr a44 = vc_varExpr(vc, "a44", vc_bv32Type(vc));
    Expr a45 = vc_varExpr(vc, "a45", vc_bv32Type(vc));
    Expr a46 = vc_varExpr(vc, "a46", vc_bv32Type(vc));
    Expr a47 = vc_varExpr(vc, "a47", vc_bv32Type(vc));
    Expr a48 = vc_varExpr(vc, "a48", vc_bv32Type(vc));
    Expr a49 = vc_varExpr(vc, "a49", vc_bv32Type(vc));
    Expr a50 = vc_varExpr(vc, "a50", vc_bv32Type(vc));
    
    vc_DeleteExpr(a1);
    vc_DeleteExpr(a2);
    vc_DeleteExpr(a3);
    vc_DeleteExpr(a4);
    vc_DeleteExpr(a5);
    vc_DeleteExpr(a6);
    vc_DeleteExpr(a7);
    vc_DeleteExpr(a8);
    vc_DeleteExpr(a9);
    vc_DeleteExpr(a10);
    vc_DeleteExpr(a11);
    vc_DeleteExpr(a12);
    vc_DeleteExpr(a13);
    vc_DeleteExpr(a14);
    vc_DeleteExpr(a15);
    vc_DeleteExpr(a16);
    vc_DeleteExpr(a17);
    vc_DeleteExpr(a18);
    vc_DeleteExpr(a19);
    vc_DeleteExpr(a20);
    vc_DeleteExpr(a21);
    vc_DeleteExpr(a22);
    vc_DeleteExpr(a23);
    vc_DeleteExpr(a24);
    vc_DeleteExpr(a25);
    vc_DeleteExpr(a26);
    vc_DeleteExpr(a27);
    vc_DeleteExpr(a28);
    vc_DeleteExpr(a29);
    vc_DeleteExpr(a30);
    vc_DeleteExpr(a31);
    vc_DeleteExpr(a32);
    vc_DeleteExpr(a33);
    vc_DeleteExpr(a34);
    vc_DeleteExpr(a35);
    vc_DeleteExpr(a36);
    vc_DeleteExpr(a37);
    vc_DeleteExpr(a38);
    vc_DeleteExpr(a39);
    vc_DeleteExpr(a40);
    vc_DeleteExpr(a41);
    vc_DeleteExpr(a42);
    vc_DeleteExpr(a43);
    vc_DeleteExpr(a44);
    vc_DeleteExpr(a45);
    vc_DeleteExpr(a46);
    vc_DeleteExpr(a47);
    vc_DeleteExpr(a48);
    vc_DeleteExpr(a49);
    vc_DeleteExpr(a50);
    
    vc_Destroy(vc);
    }
}
