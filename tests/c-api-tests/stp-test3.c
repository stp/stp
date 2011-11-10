#include <stdio.h>
#include "c_interface.h"


void go (enum ifaceflag_t f)
{
	VC vc;
	

	vc = vc_createValidityChecker ();
	vc_setInterfaceFlags(vc, f, 0);
	//vc_setFlags(vc,'s',0);

	vc_parseExpr(vc, "f.cvc");

  	Expr a = vc_varExpr(vc, "a", vc_bvType(vc, 8));
	Expr ct_0 = vc_bvConstExprFromInt(vc, 8, 0);

  	Expr a_eq_0 = vc_eqExpr(vc, a, ct_0);

  	int query = vc_query(vc, a_eq_0);
	vc_Destroy (vc);
}


int main ()
{
	go(SMS);
	go(MS);
	go(CMS2);
	go(MSP);
}
