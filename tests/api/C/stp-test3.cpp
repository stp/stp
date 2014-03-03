#include <gtest/gtest.h>
#include <stdio.h>
#include "c_interface.h"

void go (enum ifaceflag_t f)
{
	VC vc;
	

	vc = vc_createValidityChecker ();
	vc_setInterfaceFlags(vc, f, 0);
	//vc_setFlags(vc,'s',0);

    // FIXME: Find a way to load this file from correct location
	vc_parseExpr(vc, "f.cvc");

  	Expr a = vc_varExpr(vc, "a", vc_bvType(vc, 8));
	Expr ct_0 = vc_bvConstExprFromInt(vc, 8, 0);

  	Expr a_eq_0 = vc_eqExpr(vc, a, ct_0);

  	int query = vc_query(vc, a_eq_0);
	vc_Destroy (vc);
    ASSERT_TRUE(false && "FIXME: Actually test something");
}


TEST(stp_test,SMS)
{
    go(SMS);
}

TEST(stp_test,MS)
{
    go(MS);
}

TEST(stp_test,CMS2)
{
    go(CMS2);
}

TEST(stp_test,MSP)
{
    go(MSP);
}
