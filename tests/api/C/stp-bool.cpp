#include <gtest/gtest.h>
#include <stdio.h>
#include "stp/c_interface.h"

TEST(stp_bool,one)
{
	VC vc;
	int query_result;
	int count = 0;

	vc = vc_createValidityChecker ();


	Type type64 = vc_boolType (vc);


	vc_Destroy (vc);
    // FIXME: Actually test something
    //ASSERT_TRUE(false && "FIXME: Actually test something");
}
