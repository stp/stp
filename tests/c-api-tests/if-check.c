#include <stdio.h>
#include "c_interface.h"
#include <stdlib.h>

int main ()
{
	VC vc;
	int query_result;
	int count = 0;

	vc = vc_createValidityChecker ();
	vc_setFlags (vc,'n');
	vc_setFlags (vc,'d');
	vc_setFlags (vc,'p');
	//vc_setFlags (vc,'s');
	vc_setFlags (vc,'v');






	Expr x00000003 = vc_varExpr (vc, "x00000003", vc_bvType (vc, 16));
	Expr hex00FF = vc_bvConstExprFromInt (vc, 16, 0x00FF);

	Expr query1 = vc_eqExpr (vc, x00000003, hex00FF);
	Expr query2 = vc_notExpr (vc, query1);


	// 1
	printf ("******** %02d ********\n", ++count);
	vc_push (vc);
	query_result = vc_query (vc, query1);
	printf ("==> %d\n", query_result);
	vc_pop (vc);
	// 2
	

	printf ("******** %02d ********\n", ++count);
	vc_push (vc);
	query_result = vc_query (vc, query2);
	printf ("==> %d\n", query_result);
	vc_pop (vc);
	////
	Expr x00000005 = vc_varExpr (vc, "x00000005", vc_bvType (vc, 16));
	Expr query3 = vc_eqExpr (vc, x00000005, hex00FF);
	Expr query4 = vc_notExpr (vc, query3);
	// 3
	printf ("******** %02d ********\n", ++count);
	vc_push (vc);
	vc_assertFormula (vc, query1);
	query_result = vc_query (vc, query3);
	printf ("==> %d\n", query_result);
	vc_pop (vc);
	// 4
	printf ("******** %02d ********\n", ++count);
	vc_push (vc);
	vc_assertFormula (vc, query1);
	query_result = vc_query (vc, query4);
	printf ("==> %d\n", query_result);
	vc_pop (vc);
	////
	Expr x00000007 = vc_varExpr (vc, "x00000007", vc_bvType (vc, 16));
	Expr query5 = vc_eqExpr (vc, x00000007, hex00FF);
	Expr query6 = vc_notExpr (vc, query5);
	// 5
	printf ("******** %02d ********\n", ++count);
	vc_push (vc);
	vc_assertFormula (vc, query3);
	vc_assertFormula (vc, query1);
	query_result = vc_query (vc, query5);
	printf ("==> %d\n", query_result);
	vc_pop (vc);
	// 6
	printf ("******** %02d ********\n", ++count);
	vc_push (vc);
	vc_assertFormula (vc, query3);
	vc_assertFormula (vc, query1);
	query_result = vc_query (vc, query6);
	printf ("==> %d\n", query_result);
	vc_pop (vc);
	////
	Expr x00000009 = vc_varExpr (vc, "x00000009", vc_bvType (vc, 32));
	Expr ct_0_32 = vc_bvConstExprFromInt (vc, 32, 0x0);
	Expr query8 = vc_eqExpr (vc, x00000009, ct_0_32);
	Expr query7 = vc_notExpr (vc, query8);
	// 7
	printf ("******** %02d ********\n", ++count);
	vc_push (vc);
	vc_assertFormula (vc, query5);
	vc_assertFormula (vc, query3);
	vc_assertFormula (vc, query1);
	query_result = vc_query (vc, query7);
	printf ("==> %d\n", query_result);
	vc_pop (vc);
	// 8
	printf ("******** %02d ********\n", ++count);
	vc_push (vc);
	vc_assertFormula (vc, query5);
	vc_assertFormula (vc, query3);
	vc_assertFormula (vc, query1);
	query_result = vc_query (vc, query8);
	printf ("==> %d\n", query_result);
	vc_pop (vc);
	////
	Expr x0000000b = vc_varExpr (vc, "x0000000b", vc_bvType (vc, 32));
	Expr query9 = vc_eqExpr (vc, x0000000b, ct_0_32);
	Expr query10 = vc_notExpr (vc, query9);
	// 9
	printf ("******** %02d ********\n", ++count);
	vc_push (vc);
	vc_assertFormula (vc, query7);
	vc_assertFormula (vc, query5);
	vc_assertFormula (vc, query3);
	vc_assertFormula (vc, query1);
	query_result = vc_query (vc, query9);
	printf ("==> %d\n", query_result);
	vc_pop (vc);
	// 10
	printf ("******** %02d ********\n", ++count);
	vc_push (vc);
	vc_assertFormula (vc, query7);
	vc_assertFormula (vc, query5);
	vc_assertFormula (vc, query3);
	vc_assertFormula (vc, query1);
	query_result = vc_query (vc, query10);
	printf ("==> %d\n", query_result);
	vc_pop (vc);
	////
	Expr x0000000d = vc_varExpr (vc, "x0000000d", vc_bvType (vc, 32));
	Expr query11 = vc_eqExpr (vc, x0000000d, ct_0_32);
	Expr query12 = vc_notExpr (vc, query11);
	// 11
	printf ("******** %02d ********\n", ++count);
	vc_push (vc);
	vc_assertFormula (vc, query2);
	query_result = vc_query (vc, query11);
	printf ("==> %d\n", query_result);
	vc_pop (vc);
	// 12
	printf ("******** %02d ********\n", ++count);
	vc_push (vc);
	vc_assertFormula (vc, query2);
	query_result = vc_query (vc, query12);
	printf ("==> %d\n", query_result);
	vc_pop (vc);
	////
	Expr x00000075 = vc_varExpr (vc, "x00000075", vc_bvType (vc, 8));
	Expr ct_0_8 = vc_bvConstExprFromInt (vc, 8, 0x0);
	Expr query14 = vc_eqExpr (vc, x00000075, ct_0_8);
	Expr query13 = vc_notExpr (vc, query14);
	// 13
	printf ("******** %02d ********\n", ++count);
	vc_push (vc);
	vc_assertFormula (vc, query12);
	vc_assertFormula (vc, query2);
	query_result = vc_query (vc, query13);
	printf ("==> %d\n", query_result);
	vc_pop (vc);

	// 14
	printf ("******** %02d ********\n", ++count);
	vc_push (vc);
	vc_assertFormula (vc, query12);
	vc_assertFormula (vc, query2);
	query_result = vc_query (vc, query14);
	printf ("==> %d\n", query_result);
	vc_pop (vc);
	////
	Expr x00000015 = vc_varExpr (vc, "x00000015", vc_bv32Type(vc));
	Expr x0000001b = vc_varExpr (vc, "x0000001b", vc_bv32Type(vc));
	Expr x00000021 = vc_varExpr (vc, "x00000021", vc_bv32Type(vc));
	Expr x00000010 = vc_varExpr (vc, "x00000010", vc_bv32Type(vc));
	Expr x00000017 = vc_varExpr (vc, "x00000017", vc_bv32Type(vc));
	Expr ct_F_32 = vc_bvConstExprFromInt (vc, 32, 0xFFFFFFFF);
	Expr x1b_sub_x21 = vc_bvMinusExpr (vc, 32, x0000001b, x00000021); // Q1
	Expr Q1_plus_x15 = vc_bvPlusExpr (vc, 32, x1b_sub_x21, x00000015); //Q2
	Expr Q2_plus_FF = vc_bvPlusExpr (vc, 32, Q1_plus_x15, ct_F_32); //Q3
	Expr Q3_div_x15 = vc_bvDivExpr (vc, 32, Q2_plus_FF, x00000015); //T1
	Expr x10_sub_x17 = vc_bvMinusExpr (vc, 32, x00000010, x00000017); //Q4
	Expr Q4_div_x15 = vc_bvDivExpr (vc, 32, x10_sub_x17, x00000015); //T2
	Expr query15 = vc_sbvGtExpr (vc, Q3_div_x15, Q4_div_x15);
	Expr query16 = vc_notExpr (vc, query15);
	
	// 15
	printf ("******** %02d ********\n", ++count);
	vc_push (vc);

	Expr query15_0 = vc_eqExpr (vc, x00000015, ct_0_32);
	Expr query15_1 = vc_notExpr (vc, query15_0);
	vc_assertFormula (vc, query15_1);

	vc_assertFormula (vc, query13);
	vc_assertFormula (vc, query12);
	vc_assertFormula (vc, query2);
	query_result = vc_query (vc, query15);
	printf ("==> %d\n", query_result);
	vc_pop (vc);
	// 16
	printf ("******** %02d ********\n", ++count);
	vc_push (vc);
	vc_assertFormula (vc, query13);
	vc_assertFormula (vc, query12);
	vc_assertFormula (vc, query2);
	query_result = vc_query (vc, query16);
	printf ("==> %d\n", query_result);
	vc_pop (vc);
	////
	Expr x00000032 = vc_varExpr (vc, "x00000032", vc_bv32Type(vc));
	Expr x00000038 = vc_varExpr (vc, "x00000038", vc_bv32Type(vc));
	Expr x00000028 = vc_varExpr (vc, "x00000028", vc_bv32Type(vc));
	Expr x0000002e = vc_varExpr (vc, "x0000002e", vc_bv32Type(vc));
	Expr x32_sub_x38 = vc_bvMinusExpr (vc, 32, x00000032, x00000038); //A1
	Expr A1_plus_x15 = vc_bvPlusExpr (vc, 32, x32_sub_x38, x00000015); //A2
	Expr A2_plus_FF = vc_bvPlusExpr (vc, 32, A1_plus_x15, ct_F_32); //A3
	Expr A3_div_x15 = vc_bvDivExpr (vc, 32, A2_plus_FF, x00000015); //A4
	Expr x28_sub_x2e = vc_bvMinusExpr (vc, 32, x00000028, x0000002e); //A5
	Expr A5_div_x15 = vc_bvDivExpr (vc, 32, x28_sub_x2e, x00000015); //A6
	Expr A4_sub_A6 = vc_bvMinusExpr (vc, 32, A3_div_x15, A5_div_x15); //A7
	Expr query17 = vc_sbvGtExpr (vc, A4_sub_A6, ct_0_32);
	Expr query18 = vc_notExpr (vc, query17);
	// 17
	printf ("******** %02d ********\n", ++count);
	vc_push (vc);
	vc_assertFormula (vc, query15);
	vc_assertFormula (vc, query13);
	vc_assertFormula (vc, query12);
	vc_assertFormula (vc, query2);
	query_result = vc_query (vc, query17);
	printf ("==> %d\n", query_result);
	vc_pop (vc);
	// 18
	printf ("******** %02d ********\n", ++count);
	vc_push (vc);
	vc_assertFormula (vc, query15);
	vc_assertFormula (vc, query13);
	vc_assertFormula (vc, query12);
	vc_assertFormula (vc, query2);
	query_result = vc_query (vc, query18);
	printf ("==> %d\n", query_result);
	vc_pop (vc);
	////
	Expr query19 = vc_bvLtExpr (vc, ct_0_32, x00000015);
	// 19 : Problem occurs here.
	printf ("******** %02d ********\n", ++count);
	vc_push (vc);
	vc_assertFormula (vc, query17);
	vc_assertFormula (vc, query15);
	vc_assertFormula (vc, query13);
	vc_assertFormula (vc, query12);
	vc_assertFormula (vc, query2);
	query_result = vc_query (vc, query19);
	printf ("==> %d\n", query_result);
	vc_pop (vc);

	vc_Destroy (vc);
}
