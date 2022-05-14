/***********
AUTHORS: Stephen McCamant

BEGIN DATE: Feb, 2015

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
**********************/

#include "stp/c_interface.h"
#include <gtest/gtest.h>
#include <string>

TEST(even_eqn_assert, one)
{
  VC vc = vc_createValidityChecker();
  vc_setInterfaceFlags(vc, (ifaceflag_t)0, 0);
  vc_push(vc);
  Type ty_bv16 = vc_bvType(vc, 16);
  Type ty_bv32 = vc_bvType(vc, 32);

  Expr var_is4a = vc_varExpr(vc, "is4a", ty_bv16);
  Expr var_is48 = vc_varExpr(vc, "is48", ty_bv16);
  Expr var_iw48 = vc_varExpr(vc, "iw48", ty_bv32);

  Expr var_t343 = vc_varExpr(vc, "t343", ty_bv32);

  Expr const_0_16 = vc_bvConstExprFromInt(vc, 16, 0);
  Expr const_0_32 = vc_bvConstExprFromInt(vc, 32, 0);

  Expr const_1_1 = vc_bvConstExprFromInt(vc, 1, 1);

  Expr const_42_32 = vc_bvConstExprFromLL(vc, 32, 42);
  Expr const_68_32 = vc_bvConstExprFromLL(vc, 32, 68);
  Expr const_69_32 = vc_bvConstExprFromLL(vc, 32, 69);

  Expr e_concat_35 = vc_bvConcatExpr(vc, const_0_16, var_is48);
  Expr e_concat_36 = vc_bvConcatExpr(vc, const_0_16, var_is4a);

  Expr e_concat_52 = vc_bvConcatExpr(vc, e_concat_36, const_0_16);
  Expr e_extract_50 = vc_bvExtract(vc, e_concat_52, 31, 0);

  Expr e_simp_5 = vc_simplify(vc, e_extract_50);
  Expr e_bvor_3 = vc_bvOrExpr(vc, e_concat_35, e_simp_5);
  Expr e_eq_69 = vc_eqExpr(vc, var_iw48, e_bvor_3);
  Expr e_boolbv_3 = vc_boolToBVExpr(vc, e_eq_69);
  Expr e_simp_6 = vc_simplify(vc, e_boolbv_3);
  Expr e_extract_67 = vc_bvExtract(vc, e_simp_6, 0, 0);
  Expr e_eq_70 = vc_eqExpr(vc, e_extract_67, const_1_1);
  vc_assertFormula(vc, e_eq_70);

  Expr e_bvplus = vc_bvPlusExpr(vc, 32, var_iw48, const_69_32);
  Expr e_sx = vc_bvSignExtend(vc, e_bvplus, 64);
  Expr const_2_64 = vc_bvConstExprFromLL(vc, 64, 2);
  Expr e_sbvmod = vc_sbvModExpr(vc, 64, e_sx, const_2_64);
  Expr e_extract_68 = vc_bvExtract(vc, e_sbvmod, 31, 0);
  Expr e_bvplus_2 = vc_bvPlusExpr(vc, 32, e_extract_68, const_42_32);
  Expr e_eq_71 = vc_eqExpr(vc, var_t343, e_bvplus_2);
  Expr e_boolbv_4 = vc_boolToBVExpr(vc, e_eq_71);
  Expr e_simp_7 = vc_simplify(vc, e_boolbv_4);
  Expr e_extract_69 = vc_bvExtract(vc, e_simp_7, 0, 0);
  Expr e_eq_72 = vc_eqExpr(vc, e_extract_69, const_1_1);
  vc_assertFormula(vc, e_eq_72);

  Expr e_eq_73 = vc_eqExpr(vc, var_t343, const_0_32);
  Expr e_boolbv_5 = vc_boolToBVExpr(vc, e_eq_73);

  Expr e_bvplus_3 = vc_bvPlusExpr(vc, 32, var_iw48, const_68_32);
  Expr e_eq_142 = vc_eqExpr(vc, e_bvplus_3, const_0_32);
  Expr e_boolbv_74 = vc_boolToBVExpr(vc, e_eq_142);

  Expr e_bvand_69 = vc_bvAndExpr(vc, e_boolbv_5, e_boolbv_74);
  Expr e_extract_70 = vc_bvExtract(vc, e_bvand_69, 0, 0);
  Expr e_eq_143 = vc_eqExpr(vc, e_extract_70, const_1_1);
  Expr e_not = vc_notExpr(vc, e_eq_143);
  Expr e_simp_9 = vc_simplify(vc, e_not);
  int ret = vc_query(vc, e_simp_9);
  ASSERT_TRUE(ret);
}

