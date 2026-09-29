/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: September, 2026
 *
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
********************************************************************/

// stp-even-eqn-assert.cpp -- a regression from a client that builds its
// formulas through Bool-to-bit-vector conversions (2.x's vc_boolToBVExpr is
// bool_to_bv1) and simplifies the pieces as it goes: iw48 packs two 16-bit
// halves, t343 = (sign_extend(iw48 + 69) smod 2) + 42, and the query
// "not (t343 = 0 and iw48 + 68 = 0)" is entailed. The calls are the
// client's, in its order. TermManager::simplify re-folds a term through the
// constructors only, where 2.x's vc_simplify ran the solver's simplifier, so
// the four simplified pieces (and with them the assertions and the query)
// are not the terms 2.x handed to the solver; the verdict is the same.

#include "api_common.hpp"

using namespace stp;

namespace
{

TEST(even_eqn_assert, one)
{
  TermManager tm;
  Solver s(tm);
  s.options().set_bool(Option::CHECK_SANITY, true); // every 2.x checker had 'd' on
  // (2.x switched handle deletion off first, vc_setInterfaceFlags with
  // ordinal 0, EXPRDELETE; terms are values, so there is nothing to switch)
  s.push();
  const Sort ty_bv16 = tm.mk_bv_sort(16);
  const Sort ty_bv32 = tm.mk_bv_sort(32);

  const Term var_is4a = tm.declare("is4a", ty_bv16);
  const Term var_is48 = tm.declare("is48", ty_bv16);
  const Term var_iw48 = tm.declare("iw48", ty_bv32);

  const Term var_t343 = tm.declare("t343", ty_bv32);

  const Term const_0_16 = tm.mk_bv(16, 0);
  const Term const_0_32 = tm.mk_bv(32, 0);

  const Term const_1_1 = tm.mk_bv(1, 1);

  const Term const_42_32 = tm.mk_bv(32, 42);
  const Term const_68_32 = tm.mk_bv(32, 68);
  const Term const_69_32 = tm.mk_bv(32, 69);

  const Term e_concat_35 = concat(const_0_16, var_is48);
  const Term e_concat_36 = concat(const_0_16, var_is4a);

  const Term e_concat_52 = concat(e_concat_36, const_0_16);
  const Term e_extract_50 = extract(31, 0, e_concat_52);

  const Term e_simp_5 = tm.simplify(e_extract_50);
  const Term e_bvor_3 = bvor(e_concat_35, e_simp_5);
  const Term e_eq_69 = var_iw48 == e_bvor_3;
  const Term e_boolbv_3 = bool_to_bv1(e_eq_69);
  const Term e_simp_6 = tm.simplify(e_boolbv_3);
  const Term e_extract_67 = extract(0, 0, e_simp_6);
  const Term e_eq_70 = e_extract_67 == const_1_1;
  s.add(e_eq_70);

  const Term e_bvplus = bvadd(var_iw48, const_69_32);
  const Term e_sx = sign_extend(32, e_bvplus); // 2.x: vc_bvSignExtend(e_bvplus, 64), to 64 bits
  const Term const_2_64 = tm.mk_bv(64, 2);
  const Term e_sbvmod = bvsmod(e_sx, const_2_64);
  const Term e_extract_68 = extract(31, 0, e_sbvmod);
  const Term e_bvplus_2 = bvadd(e_extract_68, const_42_32);
  const Term e_eq_71 = var_t343 == e_bvplus_2;
  const Term e_boolbv_4 = bool_to_bv1(e_eq_71);
  const Term e_simp_7 = tm.simplify(e_boolbv_4);
  const Term e_extract_69 = extract(0, 0, e_simp_7);
  const Term e_eq_72 = e_extract_69 == const_1_1;
  s.add(e_eq_72);

  const Term e_eq_73 = var_t343 == const_0_32;
  const Term e_boolbv_5 = bool_to_bv1(e_eq_73);

  const Term e_bvplus_3 = bvadd(var_iw48, const_68_32);
  const Term e_eq_142 = e_bvplus_3 == const_0_32;
  const Term e_boolbv_74 = bool_to_bv1(e_eq_142);

  const Term e_bvand_69 = bvand(e_boolbv_5, e_boolbv_74);
  const Term e_extract_70 = extract(0, 0, e_bvand_69);
  const Term e_eq_143 = e_extract_70 == const_1_1;
  const Term e_not = !e_eq_143;
  const Term e_simp_9 = tm.simplify(e_not);
  const Entailment ret = s.entails(e_simp_9);
  ASSERT_TRUE(ret.is_valid()) << ret;
}

} // namespace
