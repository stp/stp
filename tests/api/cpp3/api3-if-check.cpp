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

// api3-if-check.cpp -- nineteen queries on one solver, each in its own
// push/pop with the path conditions of a branching program asserted first:
// the first eighteen, a branch condition or its negation, are not entailed;
// the nineteenth, 0 < x00000015 under conditions that imply it, is (the
// query where the problem once occurred).

#include "api3_common.hpp"

using namespace stp;

namespace
{

TEST(if_check, one)
{
  TermManager tm;
  Solver s(tm);
  s.options().set_bool(Option::CHECK_SANITY, true); // 2.x flag 'd'

  const Term x00000003 = tm.declare("x00000003", tm.mk_bv_sort(16));
  const Term hex00FF = tm.mk_bv(16, 0x00FF);

  const Term query1 = x00000003 == hex00FF;
  const Term query2 = !query1;

  // 1
  s.push();
  ASSERT_TRUE(s.entails(query1).is_invalid());
  s.pop();

  // 2
  s.push();
  ASSERT_TRUE(s.entails(query2).is_invalid());
  s.pop();
  ////
  const Term x00000005 = tm.declare("x00000005", tm.mk_bv_sort(16));
  const Term query3 = x00000005 == hex00FF;
  const Term query4 = !query3;

  // 3
  s.push();
  s.add(query1);
  ASSERT_TRUE(s.entails(query3).is_invalid());
  s.pop();

  // 4
  s.push();
  s.add(query1);
  ASSERT_TRUE(s.entails(query4).is_invalid());
  s.pop();
  ////
  const Term x00000007 = tm.declare("x00000007", tm.mk_bv_sort(16));
  const Term query5 = x00000007 == hex00FF;
  const Term query6 = !query5;

  // 5

  s.push();
  s.add(query3);
  s.add(query1);
  ASSERT_TRUE(s.entails(query5).is_invalid());
  s.pop();

  // 6
  s.push();
  s.add(query3);
  s.add(query1);
  ASSERT_TRUE(s.entails(query6).is_invalid());
  s.pop();
  ////
  const Term x00000009 = tm.declare("x00000009", tm.mk_bv_sort(32));
  const Term ct_0_32 = tm.mk_bv(32, 0x0);
  const Term query8 = x00000009 == ct_0_32;
  const Term query7 = !query8;

  // 7
  s.push();
  s.add(query5);
  s.add(query3);
  s.add(query1);
  ASSERT_TRUE(s.entails(query7).is_invalid());
  s.pop();

  // 8
  s.push();
  s.add(query5);
  s.add(query3);
  s.add(query1);
  ASSERT_TRUE(s.entails(query8).is_invalid());
  s.pop();
  ////
  const Term x0000000b = tm.declare("x0000000b", tm.mk_bv_sort(32));
  const Term query9 = x0000000b == ct_0_32;
  const Term query10 = !query9;

  // 9
  s.push();
  s.add(query7);
  s.add(query5);
  s.add(query3);
  s.add(query1);
  ASSERT_TRUE(s.entails(query9).is_invalid());
  s.pop();

  // 10
  s.push();
  s.add(query7);
  s.add(query5);
  s.add(query3);
  s.add(query1);
  ASSERT_TRUE(s.entails(query10).is_invalid());
  s.pop();
  ////
  const Term x0000000d = tm.declare("x0000000d", tm.mk_bv_sort(32));
  const Term query11 = x0000000d == ct_0_32;
  const Term query12 = !query11;

  // 11
  s.push();
  s.add(query2);
  ASSERT_TRUE(s.entails(query11).is_invalid());
  s.pop();

  // 12
  s.push();
  s.add(query2);
  ASSERT_TRUE(s.entails(query12).is_invalid());
  s.pop();
  ////
  const Term x00000075 = tm.declare("x00000075", tm.mk_bv_sort(8));
  const Term ct_0_8 = tm.mk_bv(8, 0x0);
  const Term query14 = x00000075 == ct_0_8;
  const Term query13 = !query14;

  // 13
  s.push();
  s.add(query12);
  s.add(query2);
  ASSERT_TRUE(s.entails(query13).is_invalid());
  s.pop();

  // 14
  s.push();
  s.add(query12);
  s.add(query2);
  ASSERT_TRUE(s.entails(query14).is_invalid());
  s.pop();
  ////
  const Term x00000015 = tm.declare("x00000015", tm.mk_bv_sort(32));
  const Term x0000001b = tm.declare("x0000001b", tm.mk_bv_sort(32));
  const Term x00000021 = tm.declare("x00000021", tm.mk_bv_sort(32));
  const Term x00000010 = tm.declare("x00000010", tm.mk_bv_sort(32));
  const Term x00000017 = tm.declare("x00000017", tm.mk_bv_sort(32));
  const Term ct_F_32 = tm.mk_bv(32, 0xFFFFFFFF);
  const Term x1b_sub_x21 = bvsub(x0000001b, x00000021);  // Q1
  const Term Q1_plus_x15 = bvadd(x1b_sub_x21, x00000015); // Q2
  const Term Q2_plus_FF = bvadd(Q1_plus_x15, ct_F_32);    // Q3
  const Term Q3_div_x15 = bvudiv(Q2_plus_FF, x00000015);  // T1
  const Term x10_sub_x17 = bvsub(x00000010, x00000017);  // Q4
  const Term Q4_div_x15 = bvudiv(x10_sub_x17, x00000015); // T2
  const Term query15 = bvsgt(Q3_div_x15, Q4_div_x15);
  const Term query16 = !query15;

  // 15
  s.push();
  const Term query15_0 = x00000015 == ct_0_32;
  const Term query15_1 = !query15_0;
  s.add(query15_1);
  s.add(query13);
  s.add(query12);
  s.add(query2);
  ASSERT_TRUE(s.entails(query15).is_invalid());
  s.pop();

  // 16
  s.push();
  s.add(query13);
  s.add(query12);
  s.add(query2);
  ASSERT_TRUE(s.entails(query16).is_invalid());
  s.pop();
  ////
  const Term x00000032 = tm.declare("x00000032", tm.mk_bv_sort(32));
  const Term x00000038 = tm.declare("x00000038", tm.mk_bv_sort(32));
  const Term x00000028 = tm.declare("x00000028", tm.mk_bv_sort(32));
  const Term x0000002e = tm.declare("x0000002e", tm.mk_bv_sort(32));
  const Term x32_sub_x38 = bvsub(x00000032, x00000038);  // A1
  const Term A1_plus_x15 = bvadd(x32_sub_x38, x00000015); // A2
  const Term A2_plus_FF = bvadd(A1_plus_x15, ct_F_32);    // A3
  const Term A3_div_x15 = bvudiv(A2_plus_FF, x00000015);  // A4
  const Term x28_sub_x2e = bvsub(x00000028, x0000002e);  // A5
  const Term A5_div_x15 = bvudiv(x28_sub_x2e, x00000015); // A6
  const Term A4_sub_A6 = bvsub(A3_div_x15, A5_div_x15);   // A7
  const Term query17 = bvsgt(A4_sub_A6, ct_0_32);
  const Term query18 = !query17;

  // 17
  s.push();
  s.add(query15);
  s.add(query13);
  s.add(query12);
  s.add(query2);
  ASSERT_TRUE(s.entails(query17).is_invalid());
  s.pop();

  // 18
  s.push();
  s.add(query15);
  s.add(query13);
  s.add(query12);
  s.add(query2);
  ASSERT_TRUE(s.entails(query18).is_invalid());
  s.pop();
  ////
  const Term query19 = bvult(ct_0_32, x00000015);

  // 19 : Problem occurs here.
  s.push();
  s.add(query17);
  s.add(query15);
  s.add(query13);
  s.add(query12);
  s.add(query2);
  const Entailment query_result = s.entails(query19);
  ASSERT_TRUE(query_result.is_valid()) << query_result;
  s.pop();
}

} // namespace
