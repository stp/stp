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


// api3-b4-c.cpp -- a regression recorded from a client's C API calls: a
// transition-relation formula over a one-hot 5-bit location (at), 8-bit
// variables k, x, lambda and y, and their underscored next-state copies
// (_at, _k, ...), with shifts by a variable amount spelled out as
// if-then-else barrel shifters, asserted as one formula whose satisfiability
// is checked. The body is generated from the 2.x recording and builds the
// same formula in the same order: eN is the 2.x term of that number, a
// declared symbol is named after itself (with a leading underscore moved to
// the end: _at is at_), and 2.x's handle copies (Expr eB = eA) are folded
// into their source.

#include "api3_common.hpp"

#include <cstdint>

using namespace stp;

namespace
{

// Three 2.x constructors whose formulas have no one-call spelling here, built
// exactly as 2.x built them (the formula is the regression).

// vc_bvBoolExtract(e, i): (= ((_ extract i i) e) #b0), true when bit i of e
// is *zero* -- unlike bit(e, i), which is true when the bit is one.
Term bit_is_zero(const Term& e, std::uint32_t i)
{
  return extract(i, i, e) == e.manager().mk_bv(1, 0);
}

// vc_bvRightShiftExpr(k, e): e shifted right by the constant k as k zero bits
// followed by e's top bits; zero once k reaches the width.
Term shift_right(const Term& e, std::uint32_t k)
{
  const std::uint32_t w = e.sort().bv_size();
  if (k == 0)
    return e;
  if (k < w)
    return concat(e.manager().mk_bv_zero(k), extract(w - 1, k, e));
  return e.manager().mk_bv_zero(w);
}

// vc_bvLeftShiftExpr(k, e): e followed by k zero bits, so k bits *wider* than e.
Term shift_left_widening(const Term& e, std::uint32_t k)
{
  if (k == 0)
    return e;
  return concat(e, e.manager().mk_bv_zero(k));
}

TEST(b4_c, one)
{
  TermManager tm;
  Solver s(tm);
  s.options().set_bool(Option::CHECK_SANITY, true); // 2.x flag 'd'

  const Term at = tm.declare("at", tm.mk_bv_sort(5));
  const Term e12868 = tm.mk_bv(5, 0b10000);
  const Term e12869 = at == e12868;
  const Term x = tm.declare("x", tm.mk_bv_sort(8));
  const Term e12872 = tm.mk_bv(8, 0b00000000);
  const Term e12873 = bvsgt(x, e12872);
  const Term e12874 = e12869 && e12873;
  const Term lambda = tm.declare("lambda", tm.mk_bv_sort(8));
  const Term e12878 = ite(bit_is_zero(lambda, 0), shift_right(x, 1), x);
  const Term e12879 = ite(bit_is_zero(lambda, 1), shift_right(e12878, 2), e12878);
  const Term e12880 = ite(bit_is_zero(lambda, 2), shift_right(e12879, 4), e12879);
  const Term e12881 = tm.mk_bv(8, 0b00000001);
  const Term e12882 = e12880 == e12881;
  const Term e12883 = implies(e12874, e12882);
  const Term e12885 = bit(at, 0);
  const Term k = tm.declare("k", tm.mk_bv_sort(8));
  const Term e12888 = bit(k, 7);
  const Term e12889 = !e12888;
  const Term e12891 = bit(at, 4);
  const Term e12892 = e12889 || e12891;
  const Term e12893 = e12885 || e12892;
  const Term e12894 = tm.mk_true();
  const Term e12895 = e12893 && e12894;
  const Term e12896 = e12883 && e12895;
  const Term e12898 = tm.mk_bv(5, 0b00001);
  const Term e12899 = at == e12898;
  const Term e12901 = tm.mk_bv(8, 0b00000000);
  const Term e12902 = bvsge(k, e12901);
  const Term e12903 = e12899 && e12902;
  const Term at_ = tm.declare("_at", tm.mk_bv_sort(5));
  const Term e12906 = tm.mk_bv(5, 0b00010);
  const Term e12907 = at_ == e12906;
  const Term lambda_ = tm.declare("_lambda", tm.mk_bv_sort(8));
  const Term e12911 = lambda_ == lambda;
  const Term e12912 = e12907 && e12911;
  const Term x_ = tm.declare("_x", tm.mk_bv_sort(8));
  const Term e12916 = x_ == x;
  const Term e12917 = e12912 && e12916;
  const Term y_ = tm.declare("_y", tm.mk_bv_sort(8));
  const Term y = tm.declare("y", tm.mk_bv_sort(8));
  const Term e12922 = y_ == y;
  const Term e12923 = e12917 && e12922;
  const Term k_ = tm.declare("_k", tm.mk_bv_sort(8));
  const Term e12927 = k_ == k;
  const Term e12928 = e12923 && e12927;
  const Term e12929 = e12903 && e12928;
  const Term e12931 = tm.mk_bv(5, 0b00001);
  const Term e12932 = at == e12931;
  const Term e12934 = tm.mk_bv(8, 0b00000000);
  const Term e12935 = bvsge(k, e12934);
  const Term e12936 = !e12935;
  const Term e12937 = e12932 && e12936;
  const Term e12939 = tm.mk_bv(5, 0b10000);
  const Term e12940 = at_ == e12939;
  const Term e12943 = lambda_ == lambda;
  const Term e12944 = e12940 && e12943;
  const Term e12947 = x_ == x;
  const Term e12948 = e12944 && e12947;
  const Term e12951 = y_ == y;
  const Term e12952 = e12948 && e12951;
  const Term e12955 = k_ == k;
  const Term e12956 = e12952 && e12955;
  const Term e12957 = e12937 && e12956;
  const Term e12958 = e12929 || e12957;
  const Term e12960 = tm.mk_bv(5, 0b00010);
  const Term e12961 = at == e12960;
  const Term e12964 = shift_left_widening(k, 3);
  const Term e12965 = tm.mk_bv(24, 0b111100001100110010101010);
  const Term e12966 = ite(bit_is_zero(e12964, 0), shift_right(e12965, 1), e12965);
  const Term e12967 = ite(bit_is_zero(e12964, 1), shift_right(e12966, 2), e12966);
  const Term e12968 = ite(bit_is_zero(e12964, 2), shift_right(e12967, 4), e12967);
  const Term e12969 = ite(bit_is_zero(e12964, 3), shift_right(e12968, 8), e12968);
  const Term e12970 = extract(7, 0, e12969);
  const Term e12971 = bvand(y, e12970);
  const Term e12972 = tm.mk_bv(8, 0b00000000);
  const Term e12973 = e12971 == e12972;
  const Term e12974 = !e12973;
  const Term e12975 = e12961 && e12974;
  const Term e12977 = tm.mk_bv(5, 0b00100);
  const Term e12978 = at_ == e12977;
  const Term e12981 = lambda_ == lambda;
  const Term e12982 = e12978 && e12981;
  const Term e12985 = x_ == x;
  const Term e12986 = e12982 && e12985;
  const Term e12989 = y_ == y;
  const Term e12990 = e12986 && e12989;
  const Term e12993 = k_ == k;
  const Term e12994 = e12990 && e12993;
  const Term e12995 = e12975 && e12994;
  const Term e12996 = e12958 || e12995;
  const Term e12998 = tm.mk_bv(5, 0b00010);
  const Term e12999 = at == e12998;
  const Term e13002 = shift_left_widening(k, 3);
  const Term e13003 = tm.mk_bv(24, 0b111100001100110010101010);
  const Term e13004 = ite(bit_is_zero(e13002, 0), shift_right(e13003, 1), e13003);
  const Term e13005 = ite(bit_is_zero(e13002, 1), shift_right(e13004, 2), e13004);
  const Term e13006 = ite(bit_is_zero(e13002, 2), shift_right(e13005, 4), e13005);
  const Term e13007 = ite(bit_is_zero(e13002, 3), shift_right(e13006, 8), e13006);
  const Term e13008 = extract(7, 0, e13007);
  const Term e13009 = bvand(y, e13008);
  const Term e13010 = tm.mk_bv(8, 0b00000000);
  const Term e13011 = e13009 == e13010;
  const Term e13012 = e12999 && e13011;
  const Term e13014 = tm.mk_bv(5, 0b01000);
  const Term e13015 = at_ == e13014;
  const Term e13018 = lambda_ == lambda;
  const Term e13019 = e13015 && e13018;
  const Term e13022 = x_ == x;
  const Term e13023 = e13019 && e13022;
  const Term e13026 = y_ == y;
  const Term e13027 = e13023 && e13026;
  const Term e13030 = k_ == k;
  const Term e13031 = e13027 && e13030;
  const Term e13032 = e13012 && e13031;
  const Term e13033 = e12996 || e13032;
  const Term e13035 = tm.mk_bv(5, 0b00100);
  const Term e13036 = at == e13035;
  const Term e13040 = tm.mk_bv(8, 0b00000001);
  const Term e13041 = ite(bit_is_zero(k, 0), extract(8, 1, shift_left_widening(e13040, 1)), e13040);
  const Term e13042 = ite(bit_is_zero(k, 1), extract(9, 2, shift_left_widening(e13041, 2)), e13041);
  const Term e13043 =
      ite(bit_is_zero(k, 2), extract(11, 4, shift_left_widening(e13042, 4)), e13042);
  const Term e13044 = bvadd(lambda, e13043);
  const Term e13045 = lambda_ == e13044;
  const Term e13048 = tm.mk_bv(8, 0b00000001);
  const Term e13049 = ite(bit_is_zero(k, 0), extract(8, 1, shift_left_widening(e13048, 1)), e13048);
  const Term e13050 = ite(bit_is_zero(k, 1), extract(9, 2, shift_left_widening(e13049, 2)), e13049);
  const Term e13051 =
      ite(bit_is_zero(k, 2), extract(11, 4, shift_left_widening(e13050, 4)), e13050);
  const Term e13053 = ite(bit_is_zero(e13051, 0), shift_right(y, 1), y);
  const Term e13054 = ite(bit_is_zero(e13051, 1), shift_right(e13053, 2), e13053);
  const Term e13055 = ite(bit_is_zero(e13051, 2), shift_right(e13054, 4), e13054);
  const Term e13056 = y_ == e13055;
  const Term e13057 = e13045 && e13056;
  const Term e13059 = tm.mk_bv(5, 0b01000);
  const Term e13060 = at_ == e13059;
  const Term e13061 = e13057 && e13060;
  const Term e13064 = x_ == x;
  const Term e13065 = e13061 && e13064;
  const Term e13068 = k_ == k;
  const Term e13069 = e13065 && e13068;
  const Term e13070 = e13036 && e13069;
  const Term e13071 = e13033 || e13070;
  const Term e13073 = tm.mk_bv(5, 0b01000);
  const Term e13074 = at == e13073;
  const Term e13077 = tm.mk_bv(8, 0b00000001);
  const Term e13078 = bvsub(k, e13077);
  const Term e13079 = k_ == e13078;
  const Term e13081 = tm.mk_bv(5, 0b00001);
  const Term e13082 = at_ == e13081;
  const Term e13083 = e13079 && e13082;
  const Term e13086 = lambda_ == lambda;
  const Term e13087 = e13083 && e13086;
  const Term e13090 = x_ == x;
  const Term e13091 = e13087 && e13090;
  const Term e13094 = y_ == y;
  const Term e13095 = e13091 && e13094;
  const Term e13096 = e13074 && e13095;
  const Term e13097 = e13071 || e13096;
  const Term e13099 = tm.mk_bv(5, 0b10000);
  const Term e13100 = at == e13099;
  const Term e13103 = at_ == at;
  const Term e13106 = lambda_ == lambda;
  const Term e13107 = e13103 && e13106;
  const Term e13110 = x_ == x;
  const Term e13111 = e13107 && e13110;
  const Term e13114 = y_ == y;
  const Term e13115 = e13111 && e13114;
  const Term e13118 = k_ == k;
  const Term e13119 = e13115 && e13118;
  const Term e13120 = e13100 && e13119;
  const Term e13121 = e13097 || e13120;
  const Term e13122 = e12896 && e13121;
  const Term e13124 = bit(k, 7);
  const Term e13125 = !e13124;
  const Term e13127 = bit(k_, 7);
  const Term e13128 = !e13127;
  const Term e13129 = !e13128;
  const Term e13130 = e13125 && e13129;
  const Term e13131 = e13122 && e13130;
  s.add(e13131);

  // 2.x: vc_query(false) == 0, i.e. the assertion is satisfiable
  const Result ret = s.check_sat();
  ASSERT_TRUE(ret.is_sat()) << ret;
}

} // namespace
