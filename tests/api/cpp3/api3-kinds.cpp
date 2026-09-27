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

// api3-kinds.cpp -- every one of the 102 kinds: built through mk_term and
// through its named constructor, viewed under a non-simplifying manager
// (kind, children, indices, sort, and the children()/mk_term round trip),
// evaluated on values through a model, and refused with the right code when
// mis-sorted, mis-counted, mis-indexed or unsupported.
//
// Where kind() reports a lowered form even under simplify = false the
// expectation is marked "lowered:" (FINDINGS.md, design points).

#include "api3_common.hpp"

#include <functional>
#include <vector>

using namespace stp;

namespace
{

// ---------------------------------------------------------------- the view

class Kinds : public ::testing::Test
{
protected:
  TermManager tm = api3::raw_manager();
  Sort B = tm.mk_bool_sort();
  Sort bv1 = tm.mk_bv_sort(1), bv4 = tm.mk_bv_sort(4), bv8 = tm.mk_bv_sort(8);
  Sort bv12 = tm.mk_bv_sort(12), bv16 = tm.mk_bv_sort(16), bv23 = tm.mk_bv_sort(23);
  Sort bv24 = tm.mk_bv_sort(24), bv32 = tm.mk_bv_sort(32);
  Sort f32 = tm.mk_fp32_sort(), f64 = tm.mk_fp64_sort();
  Sort RM = tm.mk_rm_sort(), R = tm.mk_real_sort();
  Sort A = tm.mk_array_sort(bv8, bv8);
  Sort S = tm.declare_sort("S");
  Sort FS = tm.mk_fun_sort({bv8, bv8}, bv8);
  Term x = tm.declare("x", bv8), y = tm.declare("y", bv8), z = tm.declare("z", bv8);
  Term a = tm.declare("a", B), b = tm.declare("b", B);
  Term fx = tm.declare("fx", f32), fy = tm.declare("fy", f32), fz = tm.declare("fz", f32);
  Term dx = tm.declare("dx", f64);
  Term rx = tm.declare("rx", R), ry = tm.declare("ry", R);
  Term rm = tm.declare("rm", RM), rm2 = tm.declare("rm2", RM);
  Term ar = tm.declare("ar", A), ar2 = tm.declare("ar2", A);
  Term p = tm.declare("p", S), q = tm.declare("q", S);
  Term f = tm.declare("f", FS);
  Term b32 = tm.declare("b32", bv32);

  // The named constructor's result must be the node mk_term builds from
  // the same arguments: both doors lead to one term.
  Term both(const Term& named, Kind k, const std::vector<Term>& args,
            const std::vector<std::uint32_t>& idx = {},
            std::optional<Sort> result_sort = std::nullopt)
  {
    const Term generic = tm.mk_term(k, args, idx, result_sort);
    EXPECT_TRUE(generic.same_as(named)) << named << " vs " << generic;
    return named;
  }

  // kind, children, indices, sort; and the rebuild from the view.
  void view(const Term& t, Kind k, std::size_t n, const std::vector<std::uint32_t>& idx,
            const Sort& sort)
  {
    EXPECT_EQ(t.kind(), k) << t;
    EXPECT_EQ(t.num_children(), n) << t;
    EXPECT_EQ(t.children().size(), n) << t;
    EXPECT_EQ(t.indices(), idx) << t;
    EXPECT_TRUE(t.sort() == sort) << t << " has sort " << t.sort();
    if (k == Kind::VALUE || k == Kind::CONSTANT)
      return;
    const Term rebuilt = tm.mk_term(t.kind(), t.children(), t.indices(), t.sort());
    EXPECT_TRUE(rebuilt.same_as(t)) << t << " rebuilt as " << rebuilt;
    for (std::size_t i = 0; i < n; ++i)
      EXPECT_TRUE(t.child(i).same_as(t.children()[i]));
  }
};

TEST_F(Kinds, values_and_constants)
{
  view(tm.mk_bv(8, 5), Kind::VALUE, 0, {}, bv8);
  view(tm.mk_true(), Kind::VALUE, 0, {}, B);
  view(tm.mk_fp(f32, RoundingMode::RNE, 1.0), Kind::VALUE, 0, {}, f32);
  view(tm.mk_rm(RoundingMode::RTZ), Kind::VALUE, 0, {}, RM);
  view(tm.mk_real(1, 2), Kind::VALUE, 0, {}, R);
  view(x, Kind::CONSTANT, 0, {}, bv8);
  view(f, Kind::CONSTANT, 0, {}, FS);
  view(p, Kind::CONSTANT, 0, {}, S);
  EXPECT_TRUE(x.is_const());
  EXPECT_FALSE(x.is_value());
  EXPECT_TRUE(tm.mk_bv(8, 5).is_value());
  EXPECT_FALSE(tm.mk_bv(8, 5).is_const());
  API3_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.mk_term(Kind::VALUE, {}));
  API3_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.mk_term(Kind::CONSTANT, {}));
}

TEST_F(Kinds, core)
{
  view(both(ite(a, x, y), Kind::ITE, {a, x, y}), Kind::ITE, 3, {}, bv8);
  view(ite(a, a, b), Kind::ITE, 3, {}, B);
  view(ite(a, fx, fy), Kind::ITE, 3, {}, f32);
  view(ite(a, rx, ry), Kind::ITE, 3, {}, R);
  view(ite(a, ar, ar2), Kind::ITE, 3, {}, A);
  view(ite(a, p, q), Kind::ITE, 3, {}, S);
  view(ite(a, rm, rm2), Kind::ITE, 3, {}, RM);

  view(both(eq(x, y), Kind::EQUAL, {x, y}), Kind::EQUAL, 2, {}, B);
  view(eq(a, b), Kind::EQUAL, 2, {}, B);
  view(eq(fx, fy), Kind::EQUAL, 2, {}, B);
  view(eq(rx, ry), Kind::EQUAL, 2, {}, B);
  view(eq(ar, ar2), Kind::EQUAL, 2, {}, B);
  view(eq(p, q), Kind::EQUAL, 2, {}, B);
  view(eq(rm, rm2), Kind::EQUAL, 2, {}, B);
  EXPECT_TRUE((x == y).same_as(eq(x, y)));

  view(both(distinct({x, y, z}), Kind::DISTINCT, {x, y, z}), Kind::DISTINCT, 3, {}, B);
  view(distinct(a, b), Kind::DISTINCT, 2, {}, B);
  view(distinct(rm, rm2), Kind::DISTINCT, 2, {}, B);
  view(distinct(p, q), Kind::DISTINCT, 2, {}, B);
  EXPECT_TRUE((x != y).same_as(distinct(x, y)));
  // lowered: sorts whose equality is not the carrier's become not(=) or a
  // conjunction of those
  view(distinct(fx, fy), Kind::NOT, 1, {}, B);
  view(distinct({fx, fy, fz}), Kind::AND, 3, {}, B);
  view(distinct(rx, ry), Kind::NOT, 1, {}, B);
  view(distinct(ar, ar2), Kind::NOT, 1, {}, B);

  view(both(f(x, y), Kind::APPLY, {f, x, y}), Kind::APPLY, 3, {}, bv8);
  EXPECT_TRUE(apply({f, x, y}).same_as(f(x, y)));
  EXPECT_TRUE(f({x, y}).same_as(f(x, y)));
  EXPECT_TRUE(f(std::vector<Term>{x, y}).same_as(f(x, y)));
  EXPECT_TRUE(f(x, y).child(0).same_as(f));
}

TEST_F(Kinds, boolean)
{
  view(both(not_(a), Kind::NOT, {a}), Kind::NOT, 1, {}, B);
  EXPECT_TRUE((!a).same_as(not_(a)));
  view(both(and_(a, b), Kind::AND, {a, b}), Kind::AND, 2, {}, B);
  view(both(and_({a, b, a}), Kind::AND, {a, b, a}), Kind::AND, 3, {}, B);
  view(and_(std::vector<Term>{a, b}), Kind::AND, 2, {}, B);
  EXPECT_TRUE((a && b).same_as(and_(a, b)));
  // lowered: a one-argument and/or is the argument
  EXPECT_TRUE(and_(a).same_as(a));
  EXPECT_TRUE(or_(b).same_as(b));
  view(both(or_(a, b), Kind::OR, {a, b}), Kind::OR, 2, {}, B);
  view(or_({a, b, a}), Kind::OR, 3, {}, B);
  EXPECT_TRUE((a || b).same_as(or_(a, b)));
  view(both(xor_(a, b), Kind::XOR, {a, b}), Kind::XOR, 2, {}, B);
  view(xor_({a, b, a}), Kind::XOR, 3, {}, B);
  view(both(implies(a, b), Kind::IMPLIES, {a, b}), Kind::IMPLIES, 2, {}, B);
}

TEST_F(Kinds, bitwise)
{
  view(both(bvnot(x), Kind::BV_NOT, {x}), Kind::BV_NOT, 1, {}, bv8);
  EXPECT_TRUE((~x).same_as(bvnot(x)));
  view(both(bvand(x, y), Kind::BV_AND, {x, y}), Kind::BV_AND, 2, {}, bv8);
  view(bvand({x, y, z}), Kind::BV_AND, 3, {}, bv8);
  EXPECT_TRUE((x & y).same_as(bvand(x, y)));
  view(both(bvor(x, y), Kind::BV_OR, {x, y}), Kind::BV_OR, 2, {}, bv8);
  view(bvor({x, y, z}), Kind::BV_OR, 3, {}, bv8);
  EXPECT_TRUE((x | y).same_as(bvor(x, y)));
  view(both(bvxor(x, y), Kind::BV_XOR, {x, y}), Kind::BV_XOR, 2, {}, bv8);
  view(bvxor({x, y, z}), Kind::BV_XOR, 3, {}, bv8);
  EXPECT_TRUE((x ^ y).same_as(bvxor(x, y)));
  // lowered: nand/nor/xnor are bvnot over the bitwise op
  view(both(bvnand(x, y), Kind::BV_NAND, {x, y}), Kind::BV_NOT, 1, {}, bv8);
  EXPECT_EQ(bvnand(x, y).child(0).kind(), Kind::BV_AND);
  view(both(bvnor(x, y), Kind::BV_NOR, {x, y}), Kind::BV_NOT, 1, {}, bv8);
  EXPECT_EQ(bvnor(x, y).child(0).kind(), Kind::BV_OR);
  view(both(bvxnor(x, y), Kind::BV_XNOR, {x, y}), Kind::BV_NOT, 1, {}, bv8);
  EXPECT_EQ(bvxnor(x, y).child(0).kind(), Kind::BV_XOR);
}

TEST_F(Kinds, arithmetic)
{
  view(both(bvneg(x), Kind::BV_NEG, {x}), Kind::BV_NEG, 1, {}, bv8);
  EXPECT_TRUE((-x).same_as(bvneg(x)));
  view(both(bvadd(x, y), Kind::BV_ADD, {x, y}), Kind::BV_ADD, 2, {}, bv8);
  view(bvadd({x, y, z}), Kind::BV_ADD, 3, {}, bv8);
  EXPECT_TRUE((x + y).same_as(bvadd(x, y)));
  view(both(bvsub(x, y), Kind::BV_SUB, {x, y}), Kind::BV_SUB, 2, {}, bv8);
  EXPECT_TRUE((x - y).same_as(bvsub(x, y)));
  view(both(bvmul(x, y), Kind::BV_MUL, {x, y}), Kind::BV_MUL, 2, {}, bv8);
  view(bvmul({x, y, z}), Kind::BV_MUL, 3, {}, bv8);
  EXPECT_TRUE((x * y).same_as(bvmul(x, y)));
  view(both(bvudiv(x, y), Kind::BV_UDIV, {x, y}), Kind::BV_UDIV, 2, {}, bv8);
  view(both(bvurem(x, y), Kind::BV_UREM, {x, y}), Kind::BV_UREM, 2, {}, bv8);
  view(both(bvsdiv(x, y), Kind::BV_SDIV, {x, y}), Kind::BV_SDIV, 2, {}, bv8);
  view(both(bvsrem(x, y), Kind::BV_SREM, {x, y}), Kind::BV_SREM, 2, {}, bv8);
  view(both(bvsmod(x, y), Kind::BV_SMOD, {x, y}), Kind::BV_SMOD, 2, {}, bv8);
  view(both(bvshl(x, y), Kind::BV_SHL, {x, y}), Kind::BV_SHL, 2, {}, bv8);
  EXPECT_TRUE((x << y).same_as(bvshl(x, y)));
  view(both(bvlshr(x, y), Kind::BV_LSHR, {x, y}), Kind::BV_LSHR, 2, {}, bv8);
  view(both(bvashr(x, y), Kind::BV_ASHR, {x, y}), Kind::BV_ASHR, 2, {}, bv8);
}

TEST_F(Kinds, structure)
{
  view(both(concat(x, y), Kind::BV_CONCAT, {x, y}), Kind::BV_CONCAT, 2, {}, bv16);
  // lowered: an n-ary concat is a chain of binary ones
  view(concat({x, y, z}), Kind::BV_CONCAT, 2, {}, bv24);
  EXPECT_EQ(concat({x, y, z}).child(0).kind(), Kind::BV_CONCAT);
  view(both(extract(3, 0, x), Kind::BV_EXTRACT, {x}, {3, 0}), Kind::BV_EXTRACT, 1, {3, 0}, bv4);
  view(extract(7, 7, x), Kind::BV_EXTRACT, 1, {7, 7}, bv1);
  view(both(zero_extend(4, x), Kind::BV_ZERO_EXTEND, {x}, {4}), Kind::BV_ZERO_EXTEND, 1, {4},
       bv12);
  view(both(sign_extend(4, x), Kind::BV_SIGN_EXTEND, {x}, {4}), Kind::BV_SIGN_EXTEND, 1, {4},
       bv12);
  // lowered: extending by 0 is the operand
  EXPECT_TRUE(zero_extend(0, x).same_as(x));
  EXPECT_TRUE(sign_extend(0, x).same_as(x));
  // lowered: repeat and the rotations become concats of extracts
  view(both(repeat(2, x), Kind::BV_REPEAT, {x}, {2}), Kind::BV_CONCAT, 2, {}, bv16);
  EXPECT_TRUE(repeat(1, x).same_as(x));
  EXPECT_EQ(repeat(3, x).sort().bv_size(), 24u);
  view(both(rotate_left(3, x), Kind::BV_ROTATE_LEFT, {x}, {3}), Kind::BV_CONCAT, 2, {}, bv8);
  view(both(rotate_right(3, x), Kind::BV_ROTATE_RIGHT, {x}, {3}), Kind::BV_CONCAT, 2, {}, bv8);
  EXPECT_TRUE(rotate_left(8, x).same_as(x));
  EXPECT_TRUE(rotate_right(16, x).same_as(x));
  EXPECT_TRUE(rotate_left(11, x).same_as(rotate_left(3, x)));
  EXPECT_TRUE(rotate_right(3, x).same_as(rotate_left(5, x)));
}

TEST_F(Kinds, comparison)
{
  // lowered: bvcomp is ite(=, #b1, #b0)
  view(both(bvcomp(x, y), Kind::BV_COMP, {x, y}), Kind::ITE, 3, {}, bv1);
  view(both(bvult(x, y), Kind::BV_ULT, {x, y}), Kind::BV_ULT, 2, {}, B);
  view(both(bvule(x, y), Kind::BV_ULE, {x, y}), Kind::BV_ULE, 2, {}, B);
  view(both(bvugt(x, y), Kind::BV_UGT, {x, y}), Kind::BV_UGT, 2, {}, B);
  view(both(bvuge(x, y), Kind::BV_UGE, {x, y}), Kind::BV_UGE, 2, {}, B);
  view(both(bvslt(x, y), Kind::BV_SLT, {x, y}), Kind::BV_SLT, 2, {}, B);
  view(both(bvsle(x, y), Kind::BV_SLE, {x, y}), Kind::BV_SLE, 2, {}, B);
  view(both(bvsgt(x, y), Kind::BV_SGT, {x, y}), Kind::BV_SGT, 2, {}, B);
  view(both(bvsge(x, y), Kind::BV_SGE, {x, y}), Kind::BV_SGE, 2, {}, B);
  view(both(bvuaddo(x, y), Kind::BV_UADDO, {x, y}), Kind::BV_UADDO, 2, {}, B);
  view(both(bvsaddo(x, y), Kind::BV_SADDO, {x, y}), Kind::BV_SADDO, 2, {}, B);
  view(both(bvumulo(x, y), Kind::BV_UMULO, {x, y}), Kind::BV_UMULO, 2, {}, B);
  view(both(bvsmulo(x, y), Kind::BV_SMULO, {x, y}), Kind::BV_SMULO, 2, {}, B);
  view(both(bvusubo(x, y), Kind::BV_USUBO, {x, y}), Kind::BV_USUBO, 2, {}, B);
  view(both(bvssubo(x, y), Kind::BV_SSUBO, {x, y}), Kind::BV_SSUBO, 2, {}, B);
  // lowered: nego is (= x min_signed), sdivo is (and (= x min) (= y -1))
  view(both(bvnego(x), Kind::BV_NEGO, {x}), Kind::EQUAL, 2, {}, B);
  view(both(bvsdivo(x, y), Kind::BV_SDIVO, {x, y}), Kind::AND, 2, {}, B);
  // lowered: the reductions are ites over an equality with all ones / zero
  view(both(bvredand(x), Kind::BV_REDAND, {x}), Kind::ITE, 3, {}, bv1);
  view(both(bvredor(x), Kind::BV_REDOR, {x}), Kind::ITE, 3, {}, bv1);
}

TEST_F(Kinds, arrays)
{
  view(both(select(ar, x), Kind::SELECT, {ar, x}), Kind::SELECT, 2, {}, bv8);
  EXPECT_TRUE(ar[x].same_as(select(ar, x)));
  view(both(store(ar, x, y), Kind::STORE, {ar, x, y}), Kind::STORE, 3, {}, A);
  const Term k = tm.mk_const_array(A, tm.mk_bv(8, 9));
  view(both(k, Kind::CONST_ARRAY, {tm.mk_bv(8, 9)}, {}, A), Kind::CONST_ARRAY, 1, {}, A);
  EXPECT_TRUE(k.child(0).same_as(tm.mk_bv(8, 9)));
  EXPECT_FALSE(k.is_const());
  EXPECT_FALSE(k.symbol().has_value());
  // a read of a constant array folds to its default; one through a store stays a read
  EXPECT_TRUE(select(k, x).same_as(tm.mk_bv(8, 9)));
  view(select(store(k, x, y), z), Kind::SELECT, 2, {}, bv8);
  EXPECT_TRUE(select(k, z).same_as(tm.mk_bv(8, 9))); // a read of the constant array itself folds
  // array-sorted ites and stores keep their sort
  view(store(ite(a, ar, ar2), x, y), Kind::STORE, 3, {}, A);
  const Sort AF = tm.mk_array_sort(f32, f32);
  const Term af = tm.declare("af", AF);
  view(select(af, fx), Kind::SELECT, 2, {}, f32);
  view(store(af, fx, fy), Kind::STORE, 3, {}, AF);
  const Term kf = tm.mk_const_array(AF, fx);
  view(kf, Kind::CONST_ARRAY, 1, {}, AF);
  EXPECT_TRUE(select(kf, fy).same_as(fx));
}

TEST_F(Kinds, floating_point_arithmetic)
{
  view(both(fp_abs(fx), Kind::FP_ABS, {fx}), Kind::FP_ABS, 1, {}, f32);
  view(both(fp_neg(fx), Kind::FP_NEG, {fx}), Kind::FP_NEG, 1, {}, f32);
  EXPECT_TRUE((-fx).same_as(fp_neg(fx)));
  view(both(fp_add(rm, fx, fy), Kind::FP_ADD, {rm, fx, fy}), Kind::FP_ADD, 3, {}, f32);
  view(both(fp_sub(rm, fx, fy), Kind::FP_SUB, {rm, fx, fy}), Kind::FP_SUB, 3, {}, f32);
  view(both(fp_mul(rm, fx, fy), Kind::FP_MUL, {rm, fx, fy}), Kind::FP_MUL, 3, {}, f32);
  view(both(fp_div(rm, fx, fy), Kind::FP_DIV, {rm, fx, fy}), Kind::FP_DIV, 3, {}, f32);
  view(both(fp_fma(rm, fx, fy, fz), Kind::FP_FMA, {rm, fx, fy, fz}), Kind::FP_FMA, 4, {}, f32);
  view(both(fp_sqrt(rm, fx), Kind::FP_SQRT, {rm, fx}), Kind::FP_SQRT, 2, {}, f32);
  view(both(fp_rem(fx, fy), Kind::FP_REM, {fx, fy}), Kind::FP_REM, 2, {}, f32);
  view(both(fp_rti(rm, fx), Kind::FP_RTI, {rm, fx}), Kind::FP_RTI, 2, {}, f32);
  view(both(fp_min(fx, fy), Kind::FP_MIN, {fx, fy}), Kind::FP_MIN, 2, {}, f32);
  view(both(fp_max(fx, fy), Kind::FP_MAX, {fx, fy}), Kind::FP_MAX, 2, {}, f32);
  // the RoundingMode overloads and the operators use a mode value
  EXPECT_TRUE(fp_add(RoundingMode::RTZ, fx, fy).child(0).same_as(tm.mk_rm(RoundingMode::RTZ)));
  EXPECT_TRUE((fx + fy).same_as(fp_add(RoundingMode::RNE, fx, fy)));
  EXPECT_TRUE((fx - fy).same_as(fp_sub(RoundingMode::RNE, fx, fy)));
  EXPECT_TRUE((fx * fy).same_as(fp_mul(RoundingMode::RNE, fx, fy)));
  EXPECT_TRUE((fx / fy).same_as(fp_div(RoundingMode::RNE, fx, fy)));
  tm.set_default_rounding_mode(RoundingMode::RTP);
  EXPECT_TRUE((fx + fy).same_as(fp_add(RoundingMode::RTP, fx, fy)));
  EXPECT_TRUE(fp_sqrt(RoundingMode::RNA, fx).child(0).same_as(tm.mk_rm(RoundingMode::RNA)));
  EXPECT_TRUE(fp_rti(RoundingMode::RTN, fx).child(0).same_as(tm.mk_rm(RoundingMode::RTN)));
  EXPECT_TRUE(fp_fma(RoundingMode::RTZ, fx, fy, fz).child(0).same_as(tm.mk_rm(RoundingMode::RTZ)));
}

TEST_F(Kinds, floating_point_predicates)
{
  view(both(fp_eq(fx, fy), Kind::FP_EQ, {fx, fy}), Kind::FP_EQ, 2, {}, B);
  view(both(fp_lt(fx, fy), Kind::FP_LT, {fx, fy}), Kind::FP_LT, 2, {}, B);
  view(both(fp_leq(fx, fy), Kind::FP_LEQ, {fx, fy}), Kind::FP_LEQ, 2, {}, B);
  view(both(fp_gt(fx, fy), Kind::FP_GT, {fx, fy}), Kind::FP_GT, 2, {}, B);
  view(both(fp_geq(fx, fy), Kind::FP_GEQ, {fx, fy}), Kind::FP_GEQ, 2, {}, B);
  view(both(fp_is_normal(fx), Kind::FP_IS_NORMAL, {fx}), Kind::FP_IS_NORMAL, 1, {}, B);
  view(both(fp_is_subnormal(fx), Kind::FP_IS_SUBNORMAL, {fx}), Kind::FP_IS_SUBNORMAL, 1, {}, B);
  view(both(fp_is_zero(fx), Kind::FP_IS_ZERO, {fx}), Kind::FP_IS_ZERO, 1, {}, B);
  view(both(fp_is_inf(fx), Kind::FP_IS_INF, {fx}), Kind::FP_IS_INF, 1, {}, B);
  view(both(fp_is_nan(fx), Kind::FP_IS_NAN, {fx}), Kind::FP_IS_NAN, 1, {}, B);
  view(both(fp_is_neg(fx), Kind::FP_IS_NEG, {fx}), Kind::FP_IS_NEG, 1, {}, B);
  view(both(fp_is_pos(fx), Kind::FP_IS_POS, {fx}), Kind::FP_IS_POS, 1, {}, B);
}

TEST_F(Kinds, floating_point_conversions)
{
  const Term sg = tm.declare("sg", bv1), ex = tm.declare("ex", bv8), sig = tm.declare("sig", bv23);
  // lowered: (fp s e m) is the reinterpretation of the concatenated bits
  view(both(tm.mk_fp(sg, ex, sig), Kind::FP_FP, {sg, ex, sig}), Kind::FP_TO_FP_FROM_BV, 1,
       {8, 24}, f32);
  EXPECT_EQ(tm.mk_fp(sg, ex, sig).child(0).kind(), Kind::BV_CONCAT);
  view(both(to_fp_from_bits(f32, b32), Kind::FP_TO_FP_FROM_BV, {b32}, {8, 24}),
       Kind::FP_TO_FP_FROM_BV, 1, {8, 24}, f32);
  view(both(to_fp(f32, rm, dx), Kind::FP_TO_FP_FROM_FP, {rm, dx}, {8, 24}),
       Kind::FP_TO_FP_FROM_FP, 2, {8, 24}, f32);
  view(both(to_fp(f32, rm, x), Kind::FP_TO_FP_FROM_SBV, {rm, x}, {8, 24}),
       Kind::FP_TO_FP_FROM_SBV, 2, {8, 24}, f32);
  view(both(to_fp_unsigned(f32, rm, x), Kind::FP_TO_FP_FROM_UBV, {rm, x}, {8, 24}),
       Kind::FP_TO_FP_FROM_UBV, 2, {8, 24}, f32);
  EXPECT_TRUE(to_fp(f32, RoundingMode::RTZ, x).child(0).same_as(tm.mk_rm(RoundingMode::RTZ)));
  EXPECT_TRUE(to_fp_unsigned(f32, RoundingMode::RTZ, x).child(0).same_as(tm.mk_rm(RoundingMode::RTZ)));
  // a Real converts only as a value under a mode value: the result is a VALUE
  const Term quarter = to_fp(f32, RoundingMode::RNE, tm.mk_real(1, 4));
  view(quarter, Kind::VALUE, 0, {}, f32);
  EXPECT_TRUE(tm.mk_term(Kind::FP_TO_FP_FROM_REAL, {tm.mk_rm(RoundingMode::RNE), tm.mk_real(1, 4)},
                         {8, 24})
                  .same_as(quarter));
  EXPECT_EQ(*quarter.to_fp().to_double(), 0.25);
  view(both(fp_to_ubv(8, rm, fx), Kind::FP_TO_UBV, {rm, fx}, {8}), Kind::FP_TO_UBV, 2, {8}, bv8);
  view(both(fp_to_sbv(8, rm, fx), Kind::FP_TO_SBV, {rm, fx}, {8}), Kind::FP_TO_SBV, 2, {8}, bv8);
  EXPECT_TRUE(fp_to_ubv(8, RoundingMode::RTZ, fx).child(0).same_as(tm.mk_rm(RoundingMode::RTZ)));
  EXPECT_TRUE(fp_to_sbv(8, RoundingMode::RTZ, fx).child(0).same_as(tm.mk_rm(RoundingMode::RTZ)));
  view(both(fp_to_ieee_bv(fx), Kind::FP_TO_IEEE_BV, {fx}), Kind::FP_TO_IEEE_BV, 1, {}, bv32);
  EXPECT_EQ(fp_to_ieee_bv(dx).sort().bv_size(), 64u);
  EXPECT_EQ(fp_to_ieee_bv(fx).str(), "(fp.to_ieee_bv fx)");
  // a symbolic float has no engine conversion to a Real; a float value
  // converts exactly, whatever the simplify setting
  API3_EXPECT_ERROR(ErrorCode::UNSUPPORTED, fp_to_real(fx));
  API3_EXPECT_ERROR(ErrorCode::UNSUPPORTED, tm.mk_term(Kind::FP_TO_REAL, {fx}));
  const Sort f32v = tm.mk_fp32_sort();
  EXPECT_TRUE(fp_to_real(tm.mk_fp(f32v, RoundingMode::RNE, 1.5)).same_as(tm.mk_real(3, 2)));
  EXPECT_TRUE(fp_to_real(tm.mk_fp(f32v, RoundingMode::RNE, -2.5)).same_as(tm.mk_real(-5, 2)));
  EXPECT_TRUE(fp_to_real(tm.mk_fp_neg_zero(f32v)).same_as(tm.mk_real(0)));
  EXPECT_TRUE(fp_to_real(tm.mk_fp(f32v, RoundingMode::RNE, 16777216.0)).same_as(tm.mk_real(16777216)));
  // the smallest subnormal of binary32 is 2^-149
  EXPECT_EQ(fp_to_real(tm.mk_fp_from_bits(f32v, tm.mk_bv(32, 1))).to_rational().denominator,
            "713623846352979940529142984724747568191373312");
  API3_EXPECT_ERROR(ErrorCode::UNSUPPORTED, fp_to_real(tm.mk_fp_nan(f32v)));
  API3_EXPECT_ERROR(ErrorCode::UNSUPPORTED, fp_to_real(tm.mk_fp_pos_inf(f32v)));
}

TEST_F(Kinds, reals)
{
  view(both(real_add(rx, ry), Kind::REAL_ADD, {rx, ry}), Kind::REAL_ADD, 2, {}, R);
  view(real_add({rx, ry, rx}), Kind::REAL_ADD, 3, {}, R);
  EXPECT_TRUE((rx + ry).same_as(real_add(rx, ry)));
  view(both(real_sub(rx, ry), Kind::REAL_SUB, {rx, ry}), Kind::REAL_SUB, 2, {}, R);
  EXPECT_TRUE((rx - ry).same_as(real_sub(rx, ry)));
  view(both(real_neg(rx), Kind::REAL_NEG, {rx}), Kind::REAL_NEG, 1, {}, R);
  EXPECT_TRUE((-rx).same_as(real_neg(rx)));
  const Term two = tm.mk_real(2);
  view(both(real_mul(two, rx), Kind::REAL_MUL, {two, rx}), Kind::REAL_MUL, 2, {}, R);
  EXPECT_TRUE((rx * 2).same_as(real_mul(rx, two)));
  view(both(real_div(rx, two), Kind::REAL_DIV, {rx, two}), Kind::REAL_DIV, 2, {}, R);
  EXPECT_TRUE((rx / 2).same_as(real_div(rx, two)));
  view(both(real_lt(rx, ry), Kind::REAL_LT, {rx, ry}), Kind::REAL_LT, 2, {}, B);
  view(both(real_le(rx, ry), Kind::REAL_LE, {rx, ry}), Kind::REAL_LE, 2, {}, B);
  view(both(real_gt(rx, ry), Kind::REAL_GT, {rx, ry}), Kind::REAL_GT, 2, {}, B);
  view(both(real_ge(rx, ry), Kind::REAL_GE, {rx, ry}), Kind::REAL_GE, 2, {}, B);
  // the linear fragment: one factor of a product and the divisor must be values
  API3_EXPECT_ERROR(ErrorCode::UNSUPPORTED, real_mul(rx, ry));
  API3_EXPECT_ERROR(ErrorCode::UNSUPPORTED, (void)(rx * ry));
  API3_EXPECT_ERROR(ErrorCode::UNSUPPORTED, real_div(rx, ry));
  API3_EXPECT_ERROR(ErrorCode::UNSUPPORTED, real_div(rx, tm.mk_real(0)));
  API3_EXPECT_ERROR(ErrorCode::UNSUPPORTED, (void)(rx / 0));
}

// The recursive children()/mk_term rebuild of a nested term is the term.
TEST_F(Kinds, rebuild_round_trip)
{
  const Term nested = ite(and_(bvult(x, y), fp_lt(fx, fy)),
                          concat(extract(3, 0, bvadd({x, y, z})), fp_to_ubv(4, rm, fx)),
                          bvxor(x, zero_extend(4, extract(3, 0, y))));
  std::function<Term(const Term&)> rebuild = [&](const Term& t) -> Term {
    if (t.kind() == Kind::VALUE || t.kind() == Kind::CONSTANT)
      return t;
    std::vector<Term> kids;
    for (const Term& c : t.children())
      kids.push_back(rebuild(c));
    return tm.mk_term(t.kind(), kids, t.indices(), t.sort());
  };
  EXPECT_TRUE(rebuild(nested).same_as(nested));
  EXPECT_TRUE(rebuild(f(bvadd(x, y), select(store(ar, x, y), z))).same_as(
      f(bvadd(x, y), select(store(ar, x, y), z))));
}

// ---------------------------------------------------------------- sort checks

TEST_F(Kinds, sort_mismatch_names_the_argument)
{
  const Term v16 = tm.declare("v16", bv16);
  auto e = API3_ERROR_OF(bvadd(x, v16));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::SORT_MISMATCH);
  EXPECT_EQ(e->argument_index(), std::optional<int>(1));
  EXPECT_EQ(e->function(), "bvadd");
  ASSERT_EQ(e->terms().size(), 2u);
  EXPECT_TRUE(e->terms()[0].same_as(x));
  EXPECT_TRUE(e->terms()[1].same_as(v16));
  ASSERT_EQ(e->sorts().size(), 2u);
  EXPECT_TRUE(e->sorts()[0] == bv16);
  EXPECT_TRUE(e->sorts()[1] == bv8);
  EXPECT_NE(std::string(e->what()).find("[SORT_MISMATCH]"), std::string::npos);

  auto arg = [](const std::optional<RecoverableError>& err) {
    return err.has_value() && err->code() == ErrorCode::SORT_MISMATCH ? *err->argument_index()
                                                                         : -1;
  };
  EXPECT_EQ(arg(API3_ERROR_OF(bvadd(x, a))), 1);
  EXPECT_EQ(arg(API3_ERROR_OF(bvadd(a, x))), 0);
  EXPECT_EQ(arg(API3_ERROR_OF(ite(x, x, y))), 0);
  EXPECT_EQ(arg(API3_ERROR_OF(ite(a, x, a))), 2);
  EXPECT_EQ(arg(API3_ERROR_OF(ite(a, a, x))), 2);
  EXPECT_EQ(arg(API3_ERROR_OF(eq(x, a))), 1);
  EXPECT_EQ(arg(API3_ERROR_OF(distinct({x, y, a}))), 2);
  EXPECT_EQ(arg(API3_ERROR_OF(not_(x))), 0);
  EXPECT_EQ(arg(API3_ERROR_OF(and_(a, x))), 1);
  EXPECT_EQ(arg(API3_ERROR_OF(implies(x, a))), 0);
  EXPECT_EQ(arg(API3_ERROR_OF(bvnot(a))), 0);
  EXPECT_EQ(arg(API3_ERROR_OF(select(x, x))), 0);
  EXPECT_EQ(arg(API3_ERROR_OF(select(ar, a))), 1);
  EXPECT_EQ(arg(API3_ERROR_OF(store(ar, a, y))), 1);
  EXPECT_EQ(arg(API3_ERROR_OF(store(ar, x, a))), 2);
  EXPECT_EQ(arg(API3_ERROR_OF(fp_add(x, fx, fy))), 0);
  EXPECT_EQ(arg(API3_ERROR_OF(fp_add(rm, x, fy))), 1);
  EXPECT_EQ(arg(API3_ERROR_OF(fp_add(rm, fx, dx))), 2);
  EXPECT_EQ(arg(API3_ERROR_OF(fp_fma(rm, fx, fy, dx))), 3);
  EXPECT_EQ(arg(API3_ERROR_OF(fp_sqrt(rm, x))), 1);
  EXPECT_EQ(arg(API3_ERROR_OF(fp_lt(fx, dx))), 1);
  EXPECT_EQ(arg(API3_ERROR_OF(fp_is_nan(x))), 0);
  EXPECT_EQ(arg(API3_ERROR_OF(to_fp(f32, RoundingMode::RNE, a))), 2);
  EXPECT_EQ(arg(API3_ERROR_OF(to_fp(f32, x, fx))), 0);
  EXPECT_EQ(arg(API3_ERROR_OF(to_fp_unsigned(f32, rm, fx))), 1);
  EXPECT_EQ(arg(API3_ERROR_OF(to_fp_from_bits(f32, x))), 0);
  EXPECT_EQ(arg(API3_ERROR_OF(fp_to_ubv(8, rm, x))), 1);
  EXPECT_EQ(arg(API3_ERROR_OF(fp_to_ieee_bv(x))), 0);
  EXPECT_EQ(arg(API3_ERROR_OF(real_add(rx, x))), 1);
  EXPECT_EQ(arg(API3_ERROR_OF(real_lt(x, rx))), 0);
  EXPECT_EQ(arg(API3_ERROR_OF(f(x, a))), 2);
  EXPECT_EQ(arg(API3_ERROR_OF(f(a, y))), 1);
  EXPECT_EQ(arg(API3_ERROR_OF(x(x))), 0);
  EXPECT_EQ(arg(API3_ERROR_OF(tm.mk_fp(x, x, x))), 0);
  EXPECT_EQ(arg(API3_ERROR_OF(tm.mk_term(Kind::FP_TO_FP_FROM_BV, {b32}, {8, 25}))), 0);
  EXPECT_EQ(arg(API3_ERROR_OF(tm.mk_term(Kind::CONST_ARRAY, {a}, {}, A))), 0);
  API3_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, tm.mk_term(Kind::CONST_ARRAY, {x}, {}, bv8));
  // a sort-taking constructor given the wrong sort
  API3_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, to_fp(bv8, rm, fx));
  API3_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, to_fp_from_bits(R, b32));
  API3_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, bv1_to_bool(x));
}

TEST_F(Kinds, arity_errors)
{
  API3_EXPECT_ERROR(ErrorCode::ARITY, tm.mk_term(Kind::ITE, {a, x}));
  API3_EXPECT_ERROR(ErrorCode::ARITY, tm.mk_term(Kind::ITE, {a, x, y, z}));
  API3_EXPECT_ERROR(ErrorCode::ARITY, tm.mk_term(Kind::NOT, {a, b}));
  API3_EXPECT_ERROR(ErrorCode::ARITY, tm.mk_term(Kind::BV_ADD, {x}));
  API3_EXPECT_ERROR(ErrorCode::ARITY, tm.mk_term(Kind::XOR, {a}));
  API3_EXPECT_ERROR(ErrorCode::ARITY, tm.mk_term(Kind::DISTINCT, {x}));
  API3_EXPECT_ERROR(ErrorCode::ARITY, tm.mk_term(Kind::AND, {}));
  API3_EXPECT_ERROR(ErrorCode::ARITY, tm.mk_term(Kind::BV_SUB, {x, y, z}));
  API3_EXPECT_ERROR(ErrorCode::ARITY, tm.mk_term(Kind::FP_FMA, {rm, fx, fy}));
  API3_EXPECT_ERROR(ErrorCode::ARITY, tm.mk_term(Kind::REAL_MUL, {rx, rx, rx}));
  API3_EXPECT_ERROR(ErrorCode::ARITY, tm.mk_term(Kind::SELECT, {ar}));
  // indices are counted too
  API3_EXPECT_ERROR(ErrorCode::ARITY, tm.mk_term(Kind::BV_EXTRACT, {x}, {3}));
  API3_EXPECT_ERROR(ErrorCode::ARITY, tm.mk_term(Kind::BV_ADD, {x, y}, {1}));
  API3_EXPECT_ERROR(ErrorCode::ARITY, tm.mk_term(Kind::BV_ZERO_EXTEND, {x}, {1, 2}));
  API3_EXPECT_ERROR(ErrorCode::ARITY, tm.mk_term(Kind::FP_TO_UBV, {rm, fx}, {}));
  // function applications check their declared arity
  API3_EXPECT_ERROR(ErrorCode::ARITY, f(x));
  API3_EXPECT_ERROR(ErrorCode::ARITY, f(x, y, z));
  API3_EXPECT_ERROR(ErrorCode::ARITY, apply({f}));
  API3_EXPECT_ERROR(ErrorCode::ARITY, and_(std::vector<Term>{}));
  API3_EXPECT_ERROR(ErrorCode::ARITY, bvadd(std::vector<Term>{x}));
}

TEST_F(Kinds, index_out_of_range)
{
  auto e = API3_ERROR_OF(extract(8, 0, x));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::INDEX_OUT_OF_RANGE);
  EXPECT_EQ(e->function(), "extract");
  ASSERT_EQ(e->terms().size(), 1u);
  EXPECT_TRUE(e->terms()[0].same_as(x));
  API3_EXPECT_ERROR(ErrorCode::INDEX_OUT_OF_RANGE, extract(2, 3, x));
  API3_EXPECT_ERROR(ErrorCode::INDEX_OUT_OF_RANGE, tm.mk_term(Kind::BV_EXTRACT, {x}, {8, 0}));
  API3_EXPECT_ERROR(ErrorCode::INDEX_OUT_OF_RANGE, repeat(0, x));
  API3_EXPECT_ERROR(ErrorCode::INDEX_OUT_OF_RANGE, fp_to_ubv(0, rm, fx));
  API3_EXPECT_ERROR(ErrorCode::INDEX_OUT_OF_RANGE, fp_to_sbv(0, RoundingMode::RTZ, fx));
  API3_EXPECT_ERROR(ErrorCode::INDEX_OUT_OF_RANGE,
                    tm.mk_term(Kind::FP_TO_FP_FROM_BV, {b32}, {1, 31}));
  API3_EXPECT_ERROR(ErrorCode::INDEX_OUT_OF_RANGE,
                    tm.mk_term(Kind::FP_TO_FP_FROM_SBV, {rm, x}, {8, 1}));
  API3_EXPECT_ERROR(ErrorCode::INDEX_OUT_OF_RANGE, x.child(0));
  API3_EXPECT_ERROR(ErrorCode::INDEX_OUT_OF_RANGE, bvadd(x, y).child(2));
  // rotations wrap instead of failing
  EXPECT_EQ(rotate_left(100, x).sort().bv_size(), 8u);
  // extremes that are in range
  EXPECT_EQ(extract(7, 0, x).sort().bv_size(), 8u);
  EXPECT_EQ(extract(0, 0, x).sort().bv_size(), 1u);
}

TEST_F(Kinds, unsupported)
{
  const Term k = tm.mk_const_array(A, tm.mk_bv(8, 9));
  API3_EXPECT_ERROR(ErrorCode::UNSUPPORTED, fp_to_real(fx));
  // equality over constant arrays is supported (api3-const-arrays.cpp)
  EXPECT_EQ(eq(k, ar).kind(), Kind::EQUAL);
  EXPECT_EQ((store(k, x, y) == ar).kind(), Kind::EQUAL);
  // two-operand distinct over arrays is built as the negated equality
  const Term d = distinct(k, ar);
  ASSERT_EQ(d.kind(), Kind::NOT);
  EXPECT_EQ(d.child(0).kind(), Kind::EQUAL);
  API3_EXPECT_ERROR(ErrorCode::UNSUPPORTED, real_mul(rx, ry));
  API3_EXPECT_ERROR(ErrorCode::UNSUPPORTED, eq(f, f));
  API3_EXPECT_ERROR(ErrorCode::UNSUPPORTED, distinct(f, f));
  API3_EXPECT_ERROR(ErrorCode::UNSUPPORTED, ite(a, f, f));
  // a Real converts to a float only as a value under a mode value
  API3_EXPECT_ERROR(ErrorCode::UNSUPPORTED, to_fp(f32, RoundingMode::RNE, rx));
  API3_EXPECT_ERROR(ErrorCode::UNSUPPORTED, to_fp(f32, rm, tm.mk_real(1, 4)));
  // fp.rem's circuit is bounded by the format
  const Sort wide = tm.mk_fp_sort(12, 5);
  API3_EXPECT_ERROR(ErrorCode::UNSUPPORTED,
                    fp_rem(tm.declare("w1", wide), tm.declare("w2", wide)));
  EXPECT_EQ(fp_rem(tm.declare("d1", f64), tm.declare("d2", f64)).kind(), Kind::FP_REM);
  EXPECT_EQ(capabilities()["kind.FP_TO_REAL"], "values-only");
  EXPECT_EQ(capabilities()["real.nonlinear"], "false");
  EXPECT_EQ(capabilities()["array.const-equality"], "true");
}

TEST_F(Kinds, null_and_foreign_arguments)
{
  auto e = API3_ERROR_OF(bvadd(x, Term()));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::NULL_HANDLE);
  EXPECT_EQ(e->argument_index(), std::optional<int>(1));
  API3_EXPECT_ERROR(ErrorCode::NULL_HANDLE, not_(Term()));
  API3_EXPECT_ERROR(ErrorCode::NULL_HANDLE, tm.mk_term(Kind::BV_NOT, {Term()}));
  API3_EXPECT_ERROR(ErrorCode::NULL_HANDLE, extract(1, 0, Term()));
  API3_EXPECT_ERROR(ErrorCode::NULL_HANDLE, to_fp(f32, rm, Term()));
  API3_EXPECT_ERROR(ErrorCode::NULL_HANDLE, Term().kind());
  API3_EXPECT_ERROR(ErrorCode::NULL_HANDLE, Term().sort());
  API3_EXPECT_ERROR(ErrorCode::NULL_HANDLE, Term().children());
  EXPECT_TRUE(Term().is_null());
  EXPECT_FALSE(Term().is_value());
  EXPECT_FALSE(Term().is_const());
  EXPECT_EQ(Term().id(), 0u);
  TermManager other;
  const Term ox = other.declare("ox", other.mk_bv_sort(8));
  auto fe = API3_ERROR_OF(bvadd(x, ox));
  ASSERT_TRUE(fe.has_value());
  EXPECT_EQ(fe->code(), ErrorCode::FOREIGN_MANAGER);
  EXPECT_EQ(fe->argument_index(), std::optional<int>(1));
  API3_EXPECT_ERROR(ErrorCode::FOREIGN_MANAGER, tm.mk_term(Kind::BV_ADD, {x, ox}));
  API3_EXPECT_ERROR(ErrorCode::FOREIGN_MANAGER, tm.mk_term(Kind::BV_NOT, {ox}));
  API3_EXPECT_ERROR(ErrorCode::FOREIGN_MANAGER, to_fp(f32, rm, ox));
  API3_EXPECT_ERROR(ErrorCode::FOREIGN_MANAGER, tm.mk_const_array(A, ox));
  API3_EXPECT_ERROR(ErrorCode::FOREIGN_MANAGER, tm.mk_term(Kind::BV_NOT, {x}, {}, other.mk_bv_sort(8)));
}

// ---------------------------------------------------------------- values

// Closed terms of every kind evaluated through a model (the evaluator folds
// them through the engine); the expected values follow SMT-LIB.
class KindValues : public ::testing::Test
{
protected:
  TermManager tm;
  Solver s{tm};
  std::optional<Model> m;
  Sort bv8 = tm.mk_bv_sort(8), bv4 = tm.mk_bv_sort(4);
  Sort f32 = tm.mk_fp32_sort(), f64 = tm.mk_fp64_sort();
  Sort A = tm.mk_array_sort(bv8, bv8);

  void SetUp() override
  {
    ASSERT_TRUE(s.check_sat().is_sat());
    m.emplace(s.model());
  }
  Term ev(const Term& t) { return m->value(t); }
  std::uint64_t u(const Term& t) { return ev(t).to_uint64(); }
  bool bo(const Term& t) { return ev(t).to_bool(); }
  double d(const Term& t) { return *ev(t).to_fp().to_double(); }
  std::string q(const Term& t) { return ev(t).to_rational().str(); }
  Term B(std::uint64_t v) { return tm.mk_bv(8, v); }
  Term F(double v) { return tm.mk_fp(f32, RoundingMode::RNE, v); }
  Term Q(std::int64_t n, std::int64_t dn) { return tm.mk_real(n, dn); }
  Term T() { return tm.mk_true(); }
  Term Fa() { return tm.mk_false(); }
};

TEST_F(KindValues, boolean_and_core)
{
  EXPECT_FALSE(bo(not_(T())));
  EXPECT_TRUE(bo(not_(Fa())));
  EXPECT_FALSE(bo(and_(T(), Fa())));
  EXPECT_TRUE(bo(and_({T(), T(), T()})));
  EXPECT_TRUE(bo(or_(Fa(), T())));
  EXPECT_FALSE(bo(or_({Fa(), Fa(), Fa()})));
  EXPECT_FALSE(bo(xor_(T(), T())));
  EXPECT_TRUE(bo(xor_({T(), T(), T()})));
  EXPECT_FALSE(bo(implies(T(), Fa())));
  EXPECT_TRUE(bo(implies(Fa(), Fa())));
  EXPECT_EQ(u(ite(T(), B(1), B(2))), 1u);
  EXPECT_EQ(u(ite(Fa(), B(1), B(2))), 2u);
  EXPECT_EQ(d(ite(T(), F(1.5), F(2.5))), 1.5);
  EXPECT_EQ(q(ite(Fa(), Q(1, 2), Q(1, 3))), "1/3");
  EXPECT_TRUE(bo(eq(B(5), B(5))));
  EXPECT_FALSE(bo(eq(B(5), B(6))));
  EXPECT_TRUE(bo(eq(Q(1, 2), Q(2, 4))));
  EXPECT_TRUE(bo(eq(tm.mk_fp_nan(f32), tm.mk_fp_nan(f32)))); // SMT '=' on NaN
  EXPECT_FALSE(bo(eq(tm.mk_fp_pos_zero(f32), tm.mk_fp_neg_zero(f32))));
  EXPECT_TRUE(bo(eq(tm.mk_rm(RoundingMode::RTZ), tm.mk_rm(RoundingMode::RTZ))));
  EXPECT_TRUE(bo(distinct({B(1), B(2), B(3)})));
  EXPECT_FALSE(bo(distinct({B(1), B(2), B(1)})));
  EXPECT_TRUE(bo(distinct(Q(1, 2), Q(1, 3))));
  EXPECT_FALSE(bo(distinct(Q(1, 2), Q(2, 4))));
  EXPECT_TRUE(bo(distinct(F(1.0), F(2.0))));
  EXPECT_FALSE(bo(distinct(T(), T())));
}

TEST_F(KindValues, bitvectors)
{
  EXPECT_EQ(u(bvnot(B(0x0f))), 0xf0u);
  EXPECT_EQ(u(bvand(B(0x0f), B(0x3c))), 0x0cu);
  EXPECT_EQ(u(bvand({B(0x0f), B(0x3c), B(0x08)})), 0x08u);
  EXPECT_EQ(u(bvor(B(0x0f), B(0x3c))), 0x3fu);
  EXPECT_EQ(u(bvxor(B(0x0f), B(0x3c))), 0x33u);
  EXPECT_EQ(u(bvnand(B(0x0f), B(0x3c))), 0xf3u);
  EXPECT_EQ(u(bvnor(B(0x0f), B(0x3c))), 0xc0u);
  EXPECT_EQ(u(bvxnor(B(0x0f), B(0x3c))), 0xccu);
  EXPECT_EQ(u(bvneg(B(1))), 0xffu);
  EXPECT_EQ(u(bvadd(B(200), B(100))), 44u);
  EXPECT_EQ(u(bvadd({B(1), B(2), B(3)})), 6u);
  EXPECT_EQ(u(bvsub(B(1), B(2))), 0xffu);
  EXPECT_EQ(u(bvmul(B(16), B(16))), 0u);
  EXPECT_EQ(u(bvmul({B(2), B(3), B(4)})), 24u);
  EXPECT_EQ(u(bvudiv(B(7), B(2))), 3u);
  EXPECT_EQ(u(bvudiv(B(7), B(0))), 0xffu); // total: x/0 = all ones
  EXPECT_EQ(u(bvurem(B(7), B(2))), 1u);
  EXPECT_EQ(u(bvurem(B(7), B(0))), 7u); // total: x%0 = x
  EXPECT_EQ(ev(bvsdiv(tm.mk_bv_signed(8, -7), B(2))).to_int64(), -3);
  EXPECT_EQ(ev(bvsdiv(B(7), tm.mk_bv_signed(8, -2))).to_int64(), -3);
  EXPECT_EQ(ev(bvsrem(tm.mk_bv_signed(8, -7), B(2))).to_int64(), -1);
  EXPECT_EQ(ev(bvsmod(tm.mk_bv_signed(8, -7), B(2))).to_int64(), 1);
  EXPECT_EQ(u(bvshl(B(1), B(3))), 8u);
  EXPECT_EQ(u(bvshl(B(1), B(9))), 0u); // over-shift yields 0
  EXPECT_EQ(u(bvlshr(B(0x80), B(7))), 1u);
  EXPECT_EQ(u(bvashr(B(0x80), B(7))), 0xffu);
  EXPECT_EQ(u(bvashr(B(0x80), B(9))), 0xffu); // over-shift sign-fills
  EXPECT_EQ(u(bvashr(B(0x40), B(9))), 0u);
  EXPECT_EQ(u(concat(tm.mk_bv(4, 1), tm.mk_bv(4, 2))), 0x12u);
  EXPECT_EQ(u(concat({tm.mk_bv(4, 1), tm.mk_bv(2, 0), tm.mk_bv(2, 3)})), 0x13u);
  EXPECT_EQ(u(extract(7, 4, B(0xab))), 0xau);
  EXPECT_EQ(u(extract(3, 0, B(0xab))), 0xbu);
  EXPECT_EQ(u(zero_extend(8, B(0xff))), 0x00ffu);
  EXPECT_EQ(u(sign_extend(8, B(0xff))), 0xffffu);
  EXPECT_EQ(u(sign_extend(8, B(0x7f))), 0x007fu);
  EXPECT_EQ(u(repeat(2, B(0xab))), 0xababu);
  EXPECT_EQ(u(rotate_left(4, B(0xab))), 0xbau);
  EXPECT_EQ(u(rotate_left(1, B(0x81))), 0x03u);
  EXPECT_EQ(u(rotate_right(4, B(0xab))), 0xbau);
  EXPECT_EQ(u(rotate_right(1, B(0x81))), 0xc0u);
  EXPECT_EQ(u(rotate_left(12, B(0xab))), 0xbau);
  EXPECT_EQ(u(bvcomp(B(5), B(5))), 1u);
  EXPECT_EQ(u(bvcomp(B(5), B(6))), 0u);
  EXPECT_TRUE(bo(bvult(B(1), B(0xff))));
  EXPECT_FALSE(bo(bvult(B(1), B(1))));
  EXPECT_TRUE(bo(bvule(B(1), B(1))));
  EXPECT_TRUE(bo(bvugt(B(0xff), B(1))));
  EXPECT_TRUE(bo(bvuge(B(1), B(1))));
  EXPECT_TRUE(bo(bvslt(B(0xff), B(1))));  // -1 < 1
  EXPECT_FALSE(bo(bvslt(B(1), B(0xff))));
  EXPECT_TRUE(bo(bvsle(B(0x80), B(0x80))));
  EXPECT_TRUE(bo(bvsgt(B(1), B(0xff))));
  EXPECT_TRUE(bo(bvsge(B(0x7f), B(0x80))));
  EXPECT_TRUE(bo(bvuaddo(B(0xff), B(1))));
  EXPECT_FALSE(bo(bvuaddo(B(1), B(1))));
  EXPECT_TRUE(bo(bvsaddo(B(0x7f), B(1))));
  EXPECT_FALSE(bo(bvsaddo(B(0x7e), B(1))));
  EXPECT_TRUE(bo(bvumulo(B(16), B(16))));
  EXPECT_FALSE(bo(bvumulo(B(15), B(15))));
  EXPECT_TRUE(bo(bvsmulo(B(0x7f), B(2))));
  EXPECT_FALSE(bo(bvsmulo(B(0x3f), B(2))));
  EXPECT_TRUE(bo(bvusubo(B(0), B(1))));
  EXPECT_FALSE(bo(bvusubo(B(1), B(1))));
  EXPECT_TRUE(bo(bvssubo(B(0x80), B(1))));
  EXPECT_FALSE(bo(bvssubo(B(0x81), B(1))));
  EXPECT_TRUE(bo(bvnego(B(0x80))));
  EXPECT_FALSE(bo(bvnego(B(1))));
  EXPECT_TRUE(bo(bvsdivo(B(0x80), B(0xff))));
  EXPECT_FALSE(bo(bvsdivo(B(0x80), B(1))));
  EXPECT_EQ(u(bvredand(B(0xff))), 1u);
  EXPECT_EQ(u(bvredand(B(0xfe))), 0u);
  EXPECT_EQ(u(bvredor(B(0))), 0u);
  EXPECT_EQ(u(bvredor(B(0x10))), 1u);
  EXPECT_TRUE(bo(bit(B(0x10), 4)));
  EXPECT_FALSE(bo(bit(B(0x10), 3)));
  EXPECT_EQ(u(bool_to_bv1(T())), 1u);
  EXPECT_TRUE(bo(bv1_to_bool(tm.mk_bv(1, 1))));
}

TEST_F(KindValues, arrays)
{
  const Term k = tm.mk_const_array(A, B(9));
  EXPECT_EQ(u(select(store(k, B(3), B(7)), B(3))), 7u);
  EXPECT_EQ(u(select(store(k, B(3), B(7)), B(4))), 9u);
  EXPECT_EQ(u(select(store(store(k, B(3), B(7)), B(3), B(8)), B(3))), 8u);
  EXPECT_EQ(u(select(ite(T(), store(k, B(1), B(2)), k), B(1))), 2u);
  const Term fb = array_from_bytes(tm, {1, 2, 3});
  EXPECT_EQ(u(select(fb, tm.mk_bv(32, 2))), 3u);
  EXPECT_EQ(u(select(fb, tm.mk_bv(32, 7))), 0u);
  EXPECT_EQ(u(select(array_from_bytes(tm, {5}, 8), tm.mk_bv(8, 0))), 5u);
  API3_EXPECT_ERROR(ErrorCode::VALUE_OUT_OF_RANGE, array_from_bytes(tm, {1, 2, 3}, 1));
}

TEST_F(KindValues, floating_point)
{
  EXPECT_EQ(d(fp_abs(F(-1.5))), 1.5);
  EXPECT_EQ(d(fp_neg(F(1.5))), -1.5);
  EXPECT_EQ(d(fp_add(RoundingMode::RNE, F(1.5), F(2.25))), 3.75);
  EXPECT_EQ(d(fp_sub(RoundingMode::RNE, F(1.5), F(2.25))), -0.75);
  EXPECT_EQ(d(fp_mul(RoundingMode::RNE, F(1.5), F(2.0))), 3.0);
  EXPECT_EQ(d(fp_div(RoundingMode::RNE, F(3.0), F(2.0))), 1.5);
  EXPECT_EQ(d(fp_fma(RoundingMode::RNE, F(1.5), F(2.0), F(0.25))), 3.25);
  EXPECT_EQ(d(fp_sqrt(RoundingMode::RNE, F(2.25))), 1.5);
  EXPECT_EQ(d(fp_rem(F(5.5), F(2.0))), -0.5);
  EXPECT_EQ(d(fp_rti(RoundingMode::RNE, F(2.5))), 2.0);
  EXPECT_EQ(d(fp_rti(RoundingMode::RNA, F(2.5))), 3.0);
  EXPECT_EQ(d(fp_rti(RoundingMode::RTP, F(2.25))), 3.0);
  EXPECT_EQ(d(fp_rti(RoundingMode::RTN, F(2.75))), 2.0);
  EXPECT_EQ(d(fp_rti(RoundingMode::RTZ, F(-2.75))), -2.0);
  EXPECT_EQ(d(fp_min(F(1.0), F(2.0))), 1.0);
  EXPECT_EQ(d(fp_min(F(2.0), F(1.0))), 1.0);
  EXPECT_EQ(d(fp_max(F(1.0), F(2.0))), 2.0);
  EXPECT_EQ(d(fp_max(F(-1.0), tm.mk_fp_neg_inf(f32))), -1.0);
  EXPECT_EQ(d(fp_min(tm.mk_fp_nan(f32), F(1.0))), 1.0);
  EXPECT_EQ(d(fp_max(F(1.0), tm.mk_fp_nan(f32))), 1.0);
  // the operators use the manager's default mode
  EXPECT_EQ(d(F(1.5) + F(2.25)), 3.75);
  EXPECT_EQ(d(F(1.5) - F(2.25)), -0.75);
  EXPECT_EQ(d(F(1.5) * F(2.0)), 3.0);
  EXPECT_EQ(d(F(3.0) / F(2.0)), 1.5);
  EXPECT_EQ(d(-F(1.5)), -1.5);
  // rounding is the mode's: 1/3 in binary32 under RTZ is below the RNE result
  const Term third_rne = fp_div(RoundingMode::RNE, F(1.0), F(3.0));
  const Term third_rtz = fp_div(RoundingMode::RTZ, F(1.0), F(3.0));
  EXPECT_LT(d(third_rtz), d(third_rne));
  EXPECT_TRUE(bo(fp_eq(F(1.0), F(1.0))));
  EXPECT_FALSE(bo(fp_eq(tm.mk_fp_nan(f32), tm.mk_fp_nan(f32))));
  EXPECT_TRUE(bo(fp_eq(tm.mk_fp_pos_zero(f32), tm.mk_fp_neg_zero(f32))));
  EXPECT_TRUE(bo(fp_lt(F(1.0), F(2.0))));
  EXPECT_FALSE(bo(fp_lt(F(1.0), tm.mk_fp_nan(f32))));
  EXPECT_TRUE(bo(fp_leq(F(2.0), F(2.0))));
  EXPECT_TRUE(bo(fp_gt(F(2.0), F(1.0))));
  EXPECT_TRUE(bo(fp_geq(F(1.0), F(1.0))));
  EXPECT_TRUE(bo(fp_is_normal(F(1.0))));
  EXPECT_FALSE(bo(fp_is_normal(F(1e-45))));
  EXPECT_TRUE(bo(fp_is_subnormal(F(1e-45))));
  EXPECT_TRUE(bo(fp_is_zero(tm.mk_fp_neg_zero(f32))));
  EXPECT_FALSE(bo(fp_is_zero(F(1e-45))));
  EXPECT_TRUE(bo(fp_is_inf(tm.mk_fp_pos_inf(f32))));
  EXPECT_TRUE(bo(fp_is_nan(tm.mk_fp_nan(f32))));
  EXPECT_FALSE(bo(fp_is_nan(F(1.0))));
  EXPECT_TRUE(bo(fp_is_neg(F(-1.0))));
  EXPECT_FALSE(bo(fp_is_neg(tm.mk_fp_nan(f32))));
  EXPECT_TRUE(bo(fp_is_pos(F(1.0))));
  EXPECT_FALSE(bo(fp_is_pos(tm.mk_fp_neg_zero(f32))));
  // construction and conversion
  EXPECT_EQ(d(tm.mk_fp(tm.mk_bv(1, 0), tm.mk_bv(8, 127), tm.mk_bv(23, 0))), 1.0);
  EXPECT_EQ(d(to_fp_from_bits(f32, tm.mk_bv(32, 0x3fc00000))), 1.5);
  EXPECT_EQ(d(to_fp(f32, RoundingMode::RNE, tm.mk_fp(f64, RoundingMode::RNE, 1.5))), 1.5);
  EXPECT_EQ(d(to_fp(f64, RoundingMode::RNE, F(1.5))), 1.5);
  EXPECT_EQ(d(to_fp(f32, RoundingMode::RNE, tm.mk_bv_signed(8, -3))), -3.0);
  EXPECT_EQ(d(to_fp_unsigned(f32, RoundingMode::RNE, B(0xff))), 255.0);
  EXPECT_EQ(d(to_fp(f32, RoundingMode::RNE, B(0xff))), -1.0);
  EXPECT_EQ(d(to_fp(f32, RoundingMode::RNE, Q(1, 4))), 0.25);
  EXPECT_EQ(u(fp_to_ubv(8, RoundingMode::RTZ, F(3.7))), 3u);
  EXPECT_EQ(u(fp_to_ubv(8, RoundingMode::RNE, F(3.7))), 4u);
  EXPECT_EQ(ev(fp_to_sbv(8, RoundingMode::RTZ, F(-3.7))).to_int64(), -3);
  EXPECT_EQ(ev(fp_to_sbv(8, RoundingMode::RTN, F(-3.7))).to_int64(), -4);
  EXPECT_EQ(u(fp_to_ieee_bv(F(1.0))), 0x3f800000u);
  EXPECT_EQ(u(fp_to_ieee_bv(tm.mk_fp_nan(f32))), 0x7fc00000u);
}

TEST_F(KindValues, reals)
{
  EXPECT_EQ(q(real_add(Q(1, 2), Q(1, 3))), "5/6");
  EXPECT_EQ(q(real_add({Q(1, 2), Q(1, 3), Q(1, 6)})), "1");
  EXPECT_EQ(q(real_sub(Q(1, 1), Q(1, 3))), "2/3");
  EXPECT_EQ(q(real_neg(Q(1, 2))), "-1/2");
  EXPECT_EQ(q(real_mul(Q(2, 1), Q(1, 3))), "2/3");
  EXPECT_EQ(q(real_div(Q(1, 1), Q(3, 1))), "1/3");
  EXPECT_EQ(q(Q(1, 2) + Q(1, 2)), "1");
  EXPECT_EQ(q(Q(1, 2) - Q(1, 3)), "1/6");
  EXPECT_EQ(q(Q(1, 2) * 3), "3/2");
  EXPECT_EQ(q(Q(3, 2) / 3), "1/2");
  EXPECT_EQ(q(-Q(3, 2)), "-3/2");
  EXPECT_TRUE(bo(real_lt(Q(1, 3), Q(1, 2))));
  EXPECT_FALSE(bo(real_lt(Q(1, 2), Q(1, 2))));
  EXPECT_TRUE(bo(real_le(Q(1, 2), Q(1, 2))));
  EXPECT_FALSE(bo(real_gt(Q(1, 1), Q(2, 1))));
  EXPECT_TRUE(bo(real_ge(Q(1, 1), Q(1, 1))));
}

// A symbolic instance of every theory, solved and read back, so that the
// kinds are not only folded but also blasted.
TEST(KindsSolved, every_theory_round_trip)
{
  TermManager tm;
  Solver s(tm);
  const Sort bv8 = tm.mk_bv_sort(8), f32 = tm.mk_fp32_sort(), R = tm.mk_real_sort();
  const Sort A = tm.mk_array_sort(bv8, bv8), S = tm.declare_sort("S");
  const Term x = tm.declare("x", bv8), y = tm.declare("y", bv8);
  const Term fx = tm.declare("fx", f32);
  const Term rx = tm.declare("rx", R);
  const Term ar = tm.declare("ar", A);
  const Term p = tm.declare("p", S), q = tm.declare("q", S);
  const Term f = tm.declare("f", tm.mk_fun_sort({bv8}, bv8));
  const Term rm = tm.declare("rm", tm.mk_rm_sort());
  s.add(bvmul(x, y) == 6);
  s.add(bvult(x, y));
  s.add(bvugt(x, 1));
  s.add(fp_eq(fp_mul(rm, fx, fx), tm.mk_fp(f32, RoundingMode::RNE, 2.25)));
  s.add(fp_is_pos(fx));
  s.add(real_gt(rx, 1));
  s.add(real_lt(rx * 2, 3));
  s.add(ar[x] == y);
  s.add(distinct(p, q));
  s.add(f(x) == bvadd(x, 1));
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  const std::uint64_t xv = m.uint64_value(x), yv = m.uint64_value(y);
  EXPECT_EQ((xv * yv) & 0xff, 6u);
  EXPECT_LT(xv, yv);
  EXPECT_EQ(m.fp_value(fx).to_double(), std::optional<double>(1.5));
  const RationalValue r = m.real_value(rx);
  EXPECT_GT(r.to_double(), 1.0);
  EXPECT_LT(r.to_double(), 1.5);
  EXPECT_EQ(m.uint64_value(ar[x]), yv);
  EXPECT_NE(m.uninterpreted_index(p), m.uninterpreted_index(q));
  EXPECT_EQ(m.uint64_value(f(x)), (xv + 1) & 0xff);
  EXPECT_TRUE(m.bool_value(fp_eq(fp_mul(m.value(rm), fx, fx), tm.mk_fp(f32, RoundingMode::RNE, 2.25))));
}

} // namespace
