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

// Every stp_kind through stp_mk_term: the structure under a non-simplifying
// manager (kind, children, indices, as the public view describes them) and
// the value every kind computes under the default manager.

#include <stp/stp.h>

#include <gtest/gtest.h>

#include <cstring>
#include <string>
#include <vector>

namespace
{

std::string str(stp_term t)
{
  char* s = stp_term_str(t);
  std::string out = s ? s : "<null>";
  stp_free(s);
  return out;
}

std::string pending(stp_tm tm)
{
  const stp_error* e = stp_tm_error(tm);
  std::string out = e ? e->message : "(no error)";
  stp_tm_clear_error(tm);
  return out;
}

// The symbols every kind is built over.
struct Symbols
{
  stp_sort boolean, bv1, bv8, bv23, bv32, f32, f64, rm, real, arr, fun, S;
  stp_term b1, b2, x, y, s1, m23, w32, f1, f2, f3, d1, rmv, r1, r2, rval, rne, a, fn, c9;
  void declare(stp_tm tm)
  {
    boolean = stp_mk_bool_sort(tm);
    bv1 = stp_mk_bv_sort(tm, 1);
    bv8 = stp_mk_bv_sort(tm, 8);
    bv23 = stp_mk_bv_sort(tm, 23);
    bv32 = stp_mk_bv_sort(tm, 32);
    f32 = stp_mk_fp32_sort(tm);
    f64 = stp_mk_fp64_sort(tm);
    rm = stp_mk_rm_sort(tm);
    real = stp_mk_real_sort(tm);
    arr = stp_mk_array_sort(tm, bv8, bv8);
    const stp_sort dom[2] = {bv8, bv8};
    fun = stp_mk_fun_sort(tm, 2, dom, bv8);
    S = stp_tm_declare_sort(tm, "S");
    b1 = stp_declare(tm, "b1", boolean);
    b2 = stp_declare(tm, "b2", boolean);
    x = stp_declare(tm, "x", bv8);
    y = stp_declare(tm, "y", bv8);
    s1 = stp_declare(tm, "s1", bv1);
    m23 = stp_declare(tm, "m23", bv23);
    w32 = stp_declare(tm, "w32", bv32);
    f1 = stp_declare(tm, "f1", f32);
    f2 = stp_declare(tm, "f2", f32);
    f3 = stp_declare(tm, "f3", f32);
    d1 = stp_declare(tm, "d1", f64);
    rmv = stp_declare(tm, "rmv", rm);
    r1 = stp_declare(tm, "r1", real);
    r2 = stp_declare(tm, "r2", real);
    rval = stp_mk_real_int64(tm, 2);
    rne = stp_mk_rm(tm, STP_RM_RNE);
    a = stp_declare(tm, "a", arr);
    fn = stp_declare(tm, "fn", fun);
    c9 = stp_mk_bv_uint64(tm, 8, 9); // a value, as a constant array's default must be
  }
};

struct Structure
{
  stp_kind kind;
  std::vector<stp_term> args;
  std::vector<uint32_t> idx;
  stp_sort result;
  int view;             // the public kind expected; -1: any, -2: FP_FP or FP_TO_FP_FROM_BV
  std::size_t children; // expected children; SIZE_MAX: not checked
};

const std::size_t ANY = static_cast<std::size_t>(-1);

} // namespace

TEST(c_kinds, every_kind_has_its_structure_under_simplify_off)
{
  stp_tm tm = stp_tm_new_with(false, STP_RM_RNE, 16);
  ASSERT_NE(nullptr, tm);
  ASSERT_FALSE(stp_tm_simplify_enabled(tm));
  stp_tm_scope_push(tm);
  Symbols s;
  s.declare(tm);
  ASSERT_NE(nullptr, s.fn) << pending(tm);

  const std::vector<Structure> cases = {
      {STP_KIND_ITE, {s.b1, s.x, s.y}, {}, nullptr, STP_KIND_ITE, 3},
      {STP_KIND_EQUAL, {s.x, s.y}, {}, nullptr, STP_KIND_EQUAL, 2},
      {STP_KIND_DISTINCT, {s.x, s.y}, {}, nullptr, STP_KIND_DISTINCT, 2},
      {STP_KIND_APPLY, {s.fn, s.x, s.y}, {}, nullptr, STP_KIND_APPLY, ANY},
      {STP_KIND_NOT, {s.b1}, {}, nullptr, STP_KIND_NOT, 1},
      {STP_KIND_AND, {s.b1, s.b2}, {}, nullptr, STP_KIND_AND, 2},
      {STP_KIND_OR, {s.b1, s.b2}, {}, nullptr, STP_KIND_OR, 2},
      {STP_KIND_XOR, {s.b1, s.b2}, {}, nullptr, STP_KIND_XOR, 2},
      {STP_KIND_IMPLIES, {s.b1, s.b2}, {}, nullptr, STP_KIND_IMPLIES, 2},
      {STP_KIND_BV_NOT, {s.x}, {}, nullptr, STP_KIND_BV_NOT, 1},
      {STP_KIND_BV_AND, {s.x, s.y}, {}, nullptr, STP_KIND_BV_AND, 2},
      {STP_KIND_BV_OR, {s.x, s.y}, {}, nullptr, STP_KIND_BV_OR, 2},
      {STP_KIND_BV_XOR, {s.x, s.y}, {}, nullptr, STP_KIND_BV_XOR, 2},
      // the derived bitwise kinds read as NOT over the base kind
      {STP_KIND_BV_NAND, {s.x, s.y}, {}, nullptr, STP_KIND_BV_NOT, 1},
      {STP_KIND_BV_NOR, {s.x, s.y}, {}, nullptr, STP_KIND_BV_NOT, 1},
      {STP_KIND_BV_XNOR, {s.x, s.y}, {}, nullptr, STP_KIND_BV_NOT, 1},
      {STP_KIND_BV_NEG, {s.x}, {}, nullptr, STP_KIND_BV_NEG, 1},
      {STP_KIND_BV_ADD, {s.x, s.y}, {}, nullptr, STP_KIND_BV_ADD, 2},
      {STP_KIND_BV_SUB, {s.x, s.y}, {}, nullptr, STP_KIND_BV_SUB, 2},
      {STP_KIND_BV_MUL, {s.x, s.y}, {}, nullptr, STP_KIND_BV_MUL, 2},
      {STP_KIND_BV_UDIV, {s.x, s.y}, {}, nullptr, STP_KIND_BV_UDIV, 2},
      {STP_KIND_BV_UREM, {s.x, s.y}, {}, nullptr, STP_KIND_BV_UREM, 2},
      {STP_KIND_BV_SDIV, {s.x, s.y}, {}, nullptr, STP_KIND_BV_SDIV, 2},
      {STP_KIND_BV_SREM, {s.x, s.y}, {}, nullptr, STP_KIND_BV_SREM, 2},
      {STP_KIND_BV_SMOD, {s.x, s.y}, {}, nullptr, STP_KIND_BV_SMOD, 2},
      {STP_KIND_BV_SHL, {s.x, s.y}, {}, nullptr, STP_KIND_BV_SHL, 2},
      {STP_KIND_BV_LSHR, {s.x, s.y}, {}, nullptr, STP_KIND_BV_LSHR, 2},
      {STP_KIND_BV_ASHR, {s.x, s.y}, {}, nullptr, STP_KIND_BV_ASHR, 2},
      {STP_KIND_BV_CONCAT, {s.x, s.y}, {}, nullptr, STP_KIND_BV_CONCAT, 2},
      {STP_KIND_BV_EXTRACT, {s.x}, {3, 0}, nullptr, STP_KIND_BV_EXTRACT, 1},
      {STP_KIND_BV_ZERO_EXTEND, {s.x}, {8}, nullptr, STP_KIND_BV_ZERO_EXTEND, 1},
      {STP_KIND_BV_SIGN_EXTEND, {s.x}, {8}, nullptr, STP_KIND_BV_SIGN_EXTEND, 1},
      // repeat and the rotates are concatenations of extracts
      {STP_KIND_BV_REPEAT, {s.x}, {2}, nullptr, STP_KIND_BV_CONCAT, 2},
      {STP_KIND_BV_ROTATE_LEFT, {s.x}, {3}, nullptr, STP_KIND_BV_CONCAT, 2},
      {STP_KIND_BV_ROTATE_RIGHT, {s.x}, {3}, nullptr, STP_KIND_BV_CONCAT, 2},
      {STP_KIND_BV_COMP, {s.x, s.y}, {}, nullptr, STP_KIND_ITE, 3},
      {STP_KIND_BV_ULT, {s.x, s.y}, {}, nullptr, STP_KIND_BV_ULT, 2},
      {STP_KIND_BV_ULE, {s.x, s.y}, {}, nullptr, STP_KIND_BV_ULE, 2},
      {STP_KIND_BV_UGT, {s.x, s.y}, {}, nullptr, STP_KIND_BV_UGT, 2},
      {STP_KIND_BV_UGE, {s.x, s.y}, {}, nullptr, STP_KIND_BV_UGE, 2},
      {STP_KIND_BV_SLT, {s.x, s.y}, {}, nullptr, STP_KIND_BV_SLT, 2},
      {STP_KIND_BV_SLE, {s.x, s.y}, {}, nullptr, STP_KIND_BV_SLE, 2},
      {STP_KIND_BV_SGT, {s.x, s.y}, {}, nullptr, STP_KIND_BV_SGT, 2},
      {STP_KIND_BV_SGE, {s.x, s.y}, {}, nullptr, STP_KIND_BV_SGE, 2},
      {STP_KIND_BV_UADDO, {s.x, s.y}, {}, nullptr, STP_KIND_BV_UADDO, 2},
      {STP_KIND_BV_SADDO, {s.x, s.y}, {}, nullptr, STP_KIND_BV_SADDO, 2},
      {STP_KIND_BV_UMULO, {s.x, s.y}, {}, nullptr, STP_KIND_BV_UMULO, 2},
      {STP_KIND_BV_SMULO, {s.x, s.y}, {}, nullptr, STP_KIND_BV_SMULO, 2},
      {STP_KIND_BV_USUBO, {s.x, s.y}, {}, nullptr, STP_KIND_BV_USUBO, 2},
      {STP_KIND_BV_SSUBO, {s.x, s.y}, {}, nullptr, STP_KIND_BV_SSUBO, 2},
      {STP_KIND_BV_NEGO, {s.x}, {}, nullptr, STP_KIND_EQUAL, 2},
      {STP_KIND_BV_SDIVO, {s.x, s.y}, {}, nullptr, STP_KIND_AND, 2},
      {STP_KIND_BV_REDAND, {s.x}, {}, nullptr, STP_KIND_ITE, 3},
      {STP_KIND_BV_REDOR, {s.x}, {}, nullptr, STP_KIND_ITE, 3},
      {STP_KIND_SELECT, {s.a, s.x}, {}, nullptr, STP_KIND_SELECT, 2},
      {STP_KIND_STORE, {s.a, s.x, s.y}, {}, nullptr, STP_KIND_STORE, 3},
      {STP_KIND_CONST_ARRAY, {s.c9}, {}, s.arr, STP_KIND_CONST_ARRAY, 1},
      {STP_KIND_FP_ABS, {s.f1}, {}, nullptr, STP_KIND_FP_ABS, 1},
      {STP_KIND_FP_NEG, {s.f1}, {}, nullptr, STP_KIND_FP_NEG, 1},
      {STP_KIND_FP_ADD, {s.rmv, s.f1, s.f2}, {}, nullptr, STP_KIND_FP_ADD, 3},
      {STP_KIND_FP_SUB, {s.rmv, s.f1, s.f2}, {}, nullptr, STP_KIND_FP_SUB, 3},
      {STP_KIND_FP_MUL, {s.rmv, s.f1, s.f2}, {}, nullptr, STP_KIND_FP_MUL, 3},
      {STP_KIND_FP_DIV, {s.rmv, s.f1, s.f2}, {}, nullptr, STP_KIND_FP_DIV, 3},
      {STP_KIND_FP_FMA, {s.rmv, s.f1, s.f2, s.f3}, {}, nullptr, STP_KIND_FP_FMA, 4},
      {STP_KIND_FP_SQRT, {s.rmv, s.f1}, {}, nullptr, STP_KIND_FP_SQRT, 2},
      {STP_KIND_FP_REM, {s.f1, s.f2}, {}, nullptr, STP_KIND_FP_REM, 2},
      {STP_KIND_FP_RTI, {s.rmv, s.f1}, {}, nullptr, STP_KIND_FP_RTI, 2},
      {STP_KIND_FP_MIN, {s.f1, s.f2}, {}, nullptr, STP_KIND_FP_MIN, 2},
      {STP_KIND_FP_MAX, {s.f1, s.f2}, {}, nullptr, STP_KIND_FP_MAX, 2},
      {STP_KIND_FP_EQ, {s.f1, s.f2}, {}, nullptr, STP_KIND_FP_EQ, 2},
      {STP_KIND_FP_LT, {s.f1, s.f2}, {}, nullptr, STP_KIND_FP_LT, 2},
      {STP_KIND_FP_LEQ, {s.f1, s.f2}, {}, nullptr, STP_KIND_FP_LEQ, 2},
      {STP_KIND_FP_GT, {s.f1, s.f2}, {}, nullptr, STP_KIND_FP_GT, 2},
      {STP_KIND_FP_GEQ, {s.f1, s.f2}, {}, nullptr, STP_KIND_FP_GEQ, 2},
      {STP_KIND_FP_IS_NORMAL, {s.f1}, {}, nullptr, STP_KIND_FP_IS_NORMAL, 1},
      {STP_KIND_FP_IS_SUBNORMAL, {s.f1}, {}, nullptr, STP_KIND_FP_IS_SUBNORMAL, 1},
      {STP_KIND_FP_IS_ZERO, {s.f1}, {}, nullptr, STP_KIND_FP_IS_ZERO, 1},
      {STP_KIND_FP_IS_INF, {s.f1}, {}, nullptr, STP_KIND_FP_IS_INF, 1},
      {STP_KIND_FP_IS_NAN, {s.f1}, {}, nullptr, STP_KIND_FP_IS_NAN, 1},
      {STP_KIND_FP_IS_NEG, {s.f1}, {}, nullptr, STP_KIND_FP_IS_NEG, 1},
      {STP_KIND_FP_IS_POS, {s.f1}, {}, nullptr, STP_KIND_FP_IS_POS, 1},
      {STP_KIND_FP_FP, {s.s1, s.x, s.m23}, {}, nullptr, -2, ANY},
      {STP_KIND_FP_TO_FP_FROM_BV, {s.w32}, {8, 24}, nullptr, STP_KIND_FP_TO_FP_FROM_BV, 1},
      {STP_KIND_FP_TO_FP_FROM_FP, {s.rmv, s.d1}, {8, 24}, nullptr, STP_KIND_FP_TO_FP_FROM_FP, 2},
      {STP_KIND_FP_TO_FP_FROM_SBV, {s.rmv, s.x}, {8, 24}, nullptr, STP_KIND_FP_TO_FP_FROM_SBV, 2},
      {STP_KIND_FP_TO_FP_FROM_UBV, {s.rmv, s.x}, {8, 24}, nullptr, STP_KIND_FP_TO_FP_FROM_UBV, 2},
      // the Real operand and the mode must be values; the conversion folds to one
      {STP_KIND_FP_TO_FP_FROM_REAL, {s.rne, s.rval}, {8, 24}, nullptr, STP_KIND_VALUE, 0},
      {STP_KIND_FP_TO_UBV, {s.rmv, s.f1}, {8}, nullptr, STP_KIND_FP_TO_UBV, 2},
      {STP_KIND_FP_TO_SBV, {s.rmv, s.f1}, {8}, nullptr, STP_KIND_FP_TO_SBV, 2},
      {STP_KIND_FP_TO_IEEE_BV, {s.f1}, {}, nullptr, STP_KIND_FP_TO_IEEE_BV, 1},
      {STP_KIND_FP_TO_REAL, {s.f1}, {}, nullptr, STP_KIND_FP_TO_REAL, 1},
      {STP_KIND_REAL_ADD, {s.r1, s.r2}, {}, nullptr, STP_KIND_REAL_ADD, 2},
      {STP_KIND_REAL_SUB, {s.r1, s.r2}, {}, nullptr, STP_KIND_REAL_SUB, 2},
      {STP_KIND_REAL_NEG, {s.r1}, {}, nullptr, STP_KIND_REAL_NEG, 1},
      {STP_KIND_REAL_MUL, {s.r1, s.rval}, {}, nullptr, STP_KIND_REAL_MUL, 2},
      {STP_KIND_REAL_DIV, {s.r1, s.rval}, {}, nullptr, STP_KIND_REAL_DIV, 2},
      {STP_KIND_REAL_LT, {s.r1, s.r2}, {}, nullptr, STP_KIND_REAL_LT, 2},
      {STP_KIND_REAL_LE, {s.r1, s.r2}, {}, nullptr, STP_KIND_REAL_LE, 2},
      {STP_KIND_REAL_GT, {s.r1, s.r2}, {}, nullptr, STP_KIND_REAL_GT, 2},
      {STP_KIND_REAL_GE, {s.r1, s.r2}, {}, nullptr, STP_KIND_REAL_GE, 2},
  };

  std::vector<bool> covered(STP_NUM_KINDS, false);
  for (const Structure& c : cases)
  {
    SCOPED_TRACE(stp_kind_name(c.kind));
    covered[c.kind] = true;
    stp_term t = stp_mk_term_sorted(tm, c.kind, c.args.size(), c.args.data(), c.idx.size(),
                                    c.idx.data(), c.result);
    ASSERT_NE(nullptr, t) << pending(tm);
    EXPECT_EQ(nullptr, stp_tm_error(tm)) << pending(tm);
    stp_kind k;
    ASSERT_EQ(STP_OK, stp_term_get_kind(t, &k)) << pending(tm);
    if (c.view == -2)
    {
      EXPECT_TRUE(k == STP_KIND_FP_FP || k == STP_KIND_FP_TO_FP_FROM_BV) << stp_kind_name(k);
    }
    else if (c.view >= 0)
    {
      EXPECT_EQ(c.view, static_cast<int>(k)) << "got " << stp_kind_name(k) << " for " << str(t);
    }
    if (c.children != ANY)
    {
      size_t n = 0;
      ASSERT_EQ(STP_OK, stp_term_num_children(t, &n));
      EXPECT_EQ(c.children, n) << str(t);
      for (size_t i = 0; i < n; ++i)
        EXPECT_NE(nullptr, stp_term_child(t, i));
      EXPECT_EQ(nullptr, stp_term_child(t, n));
      EXPECT_EQ(STP_ERR_INDEX_OUT_OF_RANGE, stp_tm_error(tm)->code);
      stp_tm_clear_error(tm);
    }
    if (c.view == static_cast<int>(c.kind) && !c.idx.empty())
    {
      size_t n = 0;
      ASSERT_EQ(STP_OK, stp_term_num_indices(t, &n));
      ASSERT_EQ(c.idx.size(), n);
      for (size_t i = 0; i < n; ++i)
      {
        uint32_t v = 0;
        ASSERT_EQ(STP_OK, stp_term_index(t, i, &v));
        EXPECT_EQ(c.idx[i], v);
      }
    }
    // the sort of every result is a live sort handle of this manager
    stp_sort so = stp_term_sort(t);
    ASSERT_NE(nullptr, so);
    char* text = stp_sort_str(so);
    EXPECT_NE(nullptr, text);
    stp_free(text);
  }

  // the kinds no mk_term builds
  covered[STP_KIND_VALUE] = covered[STP_KIND_CONSTANT] = true;
  EXPECT_EQ(nullptr, stp_mk_term(tm, STP_KIND_VALUE, 0, nullptr));
  EXPECT_NE(nullptr, stp_tm_error(tm));
  stp_tm_clear_error(tm);
  EXPECT_EQ(nullptr, stp_mk_term(tm, STP_KIND_CONSTANT, 0, nullptr));
  EXPECT_NE(nullptr, stp_tm_error(tm));
  stp_tm_clear_error(tm);
  EXPECT_EQ(nullptr, stp_mk_term1(tm, STP_NUM_KINDS, s.f1));
  ASSERT_NE(nullptr, stp_tm_error(tm));
  EXPECT_EQ(STP_ERR_INVALID_ARGUMENT, stp_tm_error(tm)->code);
  stp_tm_clear_error(tm);
  stp_kind k;
  EXPECT_EQ(STP_OK, stp_term_get_kind(s.x, &k));
  EXPECT_EQ(STP_KIND_CONSTANT, k);
  EXPECT_EQ(STP_OK, stp_term_get_kind(s.rval, &k));
  EXPECT_EQ(STP_KIND_VALUE, k);

  for (int i = 0; i < STP_NUM_KINDS; ++i)
    EXPECT_TRUE(covered[i]) << "kind not walked: " << stp_kind_name(static_cast<stp_kind>(i));

  stp_tm_scope_pop(tm);
  stp_tm_release(tm);
}

TEST(c_kinds, arity_and_sort_errors_are_recorded)
{
  stp_tm tm = stp_tm_new_with(false, STP_RM_RNE, 16);
  stp_tm_scope_push(tm);
  Symbols s;
  s.declare(tm);
  // wrong arity
  EXPECT_EQ(nullptr, stp_mk_term1(tm, STP_KIND_BV_ADD, s.x));
  ASSERT_NE(nullptr, stp_tm_error(tm));
  EXPECT_EQ(STP_ERR_ARITY, stp_tm_error(tm)->code);
  stp_tm_clear_error(tm);
  // wrong sort, with the argument named
  EXPECT_EQ(nullptr, stp_mk_term2(tm, STP_KIND_BV_ADD, s.x, s.b1));
  ASSERT_NE(nullptr, stp_tm_error(tm));
  EXPECT_EQ(STP_ERR_SORT_MISMATCH, stp_tm_error(tm)->code);
  EXPECT_GE(stp_tm_error_num_terms(tm), 1u);
  stp_tm_clear_error(tm);
  // a missing index
  EXPECT_EQ(nullptr, stp_mk_term1(tm, STP_KIND_BV_EXTRACT, s.x));
  ASSERT_NE(nullptr, stp_tm_error(tm));
  stp_tm_clear_error(tm);
  // CONST_ARRAY without its sort
  EXPECT_EQ(nullptr, stp_mk_term1(tm, STP_KIND_CONST_ARRAY, s.x));
  ASSERT_NE(nullptr, stp_tm_error(tm));
  EXPECT_EQ(STP_ERR_INVALID_ARGUMENT, stp_tm_error(tm)->code);
  stp_tm_clear_error(tm);
  // a NULL inside the argument array propagates silently
  const stp_term args[2] = {s.x, nullptr};
  EXPECT_EQ(nullptr, stp_mk_term(tm, STP_KIND_BV_ADD, 2, args));
  EXPECT_EQ(nullptr, stp_tm_error(tm));
  stp_tm_scope_pop(tm);
  stp_tm_release(tm);
}

TEST(c_kinds, named_constructors_build_the_same_nodes)
{
  stp_tm tm = stp_tm_new_with(false, STP_RM_RNE, 16);
  stp_tm_scope_push(tm);
  Symbols s;
  s.declare(tm);
  EXPECT_EQ(stp_bvadd(tm, s.x, s.y), stp_mk_term2(tm, STP_KIND_BV_ADD, s.x, s.y));
  EXPECT_EQ(stp_and2(tm, s.b1, s.b2), stp_mk_term2(tm, STP_KIND_AND, s.b1, s.b2));
  EXPECT_EQ(stp_extract(tm, 3, 0, s.x), stp_mk_term1_indexed2(tm, STP_KIND_BV_EXTRACT, s.x, 3, 0));
  EXPECT_EQ(stp_zero_extend(tm, 8, s.x), stp_mk_term1_indexed1(tm, STP_KIND_BV_ZERO_EXTEND, s.x, 8));
  EXPECT_EQ(stp_fp_add(tm, s.rmv, s.f1, s.f2), stp_mk_term3(tm, STP_KIND_FP_ADD, s.rmv, s.f1, s.f2));
  EXPECT_EQ(stp_fp_add_rm(tm, STP_RM_RTZ, s.f1, s.f2),
            stp_mk_term3(tm, STP_KIND_FP_ADD, stp_mk_rm(tm, STP_RM_RTZ), s.f1, s.f2));
  EXPECT_EQ(stp_fp_to_ubv(tm, 8, s.rmv, s.f1), stp_mk_term2_indexed1(tm, STP_KIND_FP_TO_UBV, s.rmv, s.f1, 8));
  EXPECT_EQ(stp_to_fp(tm, s.f32, s.rmv, s.x),
            stp_mk_term2_indexed2(tm, STP_KIND_FP_TO_FP_FROM_SBV, s.rmv, s.x, 8, 24));
  EXPECT_EQ(stp_to_fp_unsigned(tm, s.f32, s.rmv, s.x),
            stp_mk_term2_indexed2(tm, STP_KIND_FP_TO_FP_FROM_UBV, s.rmv, s.x, 8, 24));
  EXPECT_EQ(stp_to_fp_from_bits(tm, s.f32, s.w32),
            stp_mk_term1_indexed2(tm, STP_KIND_FP_TO_FP_FROM_BV, s.w32, 8, 24));
  const stp_term three[3] = {s.b1, s.b2, s.b1};
  EXPECT_NE(nullptr, stp_and(tm, 3, three));
  EXPECT_NE(nullptr, stp_or(tm, 3, three));
  EXPECT_NE(nullptr, stp_xor(tm, 3, three));
  EXPECT_NE(nullptr, stp_distinct(tm, 2, three));
  const stp_term bvs[3] = {s.x, s.y, s.x};
  EXPECT_NE(nullptr, stp_bvadd_n(tm, 3, bvs));
  EXPECT_NE(nullptr, stp_concat_n(tm, 3, bvs));
  const stp_term app[3] = {s.fn, s.x, s.y};
  EXPECT_EQ(stp_apply_n(tm, 3, app), stp_mk_term(tm, STP_KIND_APPLY, 3, app));
  EXPECT_NE(nullptr, stp_bit(tm, s.x, 3));
  EXPECT_NE(nullptr, stp_bool_to_bv1(tm, s.b1));
  EXPECT_NE(nullptr, stp_bv1_to_bool(tm, s.s1));
  EXPECT_EQ(nullptr, stp_tm_error(tm)) << pending(tm);
  stp_tm_scope_pop(tm);
  stp_tm_release(tm);
}

namespace
{
// Every kind computes: under the default (simplifying) manager the term over
// values folds to a value, which must be the expected one; where it does not
// fold, the solver must find the equality valid.
struct Values
{
  stp_tm tm;
  stp_solver s;
  int folded = 0, proved = 0;

  void expect(stp_kind kind, std::vector<stp_term> args, std::vector<uint32_t> idx, stp_sort result,
              stp_term expected)
  {
    SCOPED_TRACE(stp_kind_name(kind));
    ASSERT_NE(nullptr, expected) << pending(tm);
    stp_term t = stp_mk_term_sorted(tm, kind, args.size(), args.data(), idx.size(), idx.data(), result);
    ASSERT_NE(nullptr, t) << pending(tm);
    if (stp_term_is_value(t))
    {
      ++folded;
      EXPECT_EQ(expected, t) << "got " << str(t) << ", expected " << str(expected);
      return;
    }
    ++proved;
    stp_entailment e;
    ASSERT_EQ(STP_OK, stp_solver_entails(s, stp_eq(tm, t, expected), nullptr, &e)) << pending(tm);
    EXPECT_EQ(STP_VALID, e.kind) << str(t) << " != " << str(expected);
  }
};
} // namespace

TEST(c_kinds, every_kind_computes_its_value)
{
  Values v;
  v.tm = stp_tm_new(nullptr);
  ASSERT_NE(nullptr, v.tm);
  stp_tm_scope_push(v.tm);
  v.s = stp_solver_new(v.tm, nullptr);
  ASSERT_NE(nullptr, v.s);
  stp_tm tm = v.tm;
  auto bv = [&](uint32_t w, uint64_t val) { return stp_mk_bv_uint64(tm, w, val); };
  auto fp = [&](double d) { return stp_mk_fp_double(tm, stp_mk_fp32_sort(tm), STP_RM_RNE, d); };
  auto re = [&](const char* lit) { return stp_mk_real_str(tm, lit); };
  stp_term T = stp_mk_true(tm), F = stp_mk_false(tm);
  stp_term rne = stp_mk_rm(tm, STP_RM_RNE), rtz = stp_mk_rm(tm, STP_RM_RTZ);
  stp_sort f32 = stp_mk_fp32_sort(tm);
  stp_sort arr = stp_mk_array_sort(tm, stp_mk_bv_sort(tm, 8), stp_mk_bv_sort(tm, 8));

  v.expect(STP_KIND_ITE, {T, bv(8, 3), bv(8, 4)}, {}, nullptr, bv(8, 3));
  v.expect(STP_KIND_EQUAL, {bv(8, 3), bv(8, 3)}, {}, nullptr, T);
  v.expect(STP_KIND_DISTINCT, {bv(8, 3), bv(8, 4)}, {}, nullptr, T);
  v.expect(STP_KIND_NOT, {T}, {}, nullptr, F);
  v.expect(STP_KIND_AND, {T, F}, {}, nullptr, F);
  v.expect(STP_KIND_OR, {T, F}, {}, nullptr, T);
  v.expect(STP_KIND_XOR, {T, T}, {}, nullptr, F);
  v.expect(STP_KIND_IMPLIES, {T, F}, {}, nullptr, F);
  v.expect(STP_KIND_BV_NOT, {bv(8, 0x0f)}, {}, nullptr, bv(8, 0xf0));
  v.expect(STP_KIND_BV_AND, {bv(8, 0x0f), bv(8, 0x3c)}, {}, nullptr, bv(8, 0x0c));
  v.expect(STP_KIND_BV_OR, {bv(8, 0x0f), bv(8, 0x3c)}, {}, nullptr, bv(8, 0x3f));
  v.expect(STP_KIND_BV_XOR, {bv(8, 0x0f), bv(8, 0x3c)}, {}, nullptr, bv(8, 0x33));
  v.expect(STP_KIND_BV_NAND, {bv(8, 0x0f), bv(8, 0x3c)}, {}, nullptr, bv(8, 0xf3));
  v.expect(STP_KIND_BV_NOR, {bv(8, 0x0f), bv(8, 0x3c)}, {}, nullptr, bv(8, 0xc0));
  v.expect(STP_KIND_BV_XNOR, {bv(8, 0x0f), bv(8, 0x3c)}, {}, nullptr, bv(8, 0xcc));
  v.expect(STP_KIND_BV_NEG, {bv(8, 1)}, {}, nullptr, bv(8, 0xff));
  v.expect(STP_KIND_BV_ADD, {bv(8, 3), bv(8, 4)}, {}, nullptr, bv(8, 7));
  v.expect(STP_KIND_BV_SUB, {bv(8, 3), bv(8, 4)}, {}, nullptr, bv(8, 0xff));
  v.expect(STP_KIND_BV_MUL, {bv(8, 3), bv(8, 4)}, {}, nullptr, bv(8, 12));
  v.expect(STP_KIND_BV_UDIV, {bv(8, 7), bv(8, 2)}, {}, nullptr, bv(8, 3));
  v.expect(STP_KIND_BV_UREM, {bv(8, 7), bv(8, 2)}, {}, nullptr, bv(8, 1));
  v.expect(STP_KIND_BV_SDIV, {bv(8, 0xf9), bv(8, 2)}, {}, nullptr, bv(8, 0xfd));
  v.expect(STP_KIND_BV_SREM, {bv(8, 0xf9), bv(8, 2)}, {}, nullptr, bv(8, 0xff));
  v.expect(STP_KIND_BV_SMOD, {bv(8, 0xf9), bv(8, 2)}, {}, nullptr, bv(8, 1));
  v.expect(STP_KIND_BV_SHL, {bv(8, 1), bv(8, 3)}, {}, nullptr, bv(8, 8));
  v.expect(STP_KIND_BV_LSHR, {bv(8, 0x80), bv(8, 7)}, {}, nullptr, bv(8, 1));
  v.expect(STP_KIND_BV_ASHR, {bv(8, 0x80), bv(8, 7)}, {}, nullptr, bv(8, 0xff));
  v.expect(STP_KIND_BV_CONCAT, {bv(4, 0xa), bv(4, 0xb)}, {}, nullptr, bv(8, 0xab));
  v.expect(STP_KIND_BV_EXTRACT, {bv(8, 0xab)}, {7, 4}, nullptr, bv(4, 0xa));
  v.expect(STP_KIND_BV_ZERO_EXTEND, {bv(8, 0xab)}, {8}, nullptr, bv(16, 0x00ab));
  v.expect(STP_KIND_BV_SIGN_EXTEND, {bv(8, 0xab)}, {8}, nullptr, bv(16, 0xffab));
  v.expect(STP_KIND_BV_REPEAT, {bv(8, 0xab)}, {2}, nullptr, bv(16, 0xabab));
  v.expect(STP_KIND_BV_ROTATE_LEFT, {bv(8, 0x81)}, {1}, nullptr, bv(8, 0x03));
  v.expect(STP_KIND_BV_ROTATE_RIGHT, {bv(8, 0x81)}, {1}, nullptr, bv(8, 0xc0));
  v.expect(STP_KIND_BV_COMP, {bv(8, 3), bv(8, 3)}, {}, nullptr, bv(1, 1));
  v.expect(STP_KIND_BV_ULT, {bv(8, 3), bv(8, 4)}, {}, nullptr, T);
  v.expect(STP_KIND_BV_ULE, {bv(8, 4), bv(8, 4)}, {}, nullptr, T);
  v.expect(STP_KIND_BV_UGT, {bv(8, 4), bv(8, 3)}, {}, nullptr, T);
  v.expect(STP_KIND_BV_UGE, {bv(8, 3), bv(8, 4)}, {}, nullptr, F);
  v.expect(STP_KIND_BV_SLT, {bv(8, 0xff), bv(8, 0)}, {}, nullptr, T);
  v.expect(STP_KIND_BV_SLE, {bv(8, 0xff), bv(8, 0xff)}, {}, nullptr, T);
  v.expect(STP_KIND_BV_SGT, {bv(8, 0), bv(8, 0xff)}, {}, nullptr, T);
  v.expect(STP_KIND_BV_SGE, {bv(8, 0xff), bv(8, 0)}, {}, nullptr, F);
  v.expect(STP_KIND_BV_UADDO, {bv(8, 0xff), bv(8, 1)}, {}, nullptr, T);
  v.expect(STP_KIND_BV_SADDO, {bv(8, 0x7f), bv(8, 1)}, {}, nullptr, T);
  v.expect(STP_KIND_BV_UMULO, {bv(8, 0x10), bv(8, 0x10)}, {}, nullptr, T);
  v.expect(STP_KIND_BV_SMULO, {bv(8, 0x40), bv(8, 2)}, {}, nullptr, T);
  v.expect(STP_KIND_BV_USUBO, {bv(8, 0), bv(8, 1)}, {}, nullptr, T);
  v.expect(STP_KIND_BV_SSUBO, {bv(8, 0x80), bv(8, 1)}, {}, nullptr, T);
  v.expect(STP_KIND_BV_NEGO, {bv(8, 0x80)}, {}, nullptr, T);
  v.expect(STP_KIND_BV_SDIVO, {bv(8, 0x80), bv(8, 0xff)}, {}, nullptr, T);
  v.expect(STP_KIND_BV_REDAND, {bv(8, 0xff)}, {}, nullptr, bv(1, 1));
  v.expect(STP_KIND_BV_REDOR, {bv(8, 0)}, {}, nullptr, bv(1, 0));
  // arrays: equality over a constant array is UNSUPPORTED, so the array kinds are
  // read back through selects and through the interning of constant arrays
  stp_term k9 = stp_mk_const_array(tm, arr, bv(8, 9));
  v.expect(STP_KIND_SELECT, {k9, bv(8, 1)}, {}, nullptr, bv(8, 9));
  stp_term st = stp_mk_term3(tm, STP_KIND_STORE, k9, bv(8, 1), bv(8, 3));
  ASSERT_NE(nullptr, st);
  v.expect(STP_KIND_SELECT, {st, bv(8, 1)}, {}, nullptr, bv(8, 3));
  v.expect(STP_KIND_SELECT, {st, bv(8, 2)}, {}, nullptr, bv(8, 9));
  const stp_term nine[1] = {bv(8, 9)};
  EXPECT_EQ(k9, stp_mk_term_sorted(tm, STP_KIND_CONST_ARRAY, 1, nine, 0, nullptr, arr));
  v.expect(STP_KIND_FP_ABS, {fp(-1.0)}, {}, nullptr, fp(1.0));
  v.expect(STP_KIND_FP_NEG, {fp(1.0)}, {}, nullptr, fp(-1.0));
  v.expect(STP_KIND_FP_ADD, {rne, fp(1.0), fp(2.0)}, {}, nullptr, fp(3.0));
  v.expect(STP_KIND_FP_SUB, {rne, fp(3.0), fp(1.0)}, {}, nullptr, fp(2.0));
  v.expect(STP_KIND_FP_MUL, {rne, fp(2.0), fp(3.0)}, {}, nullptr, fp(6.0));
  v.expect(STP_KIND_FP_DIV, {rne, fp(6.0), fp(2.0)}, {}, nullptr, fp(3.0));
  v.expect(STP_KIND_FP_FMA, {rne, fp(2.0), fp(3.0), fp(1.0)}, {}, nullptr, fp(7.0));
  v.expect(STP_KIND_FP_SQRT, {rne, fp(4.0)}, {}, nullptr, fp(2.0));
  v.expect(STP_KIND_FP_REM, {fp(5.0), fp(3.0)}, {}, nullptr, fp(-1.0));
  v.expect(STP_KIND_FP_RTI, {rne, fp(2.5)}, {}, nullptr, fp(2.0));
  v.expect(STP_KIND_FP_MIN, {fp(1.0), fp(2.0)}, {}, nullptr, fp(1.0));
  v.expect(STP_KIND_FP_MAX, {fp(1.0), fp(2.0)}, {}, nullptr, fp(2.0));
  v.expect(STP_KIND_FP_EQ, {fp(1.0), fp(1.0)}, {}, nullptr, T);
  v.expect(STP_KIND_FP_LT, {fp(1.0), fp(2.0)}, {}, nullptr, T);
  v.expect(STP_KIND_FP_LEQ, {fp(2.0), fp(2.0)}, {}, nullptr, T);
  v.expect(STP_KIND_FP_GT, {fp(2.0), fp(1.0)}, {}, nullptr, T);
  v.expect(STP_KIND_FP_GEQ, {fp(1.0), fp(2.0)}, {}, nullptr, F);
  v.expect(STP_KIND_FP_IS_NORMAL, {fp(1.0)}, {}, nullptr, T);
  v.expect(STP_KIND_FP_IS_SUBNORMAL, {fp(1.0)}, {}, nullptr, F);
  v.expect(STP_KIND_FP_IS_ZERO, {fp(0.0)}, {}, nullptr, T);
  v.expect(STP_KIND_FP_IS_INF, {stp_mk_fp_pos_inf(tm, f32)}, {}, nullptr, T);
  v.expect(STP_KIND_FP_IS_NAN, {stp_mk_fp_nan(tm, f32)}, {}, nullptr, T);
  v.expect(STP_KIND_FP_IS_NEG, {fp(-1.0)}, {}, nullptr, T);
  v.expect(STP_KIND_FP_IS_POS, {fp(1.0)}, {}, nullptr, T);
  v.expect(STP_KIND_FP_FP, {bv(1, 0), bv(8, 127), bv(23, 0)}, {}, nullptr, fp(1.0));
  v.expect(STP_KIND_FP_TO_FP_FROM_BV, {bv(32, 0x3f800000u)}, {8, 24}, nullptr, fp(1.0));
  v.expect(STP_KIND_FP_TO_FP_FROM_FP,
           {rne, stp_mk_fp_double(tm, stp_mk_fp64_sort(tm), STP_RM_RNE, 1.5)}, {8, 24}, nullptr,
           fp(1.5));
  v.expect(STP_KIND_FP_TO_FP_FROM_SBV, {rne, bv(8, 0xfe)}, {8, 24}, nullptr, fp(-2.0));
  v.expect(STP_KIND_FP_TO_FP_FROM_UBV, {rne, bv(8, 0xfe)}, {8, 24}, nullptr, fp(254.0));
  v.expect(STP_KIND_FP_TO_FP_FROM_REAL, {rne, re("1/4")}, {8, 24}, nullptr, fp(0.25));
  v.expect(STP_KIND_FP_TO_UBV, {rtz, fp(3.75)}, {8}, nullptr, bv(8, 3));
  v.expect(STP_KIND_FP_TO_SBV, {rtz, fp(-3.75)}, {8}, nullptr, bv(8, 0xfd));
  v.expect(STP_KIND_FP_TO_IEEE_BV, {fp(1.0)}, {}, nullptr, bv(32, 0x3f800000u));
  v.expect(STP_KIND_REAL_ADD, {re("1/2"), re("1/2")}, {}, nullptr, re("1"));
  v.expect(STP_KIND_REAL_SUB, {re("3"), re("1")}, {}, nullptr, re("2"));
  v.expect(STP_KIND_REAL_NEG, {re("1")}, {}, nullptr, re("-1"));
  v.expect(STP_KIND_REAL_MUL, {re("3"), re("2")}, {}, nullptr, re("6"));
  v.expect(STP_KIND_REAL_DIV, {re("6"), re("2")}, {}, nullptr, re("3"));
  v.expect(STP_KIND_REAL_LT, {re("1"), re("2")}, {}, nullptr, T);
  v.expect(STP_KIND_REAL_LE, {re("2"), re("2")}, {}, nullptr, T);
  v.expect(STP_KIND_REAL_GT, {re("2"), re("1")}, {}, nullptr, T);
  v.expect(STP_KIND_REAL_GE, {re("1"), re("2")}, {}, nullptr, F);

  EXPECT_EQ(nullptr, stp_tm_error(tm)) << pending(tm);
  std::printf("folded at construction: %d, proved by the solver: %d\n", v.folded, v.proved);
  stp_solver_delete(v.s);
  stp_tm_scope_pop(tm);
  stp_tm_release(tm);
}
