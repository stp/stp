#include <gtest/gtest.h>
#include <stp/fp.hpp>

// The header-only C++ convenience wrappers (stp::fp::Solver / Float / Bool):
// build floating-point problems with operator overloading and read native
// doubles back.

TEST(fp_cpp_wrapper, arithmetic_and_model)
{
  stp::fp::Solver s;
  stp::fp::Float a = s.fp("a", 11, 53); // IEEE double
  s.add(a == 4.0);
  stp::fp::Float prod = a * a;
  stp::fp::Float rt = a.sqrt();
  s.add((a > 0.0) && a.is_normal());

  ASSERT_TRUE(s.check());
  EXPECT_EQ(4.0, s.model(a));
  EXPECT_EQ(16.0, s.model(prod));
  EXPECT_EQ(2.0, s.model(rt));
  EXPECT_EQ(4.0, s.model(abs(-a)));
  EXPECT_EQ(2.0, s.model(a.min(s.fpval(11, 53, 2.0))));
}

// Two independent solvers, both floating point -- also exercises the
// per-manager binding through the C++ layer.
TEST(fp_cpp_wrapper, two_solvers)
{
  stp::fp::Solver s1;
  stp::fp::Float a = s1.fp("a", 8, 24); // single
  s1.add(a == 1.5);

  stp::fp::Solver s2;
  stp::fp::Float b = s2.fp("b", 11, 53); // double
  s2.add(b == 3.5);

  ASSERT_TRUE(s1.check());
  ASSERT_TRUE(s2.check());
  EXPECT_EQ(1.5, s1.model(a));
  EXPECT_EQ(3.5, s2.model(b));
}

// A conflicting pair of classifications is unsatisfiable.
TEST(fp_cpp_wrapper, classification_unsat)
{
  stp::fp::Solver s;
  stp::fp::Float x = s.fp("x", 5, 11);
  s.add(x.is_nan());
  s.add(x.is_zero());
  EXPECT_FALSE(s.check());
}

TEST(fp_cpp_wrapper, more_ops)
{
  stp::fp::Solver s;
  stp::fp::Float a = s.fp("a", 11, 53);
  stp::fp::Float b = s.fp("b", 11, 53);
  s.add(a == 4.0);
  s.add(b == 2.0);
  ASSERT_TRUE(s.check());
  EXPECT_EQ(2.0, s.model(a - b));
  EXPECT_EQ(2.0, s.model(a / b));
  EXPECT_EQ(10.0, s.model(a.fma(b, b))); // 4*2 + 2
  EXPECT_EQ(0.0, s.model(a.rem(b)));
  EXPECT_EQ(2.0, s.model(a.min(b)));
  EXPECT_EQ(4.0, s.model(a.max(b)));
  EXPECT_EQ(4.0, s.model(a.round_to_integral()));
}

TEST(fp_cpp_wrapper, constants_and_comparisons)
{
  stp::fp::Solver s;
  s.add(s.fp_nan(5, 11).is_nan());
  s.add(s.fp_inf(5, 11, /*negative*/ true).is_negative());
  s.add(s.fp_zero(5, 11, /*negative*/ true).is_negative());
  s.add(s.fp_from_bits(5, 11, 0x3C00).is_normal()); // 1.0

  stp::fp::Float a = s.fp("a", 5, 11);
  s.add(a == 3.0);
  s.add(a < 4.0);
  s.add(a <= 3.0);
  s.add(a >= 3.0);
  s.add(a.ne(5.0));
  s.add(a.is_positive());
  EXPECT_TRUE(s.check());
}

TEST(fp_cpp_wrapper, bits_and_conversions)
{
  stp::fp::Solver s;
  stp::fp::Float x = s.fp("x", 5, 11);
  s.add(x == s.fp_from_bits(5, 11, 0x4200)); // half 3.0
  Expr bits = x.to_ieee_bits();
  Expr ubv = x.to_ubv(8);
  ASSERT_TRUE(s.check());
  EXPECT_EQ((unsigned long long)0x4200, s.model_bits(x));
  EXPECT_EQ((unsigned long long)0x4200,
            getBVUnsignedLongLong(vc_getCounterExample(s.raw(), bits)));
  EXPECT_EQ((unsigned)3, getBVUnsigned(vc_getCounterExample(s.raw(), ubv)));

  stp::fp::Solver s2;
  stp::fp::Float y = s2.fp("y", 5, 11);
  s2.add(y == s2.fp_from_bits(5, 11, 0xC000)); // -2.0
  ASSERT_TRUE(s2.check());
  EXPECT_EQ((unsigned)0xFE,
            getBVUnsigned(vc_getCounterExample(s2.raw(), y.to_sbv(8))) & 0xFF);
}
