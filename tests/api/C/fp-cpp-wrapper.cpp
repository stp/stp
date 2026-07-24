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
