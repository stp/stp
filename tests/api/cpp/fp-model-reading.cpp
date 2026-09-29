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

// fp-model-reading.cpp -- build a floating-point problem, solve it, and
// read the model back: mk_fp_sort, declare at a floating-point sort,
// mk_fp_from_bits, fp_eq, the Sort's format accessors (fp_exp_size and
// fp_sig_size, on a sort and on a term's sort), and a float's model value as
// a FloatValue.

#include "api_common.hpp"

#include <cstdint>
#include <string>

using namespace stp;

namespace
{

// A 2.x checker's configuration: the counterexample self-check on (3.x's
// default is off), so every satisfiable check constructs its model and checks
// each assertion against it.
Options self_checking()
{
  Options o;
  o.set_bool("check-sanity", true);
  return o;
}

// The packed interchange bits of a float value (formats up to 64 bits).
std::uint64_t packed(const FloatValue& v)
{
  return std::stoull(v.bits(), nullptr, 2);
}

} // namespace

// (eb=3, sb=5): an 8-bit format that still has zeros, subnormals, normals,
// infinities and NaNs. 1.0 packs as 0b0 011 0000 = 0x30.
TEST(fp_model_reading, small_format)
{
  TermManager tm;
  Solver s(tm, self_checking());

  const Sort f = tm.mk_fp_sort(3, 5);
  const Term x = tm.declare("x", f);

  EXPECT_EQ(x.sort().kind(), SortKind::FP);
  EXPECT_EQ(x.sort().fp_exp_size(), 3u);
  EXPECT_EQ(x.sort().fp_sig_size(), 5u);

  // The accessors are on the sort itself.
  EXPECT_EQ(f.fp_exp_size(), 3u);
  EXPECT_EQ(f.fp_sig_size(), 5u);

  const Term one = tm.mk_fp_from_bits(f, tm.mk_bv(8, 0x30));
  EXPECT_EQ(one.sort().fp_exp_size(), 3u);
  EXPECT_EQ(one.sort().fp_sig_size(), 5u);

  s.add(fp_eq(x, one)); // x == 1.0
  ASSERT_TRUE(s.check_sat().is_sat());

  const FloatValue xval = s.model().fp_value(x);
  EXPECT_EQ(xval.exp_size, 3u);
  EXPECT_EQ(xval.sig_size, 5u);
  EXPECT_EQ(packed(xval), 0x30u);
}

// IEEE double (eb=11, sb=53): the packed value is a full 64 bits, so this also
// checks that reading a value at the width of a 64-bit integer works. 1.0
// packs as 0x3FF0000000000000.
TEST(fp_model_reading, double_format)
{
  TermManager tm;
  Solver s(tm, self_checking());

  const Sort f = tm.mk_fp_sort(11, 53);
  const Term x = tm.declare("x", f);

  EXPECT_EQ(x.sort().fp_exp_size(), 11u);
  EXPECT_EQ(x.sort().fp_sig_size(), 53u);

  const Term one = tm.mk_fp_from_bits(f, tm.mk_bv(64, 0x3FF0000000000000ULL));

  s.add(fp_eq(x, one)); // x == 1.0
  ASSERT_TRUE(s.check_sat().is_sat());

  const FloatValue xval = s.model().fp_value(x);
  EXPECT_EQ(xval.bits().size(), 64u);
  EXPECT_EQ(packed(xval), 0x3FF0000000000000ULL);
  EXPECT_EQ(xval.to_double(), std::optional<double>(1.0));
}
