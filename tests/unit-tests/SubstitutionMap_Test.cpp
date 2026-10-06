/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: October 2026
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

// A float or a rounding mode shares its packed carrier with a bit-vector, so
// an equation over carriers can offer a bit-vector to stand in for one. The
// substitution map refuses that at every entry point, since lowering goes by
// the sort the replacement would take away, and keeps the other direction,
// which is how the solver's own bit-vector names are substituted away.

#include "stp/AST/AST.h"
#include "stp/FloatBlaster/rounding_modes.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/SubstitutionMap.h"

#include <gtest/gtest.h>

using namespace stp;

namespace
{

struct Terms
{
  STPMgr mgr;
  ASTNode x = mgr.CreateSourceSymbol("x", SourceSort::floatingPoint(5, 11));
  ASTNode n = mgr.CreateSourceSymbol("n", SourceSort::bitVector(16));
  ASTNode rm = mgr.CreateSourceSymbol("rm", SourceSort::roundingMode());
  ASTNode v = mgr.CreateSourceSymbol("v", SourceSort::bitVector(5));
  ASTNode rtz = mgr.CreateRMConst(symbolic_fp::ROUND_TOWARD_ZERO);
  ASTNode bits = mgr.CreateBVConst(5, symbolic_fp::ROUND_TOWARD_ZERO);

  ASTNode lowBits(const ASTNode& var)
  {
    return mgr.CreateTerm(BVEXTRACT, 3, var, mgr.CreateBVConst(32, 2),
                          mgr.CreateZeroConst(32));
  }
};

} // namespace

// UpdateSubstitutionMap asserts that a float pair agrees on its format, so a
// float meets a bit-vector only through the other two.
TEST(SubstitutionMap_Test, float_is_not_replaced_by_a_bit_vector)
{
  Terms s;
  SubstitutionMap map(&s.mgr);

  ASSERT_FALSE(map.UpdateSubstitutionMapFewChecks(s.x, s.n));
  ASSERT_FALSE(map.UpdateSolverMap(s.x, s.n));
  ASSERT_FALSE(map.InsideSubstitutionMap(s.x));
}

TEST(SubstitutionMap_Test, rounding_mode_is_not_replaced_by_its_bits)
{
  Terms s;
  SubstitutionMap map(&s.mgr);

  ASSERT_FALSE(map.UpdateSubstitutionMap(s.rm, s.bits));
  ASSERT_FALSE(map.UpdateSubstitutionMapFewChecks(s.rm, s.bits));
  ASSERT_FALSE(map.UpdateSolverMap(s.rm, s.bits));
  ASSERT_FALSE(map.InsideSubstitutionMap(s.rm));

  // BVSolver defines an extract and then the whole variable as a
  // concatenation, without checking the second. The first is refused.
  ASSERT_FALSE(map.UpdateSolverMap(s.lowBits(s.rm), s.mgr.CreateBVConst(3, 0)));
  ASSERT_TRUE(map.UpdateSolverMap(s.lowBits(s.v), s.mgr.CreateBVConst(3, 0)));

  ASSERT_TRUE(map.UpdateSubstitutionMap(s.rm, s.rtz));
}

TEST(SubstitutionMap_Test, bit_vector_name_is_replaced_by_its_value)
{
  {
    Terms s;
    SubstitutionMap map(&s.mgr);
    ASSERT_TRUE(map.UpdateSubstitutionMapFewChecks(s.n, s.x));
  }
  {
    Terms s;
    SubstitutionMap map(&s.mgr);
    ASSERT_TRUE(map.UpdateSolverMap(s.n, s.x));
  }
  {
    Terms s;
    SubstitutionMap map(&s.mgr);
    ASSERT_TRUE(map.UpdateSubstitutionMap(s.v, s.rm));
  }
}
