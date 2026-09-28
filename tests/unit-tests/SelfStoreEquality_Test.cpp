/***********
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

/*
 * The factory's self-store equality fold: A = write(A, i, v) becomes the
 * read equality select(A, i) = v, in both orientations, for bit-vector
 * and float elements, with or without --array-equality. A store onto a
 * DIFFERENT array must not fold.
 */

#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/cpp_interface.h"
#include <gtest/gtest.h>

using namespace stp;

namespace
{

struct Harness
{
  STPMgr mgr;
  SimplifyingNodeFactory snf;

  Harness() : snf(*(mgr.hashingNodeFactory), mgr)
  {
    static const bool booted = []() {
      CONSTANTBV::BitVector_Boot();
      return true;
    }();
    (void)booted;
    mgr.defaultNodeFactory = &snf;
  }

  static bool hasArrayOperand(const ASTNode& n)
  {
    for (const auto& c : n)
      if (c.GetType() == ARRAY_TYPE)
        return true;
    return false;
  }
};

TEST(SelfStoreEquality, folds_to_the_read_equality)
{
  Harness h;
  const ASTNode a = h.mgr.CreateSymbol("a", 8, 8);
  const ASTNode i = h.mgr.CreateSymbol("i", 0, 8);
  const ASTNode v = h.mgr.CreateSymbol("v", 0, 8);
  const ASTNode w = h.snf.CreateArrayTerm(WRITE, 8, 8, a, i, v);

  for (int orientation = 0; orientation < 2; orientation++)
  {
    const ASTNode eq = orientation ? h.snf.CreateNode(EQ, w, a)
                                   : h.snf.CreateNode(EQ, a, w);
    EXPECT_EQ(EQ, eq.GetKind());
    EXPECT_FALSE(Harness::hasArrayOperand(eq));
  }
}

TEST(SelfStoreEquality, float_elements_fold_to_the_float_equality)
{
  Harness h;
  const ASTNode a = h.mgr.CreateSourceSymbol(
      "fa", SourceSort::array(SourceSort::bitVector(8),
                              SourceSort::floatingPoint(8, 24)));
  const ASTNode i = h.mgr.CreateSymbol("fi", 0, 8);
  const ASTNode v =
      h.mgr.CreateSourceSymbol("fv", SourceSort::floatingPoint(8, 24));
  const ASTNode w = h.snf.CreateArrayTerm(WRITE, 8, 32, a, i, v);

  const ASTNode eq = h.snf.CreateNode(EQ, a, w);
  EXPECT_EQ(FP_SMT_EQ, eq.GetKind());
  EXPECT_FALSE(Harness::hasArrayOperand(eq));
}

TEST(SelfStoreEquality, a_store_onto_another_array_does_not_fold)
{
  Harness h;
  h.mgr.UserFlags.enable_array_equality = true;
  const ASTNode a = h.mgr.CreateSymbol("a2", 8, 8);
  const ASTNode b = h.mgr.CreateSymbol("b2", 8, 8);
  const ASTNode i = h.mgr.CreateSymbol("i2", 0, 8);
  const ASTNode v = h.mgr.CreateSymbol("v2", 0, 8);
  const ASTNode w = h.snf.CreateArrayTerm(WRITE, 8, 8, b, i, v);

  const ASTNode eq = h.snf.CreateNode(EQ, a, w);
  EXPECT_TRUE(Harness::hasArrayOperand(eq));
}

} // namespace
