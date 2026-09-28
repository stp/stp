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
 * The variadic gates of BBNodeManagerAIG at every arity that reaches them.
 *
 * An AIG node takes two inputs, so CreateNode folds longer child lists into a
 * tower and special-cases the short ones. One child is the arity that gets
 * forgotten: AND and OR handled it, the three gates built on top of them did
 * not, and a one-element list fell through to makeTower -- which folds pairs
 * until two remain and then asserts that it has two, so it aborted, or with
 * assertions off read a deque it had already emptied.
 *
 * Checked structurally rather than by solving. ABC hash-conses as it builds,
 * so the node for a gate over one input must be the very node that gate's
 * definition names -- Aig_Not(x) for NAND and NOR, x itself for AND, OR and
 * XOR -- and pointer equality says so exactly.
 */

#include "stp/ToSat/BBNodeManagerAIG.h"
#include "stp/STPManager/STPManager.h"
#include <gtest/gtest.h>

using namespace stp;

namespace
{

class AigGateArityTest : public ::testing::Test
{
protected:
  STPMgr mgr;
  BBNodeManagerAIG aig;
  unsigned counter = 0;

  // One fresh AIG input.
  BBNodeAIG input()
  {
    const ASTNode s =
        mgr.CreateSymbol(("b" + std::to_string(counter++)).c_str(), 0, 1);
    return aig.CreateSymbol(s, 0);
  }

  // `n` fresh inputs. The count is laundered through a volatile read:
  // CreateNode is inline, and given a length the optimiser can see it proves
  // the wider branches dead and warns about the children[1] inside them
  // (-Warray-bounds). Keeping the length opaque compiles every branch, which
  // is also closer to how the blaster calls this -- with a field width it
  // worked out at run time.
  std::vector<BBNodeAIG> inputs(unsigned n)
  {
    static volatile unsigned opaque;
    opaque = n;
    std::vector<BBNodeAIG> v;
    for (unsigned i = 0, size = opaque; i < size; i++)
      v.push_back(input());
    return v;
  }
};

TEST_F(AigGateArityTest, OneChildIsTheGatesDefinition)
{
  std::vector<BBNodeAIG> one = inputs(1);
  Aig_Obj_t* const x = one[0].n;

  EXPECT_EQ(x, aig.CreateNode(AND, one).n);
  EXPECT_EQ(x, aig.CreateNode(OR, one).n);
  EXPECT_EQ(x, aig.CreateNode(XOR, one).n);
  EXPECT_EQ(Aig_Not(x), aig.CreateNode(NAND, one).n);
  EXPECT_EQ(Aig_Not(x), aig.CreateNode(NOR, one).n);
}

// The negating gates are exactly the negation of their positive counterparts,
// at every arity -- which is what says the one-child case above was given the
// right answer rather than merely a defined one.
TEST_F(AigGateArityTest, NegatedGatesMatchTheirPositiveFormAtEveryArity)
{
  for (unsigned n = 1; n <= 5; n++)
  {
    std::vector<BBNodeAIG> children = inputs(n);
    EXPECT_EQ(Aig_Not(aig.CreateNode(AND, children).n),
              aig.CreateNode(NAND, children).n)
        << "NAND with " << n << " children";
    EXPECT_EQ(Aig_Not(aig.CreateNode(OR, children).n),
              aig.CreateNode(NOR, children).n)
        << "NOR with " << n << " children";
  }
}

// Two children and up already worked; pin them so the short-list handling
// cannot be "fixed" by changing what the general case builds.
TEST_F(AigGateArityTest, TwoChildrenAreThePlainGate)
{
  std::vector<BBNodeAIG> two = inputs(2);
  Aig_Obj_t* const x = two[0].n;
  Aig_Obj_t* const y = two[1].n;

  EXPECT_EQ(Aig_And(aig.aigMgr, x, y), aig.CreateNode(AND, two).n);
  EXPECT_EQ(Aig_Or(aig.aigMgr, x, y), aig.CreateNode(OR, two).n);
  EXPECT_EQ(Aig_Not(Aig_And(aig.aigMgr, x, y)), aig.CreateNode(NAND, two).n);
  EXPECT_EQ(Aig_Not(Aig_Or(aig.aigMgr, x, y)), aig.CreateNode(NOR, two).n);
}

} // namespace
