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

#include "stp/cpp_interface.h"
#include "stp/Parser/parser.h"
#include "stp/Simplifier/CommonFactor.h"
#include <gtest/gtest.h>
#include <set>
#include <string>

  const std::string start_input = R"(
  (set-logic QF_BV)
  (set-info :smt-lib-version 2.0)
  (set-info :category "check")
  (set-info :status sat)

  (declare-fun z () (_ BitVec 20))
  (declare-fun a () (_ BitVec 20))
  (declare-fun b () (_ BitVec 20))
  (declare-fun c () (_ BitVec 20))
  (declare-fun d () (_ BitVec 20))
  (declare-fun e () (_ BitVec 20))
  (declare-fun f () (_ BitVec 20))
  (declare-fun g () (_ BitVec 20))
  (declare-fun h () (_ BitVec 20))

  (push 1)
  )";

struct Context
{
  stp::STPMgr mgr;
  SimplifyingNodeFactory snf;
  stp::Cpp_interface interface;

  Context() : snf(*(mgr.hashingNodeFactory), mgr), interface(mgr, &snf)
  {
    mgr.defaultNodeFactory = &snf;
    interface.startup();
    stp::GlobalParserBM = &mgr;
    stp::GlobalParserInterface = &interface;
  }

  ASTNode parse(std::string input)
  {
    stp::SMT2ScanString((start_input + input).c_str());
    stp::SMT2Parse();
    smt2lex_destroy();
    return mgr.CreateNode(stp::AND, mgr.GetAsserts());
  }

  ASTNode process(std::string input)
  {
    ASTNode n = parse(input);
    std::cerr << "Pre common factor " << n;
    stp::CommonFactor pass(&mgr, &snf);
    n = pass.topLevel(n);
    saved = pass.multipliesSaved();
    std::cerr << "Post common factor " << n;
    return n;
  }

  long saved = 0;
};

static void collectKindNodes(const ASTNode& n, stp::Kind kind,
                             std::set<ASTNode>& out, std::set<ASTNode>& visited)
{
  if (visited.count(n))
    return;
  visited.insert(n);
  if (n.GetKind() == kind)
    out.insert(n);
  for (const ASTNode& c : n.GetChildren())
    collectKindNodes(c, kind, out, visited);
}

static std::set<ASTNode> nodesOfKind(const ASTNode& n, stp::Kind kind)
{
  std::set<ASTNode> out, visited;
  collectKindNodes(n, kind, out, visited);
  return out;
}

// The multiplications the bit-blaster builds: an n-ary one is a tree of
// n-1 binary ones, which is what the saving is counted in.
static size_t multiplications(const ASTNode& n)
{
  size_t total = 0;
  for (const ASTNode& m : nodesOfKind(n, stp::BVMULT))
    total += m.Degree() - 1;
  return total;
}

static bool holds(const ASTNode& n, const ASTNode& child)
{
  for (const ASTNode& c : n.GetChildren())
    if (c == child)
      return true;
  return false;
}

// The node the whole extraction is for: several wide products, each of them
// multiplying by the same variable.
//    (z*a*b) + (z*c*d)  -->  z*((a*b) + (c*d))
// Four multiplications become three, and z is multiplied in once.
TEST(CommonFactor_Test, shared_variable_leaves_the_products)
{
  const std::string input = R"(
    (assert (= (bvadd (bvmul z a b) (bvmul z c d)) (_ bv0 20)))
    )";

  Context ctx;
  ASTNode n = ctx.process(input);

  ASSERT_EQ(multiplications(n), 3u);
  ASSERT_EQ(ctx.saved, 1);

  // One multiplication by z, over a sum of the two remainders.
  const std::set<ASTNode> plus = nodesOfKind(n, stp::BVPLUS);
  ASSERT_EQ(plus.size(), 1u);
  ASSERT_EQ(plus.begin()->Degree(), 2u);

  const std::set<ASTNode> mult = nodesOfKind(n, stp::BVMULT);
  int factored = 0;
  for (const ASTNode& m : mult)
    if (holds(m, *plus.begin()))
    {
      ASSERT_EQ(m.Degree(), 2u);
      const ASTNode& other = m[0] == *plus.begin() ? m[1] : m[0];
      ASSERT_EQ(other.GetKind(), stp::SYMBOL);
      factored++;
    }
  ASSERT_EQ(factored, 1);
}

// The shape the user's query has, one variable down every product of a
// four-operand sum. Each product gives up its z, and what is left of it
// keeps the two constants it was multiplying.
TEST(CommonFactor_Test, every_product_of_a_wide_sum_gives_up_the_variable)
{
  const std::string input = R"(
    (assert (= (bvadd (bvmul z a b) (bvmul z c d) (bvmul z e f)
                      (bvmul z g h))
               (_ bv0 20)))
    )";

  Context ctx;
  ASTNode n = ctx.process(input);

  // Eight binary multiplications become five: one per remainder, and one
  // for z itself.
  ASSERT_EQ(multiplications(n), 5u);
  ASSERT_EQ(ctx.saved, 3);

  const std::set<ASTNode> plus = nodesOfKind(n, stp::BVPLUS);
  ASSERT_EQ(plus.size(), 1u);
  ASSERT_EQ(plus.begin()->Degree(), 4u);
}

// Two factors in common come out one after the other, the second only
// visible once the first is gone:
//    (z*d*a) + (z*d*b)  -->  z*(d*(a + b))
TEST(CommonFactor_Test, a_second_shared_factor_comes_out_of_the_remainders)
{
  const std::string input = R"(
    (assert (= (bvadd (bvmul z d a) (bvmul z d b)) (_ bv0 20)))
    )";

  Context ctx;
  ASTNode n = ctx.process(input);

  ASSERT_EQ(multiplications(n), 2u);
  ASSERT_EQ(ctx.saved, 2);

  const std::set<ASTNode> plus = nodesOfKind(n, stp::BVPLUS);
  ASSERT_EQ(plus.size(), 1u);
  ASSERT_EQ(plus.begin()->Degree(), 2u);
}

// The factor in the most products is the one taken, and what is left over
// is factored again:
//    (z*d*a) + (z*d*b) + (z*c)  -->  z*((d*(a + b)) + c)
TEST(CommonFactor_Test, the_operand_in_the_most_products_goes_first)
{
  const std::string input = R"(
    (assert (= (bvadd (bvmul z d a) (bvmul z d b) (bvmul z c)) (_ bv0 20)))
    )";

  Context ctx;
  ASTNode n = ctx.process(input);

  // z once, d once: five multiplications become two.
  ASSERT_EQ(multiplications(n), 2u);
  ASSERT_EQ(ctx.saved, 3);
}

// A constant is an operand like any other, so a coefficient every product
// carries comes out with the rest.
TEST(CommonFactor_Test, a_shared_constant_is_factored)
{
  const std::string input = R"(
    (assert (= (bvadd (bvmul (_ bv3 20) a) (bvmul (_ bv3 20) b)) (_ bv0 20)))
    )";

  Context ctx;
  ASTNode n = ctx.process(input);

  ASSERT_EQ(multiplications(n), 1u);
  ASSERT_EQ(ctx.saved, 1);
}

// Subtracted products join in: the factory spells (p - q) as (p + -q) and
// keeps the negation on top of the product, so the remainder carries it.
//    (z*a) - (z*b)  -->  z*(a + -b)
TEST(CommonFactor_Test, a_negated_product_joins_the_extraction)
{
  const std::string input = R"(
    (assert (= (bvsub (bvmul z a) (bvmul z b)) (_ bv0 20)))
    )";

  Context ctx;
  ASTNode n = ctx.process(input);

  ASSERT_EQ(multiplications(n), 1u);
  ASSERT_EQ(ctx.saved, 1);
  ASSERT_EQ(nodesOfKind(n, stp::BVUMINUS).size(), 1u);
}

// A product used somewhere else is built whether or not this sum uses it,
// so taking a factor out of it would add a multiplication rather than
// remove one. With only one product left to give up z, nothing is shared.
TEST(CommonFactor_Test, a_product_used_elsewhere_is_left_alone)
{
  const std::string input = R"(
    (assert (= (bvadd (bvmul z a) (bvmul z b)) (_ bv0 20)))
    (assert (= (bvmul z a) (_ bv1 20)))
    )";

  Context ctx;
  ASTNode n = ctx.process(input);

  ASSERT_EQ(ctx.saved, 0);
  ASSERT_EQ(multiplications(n), 2u);

  const std::set<ASTNode> plus = nodesOfKind(n, stp::BVPLUS);
  ASSERT_EQ(plus.size(), 1u);
  ASSERT_EQ(plus.begin()->Degree(), 2u);
}

// Products with nothing in common are left as they are.
TEST(CommonFactor_Test, products_sharing_nothing_are_unchanged)
{
  const std::string input = R"(
    (assert (= (bvadd (bvmul z a) (bvmul c d)) (_ bv0 20)))
    )";

  Context ctx;
  ASTNode before = ctx.parse(input);
  stp::CommonFactor pass(&ctx.mgr, &ctx.snf);
  ASTNode after = pass.topLevel(before);

  ASSERT_EQ(pass.multipliesSaved(), 0);
  ASSERT_EQ(before, after);
}

// An operand one product repeats is one operand of that product to give
// up, not two: (z*z*a) + (z*b) leaves (z*a) behind, not (a).
TEST(CommonFactor_Test, a_repeated_operand_is_given_up_once)
{
  const std::string input = R"(
    (assert (= (bvadd (bvmul z z a) (bvmul z b)) (_ bv0 20)))
    )";

  Context ctx;
  ASTNode n = ctx.process(input);

  ASSERT_EQ(ctx.saved, 1);
  // (z*a) + b under one multiplication by z.
  ASSERT_EQ(multiplications(n), 2u);
}

// The pass reaches a fixed point: what it produces holds no factor it
// would take out again.
TEST(CommonFactor_Test, running_twice_changes_nothing)
{
  const std::string input = R"(
    (assert (= (bvadd (bvmul z d a) (bvmul z d b) (bvmul z c)) (_ bv0 20)))
    (assert (= (bvadd (bvmul e a) (bvmul e b) (bvmul f a)) (_ bv1 20)))
    )";

  Context ctx;
  ASTNode once = ctx.process(input);

  stp::CommonFactor again(&ctx.mgr, &ctx.snf);
  ASTNode twice = again.topLevel(once);

  ASSERT_EQ(again.multipliesSaved(), 0);
  ASSERT_EQ(once, twice);
}

// Nothing above the sum is disturbed: the rewrite replaces the sum in
// place, and the rest of the DAG comes back as it was.
TEST(CommonFactor_Test, the_rest_of_the_dag_is_untouched)
{
  const std::string input = R"(
    (assert (= (bvadd (bvmul z a) (bvmul z b)) (bvudiv c d)))
    )";

  Context ctx;
  ASTNode n = ctx.process(input);

  ASSERT_EQ(ctx.saved, 1);
  ASSERT_EQ(nodesOfKind(n, stp::BVDIV).size(), 1u);
  ASSERT_EQ(nodesOfKind(n, stp::EQ).size(), 1u);
}

// Sharing, which is the whole of what makes the rewrite pay. A product this
// sum does not own is built whatever the sum does with it, so taking a
// factor out of it would build the reduced product beside the one that
// stays -- a multiplication added, not removed. The tests below are the
// ways a product can fail to be this sum's own.

// The same product under two sums: neither owns it, so neither takes it
// apart, and what is left in each sum is one product able to give the
// factor up. One is not sharing.
TEST(CommonFactor_Test, a_product_in_two_sums_is_left_alone)
{
  const std::string input = R"(
    (assert (= (bvadd (bvmul z a) (bvmul z b)) (_ bv0 20)))
    (assert (= (bvadd (bvmul z a) (bvmul z c)) (_ bv1 20)))
    )";

  Context ctx;
  ASTNode n = ctx.process(input);

  ASSERT_EQ(ctx.saved, 0);
  ASSERT_EQ(multiplications(n), 3u);

  const std::set<ASTNode> plus = nodesOfKind(n, stp::BVPLUS);
  ASSERT_EQ(plus.size(), 2u);
  for (const ASTNode& p : plus)
    ASSERT_EQ(p.Degree(), 2u);
}

// One shared product among several does not stop the others: the two this
// sum owns are factored and the shared one stays as it is.
TEST(CommonFactor_Test, the_products_this_sum_owns_are_still_factored)
{
  const std::string input = R"(
    (assert (= (bvadd (bvmul z a) (bvmul z b) (bvmul z c)) (_ bv0 20)))
    (assert (= (bvmul z a) (_ bv1 20)))
    )";

  Context ctx;
  ASTNode n = ctx.process(input);

  // (z*a) stays, (z*b) and (z*c) become one multiplication by z.
  ASSERT_EQ(ctx.saved, 1);
  ASSERT_EQ(multiplications(n), 2u);

  const std::set<ASTNode> plus = nodesOfKind(n, stp::BVPLUS);
  ASSERT_EQ(plus.size(), 2u);
}

// A negated product needs both nodes to die, so a negation used elsewhere
// stops the addend under it joining in.
TEST(CommonFactor_Test, a_shared_negation_is_left_alone)
{
  const std::string input = R"(
    (assert (= (bvadd (bvmul z a) (bvneg (bvmul z b))) (_ bv0 20)))
    (assert (= (bvneg (bvmul z b)) c))
    )";

  Context ctx;
  ASTNode n = ctx.process(input);

  ASSERT_EQ(ctx.saved, 0);
  ASSERT_EQ(multiplications(n), 2u);
}

// ... and so does a product used elsewhere, even where the negation above
// it is this sum's own.
TEST(CommonFactor_Test, a_shared_product_under_a_negation_is_left_alone)
{
  const std::string input = R"(
    (assert (= (bvadd (bvmul z a) (bvneg (bvmul z b))) (_ bv0 20)))
    (assert (= (bvmul z b) (_ bv1 20)))
    )";

  Context ctx;
  ASTNode n = ctx.process(input);

  ASSERT_EQ(ctx.saved, 0);
  ASSERT_EQ(multiplications(n), 2u);
}

// A product under a product is a reference like any other: the inner one is
// built for the outer whatever this sum does.
TEST(CommonFactor_Test, a_product_used_inside_another_is_left_alone)
{
  const std::string input = R"(
    (assert (= (bvadd (bvmul z a) (bvmul z b)) (_ bv0 20)))
    (assert (= (bvmul c (bvmul z a)) (_ bv1 20)))
    )";

  Context ctx;
  ASTNode n = ctx.process(input);

  ASSERT_EQ(ctx.saved, 0);
}

// The sum being shared is not the same thing: the rewrite replaces the sum
// itself, so every place that held it holds the factored form, and the
// products still die.
TEST(CommonFactor_Test, a_shared_sum_is_still_factored)
{
  const std::string input = R"(
    (assert (= (bvadd (bvmul z a) (bvmul z b)) (_ bv0 20)))
    (assert (= (bvmul c (bvadd (bvmul z a) (bvmul z b))) (_ bv1 20)))
    )";

  Context ctx;
  ASTNode n = ctx.process(input);

  ASSERT_EQ(ctx.saved, 1);

  // One addition, under one multiplication by z, under the outer product.
  const std::set<ASTNode> plus = nodesOfKind(n, stp::BVPLUS);
  ASSERT_EQ(plus.size(), 1u);
  ASSERT_EQ(multiplications(n), 2u);
}

// Nor is the factor: it is the operand being multiplied in once instead of
// several times, and what it is used for elsewhere does not change that.
TEST(CommonFactor_Test, a_shared_factor_is_still_taken_out)
{
  const std::string input = R"(
    (assert (= (bvadd (bvmul z a) (bvmul z b)) (_ bv0 20)))
    (assert (= (bvmul z c) (_ bv1 20)))
    (assert (bvult z (_ bv7 20)))
    )";

  Context ctx;
  ASTNode n = ctx.process(input);

  ASSERT_EQ(ctx.saved, 1);
  // (z*(a+b)) and the untouched (z*c).
  ASSERT_EQ(multiplications(n), 2u);
}

// The guard is a reference count, not a liveness analysis. A product this
// one sum holds twice has two references, and both would die with the
// rewrite -- but it is declined, because "this sum's own" is answered by
// counting rather than by proving where the references are. Deliberate:
// the rule stays one sentence, and the shape is rare. What is left is one
// product able to give z up, which is not sharing.
TEST(CommonFactor_Test, a_product_the_sum_holds_twice_is_left_alone)
{
  const std::string input = R"(
    (assert (= (bvadd (bvmul z a) (bvmul z a) (bvmul z b)) (_ bv0 20)))
    )";

  Context ctx;
  ASTNode n = ctx.process(input);

  ASSERT_EQ(ctx.saved, 0);
  ASSERT_EQ(multiplications(n), 2u);
}
