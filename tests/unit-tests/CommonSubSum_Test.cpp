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
#include "stp/Simplifier/CommonSubSum.h"
#include "stp/Simplifier/Flatten.h"
#include <gtest/gtest.h>
#include <set>

  const std::string start_input = R"(
  (set-logic QF_BV)
  (set-info :smt-lib-version 2.0)
  (set-info :category "check")
  (set-info :status sat)

  (declare-fun v0 () (_ BitVec 20))
  (declare-fun v1 () (_ BitVec 20))
  (declare-fun v2 () (_ BitVec 20))
  (declare-fun v3 () (_ BitVec 20))

  (push 1)
  )";

struct Context
{
   stp::STPMgr mgr;
   SimplifyingNodeFactory snf;
   stp::Cpp_interface interface;
   stp::CommonSubSum subSum;
   stp::CommonSubSum subProd;

   Context() :
   snf (*(mgr.hashingNodeFactory), mgr),
   interface(mgr, &snf),
   subSum(&mgr, &snf, stp::BVPLUS),
   subProd(&mgr, &snf, stp::BVMULT)
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
      std::cerr << "Pre common sub-sum " << n;
      n = subSum.topLevel(n);
      std::cerr << "Post common sub-sum " << n;
      return n;
    }

   ASTNode processProducts(std::string input)
   {
      ASTNode n = parse(input);
      std::cerr << "Pre common sub-product " << n;
      n = subProd.topLevel(n);
      std::cerr << "Post common sub-product " << n;
      return n;
    }
};

static void collectKindNodes(const ASTNode& n, stp::Kind kind,
                             std::set<ASTNode>& out,
                             std::set<ASTNode>& visited)
{
  if (visited.count(n))
    return;
  visited.insert(n);
  if (n.GetKind() == kind)
    out.insert(n);
  for (const ASTNode& c : n.GetChildren())
    collectKindNodes(c, kind, out, visited);
}

static void collectPlusNodes(const ASTNode& n, std::set<ASTNode>& out,
                             std::set<ASTNode>& visited)
{
  collectKindNodes(n, stp::BVPLUS, out, visited);
}

// Two additions sharing the operand pair {v0, v1} come back with that pair
// factored into one shared addition:
//   (v0 + v1 + v2), (v0 + v1 + v3)  -->  s = (v0 + v1); (s + v2), (s + v3)
// The multiplications only stop the equalities being solved word-level at
// node creation, so the additions genuinely reach the pass.
TEST(CommonSubSum_Test, shared_pair_factored_into_one_node)
{
  const std::string input = R"(
    (assert (= (bvmul v2 (bvadd v0 v1 v2)) (_ bv0 20)))
    (assert (= (bvmul v3 (bvadd v0 v1 v3)) (_ bv33 20)))
    )";

  Context c;
  ASTNode n = c.process(input);

  std::set<ASTNode> plusNodes, visited;
  collectPlusNodes(n, plusNodes, visited);

  // Three binary additions: the shared pair and the two rewritten sums.
  ASSERT_EQ(plusNodes.size(), 3u);
  for (const ASTNode& p : plusNodes)
    ASSERT_EQ(p.Degree(), 2u);

  // Exactly one of them is the shared node: an addition that appears as a
  // child of both of the other two.
  int shared = 0;
  for (const ASTNode& s : plusNodes)
  {
    int parents = 0;
    for (const ASTNode& p : plusNodes)
      for (const ASTNode& child : p.GetChildren())
        if (child == s)
          parents++;
    if (parents == 2)
      shared++;
  }
  ASSERT_EQ(shared, 1);
}

// An addition with no partner shares nothing and must come back unchanged.
TEST(CommonSubSum_Test, lone_sum_unchanged)
{
  const std::string input = R"(
    (assert (= (bvmul v2 (bvadd v0 v1 v2)) (_ bv0 20)))
    )";

  Context c;
  ASTNode n = c.process(input);

  std::set<ASTNode> plusNodes, visited;
  collectPlusNodes(n, plusNodes, visited);

  ASSERT_EQ(plusNodes.size(), 1u);
  ASSERT_EQ(plusNodes.begin()->Degree(), 3u);
}

// The product instance of the pass does the same for multiplies:
//   (v0 * v1 * v2), (v0 * v1 * v3)  -->  s = (v0 * v1); (s * v2), (s * v3)
// The additions keep the equalities from being solved word-level at node
// creation, so the products genuinely reach the pass.
TEST(CommonSubSum_Test, shared_pair_factored_into_one_product_node)
{
  const std::string input = R"(
    (assert (= (bvadd v2 (bvmul v0 v1 v2)) (_ bv0 20)))
    (assert (= (bvadd v3 (bvmul v0 v1 v3)) (_ bv33 20)))
    )";

  Context c;
  ASTNode n = c.processProducts(input);

  std::set<ASTNode> multNodes, visited;
  collectKindNodes(n, stp::BVMULT, multNodes, visited);

  // Three binary multiplies: the shared pair and the two rewritten products.
  ASSERT_EQ(multNodes.size(), 3u);
  for (const ASTNode& p : multNodes)
    ASSERT_EQ(p.Degree(), 2u);

  // Exactly one of them is the shared node: a multiply that appears as a
  // child of both of the other two.
  int shared = 0;
  for (const ASTNode& s : multNodes)
  {
    int parents = 0;
    for (const ASTNode& p : multNodes)
      for (const ASTNode& child : p.GetChildren())
        if (child == s)
          parents++;
    if (parents == 2)
      shared++;
  }
  ASSERT_EQ(shared, 1);
}

// A larger shared operand subset falls out of repeated pair extraction.
// {v0,v1,v4,v6} is common to both sums, so two rounds pull out two shared
// pairs; the smaller sum ends as exactly the sum of those pairs and the
// larger one keeps them as operands:
//   (v0+v1+v4+v6), (v0+v1+v2+v3+v4+v5+v6)
//     -->  s1+s2, (s1+s2+v2+v3+v5)   with s1, s2 shared.
TEST(CommonSubSum_Test, overlapping_operand_subset_cascades)
{
  const std::string input = R"(
    (declare-fun v4 () (_ BitVec 20))
    (declare-fun v5 () (_ BitVec 20))
    (declare-fun v6 () (_ BitVec 20))
    (assert (= (bvmul v2 (bvadd v0 v1 v4 v6)) (_ bv0 20)))
    (assert (= (bvmul v3 (bvadd v0 v1 v2 v3 v4 v5 v6)) (_ bv33 20)))
    )";

  Context c;
  ASTNode n = c.process(input);

  std::set<ASTNode> plusNodes, visited;
  collectPlusNodes(n, plusNodes, visited);

  // The two shared pairs, the two-operand rewrite of the small sum, and the
  // five-operand rewrite of the wide one.
  ASSERT_EQ(plusNodes.size(), 4u);

  std::multiset<unsigned> degrees;
  int sharedTwice = 0;
  for (const ASTNode& s : plusNodes)
  {
    degrees.insert(s.Degree());
    int parents = 0;
    for (const ASTNode& p : plusNodes)
      for (const ASTNode& child : p.GetChildren())
        if (child == s)
          parents++;
    if (parents == 2)
      sharedTwice++;
  }
  EXPECT_EQ(degrees, (std::multiset<unsigned>{2, 2, 2, 5}));
  EXPECT_EQ(sharedTwice, 2);
}

// A pair held by three sums is built once and referenced from all three.
TEST(CommonSubSum_Test, pair_shared_by_three_sums_extracted_once)
{
  const std::string input = R"(
    (declare-fun v4 () (_ BitVec 20))
    (assert (= (bvmul v2 (bvadd v0 v1 v2)) (_ bv0 20)))
    (assert (= (bvmul v3 (bvadd v0 v1 v3)) (_ bv33 20)))
    (assert (= (bvmul v4 (bvadd v0 v1 v4)) (_ bv7 20)))
    )";

  Context c;
  ASTNode n = c.process(input);

  std::set<ASTNode> plusNodes, visited;
  collectPlusNodes(n, plusNodes, visited);

  ASSERT_EQ(plusNodes.size(), 4u);
  int sharedByThree = 0;
  for (const ASTNode& s : plusNodes)
  {
    ASSERT_EQ(s.Degree(), 2u);
    int parents = 0;
    for (const ASTNode& p : plusNodes)
      for (const ASTNode& child : p.GetChildren())
        if (child == s)
          parents++;
    if (parents == 3)
      sharedByThree++;
  }
  EXPECT_EQ(sharedByThree, 1);
}

// Nesting hides the pair -- (v0 + (v1 + v2)) and (v1 + (v0 + v3)) share
// {v0,v1} but no node, and two-operand sums are below the pass's reach --
// so extraction only fires once Flatten has widened the sums. This is the
// pipeline ordering the pass is written for.
TEST(CommonSubSum_Test, flatten_exposes_pairs_hidden_by_nesting)
{
  const std::string input = R"(
    (assert (= (bvmul v2 (bvadd v0 (bvadd v1 v2))) (_ bv0 20)))
    (assert (= (bvmul v3 (bvadd v1 (bvadd v0 v3))) (_ bv33 20)))
    )";

  Context c;
  ASTNode parsed = c.parse(input);

  ASTNode untouched = c.subSum.topLevel(parsed);
  EXPECT_EQ(untouched, parsed);

  stp::Flatten flatten(&c.mgr, &c.snf);
  ASTNode flat = flatten.topLevel(parsed);
  ASTNode extracted = c.subSum.topLevel(flat);

  std::set<ASTNode> plusNodes, visited;
  collectPlusNodes(extracted, plusNodes, visited);

  ASSERT_EQ(plusNodes.size(), 3u);
  int shared = 0;
  for (const ASTNode& s : plusNodes)
  {
    ASSERT_EQ(s.Degree(), 2u);
    int parents = 0;
    for (const ASTNode& p : plusNodes)
      for (const ASTNode& child : p.GetChildren())
        if (child == s)
          parents++;
    if (parents == 2)
      shared++;
  }
  EXPECT_EQ(shared, 1);
}

// A pair shared between a sum and a product has no node both could use:
// neither instance of the pass may pair across kinds.
TEST(CommonSubSum_Test, sum_and_product_do_not_pair)
{
  const std::string input = R"(
    (assert (= (bvmul v3 (bvadd v0 v1 v2)) (_ bv0 20)))
    (assert (= (bvadd v3 (bvmul v0 v1 v2)) (_ bv33 20)))
    )";

  Context c;
  ASTNode n = c.subProd.topLevel(c.subSum.topLevel(c.parse(input)));

  std::set<ASTNode> plusNodes, multNodes, visited;
  collectKindNodes(n, stp::BVPLUS, plusNodes, visited);
  visited.clear();
  collectKindNodes(n, stp::BVMULT, multNodes, visited);

  // One three-operand application of each kind survives untouched (plus
  // the binary wrappers the asserts are built from).
  int wideSums = 0, wideMults = 0;
  for (const ASTNode& p : plusNodes)
    if (p.Degree() == 3)
      wideSums++;
  for (const ASTNode& p : multNodes)
    if (p.Degree() == 3)
      wideMults++;
  ASSERT_EQ(wideSums, 1);
  ASSERT_EQ(wideMults, 1);
}
