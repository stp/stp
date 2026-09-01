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
#include <algorithm>
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

   ASTNode processKind(stp::Kind k, std::string input)
   {
      ASTNode n = parse(input);
      stp::CommonSubSum pass(&mgr, &snf, k);
      return pass.topLevel(n);
    }
};

// How many of `nodes` appear as a child of exactly `wanted` of the others.
static int nodesWithParents(const std::set<ASTNode>& nodes, int wanted)
{
  int matching = 0;
  for (const ASTNode& s : nodes)
  {
    int parents = 0;
    for (const ASTNode& p : nodes)
      for (const ASTNode& child : p.GetChildren())
        if (child == s)
          parents++;
    if (parents == wanted)
      matching++;
  }
  return matching;
}

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

// An addition whose operands are a sub-multiset of another's ends up being
// the adder they have in common, rather than having it built twice:
//   (v0 + v1 + v2), (v0 + v1 + v2 + v3)
//     -->  s = (v0 + v1);  t = (s + v2);  t, (t + v3)
// The greedy walks the smaller addition down to two operands and, at that
// point, it *is* the pair the wider one still holds. Without counting a
// two-operand addition as an adder others can reuse it votes for nothing
// from there and stops one step short, leaving `t` built twice. This is the
// shape stp#444 reduces to.
TEST(CommonSubSum_Test, sub_multiset_sum_becomes_the_shared_node)
{
  const std::string input = R"(
    (assert (= (bvmul v3 (bvadd v0 v1 v2)) (_ bv0 20)))
    (assert (= (bvmul v0 (bvadd v0 v1 v2 v3)) (_ bv33 20)))
    )";

  Context c;
  ASTNode n = c.process(input);

  std::set<ASTNode> plusNodes, visited;
  collectPlusNodes(n, plusNodes, visited);

  // s, t, and the wider addition rewritten around t: three binary adders
  // for what arrived as a three-operand and a four-operand addition.
  ASSERT_EQ(plusNodes.size(), 3u);
  for (const ASTNode& p : plusNodes)
    ASSERT_EQ(p.Degree(), 2u);

  // The smaller addition is now a child of the wider one. That is the last
  // extraction, and it is the one that does not happen without the change.
  const ASTNode& widest = *std::max_element(
      plusNodes.begin(), plusNodes.end(),
      [](const ASTNode& a, const ASTNode& b) {
        return a.GetNodeNum() < b.GetNodeNum();
      });

  int shared = 0;
  for (const ASTNode& s : plusNodes)
    for (const ASTNode& child : widest.GetChildren())
      if (child == s)
        shared++;
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
// pairs, and once the smaller sum has narrowed to exactly those pairs it
// counts as an adder the wider one can reuse, so a third round finishes
// the job:
//   (v0+v1+v4+v6), (v0+v1+v2+v3+v4+v5+v6)
//     -->  t = s1+s2;  t, (t+v2+v3+v5)   with s1, s2 under t alone.
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

  // The two pairs, the narrowed small sum over them, and the wide sum
  // rewritten around the small one.
  ASSERT_EQ(plusNodes.size(), 4u);

  std::multiset<unsigned> degrees;
  int sharedOnce = 0;
  for (const ASTNode& s : plusNodes)
  {
    degrees.insert(s.Degree());
    int parents = 0;
    for (const ASTNode& p : plusNodes)
      for (const ASTNode& child : p.GetChildren())
        if (child == s)
          parents++;
    if (parents == 1)
      sharedOnce++;
  }
  EXPECT_EQ(degrees, (std::multiset<unsigned>{2, 2, 2, 4}));
  // s1 and s2 sit under the small sum, and the small sum under the wide
  // one: a chain, not two duplicated adders.
  EXPECT_EQ(sharedOnce, 3);
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

// The same extraction applies to each associative-commutative kind. The
// multiplies again keep the equalities from being solved word-level at node
// creation, so the applications genuinely reach the pass.
TEST(CommonSubSum_Test, shared_pair_factored_for_bvxor)
{
  const std::string input = R"(
    (assert (= (bvmul v2 (bvxor v0 v1 v2)) (_ bv0 20)))
    (assert (= (bvmul v3 (bvxor v0 v1 v3)) (_ bv33 20)))
    )";

  Context c;
  ASTNode n = c.processKind(stp::BVXOR, input);

  std::set<ASTNode> nodes, visited;
  collectKindNodes(n, stp::BVXOR, nodes, visited);

  ASSERT_EQ(nodes.size(), 3u);
  for (const ASTNode& p : nodes)
    ASSERT_EQ(p.Degree(), 2u);
  EXPECT_EQ(nodesWithParents(nodes, 2), 1);
}

TEST(CommonSubSum_Test, shared_pair_factored_for_bvand)
{
  const std::string input = R"(
    (assert (= (bvmul v2 (bvand v0 v1 v2)) (_ bv0 20)))
    (assert (= (bvmul v3 (bvand v0 v1 v3)) (_ bv33 20)))
    )";

  Context c;
  ASTNode n = c.processKind(stp::BVAND, input);

  std::set<ASTNode> nodes, visited;
  collectKindNodes(n, stp::BVAND, nodes, visited);

  ASSERT_EQ(nodes.size(), 3u);
  for (const ASTNode& p : nodes)
    ASSERT_EQ(p.Degree(), 2u);
  EXPECT_EQ(nodesWithParents(nodes, 2), 1);
}

// bvor never reaches the pass as BVOR: the factory lowers it to
// BVNOT/BVAND at creation, so its shared pair surfaces -- negated -- in
// the BVAND run.
TEST(CommonSubSum_Test, bvor_reaches_extraction_as_bvand)
{
  const std::string input = R"(
    (assert (= (bvmul v2 (bvor v0 v1 v2)) (_ bv0 20)))
    (assert (= (bvmul v3 (bvor v0 v1 v3)) (_ bv33 20)))
    )";

  Context c;
  ASTNode n = c.processKind(stp::BVAND, input);

  std::set<ASTNode> nodes, visited;
  collectKindNodes(n, stp::BVAND, nodes, visited);

  ASSERT_EQ(nodes.size(), 3u);
  for (const ASTNode& p : nodes)
    ASSERT_EQ(p.Degree(), 2u);
  EXPECT_EQ(nodesWithParents(nodes, 2), 1);
}

TEST(CommonSubSum_Test, shared_pair_factored_for_boolean_xor)
{
  const std::string input = R"(
    (declare-fun a () Bool)
    (declare-fun b () Bool)
    (declare-fun p () Bool)
    (declare-fun q () Bool)
    (assert (xor a b p))
    (assert (xor a b q))
    )";

  Context c;
  ASTNode n = c.processKind(stp::XOR, input);

  std::set<ASTNode> nodes, visited;
  collectKindNodes(n, stp::XOR, nodes, visited);

  ASSERT_EQ(nodes.size(), 3u);
  for (const ASTNode& p : nodes)
    ASSERT_EQ(p.Degree(), 2u);
  EXPECT_EQ(nodesWithParents(nodes, 2), 1);
}

// The shared conjunctions sit under ORs so that the top-level conjunction
// -- itself an AND, and too narrow to enumerate -- stays out of the way.
TEST(CommonSubSum_Test, shared_pair_factored_for_boolean_and)
{
  const std::string input = R"(
    (declare-fun a () Bool)
    (declare-fun b () Bool)
    (declare-fun p () Bool)
    (declare-fun q () Bool)
    (declare-fun r () Bool)
    (declare-fun s () Bool)
    (assert (or r (and a b p)))
    (assert (or s (and a b q)))
    )";

  Context c;
  ASTNode n = c.processKind(stp::AND, input);

  std::set<ASTNode> nodes, visited;
  collectKindNodes(n, stp::AND, nodes, visited);

  // The top-level conjunction of the two asserts, the shared pair, and the
  // two rewritten conjunctions.
  ASSERT_EQ(nodes.size(), 4u);
  EXPECT_EQ(nodesWithParents(nodes, 2), 1);
}

TEST(CommonSubSum_Test, shared_pair_factored_for_boolean_or)
{
  const std::string input = R"(
    (declare-fun a () Bool)
    (declare-fun b () Bool)
    (declare-fun p () Bool)
    (declare-fun q () Bool)
    (assert (or a b p))
    (assert (or a b q))
    )";

  Context c;
  ASTNode n = c.processKind(stp::OR, input);

  std::set<ASTNode> nodes, visited;
  collectKindNodes(n, stp::OR, nodes, visited);

  ASSERT_EQ(nodes.size(), 3u);
  for (const ASTNode& p : nodes)
    ASSERT_EQ(p.Degree(), 2u);
  EXPECT_EQ(nodesWithParents(nodes, 2), 1);
}

// A substitution can hand a self-inverse kind its own pair node twice:
// extracting {v0,v1} from (v0 ^ v1 ^ (v0 ^ v1)) removes both operands and
// inserts the hash-consed pair beside the copy already there. The factory
// folds the rebuilt application to zero, and the enclosing assert to true.
TEST(CommonSubSum_Test, duplicate_arrival_collapses_soundly)
{
  const std::string input = R"(
    (assert (= (bvmul v2 (bvxor v0 v1 v2)) (_ bv33 20)))
    (assert (= (bvmul v3 (bvxor v0 v1 (bvxor v0 v1))) (_ bv0 20)))
    )";

  Context c;
  ASTNode n = c.processKind(stp::BVXOR, input);

  std::set<ASTNode> nodes, visited;
  collectKindNodes(n, stp::BVXOR, nodes, visited);

  // The second assert folded away; the first keeps the shared pair nested
  // in its rewritten application.
  ASSERT_EQ(nodes.size(), 2u);
  for (const ASTNode& p : nodes)
    ASSERT_EQ(p.Degree(), 2u);
  EXPECT_EQ(nodesWithParents(nodes, 1), 1);
}
