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

   Context() :
   snf (*(mgr.hashingNodeFactory), mgr),
   interface(mgr, &snf),
   subSum(&mgr, &snf)
   {
    mgr.defaultNodeFactory = &snf;
    interface.startup();
    stp::GlobalParserBM = &mgr;
    stp::GlobalParserInterface = &interface;
   }

   ASTNode process(std::string input)
   {
      stp::SMT2ScanString((start_input + input).c_str());
      stp::SMT2Parse();
      smt2lex_destroy();
      ASTNode n = mgr.CreateNode(stp::AND, mgr.GetAsserts());
      std::cerr << "Pre common sub-sum " << n;
      n = subSum.topLevel(n);
      std::cerr << "Post common sub-sum " << n;
      return n;
    }
};

static void collectPlusNodes(const ASTNode& n, std::set<ASTNode>& out,
                             std::set<ASTNode>& visited)
{
  if (visited.count(n))
    return;
  visited.insert(n);
  if (n.GetKind() == stp::BVPLUS)
    out.insert(n);
  for (const ASTNode& c : n.GetChildren())
    collectPlusNodes(c, out, visited);
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
