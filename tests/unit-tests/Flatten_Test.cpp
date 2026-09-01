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
#include "stp/Simplifier/Flatten.h"
#include <gtest/gtest.h>
#include <stdio.h>
#include <unordered_set>


  const std::string start_input = R"(
  (set-logic QF_BV)
  (set-info :smt-lib-version 2.0)
  (set-info :category "check")
  (set-info :status sat)

  (declare-fun v0 () (_ BitVec 20))
  (declare-fun v1 () (_ BitVec 20))
  (declare-fun v2 () (_ BitVec 20))
  (declare-fun v3 () (_ BitVec 20))
  (declare-fun v4 () (_ BitVec 20))

  (declare-fun x0 () (_ BitVec 1))

  (declare-fun a () Bool)
  (declare-fun b () Bool)
  (declare-fun c () Bool)

  (push 1)
  )";

struct Context
{
   stp::STPMgr mgr;
   SimplifyingNodeFactory snf;
   stp::Cpp_interface interface;
   stp::Flatten flatten;

   Context() :
   snf (*(mgr.hashingNodeFactory), mgr),
   interface(mgr, &snf),
   flatten(&mgr, &snf)
   { 
    mgr.defaultNodeFactory = &snf;
    interface.startup();
    stp::GlobalParserBM = &mgr;
    stp::GlobalParserInterface = &interface;
   }
   
   ASTNode parseRaw(std::string input)
   {
      stp::SMT2ScanString(input.c_str());
      stp::SMT2Parse();
      // TODO assert it was parsed properly.
      smt2lex_destroy();
      return mgr.CreateNode(stp::AND, mgr.GetAsserts());
   }

   ASTNode parse(std::string input)
   {
      return parseRaw(start_input + input);
   }

   ASTNode process(std::string input)
   {
      ASTNode n = parse(input);
      std::cerr << "Pre flatten " << n;
      n = flatten.topLevel(n);
      std::cerr << "Post flatten "<< n;
      return n;
    }
};

// Whether some node of kind k has a child of kind k.
static bool hasSameKindEdge(const ASTNode& n, stp::Kind k)
{
  std::unordered_set<uint64_t> visited;
  ASTVec stack{n};
  while (!stack.empty())
  {
    const ASTNode node = stack.back();
    stack.pop_back();
    if (!visited.insert(node.GetNodeNum()).second)
      continue;
    for (const ASTNode& c : node.GetChildren())
    {
      if (node.GetKind() == k && c.GetKind() == k)
        return true;
      stack.push_back(c);
    }
  }
  return false;
}

TEST(Flatten_Test , __LINE__)
{
  const std::string input = R"(
    (assert (xor b (xor a b ) a a a) )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(n, c.mgr.ASTFalse);
}

// Multiplication chains flatten too: the two groupings become one wide
// product each, and the same node.
TEST(Flatten_Test, __LINE__)
{
  const std::string input = R"(
        (assert (=
                  (bvmul v0 (bvmul v1 v2))
                  (bvmul (bvmul v0 v1) v2)
                )
        )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(n, c.mgr.ASTTrue);
}

TEST(Flatten_Test, __LINE__)
{
  const std::string input = R"(
        (assert (= 
                  (and b (and a b ) c a a a) 
                  (and b c a) 
                )
        )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(n, c.mgr.ASTTrue);
}

// This fails because the node count for (and a b) is updated to one after it's been added to the top-level conjunct.
TEST(Flatten_Test, DISABLED__LINE__)
{
  const std::string input = R"(
        (assert
          (=
            (and 
                (and a b )
                (and a b (and a b ) )
                (and b (and a b ) (and a b ) (and a b ) c a a a)
                (and a (and a b ) ) 
            )
            (and a b c)
          )
        ))";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(n, c.mgr.ASTTrue);
}



// The three conjuncts contain one another: expanding the chainable
// equalities makes each later assertion an AND wrapping the previous one.
// Merging them into the top-level conjunction sends only already-seen
// entries through the AND/OR duplicate filter, so the rebuilt AND has
// fewer children than the original's degree -- which is fine, and used to
// trip an over-strong assert. Found by murxla.
TEST(Flatten_Test, __LINE__)
{
  const std::string input = R"(
    (assert (= true a (= b a)))
    (assert (and (= true a (= b a)) a))
    (assert (= (and (= true a (= b a)) a) true a))
    )";

  Context c;
  ASTNode n = c.process(input);
  ASTNode a = c.mgr.LookupOrCreateSymbol("a");
  ASTNode b = c.mgr.LookupOrCreateSymbol("b");
  ASSERT_EQ(n, c.mgr.CreateNode(stp::AND, a, b));
}

TEST(Flatten_Test, __LINE__)
{
  const std::string input = R"(
    (assert (= (bvadd v0 (bvadd v1 v0) v1 ) (bvadd v0 v1 v0 v1 )))
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(n, c.mgr.ASTTrue);
}

TEST(Flatten_Test, __LINE__)
{
  const std::string input = R"(
    (assert (= (bvadd v0 (bvadd v1 v0) v1 v0 ) 
               (bvadd v0 v1 v0 v1 v0 )))
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(n, c.mgr.ASTTrue);
}

TEST(Flatten_Test, __LINE__)
{
  const std::string input = R"(
    (assert (= (bvadd v0 (bvadd v1 v0) v1 v0 )
               (bvadd v0 v0 (bvadd v1 v0 v1) )))
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(n, c.mgr.ASTTrue);
}

struct KindCase
{
  const char* name;
  stp::Kind kind; // the kind whose nesting the input produces
  std::string input;
};

// Every associative+commutative kind flattens an unshared same-kind child:
// the two groupings meet at the same wide node, so the equality folds to
// true when the parent is rebuilt.
//
// bvor is checked as BVAND because the simplifying factory lowers BVOR to
// BVNOT/BVAND at creation; the nested chain it leaves behind is a BVAND one.
TEST(Flatten_Test, EachKindFlattensAnUnsharedChild)
{
  const std::vector<KindCase> cases = {
      {"and", stp::AND,
       "(assert (= (and a (and b c)) (and (and a b) c)))"},
      {"or", stp::OR,
       "(assert (= (or a (or b c)) (or (or a b) c)))"},
      {"xor", stp::XOR,
       "(assert (= (xor a (xor b c)) (xor (xor a b) c)))"},
      {"bvand", stp::BVAND,
       "(assert (= (bvand v0 (bvand v1 v2)) (bvand (bvand v0 v1) v2)))"},
      {"bvor", stp::BVAND,
       "(assert (= (bvor v0 (bvor v1 v2)) (bvor (bvor v0 v1) v2)))"},
      {"bvxor", stp::BVXOR,
       "(assert (= (bvxor v0 (bvxor v1 v2)) (bvxor (bvxor v0 v1) v2)))"},
      {"bvadd", stp::BVPLUS,
       "(assert (= (bvadd v0 (bvadd v1 v2)) (bvadd (bvadd v0 v1) v2)))"},
      {"bvmul", stp::BVMULT,
       "(assert (= (bvmul v0 (bvmul v1 v2)) (bvmul (bvmul v0 v1) v2)))"},
  };

  for (const auto& tc : cases)
  {
    SCOPED_TRACE(tc.name);
    Context c;
    ASTNode pre = c.parse(tc.input);
    // The factory must not have flattened at creation, or this proves nothing.
    ASSERT_TRUE(hasSameKindEdge(pre, tc.kind));
    ASSERT_NE(pre, c.mgr.ASTTrue);
    ASTNode post = c.flatten.topLevel(pre);
    EXPECT_EQ(post, c.mgr.ASTTrue);
  }
}

// A same-kind child with two parents stays nested: merging it into one
// parent would leave the other still referencing it, growing the DAG.
// The second assertion is the second parent.
TEST(Flatten_Test, NoKindFlattensASharedChild)
{
  const std::vector<KindCase> cases = {
      // The nested ANDs sit under ORs: conjuncts of the top-level AND
      // flatten irrespective of sharing, which is not what's under test.
      {"and", stp::AND,
       "(declare-fun d () Bool)(declare-fun e () Bool)"
       "(assert (or b (and d (and a c))))"
       "(assert (or e (and a c)))"},
      {"or", stp::OR,
       "(declare-fun d () Bool)"
       "(assert (or b (or a c)))"
       "(assert (or d (or a c)))"},
      {"xor", stp::XOR,
       "(declare-fun d () Bool)"
       "(assert (xor b (xor a c)))"
       "(assert (xor d (xor a c)))"},
      {"bvand", stp::BVAND,
       "(assert (= v3 (bvand v2 (bvand v0 v1))))"
       "(assert (= v4 (bvand v0 v1)))"},
      {"bvor", stp::BVAND,
       "(assert (= v3 (bvor v2 (bvor v0 v1))))"
       "(assert (= v4 (bvor v0 v1)))"},
      {"bvxor", stp::BVXOR,
       "(assert (= v3 (bvxor v2 (bvxor v0 v1))))"
       "(assert (= v4 (bvxor v0 v1)))"},
      {"bvadd", stp::BVPLUS,
       "(assert (= v3 (bvadd v2 (bvadd v0 v1))))"
       "(assert (= v4 (bvadd v0 v1)))"},
      {"bvmul", stp::BVMULT,
       "(assert (= v3 (bvmul v2 (bvmul v0 v1))))"
       "(assert (= v4 (bvmul v0 v1)))"},
  };

  for (const auto& tc : cases)
  {
    SCOPED_TRACE(tc.name);
    Context c;
    ASTNode pre = c.parse(tc.input);
    ASSERT_TRUE(hasSameKindEdge(pre, tc.kind));
    ASTNode post = c.flatten.topLevel(pre);
    EXPECT_EQ(post, pre);
  }
}

// Conjuncts of the top-level AND flatten even when shared: the child node
// survives under its other parent, so nothing is duplicated.
TEST(Flatten_Test, TopLevelAndFlattensASharedConjunct)
{
  const std::string input = R"(
    (declare-fun d () Bool)
    (assert (and a b))
    (assert (or d (and a b)))
    )";

  Context c;
  ASTNode pre = c.parse(input);
  ASSERT_TRUE(hasSameKindEdge(pre, stp::AND));
  ASTNode post = c.flatten.topLevel(pre);

  ASTNode a = c.mgr.LookupOrCreateSymbol("a");
  ASTNode b = c.mgr.LookupOrCreateSymbol("b");
  ASTNode d = c.mgr.LookupOrCreateSymbol("d");
  ASTNode inner = c.mgr.CreateNode(stp::AND, a, b);
  ASTNode expected =
      c.mgr.CreateNode(stp::AND, a, b, c.mgr.CreateNode(stp::OR, d, inner));
  EXPECT_EQ(post, expected);
}

// A node with 257 parents is shared however the count is stored: with the
// old uint8_t counter the reference count wrapped to 1 and the node was
// flattened into its first parent.
TEST(Flatten_Test, ManyParentsIsStillShared)
{
  Context c;
  const unsigned width = 20;
  ASTNode v0 = c.mgr.CreateSymbol("m_v0", 0, width);
  ASTNode v1 = c.mgr.CreateSymbol("m_v1", 0, width);
  ASTNode shared = c.mgr.CreateTerm(stp::BVPLUS, width, v0, v1);

  ASTVec conjuncts;
  for (unsigned i = 0; i < 257; i++)
  {
    const std::string u_name = "m_u" + std::to_string(i);
    const std::string w_name = "m_w" + std::to_string(i);
    ASTNode u = c.mgr.CreateSymbol(u_name.c_str(), 0, width);
    ASTNode w = c.mgr.CreateSymbol(w_name.c_str(), 0, width);
    ASTNode parent = c.mgr.CreateTerm(stp::BVPLUS, width, u, shared);
    conjuncts.push_back(c.mgr.CreateNode(stp::EQ, w, parent));
  }
  ASTNode pre = c.mgr.CreateNode(stp::AND, conjuncts);
  ASSERT_TRUE(hasSameKindEdge(pre, stp::BVPLUS));
  ASTNode post = c.flatten.topLevel(pre);
  EXPECT_EQ(post, pre);
}

// A NOT among XOR operands is pulled above the XOR: the factory strips it
// at creation and accumulates the parity, and flattening then widens the
// stripped chain. Both groupings must meet at the same NOT(XOR(a,b,c)).
TEST(Flatten_Test, XorFlattensThroughAPulledUpNot)
{
  const std::string input = R"(
    (assert (= (xor a (not (xor b c))) (not (xor (xor a b) c))))
    )";

  Context c;
  ASTNode pre = c.parse(input);
  ASSERT_TRUE(hasSameKindEdge(pre, stp::XOR));
  ASSERT_NE(pre, c.mgr.ASTTrue);
  ASTNode post = c.flatten.topLevel(pre);
  EXPECT_EQ(post, c.mgr.ASTTrue);
}

// The BVNOT analogue, odd parity: one BVNOT below meets one written above.
TEST(Flatten_Test, BvxorFlattensThroughAPulledUpBvnot)
{
  const std::string input = R"(
    (assert (= (bvxor v0 (bvnot (bvxor v1 v2)))
               (bvnot (bvxor (bvxor v0 v1) v2))))
    )";

  Context c;
  ASTNode pre = c.parse(input);
  ASSERT_TRUE(hasSameKindEdge(pre, stp::BVXOR));
  ASSERT_NE(pre, c.mgr.ASTTrue);
  ASTNode post = c.flatten.topLevel(pre);
  EXPECT_EQ(post, c.mgr.ASTTrue);
}

// Even parity: two pulled-up BVNOTs cancel and no BVNOT survives.
TEST(Flatten_Test, TwoPulledUpBvnotsCancel)
{
  const std::string input = R"(
    (assert (= (bvxor (bvnot v0) (bvnot (bvxor v1 v2)))
               (bvxor v0 v1 v2)))
    )";

  Context c;
  ASTNode pre = c.parse(input);
  ASSERT_NE(pre, c.mgr.ASTTrue);
  ASTNode post = c.flatten.topLevel(pre);
  EXPECT_EQ(post, c.mgr.ASTTrue);
}

// Pulling the BVNOT up must not defeat the sharing rule: the xor chain the
// strip exposes is still shared, so it stays nested.
TEST(Flatten_Test, SharedChildExposedByBvnotStripStaysShared)
{
  const std::string input = R"(
    (assert (= v3 (bvxor v2 (bvnot (bvxor v0 v1)))))
    (assert (= v4 (bvxor v0 v1)))
    )";

  Context c;
  ASTNode pre = c.parse(input);
  ASSERT_TRUE(hasSameKindEdge(pre, stp::BVXOR));
  ASTNode post = c.flatten.topLevel(pre);
  EXPECT_EQ(post, pre);
}

// FP arithmetic is commutative but not associative under rounding, so no
// FP kind may flatten. FP_ADD also carries its rounding mode as a child.
TEST(Flatten_Test, FpAddChainIsLeftAlone)
{
  const std::string input = R"(
    (set-logic QF_FP)
    (declare-fun f0 () (_ FloatingPoint 8 24))
    (declare-fun f1 () (_ FloatingPoint 8 24))
    (declare-fun f2 () (_ FloatingPoint 8 24))
    (assert (fp.eq (fp.add RNE f0 (fp.add RNE f1 f2)) f0))
    )";

  Context c;
  ASTNode pre = c.parseRaw(input);
  ASSERT_TRUE(hasSameKindEdge(pre, stp::FP_ADD));
  ASTNode post = c.flatten.topLevel(pre);
  EXPECT_EQ(post, pre);
}
