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
#include "stp/Simplifier/StrengthReduction.h"
#include <gtest/gtest.h>
#include <stdio.h>


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
   stp::StrengthReduction sr;
   stp::NodeDomainAnalysis nda;

   Context() :
   snf (*(mgr.hashingNodeFactory), mgr),
   interface(mgr, &snf),
   sr(&snf, &mgr.UserFlags),
   nda(&mgr)
   { 
    mgr.defaultNodeFactory = &snf;
    interface.startup();
    stp::GlobalParserBM = &mgr;
    stp::GlobalParserInterface = &interface;
   }
   
   bool present(const Kind k, const ASTNode& n)
   {
      if (n.GetKind() == k)
        return true;

      for (const auto& c: n)
        if (present(k,c))
          return true;

      return false;
   }

   // The first node of this kind in a pre-order walk, or a null node when
   // there is none. For asserting on the shape a rewrite left behind, where
   // "a node of this kind is somewhere in the tree" is too weak a question.
   ASTNode find(const Kind k, const ASTNode& n)
   {
      if (n.GetKind() == k)
        return n;

      for (const auto& c: n)
      {
        const ASTNode r = find(k,c);
        if (!r.IsNull())
          return r;
      }

      return ASTNode();
   }

   ASTNode process(std::string input)
   {
      stp::SMT2ScanString((start_input + input).c_str());
      stp::SMT2Parse();
      // TODO assert it was parsed properly.
      smt2lex_destroy();
      ASTNode n = mgr.CreateNode(stp::AND, mgr.GetAsserts());
      std::cerr << "Pre Strength reduction " << n;
      n = sr.topLevel(n, nda);
      std::cerr << "Post Strengthen reduction"<< n;
      return n;
    }
};

// signed comparison converted to unsigned.
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (
      assert 
            (bvsgt 
                  ((_ zero_extend 1) v0)  
                  ((_ zero_extend 1) v1) 
            )
    )
    
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_TRUE(c.present(stp::BVGT, n));
}

// signed division converted to unsigned.
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (
      assert 
            ( = 
              (bvsdiv 
                    (bvudiv v0 (_ bv3 20))  
                    (bvudiv v1 (_ bv3 20))  
              )
            v2
            )
    )
    
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_FALSE(c.present(stp::SBVDIV, n));
  ASSERT_TRUE(c.present(stp::BVDIV, n));
}

// Signed division is removed
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (
      assert 
            ( = 
              (bvsdiv
                    (concat  (_ bv1 1 ) v0)  
                    (concat  (_ bv1 1 ) v1)  
              )
            (concat  (_ bv1 1 ) v2)  
            )
    )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_FALSE(c.present(stp::SBVDIV, n));
  ASSERT_TRUE(c.present(stp::BVDIV, n));
}


// plus to OR.
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (
      assert 
            ( = 
              (bvadd
                    (concat v0 (_ bv0 20))  
                    (concat (_ bv0 20) v1 )  
              )
            (concat v2 v3)
            )
    )
    
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_FALSE(c.present(stp::BVPLUS, n));
}

// Signed shift is converted to normal shift.
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (
      assert 
            ( = 
              (bvashr
                    (bvudiv v0 (_ bv3 20))  
                    v1
              )
            v2
            )
    )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_TRUE(c.present(stp::BVRIGHTSHIFT, n));
}

// Every equality in "n" compares against a constant.
static bool eqsAgainstConstants(const ASTNode& n)
{
  if (n.GetKind() == stp::EQ && !n[0].isConstant() && !n[1].isConstant())
    return false;

  for (const auto& c : n)
    if (!eqsAgainstConstants(c))
      return false;

  return true;
}

// The sides' intervals, [0,99] and [99,148], meet at exactly one
// point, so the equality splits into equalities against that point.
// Both sides have too many values for the set domain to track.
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (
      assert
            ( =
              (bvurem v0 (_ bv100 20))
              (bvadd (bvurem v1 (_ bv50 20)) (_ bv99 20))
            )
    )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_TRUE(c.present(stp::EQ, n));
  ASSERT_TRUE(eqsAgainstConstants(n));
}


// The following pin down that differing leading constant bits decide
// comparisons here (via the fixed-bit transfer functions for concat and
// the comparisons), so neither the simplifying node factory nor the
// Simplifier needs a leading-constant rule.

// Equality with differing leading constant bits folds to false.
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (
      assert
            ( =
              (concat (_ bv1 1) v0)
              (concat (_ bv0 1) v1)
            )
    )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(n, c.mgr.ASTFalse);
}

// Unsigned comparison decided by differing leading constant bits.
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (
      assert
            (bvugt
              (concat (_ bv0 1) v0)
              (concat (_ bv1 1) v1)
            )
    )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(n, c.mgr.ASTFalse);
}

// Signed comparison with differing sign bits: positive > negative.
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (
      assert
            (bvsgt
              (concat (_ bv0 1) v0)
              (concat (_ bv1 1) v1)
            )
    )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(n, c.mgr.ASTTrue);
}

// Signed comparison, same sign bit: the unsigned order of the leading
// constant bits decides.
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (
      assert
            (bvsgt
              (concat (_ bv3 2) v0)
              (concat (_ bv2 2) v1)
            )
    )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(n, c.mgr.ASTTrue);
}

// Signed add overflow with operands of known-opposite sign folds to false:
// overflow requires the operands to share a sign.
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (
      assert
            (bvsaddo
              (concat (_ bv0 1) v0)
              (concat (_ bv1 1) v1)
            )
    )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(n, c.mgr.ASTFalse);
}

// Signed sub overflow with operands of known-equal sign folds to false:
// overflow requires the operands to differ in sign.
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (
      assert
            (bvssubo
              (concat (_ bv1 1) v0)
              (concat (_ bv1 1) v1)
            )
    )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(n, c.mgr.ASTFalse);
}

// Signed add overflow with matching sign bits is not decided: the node
// still contains the overflow predicate.
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (
      assert
            (bvsaddo
              (concat (_ bv1 1) v0)
              (concat (_ bv1 1) v1)
            )
    )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_TRUE(c.present(stp::BVSADDO, n));
}

static bool presentWithWidth(const stp::Kind k, const ASTNode& n,
                             const unsigned width)
{
  if (n.GetKind() == k && n.GetValueWidth() == width)
    return true;

  for (const auto& c : n)
    if (presentWithWidth(k, c, width))
      return true;

  return false;
}

// A division whose dividend has fixed leading zero bits (here via a
// mask) narrows to the width that can be non-zero. With a constant
// divisor that fits, the guard folds away and only the narrow division
// remains.
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (
      assert
            ( = v2
              (bvudiv (bvand v0 (_ bv1023 20)) (_ bv100 20))
            )
    )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_FALSE(presentWithWidth(stp::BVDIV, n, 20));
  ASSERT_TRUE(presentWithWidth(stp::BVDIV, n, 10));
}

// When the constant divisor doesn't fit into the narrowed width it
// exceeds the dividend, so the quotient folds to zero outright.
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (
      assert
            ( = v2
              (bvudiv (bvand v0 (_ bv15 20)) (_ bv100 20))
            )
    )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_FALSE(c.present(stp::BVDIV, n));
}

// The remainder version: a dividend below the divisor is returned
// unchanged, so the remainder disappears.
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (
      assert
            ( = v2
              (bvurem (bvand v0 (_ bv15 20)) (_ bv100 20))
            )
    )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_FALSE(c.present(stp::BVMOD, n));
  ASSERT_TRUE(c.present(stp::BVAND, n));
}

// A sign extension whose argument's top bit is fixed becomes a concat.
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (
      assert
            ( = v2
              ((_ sign_extend 4) (bvand ((_ extract 15 0) v0) (_ bv1023 16)))
            )
    )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_FALSE(c.present(stp::BVSX, n));
}

// A multiplication whose operands are masked down narrows to the width
// the product can occupy: here 2 + 3 bits.
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (
      assert
            ( = v2
              (bvmul (bvand v0 (_ bv3 20)) (bvand v1 (_ bv7 20)))
            )
    )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_FALSE(presentWithWidth(stp::BVMULT, n, 20));
  ASSERT_TRUE(presentWithWidth(stp::BVMULT, n, 5));
}

// An addition of two masked operands narrows to the width the sum can
// occupy: here 4 + 1 carry bits.
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (
      assert
            ( = v2
              (bvadd (bvand v0 (_ bv15 20)) (bvand v1 (_ bv15 20)))
            )
    )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_FALSE(presentWithWidth(stp::BVPLUS, n, 20));
  ASSERT_TRUE(presentWithWidth(stp::BVPLUS, n, 5));
}

// Two additions over the same masked operands, one of them carrying an extra
// one-bit addend, narrow to the *same* width. Bounding the sum by the sum of
// the operands' bounds is what makes that true: allowing the widest operand
// ceil(log2(degree)) bits of carry instead would read the operand count, put
// the four-operand sum in 6 bits and the five-operand one in 7, and leave the
// two sharing no operand node at all. Issue #444.
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (
      assert
            (and
              ( = v4
                (bvadd (bvand v0 (_ bv15 20)) (bvand v1 (_ bv15 20))
                       (bvand v2 (_ bv15 20)) (bvand v3 (_ bv15 20)))
              )
              ( = v4
                (bvadd (bvand v0 (_ bv15 20)) (bvand v1 (_ bv15 20))
                       (bvand v2 (_ bv15 20)) (bvand v3 (_ bv15 20))
                       ((_ zero_extend 19) x0))
              )
            )
    )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_FALSE(presentWithWidth(stp::BVPLUS, n, 20));
  ASSERT_FALSE(presentWithWidth(stp::BVPLUS, n, 7));
  ASSERT_TRUE(presentWithWidth(stp::BVPLUS, n, 6));
}

// An addition whose operands split at a bit boundary becomes a concat:
// no adder, no bitwise operation at all.
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (
      assert
            ( = v2
              (bvadd (bvand v0 (_ bv240 20)) (bvand v1 (_ bv15 20)))
            )
    )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_FALSE(c.present(stp::BVPLUS, n));
  ASSERT_FALSE(c.present(stp::BVNOT, n));
  ASSERT_TRUE(c.present(stp::BVCONCAT, n));
}


// A read moves past a write whose index disagrees with it on a fixed bit.
// The masks make the low bit of one index zero and of the other one, which
// the node factory's own chase cannot see.
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (declare-fun arr () (Array (_ BitVec 4) (_ BitVec 8)))
    (declare-fun x () (_ BitVec 4))
    (declare-fun y () (_ BitVec 4))
    (
      assert
            ( =
              (select (store arr (bvand x #xC) #x01) (bvor y #x1))
              #x02
            )
    )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_TRUE(c.present(stp::READ, n));
  ASSERT_FALSE(c.present(stp::WRITE, n));
}

// Disjoint intervals, with no fixed bit to separate them: the written
// index lies in [1,4] and the read index in [5,8].
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (declare-fun arr () (Array (_ BitVec 4) (_ BitVec 8)))
    (declare-fun x () (_ BitVec 4))
    (declare-fun y () (_ BitVec 4))
    (
      assert
            ( =
              (select
                (store arr (bvadd (bvand x #x3) #x1) #x01)
                (bvadd (bvand y #x3) #x5))
              #x02
            )
    )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_TRUE(c.present(stp::READ, n));
  ASSERT_FALSE(c.present(stp::WRITE, n));
}

// Only the value sets separate these: {2,5} and {3,4} share a fixed-bit
// pattern and their hulls [2,5] and [3,4] overlap.
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (declare-fun arr () (Array (_ BitVec 4) (_ BitVec 8)))
    (
      assert
            ( =
              (select
                (store arr (ite a #x2 #x5) #x01)
                (ite b #x3 #x4))
              #x02
            )
    )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_TRUE(c.present(stp::READ, n));
  ASSERT_FALSE(c.present(stp::WRITE, n));
}

// Both indexes are masked the same way, so they might be equal and the
// write has to stay.
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (declare-fun arr () (Array (_ BitVec 4) (_ BitVec 8)))
    (declare-fun x () (_ BitVec 4))
    (declare-fun y () (_ BitVec 4))
    (
      assert
            ( =
              (select (store arr (bvand x #x3) #x01) (bvand y #x3))
              #x02
            )
    )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_TRUE(c.present(stp::WRITE, n));
}

// Nothing is known about either index, so nothing is skipped.
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (declare-fun arr () (Array (_ BitVec 4) (_ BitVec 8)))
    (declare-fun x () (_ BitVec 4))
    (declare-fun y () (_ BitVec 4))
    (
      assert
            ( = (select (store arr x #x01) y) #x02 )
    )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_TRUE(c.present(stp::WRITE, n));
}

// Several writes in one chase: both written indexes are even and the read
// index is odd, so the read reaches the base array.
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (declare-fun arr () (Array (_ BitVec 4) (_ BitVec 8)))
    (declare-fun x () (_ BitVec 4))
    (declare-fun y () (_ BitVec 4))
    (declare-fun z () (_ BitVec 4))
    (
      assert
            ( =
              (select
                (store (store arr (bvand x #xE) #x01) (bvand y #xC) #x03)
                (bvor z #x1))
              #x02
            )
    )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_TRUE(c.present(stp::READ, n));
  ASSERT_FALSE(c.present(stp::WRITE, n));
}

// The chase stops at the first write that might alias, and keeps the ones
// below it. The outer write is to an odd index, which the read's mask rules
// out; the inner one is to an unconstrained index, which it cannot.
//
// The masks are deliberately misaligned (two low bits against one), because
// aligned ones are already handled without this pass: the fixed-bit
// reduction below rewrites each masked index to a concat, and the node
// factory's own chase then splits the two concats and folds the index
// equality to false by itself.
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (declare-fun arr () (Array (_ BitVec 4) (_ BitVec 8)))
    (declare-fun x () (_ BitVec 4))
    (declare-fun y () (_ BitVec 4))
    (declare-fun z () (_ BitVec 4))
    (
      assert
            ( =
              (select
                (store (store arr z #x03) (bvor y #x1) #x01)
                (bvand x #xC))
              #x02
            )
    )
    )";

  Context c;
  ASTNode n = c.process(input);

  // Exactly one write survives, the inner one: the read sits on a write
  // whose index is the unconstrained symbol and whose array is the base.
  const ASTNode read = c.find(stp::READ, n);
  ASSERT_FALSE(read.IsNull());
  ASSERT_EQ(stp::WRITE, read[0].GetKind());
  ASSERT_EQ(stp::SYMBOL, read[0][1].GetKind());
  ASSERT_EQ(stp::SYMBOL, read[0][0].GetKind());
}


// A write the read misses is deleted even when a write that might alias
// sits above it. The read index is odd, the top write's index is a bare
// symbol (so it might be that odd index), and the one below it is even.
// Both writes belong to this chain alone, so rebuilding the chain around
// the gap is strictly smaller.
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (declare-fun arr () (Array (_ BitVec 4) (_ BitVec 8)))
    (declare-fun x () (_ BitVec 4))
    (declare-fun y () (_ BitVec 4))
    (declare-fun s () (_ BitVec 4))
    (
      assert
            ( =
              (select
                (store (store arr (bvand y #xE) #x03) s #x01)
                (bvor x #x1))
              #x02
            )
    )
    )";

  Context c;
  ASTNode n = c.process(input);

  // One write is left, the symbolic one, sitting straight on the array.
  const ASTNode read = c.find(stp::READ, n);
  ASSERT_FALSE(read.IsNull());
  ASSERT_EQ(stp::WRITE, read[0].GetKind());
  ASSERT_EQ(stp::SYMBOL, read[0][1].GetKind());
  ASSERT_EQ(stp::SYMBOL, read[0][0].GetKind());
}

// The same chain, with the even write also read somewhere else. It is no
// longer this chain's to delete: rebuilding around the gap would copy the
// writes above it rather than replace them, so the chain stays whole.
TEST(StrengthReduction_Test , __LINE__)
{
  const std::string input = R"(
    (declare-fun arr () (Array (_ BitVec 4) (_ BitVec 8)))
    (declare-fun x () (_ BitVec 4))
    (declare-fun y () (_ BitVec 4))
    (declare-fun s () (_ BitVec 4))
    (
      assert
            (and
              ( =
                (select
                  (store (store arr (bvand y #xE) #x03) s #x01)
                  (bvor x #x1))
                #x02
              )
              ( = (select (store arr (bvand y #xE) #x03) s) #x04 )
            )
    )
    )";

  Context c;
  ASTNode n = c.process(input);

  const ASTNode read = c.find(stp::READ, n);
  ASSERT_FALSE(read.IsNull());
  ASSERT_EQ(stp::WRITE, read[0].GetKind());
  // Both writes survive: the shared one is still under the symbolic one.
  ASSERT_EQ(stp::WRITE, read[0][0].GetKind());
}
