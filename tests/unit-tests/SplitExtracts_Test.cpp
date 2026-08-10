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
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SplitExtracts.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include <gtest/gtest.h>
#include <stdio.h>
#include <string>
#include <vector>


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
   stp::SubstitutionMap substitutionMap;
   stp::Simplifier simplifier;
   stp::SplitExtracts split;

   Context() :
   snf (*(mgr.hashingNodeFactory), mgr),
   interface(mgr, &snf),
   substitutionMap(&mgr),
   simplifier(&mgr,&substitutionMap),
   split(mgr)
   { 
    mgr.defaultNodeFactory = &snf;
    interface.startup();
    stp::GlobalParserBM = &mgr;
    stp::GlobalParserInterface = &interface;
   }
   
   ASTNode pre; // the formula before the pass ran.

   ASTNode process(std::string input)
   {
      stp::SMT2ScanString((start_input + input).c_str());
      stp::SMT2Parse();
      // TODO assert it was parsed properly.
      smt2lex_destroy();
      pre = mgr.CreateNode(stp::AND, mgr.GetAsserts());
      std::cerr << "Pre split " << pre;
      ASTNode n = split.topLevel(pre, &simplifier);
      std::cerr << "Post split "<< n;
      return n;
    }

   bool present(stp::Kind k, const ASTNode& n)
   {
     if (n.GetKind() == k)
       return true;
     for (const auto& c : n)
       if (present(k, c))
         return true;
     return false;
   }

   void collectSymbols(const ASTNode& n, stp::ASTNodeSet& out)
   {
     if (n.GetKind() == stp::SYMBOL)
     {
       out.insert(n);
       return;
     }
     for (const auto& c : n)
       collectSymbols(c, out);
   }

   // Apply the substitution map produced by the pass to `n`. The pass
   // defines each split symbol only in terms of fresh variables, so one
   // application reaches the fixed point.
   ASTNode backSubstitute(const ASTNode& n)
   {
     stp::DenseNodeMap fromTo = *simplifier.Return_SolverMap(); // replace() mutates it.
     stp::DenseNodeMap cache;
     return stp::SubstitutionMap::replace(n, fromTo, cache, &snf);
   }

   // Evaluate a fully-assigned node down to a constant.
   ASTNode eval(const ASTNode& n, stp::ASTNodeMap assignment /*by value*/)
   {
     stp::ASTNodeMap cache;
     ASTNode s = stp::SubstitutionMap::replace(n, assignment, cache, &snf);
     if (s.isConstant())
       return s;
     return stp::NonMemberBVConstEvaluator(&mgr, s);
   }

   // The rewrite is a piecewise renaming of the split symbols, so the
   // original formula with the definitions substituted back in must be the
   // same function of the fresh variables as the pass's output. Check that
   // exhaustively (the tests use widths small enough to enumerate).
   void checkSound(const ASTNode& post)
   {
     const ASTNode back = backSubstitute(pre);

     stp::ASTNodeSet symSet;
     collectSymbols(back, symSet);
     collectSymbols(post, symSet);
     std::vector<ASTNode> syms(symSet.begin(), symSet.end());

     uint64_t combos = 1;
     for (const auto& s : syms)
       combos *= (s.GetType() == stp::BOOLEAN_TYPE)
                     ? 2u
                     : (1u << s.GetValueWidth());
     ASSERT_LE(combos, 1u << 16)
         << "too many assignments (" << combos << ") -- lower the width";

     for (uint64_t c = 0; c < combos; c++)
     {
       stp::ASTNodeMap assignment;
       uint64_t rest = c;
       for (const auto& s : syms)
       {
         if (s.GetType() == stp::BOOLEAN_TYPE)
         {
           assignment.insert({s, (rest & 1) ? mgr.ASTTrue : mgr.ASTFalse});
           rest /= 2;
         }
         else
         {
           const unsigned size = 1u << s.GetValueWidth();
           assignment.insert(
               {s, mgr.CreateBVConst(s.GetValueWidth(), rest % size)});
           rest /= size;
         }
       }
       stp::ASTNodeMap a2 = assignment; // eval() consumes the map.
       ASSERT_EQ(eval(back, assignment), eval(post, a2))
           << "split changed the meaning at assignment " << c;
     }
   }
};

// intersect - dont replace.
TEST(SplitExtracts_Test , __LINE__)
{
  const std::string input = R"(
    (assert 
      (= 
         (((_ extract 6 0 ) v1) )  
         (((_ extract 12 6 ) v1) ) 
       )
    ))";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(0, c.split.getIntroduced());
}

// intersect - dont replace.
TEST(SplitExtracts_Test , __LINE__)
{
  const std::string input = R"(
    (assert 
      (= 
         (((_ extract 11 6 ) v1) )  
         (((_ extract 6 1 ) v1) ) 
       )
    ))";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(0, c.split.getIntroduced());
}

// no intersect
TEST(SplitExtracts_Test , __LINE__)
{
  const std::string input = R"(
    (assert 
      (= 
         (((_ extract 6 0 ) v1) )  
         (((_ extract 13 7 ) v1) ) 
       )
    ))";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(2, c.split.getIntroduced());
}

// no intersect
TEST(SplitExtracts_Test , __LINE__)
{
  const std::string input = R"(
    (assert 
      (= 
         (concat 
           (((_ extract 9 0 ) v1) )  
           (((_ extract 19 10 ) v1) ) 
          )
          v0
       )
    ))";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(2, c.split.getIntroduced());
}

// One instance is unextracted. (The reassembled side must be the full 20
// bits: = between different widths is ill-sorted and now rejected at parse.)
TEST(SplitExtracts_Test , __LINE__)
{
  const std::string input = R"(
    (assert
      (=
        (concat
           (((_ extract 4 0 ) v1) )
           (((_ extract 19 5 ) v1) ))
          v1
       )
    )
  )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(0, c.split.getIntroduced());
}

// The (8,5) doesn't intersect. (The other side must match the concat's 10
// bits -- = between different widths is ill-sorted and now rejected at
// parse -- so compare against a fresh 10-bit variable, which contributes no
// extracts of its own.)
TEST(SplitExtracts_Test , __LINE__)
{
  const std::string input = R"(
    (declare-fun w10 () (_ BitVec 10))
    (assert
      (=
        (concat
         (concat
           (((_ extract 4 0 ) v1) )
           (((_ extract 8 5 ) v1) ))
           (((_ extract 3 3 ) v1) ))
          w10
       )
    )
  )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(1, c.split.getIntroduced());
}

// Splitting records a whole-width definition of the symbol in the
// substitution map; that is what rebuilds its value during model
// construction.
TEST(SplitExtracts_Test, records_whole_width_definition)
{
  const std::string input = R"(
    (assert
      (=
         (((_ extract 6 0 ) v1) )
         (((_ extract 13 7 ) v1) )
       )
    ))";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(2, c.split.getIntroduced());

  const auto& map = *c.simplifier.Return_SolverMap();
  ASSERT_EQ(map.size(), 1u);
  const auto& entry = *map.begin();
  EXPECT_EQ(entry.first.GetKind(), stp::SYMBOL);
  EXPECT_EQ(entry.second.GetValueWidth(), entry.first.GetValueWidth());
  // Both extracts aligned with pieces of the definition, so none survive.
  EXPECT_FALSE(c.present(stp::BVEXTRACT, n));
}

// Two disjoint extracts that together cover all of y. They must not appear
// adjacent under one concat -- the simplifying factory would merge them
// back into y.
TEST(SplitExtracts_Test, sound_full_cover)
{
  const std::string input = R"(
    (declare-fun y () (_ BitVec 4))
    (assert (bvult ((_ extract 1 0) y) #b10))
    (assert (bvugt ((_ extract 3 2) y) #b01))
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(2, c.split.getIntroduced());
  EXPECT_FALSE(c.present(stp::BVEXTRACT, n));
  c.checkSound(n);
}

// The extracts leave a gap (bit 2), exercising the filler branch.
TEST(SplitExtracts_Test, sound_with_gap)
{
  const std::string input = R"(
    (declare-fun y () (_ BitVec 4))
    (assert
      (bvult (concat ((_ extract 3 3) y) ((_ extract 1 0) y)) #b101)
    ))";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(2, c.split.getIntroduced());
  EXPECT_FALSE(c.present(stp::BVEXTRACT, n));
  c.checkSound(n);
}

// The extracts cover the low bits but leave the top uncovered, exercising
// the trailing filler branch.
TEST(SplitExtracts_Test, sound_top_gap)
{
  const std::string input = R"(
    (declare-fun y () (_ BitVec 5))
    (assert (bvult ((_ extract 1 0) y) #b10))
    (assert (bvugt ((_ extract 3 2) y) #b01))
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(2, c.split.getIntroduced());
  EXPECT_FALSE(c.present(stp::BVEXTRACT, n));
  c.checkSound(n);
}

// [2:0] and [2:1] overlap each other so they stay; [5:3] overlaps nothing
// and is split out. The surviving extracts read the filler variable.
TEST(SplitExtracts_Test, sound_partial_overlap)
{
  const std::string input = R"(
    (declare-fun y () (_ BitVec 6))
    (assert
      (and
        (bvult ((_ extract 2 0) y) (concat ((_ extract 2 1) y) #b1))
        (bvult ((_ extract 5 3) y) #b101)
      )
    ))";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(1, c.split.getIntroduced());
  EXPECT_TRUE(c.present(stp::BVEXTRACT, n));
  c.checkSound(n);
}


