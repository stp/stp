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

#include "stp/Simplifier/PropagateEqualities.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Parser/LetMgr.h"
#include "stp/cpp_interface.h"
#include "stp/Parser/parser.h"
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

  
void verify(const std::string input)
{
  //TODO too complex to initialise.
  stp::STPMgr mgr;
  SimplifyingNodeFactory snf (*(mgr.hashingNodeFactory), mgr);
  mgr.defaultNodeFactory = &snf;
  stp::Cpp_interface interface(mgr, mgr.defaultNodeFactory);

  interface.startup();
  stp::GlobalParserBM = &mgr;
  stp::GlobalParserInterface = &interface;

  stp::SubstitutionMap sm(&mgr);
  stp::Simplifier simp(&mgr, &sm);
  stp::ArrayTransformer at(&mgr, &simp);
  
  ASTVec AssertsQuery;
  
  stp::SMT2ScanString((start_input + input).c_str());
  stp::SMT2Parse();
  smt2lex_destroy();

  // TODO assert it was parsed properly.

  ASTVec values = mgr.GetAsserts();
  ASTNode n = mgr.CreateNode(stp::AND, values);
  
  stp::PropagateEqualities propagate(&simp, mgr.defaultNodeFactory, &mgr);
  propagate.setSpeculativeOn();
  n = propagate.topLevel(n);

  if (simp.hasUnappliedSubstitutions())
  {
    n = simp.applySubstitutionMap(n);
    simp.haveAppliedSubstitutionMap();
  }

  std::cerr << n;

  ASSERT_EQ(n.Degree(), 0u);
}

TEST(PropagateEquality_Test, a)
{

 const std::string input = R"(
    (assert ( not a  ) )
    )";

  verify(input);
}

TEST(PropagateEquality_Test, b)
{

 const std::string input = R"( 
  (assert (a) )
   )";

  verify(input);
}

TEST(PropagateEquality_Test, c)
{
 const std::string input = R"( 
    (assert 
          (xor 
              (= (_ bv1 1) x0)
              (= v1 v2)
          )  
    )
    )";

  verify(input);
}

TEST(PropagateEquality_Test, c0)
{
 const std::string input = R"( 
    (assert 
          (xor 
              (not (= (_ bv1 1) x0) )
              (= v1 v2)
          )  
    )
    )";

  verify(input);
}

TEST(PropagateEquality_Test, c1)
{
 const std::string input = R"( 
    (assert 
          (xor 
              (= (_ bv1 1) (bvnot x0) )
              (= v1 v2)
          )  
    )
    )";

  verify(input);
}

TEST(PropagateEquality_Test, c2)
{
 const std::string input = R"( 
    (assert 
          (xor 
              (= (_ bv1 1) (bvneg x0) )
              (= v1 v2)
          )  
    )
    )";

  verify(input);
}

TEST(PropagateEquality_Test, c3)
{
 const std::string input = R"( 
    (assert 
          (not (xor 
              (= (_ bv1 1) (bvneg x0) )
              (= v1 v2)
          ))
    )
    )";

  verify(input);
}

TEST(PropagateEquality_Test, c6)
{
 const std::string input = R"( 
    (assert 
          (xor 
              a
              (= v1 v2)
          )
    )
    )";

  verify(input);
}


TEST(PropagateEquality_Test, c5)
{
 const std::string input = R"( 
    (assert 
          (not (xor 
              a
              (= v1 v2)
          ))
    )
    )";

  verify(input);
}

TEST(PropagateEquality_Test, e0)
{
 const std::string input = R"( 
    (assert 
          (not (xor 
              (not a)
              (= v1 v2)
          ))
    )
    )";

  verify(input);
}

TEST(PropagateEquality_Test, DISABLED_c4)
{
 const std::string input = R"( 
    (assert 
          (not (xor 
              (= (ite (= v1 v2) (_ bv0 1) (_ bv1 1)) x0)
              (= v1 v2)
          ))
    )
    )";

  verify(input);
}


TEST(PropagateEquality_Test, d)
{
 const std::string input = R"( 
    (assert 
          (xor 
              (= v1 v2)
              (not (= (_ bv1 1) x0) )
          )  
    )
    )";

  verify(input);
}


TEST(PropagateEquality_Test, DISABLED_g)
{

 const std::string input = R"( 
    (assert (and 
         (= v0 v1 )
         (= v0 (bvadd v2 v3) )
         (= v0 (bvadd v3 v4) )
            )
    )
 )";

  verify(input);
}


TEST(PropagateEquality_Test, gk)
{

 const std::string input = R"( 
    (assert (and 
         (= v0 (bvnot  v1) )
         (= v0 (bvnot  v2) )
             )
    )
 )";

  verify(input);
}


TEST(PropagateEquality_Test, gj)
{

 const std::string input = R"( 
    (assert (and 
         (= v0 (bvneg  v1) )
         (= v0 (bvneg  v2) )
             )
    )
 )";

  verify(input);
}

TEST(PropagateEquality_Test, h)
{
 const std::string input = R"( 
  (assert (= (bvneg v0) (bvudiv v1 v2)) )
 )";

  verify(input);
}



TEST(PropagateEquality_Test, i)
{
 const std::string input = R"( 
  (assert (= (bvnot v0) (bvudiv v1 v2)) )
 )";

  verify(input);
}


TEST(PropagateEquality_Test, isFalse)
{
 const std::string input = R"( 
  (assert (= v1 v2) )
  (assert (not (= v1 v2)) )
 )";

  verify(input);
}

TEST(PropagateEquality_Test, g_Booleans)
{
 const std::string input = R"( 
  (assert (= a b) )
  (assert (= b c) )
 )";

  verify(input);
}

#ifdef STP_ENABLE_FLOATING_POINT

// SMT `=` on floats (FP_SMT_EQ) is true equality on the abstract domain,
// so it propagates like EQ. fp.eq (FP_EQ) identifies +0 with -0 and must
// never propagate. These parse their own QF_FP prelude and return the
// propagated conjunction for inspection.
static stp::ASTNode propagateFP(const std::string& input)
{
  stp::STPMgr mgr;
  SimplifyingNodeFactory snf(*(mgr.hashingNodeFactory), mgr);
  mgr.defaultNodeFactory = &snf;
  stp::Cpp_interface interface(mgr, mgr.defaultNodeFactory);

  interface.startup();
  stp::GlobalParserBM = &mgr;
  stp::GlobalParserInterface = &interface;

  stp::SubstitutionMap sm(&mgr);
  stp::Simplifier simp(&mgr, &sm);

  const std::string prelude = R"(
  (set-logic QF_FP)
  (declare-fun x () (_ FloatingPoint 8 24))
  (declare-fun y () (_ FloatingPoint 8 24))
  )";

  stp::SMT2ScanString((prelude + input).c_str());
  stp::SMT2Parse();
  smt2lex_destroy();

  ASTVec values = mgr.GetAsserts();
  stp::ASTNode n = values.size() == 1 ? values[0]
                                      : mgr.CreateNode(stp::AND, values);

  stp::PropagateEqualities propagate(&simp, mgr.defaultNodeFactory, &mgr);
  propagate.setSpeculativeOn();
  n = propagate.topLevel(n);

  if (simp.hasUnappliedSubstitutions())
  {
    n = simp.applySubstitutionMap(n);
    simp.haveAppliedSubstitutionMap();
  }
  return n;
}

// The propagated conjunction is not fully constant-folded here (all-constant
// FP predicates fold in later passes, not at node creation), so the tests
// assert the guarantee propagation itself makes: the substituted symbol is
// gone from the formula.
static bool containsSymbolNamed(const stp::ASTNode& n, const std::string& s)
{
  if (n.GetKind() == stp::SYMBOL)
    return n.GetName() == s;
  for (size_t i = 0; i < n.Degree(); i++)
    if (containsSymbolNamed(n[i], s))
      return true;
  return false;
}

TEST(PropagateEquality_Test, fp_smt_eq_constant)
{
  const stp::ASTNode n = propagateFP(R"(
   (assert (= x (fp #b0 #b01111111 #b10000000000000000000000)))
   (assert (fp.gt x (fp #b0 #b01111111 #b00000000000000000000000)))
  )");
  ASSERT_FALSE(containsSymbolNamed(n, "x"));
}

TEST(PropagateEquality_Test, fp_smt_eq_tofp_literal)
{
  // The literal arrives as to_fp's unfolded reinterpret form; the
  // lookthrough resolves it to an interned constant before substituting.
  const stp::ASTNode n = propagateFP(R"(
   (assert (= x ((_ to_fp 8 24) #x3FC00000)))
   (assert (fp.lt x ((_ to_fp 8 24) #x40000000)))
  )");
  ASSERT_FALSE(containsSymbolNamed(n, "x"));
}

TEST(PropagateEquality_Test, fp_smt_eq_symbols)
{
  // One of the two symbols substitutes for the other.
  const stp::ASTNode n = propagateFP(R"(
   (assert (= x y))
   (assert (fp.isNormal x))
   (assert (fp.isNormal y))
  )");
  ASSERT_TRUE(!containsSymbolNamed(n, "x") || !containsSymbolNamed(n, "y"));
}

TEST(PropagateEquality_Test, fp_eq_never_propagates)
{
  // fp.eq's +0 = -0 makes substitution unsound; the node must survive.
  const stp::ASTNode n = propagateFP(R"(
   (assert (fp.eq x (fp #b0 #b00000000 #b00000000000000000000000)))
  )");
  ASSERT_EQ(stp::FP_EQ, n.GetKind());
}

TEST(PropagateEquality_Test, fp_smt_eq_occurs_check)
{
  // x appears on both sides; the candidate must be rejected, not looped.
  const stp::ASTNode n = propagateFP(R"(
   (assert (= x (fp.add RNE x y)))
  )");
  ASSERT_EQ(stp::FP_SMT_EQ, n.GetKind());
}

#endif // STP_ENABLE_FLOATING_POINT
