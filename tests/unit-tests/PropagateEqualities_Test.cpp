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
