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

