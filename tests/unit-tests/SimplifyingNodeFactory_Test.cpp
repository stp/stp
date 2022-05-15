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

   Context() :
   snf (*(mgr.hashingNodeFactory), mgr),
   interface(mgr, &snf)
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
      // TODO assert it was parsed properly.
      smt2lex_destroy();
      ASTNode n = mgr.CreateNode(stp::AND, mgr.GetAsserts());
      std::cerr << n;
      return n;
    }
};


TEST(SimplifyingNodeFactory_Test, a)
{
  const std::string input = R"(
    (assert (and a a a a) )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(n, c.mgr.LookupOrCreateSymbol("a"));
}

TEST(SimplifyingNodeFactory_Test, b)
{
  const std::string input = R"(
    (assert (and a a a (not a)) )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTFalse);
}

TEST(SimplifyingNodeFactory_Test, c)
{
  const std::string input = R"(
    (assert (and (not a) a a a ) )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTFalse);
}

TEST(SimplifyingNodeFactory_Test, d)
{
  const std::string input = R"(
    (assert ( = (and a b a c b a  a a a )  (and  a b c a b ))  )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}

TEST(SimplifyingNodeFactory_Test, e)
{
  const std::string input = R"(
    (assert ( = (= a b )  (= b a ))  )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}

TEST(SimplifyingNodeFactory_Test, f)
{
  const std::string input = R"(
    (assert ( = (= v0 v1 )  (= v1 v0 ))  )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}


TEST(SimplifyingNodeFactory_Test, i)
{
  const std::string input = R"(
    (assert (and a (not a) )  )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTFalse);
}

TEST(SimplifyingNodeFactory_Test, j)
{
  const std::string input = R"(
    (assert (and (not a) a )  )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTFalse);
}





TEST(SimplifyingNodeFactory_Test, n)
{
  const std::string input = R"(
    (assert (or (not a) a )  )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}

TEST(SimplifyingNodeFactory_Test, n0)
{
  const std::string input = R"(
    (assert (= a  (or a a a a a ) ))
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}


TEST(SimplifyingNodeFactory_Test, n1)
{
  const std::string input = R"(
    (assert (= (or b a)  (or a a b a a b a ) ))
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}



TEST(SimplifyingNodeFactory_Test, bvand0)
{
  const std::string input = R"(
    (assert (= (bvand v0 v1 v0 v1 v0) (bvand v0 v1)  )  )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}
TEST(SimplifyingNodeFactory_Test, bvand1)
{
  const std::string input = R"(
    (assert (= (bvand v0 v1 v1 (bvnot v0) ) (_ bv0 20) )  )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}
TEST(SimplifyingNodeFactory_Test, bvand2)
{
  const std::string input = R"(
    (assert (= (bvand v0 v1 v0 v1) (bvand v0 v1)  )  )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}
TEST(SimplifyingNodeFactory_Test, bvand3)
{
  const std::string input = R"(
    (assert (= (bvand v0 (bvnot v0) ) (_ bv0 20) )  )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}


TEST(SimplifyingNodeFactory_Test, bvand4)
{
  const std::string input = R"(
    (assert 
      (= (bvand v0 (bvnot v1) (bvneg v1) (bvneg v0) (bvneg v1) (bvnot v0) ) 
      (_ bv0 20) )  )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}





TEST(SimplifyingNodeFactory_Test, bvor0)
{
  const std::string input = R"(
    (assert (= (bvor v0 v1 v0 v1 v0) (bvor v0 v1)  )  )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}
TEST(SimplifyingNodeFactory_Test, bvor1)
{
  const std::string input = R"(
    (assert (= (bvor v0 v1 v1 (bvnot v0) ) (bvnot (_ bv0 20)) )  )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}
TEST(SimplifyingNodeFactory_Test, bvor2)
{
  const std::string input = R"(
    (assert (= (bvor v0 v1 v0 v1) (bvor v0 v1)  )  )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}
TEST(SimplifyingNodeFactory_Test, bvor3)
{
  const std::string input = R"(
    (assert (= (bvor v0 (bvnot v0) ) ( bvnot (_ bv0 20)) )  )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}




TEST(SimplifyingNodeFactory_Test, xor0)
{
  const std::string input = R"(
    (assert ( = (xor a b a c b a a a a )  (xor  a b c a b ))  )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}

TEST(SimplifyingNodeFactory_Test, xor1)
{
  const std::string input = R"(
    (assert ( = (xor a b a c b a a a a )  (xor  c a b c c a b ))  )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}

TEST(SimplifyingNodeFactory_Test, xor2)
{
  const std::string input = R"(
    (assert ( = (xor (not a ) (not b))  (xor  a b  ))  )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}

TEST(SimplifyingNodeFactory_Test, xor3)
{
  const std::string input = R"(
    (assert ( = (xor a (not b))  (xor  (not a) b  ))  )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}



TEST(SimplifyingNodeFactory_Test, bvxor0)
{
  const std::string input = R"(
    (assert ( = (bvxor v1 v0 v1 v0)   (bvxor  v0 v1 v1 v1 v1 v0 v0 v0 ))  )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}

TEST(SimplifyingNodeFactory_Test, bvxor1)
{
  const std::string input = R"(
    (assert ( = (bvxor (bvnot v0) v1 )  (bvxor (bvnot v1) v0))  )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}

TEST(SimplifyingNodeFactory_Test, bvxor2)
{
  const std::string input = R"(
    (assert ( = (bvxor v1 (bvnot v0) v1 v1 v0 )  (bvnot v1))  )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}


TEST(SimplifyingNodeFactory_Test, bvgt)
{
  const std::string input = R"(
    (assert ( = (bvult v0 (_ bv1 20) )  (= v0 (_ bv0 20)))  )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}



TEST(SimplifyingNodeFactory_Test, bvplus0)
{
  const std::string input = R"(
    (assert ( = (bvadd v1 (bvneg v1) v1 )   v1)  )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}

TEST(SimplifyingNodeFactory_Test, bvplus1)
{
  const std::string input = R"(
      (assert (= 
                (bvadd v1 (bvneg v1) (bvneg v1) v1 v1 (bvnot v1) v1 )   
                (bvsub v1 (_ bv1 20))  
               )
      )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}

TEST(SimplifyingNodeFactory_Test, bvplus2)
{
  const std::string input = R"(
      (assert (= 
                (bvadd v1 (_ bv1 20) (bvneg v1) (bvneg v1) (_ bv1 20) v1 v1 (bvnot v1) v1 (_ bv0 20) )   
                 (bvadd v1 (_ bv1 20) )
               )
      )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}

TEST(SimplifyingNodeFactory_Test, bvplus3)
{
  const std::string input = R"(
      (assert (= 
                (bvadd v1 (_ bv0 20) (_ bv0 20) (_ bv0 20)  )   
                 v1
               )
      )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}

TEST(SimplifyingNodeFactory_Test, bvplus4)
{
  const std::string input = R"(
      (assert (= 
                (bvadd v1 v2 (_ bv0 20)   )   
                 (bvadd v1 v2 )
               )
      )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}


TEST(SimplifyingNodeFactory_Test, bvplus5)
{
  const std::string input = R"(
      (assert (= 
                (bvadd (bvneg (bvneg (bvneg v1) ))  v1   )   
                 (_ bv0 20)  
               )
      )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}

TEST(SimplifyingNodeFactory_Test, bvplus6)
{
  const std::string input = R"(
      (assert (= 
                (bvadd (bvnot (bvnot (bvnot v1) ))  v1   )   
                 (bvnot (_ bv0 20)  )
               )
      )
    )";

   Context c;
   ASTNode n = c.process(input);
   ASSERT_EQ(n, c.mgr.ASTTrue);
}
