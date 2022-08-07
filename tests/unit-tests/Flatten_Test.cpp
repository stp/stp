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
   
   ASTNode process(std::string input)
   {
      stp::SMT2ScanString((start_input + input).c_str());
      stp::SMT2Parse();
      // TODO assert it was parsed properly.
      smt2lex_destroy();
      ASTNode n = mgr.CreateNode(stp::AND, mgr.GetAsserts());
      std::cerr << "Pre flatten " << n;
      n = flatten.topLevel(n);
      std::cerr << "Post flatten "<< n;
      return n;
    }
};

TEST(Flatten_Test , __LINE__)
{
  const std::string input = R"(
    (assert (xor b (xor a b ) a a a) )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(n, c.mgr.ASTFalse);
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
