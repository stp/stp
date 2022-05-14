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
#include "stp/Simplifier/FindPureLiterals.h"
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
  (declare-fun d () Bool)

  (push 1)
  )";

struct Context
{
   stp::STPMgr mgr;
   SimplifyingNodeFactory snf;
   stp::Cpp_interface interface;
   stp::SubstitutionMap substitutionMap;
   stp::Simplifier simplifier;

   Context() :
   snf (*(mgr.hashingNodeFactory), mgr),
   interface(mgr, &snf),
   substitutionMap(&mgr),
   simplifier(&mgr,&substitutionMap)

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
      stp::FindPureLiterals find;
      const auto changed = find.topLevel(n, &simplifier, &mgr);

      if (changed)
      {
        n = simplifier.applySubstitutionMap(n);
        simplifier.haveAppliedSubstitutionMap();
      }
      return n;
    }
};


TEST(FindPureLiterals_Test, a)
{
  const std::string input = R"(
    (assert (and a a a a) )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(n, c.mgr.ASTTrue);
}

TEST(FindPureLiterals_Test, a0)
{
  const std::string input = R"(
    (assert (and a b) )
    (assert (and a c) )
    (assert (or b (not c)))
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(n, c.mgr.LookupOrCreateSymbol("c"));
}


TEST(FindPureLiterals_Test, b)
{
  const std::string input = R"(
    (assert (or a b) )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(n, c.mgr.ASTTrue);
}

TEST(FindPureLiterals_Test, c)
{
  const std::string input = R"(
    (assert (ite a (or b c) (or c d) ))
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(n, c.mgr.ASTTrue);
}

TEST(FindPureLiterals_Test, c0)
{
  const std::string input = R"(
    (assert (ite a (not b) (or c d) ))
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(n, c.mgr.ASTTrue);
}

TEST(FindPureLiterals_Test, c1)
{
  const std::string input = R"(
    (assert  (ite b (not b) (or c d) ))
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(n, c.mgr.CreateNode(stp::NOT, c.mgr.LookupOrCreateSymbol("b")));
}

TEST(FindPureLiterals_Test, c2)
{
  const std::string input = R"(
    (assert  (not (ite a (not b) (or c d) )))
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(n, c.mgr.ASTTrue);
}


TEST(FindPureLiterals_Test, d)
{
  const std::string input = R"(
    (assert (or a b) )
    (assert (or a c) )
    (assert (or a d) )
    (assert (or a (not b)) )
    (assert (or a (not c)) )
    (assert (or a (not d)) )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(n, c.mgr.ASTTrue);
}

TEST(FindPureLiterals_Test, e)
{
  const std::string input = R"(
    (assert (or (not a) b) )
    (assert (or (not a) (not b) ) )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(n, c.mgr.ASTTrue);
}

