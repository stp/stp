/***********
AUTHORS: Trevor Hansen

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

#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/Parser/parser.h"
#include "stp/Printer/printers.h"
#include "stp/STPManager/STPManager.h"
#include "stp/cpp_interface.h"
#include <gtest/gtest.h>
#include <sstream>

using namespace stp;

namespace
{

// An n-ary multiplication is stored as one node but printed as a chain of
// binary applications, as bvadd always has been, so that a consumer limited
// to binary operators can read the output.
TEST(SMTLIB2Printer, NaryMultiplicationPrintsAsBinaryChain)
{
  STPMgr mgr;
  SimplifyingNodeFactory simplifying(*mgr.hashingNodeFactory, mgr);
  Cpp_interface interface(mgr, &simplifying);
  mgr.defaultNodeFactory = &simplifying;
  interface.startup();
  GlobalParserBM = &mgr;
  GlobalParserInterface = &interface;

  SMT2ScanString(R"(
    (set-logic QF_BV)
    (declare-const a (_ BitVec 4))
    (declare-const b (_ BitVec 4))
    (declare-const c (_ BitVec 4))
    (assert (= (bvmul a b c) (_ bv8 4)))
  )");
  ASSERT_EQ(0, SMT2Parse());
  smt2lex_destroy();

  const ASTVec assertions = mgr.GetAsserts();
  ASSERT_EQ(1u, assertions.size());
  const ASTNode product = assertions[0][0];
  ASSERT_EQ(BVMULT, product.GetKind());
  ASSERT_EQ(3u, product.Degree());

  std::ostringstream out;
  printer::SMTLIB2_Print1(out, product, 0, false);
  const std::string text = out.str();
  size_t applications = 0;
  for (size_t at = text.find("(bvmul"); at != std::string::npos;
       at = text.find("(bvmul", at + 1))
    applications++;
  EXPECT_EQ(2u, applications) << text;
}

}
