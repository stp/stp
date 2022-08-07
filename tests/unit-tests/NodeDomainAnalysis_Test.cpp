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
#include "stp/Simplifier/NodeDomainAnalysis.h"
#include "stp/Simplifier/UnsignedInterval.h"
#include "stp/Simplifier/constantBitP/FixedBits.h"
#include "stp/Simplifier/constantBitP/MersenneTwister.h"
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
   stp::NodeDomainAnalysis domain;

   Context() :
   snf (*(mgr.hashingNodeFactory), mgr),
   interface(mgr, &snf),
   domain(&mgr)
   { 
    mgr.defaultNodeFactory = &snf;
    stp::GlobalParserBM = &mgr;
    stp::GlobalParserInterface = &interface;
   }
   
   void process(std::string input)
   {
      stp::SMT2ScanString((start_input + input).c_str());
      stp::SMT2Parse();
      // TODO assert it was parsed properly.
      smt2lex_destroy();
      ASTNode n = mgr.CreateNode(stp::AND, mgr.GetAsserts());
      domain.buildMap(n);
    }
};
 
// fixed bits are constant, internval is null
TEST(NodeDomainAnalysis_Test, 0)
{
  CONSTANTBV::BitVector_Boot(); // TODO hack. needs to be run once before the constructors start allocating constantbvs.
  Context c;

  const auto width = 10;
  stp::FixedBits a = stp::FixedBits::fromUnsignedInt(width,3);

  auto a_ptr = &a;
  stp::UnsignedInterval* b_ptr = nullptr;

  c.domain.harmonise(a_ptr, b_ptr);

  ASSERT_TRUE(a.isTotallyFixed());
  ASSERT_TRUE(b_ptr != nullptr && b_ptr->isConstant());
}

// fixed bits are null, internval is costant.
TEST(NodeDomainAnalysis_Test, DISABLED_1)
{
  Context c;

  stp::FixedBits * a_ptr = nullptr;

  ASTNode constant = c.mgr.CreateBVConst("1",10, 10); // hold a reference otherwise garbage collected.
  stp::CBV cbv  = constant.GetBVConst();
  stp::UnsignedInterval* b_ptr = new stp::UnsignedInterval(CONSTANTBV::BitVector_Clone(cbv), CONSTANTBV::BitVector_Clone(cbv));

  c.domain.harmonise(a_ptr, b_ptr);

  ASSERT_TRUE(a_ptr != NULL && a_ptr->isTotallyFixed());
  ASSERT_TRUE(b_ptr->isConstant());
}


TEST(NodeDomainAnalysis_Test, DISABLED_2)
{
  Context c;
  MTRand rand(10U);

  for (int i = 0; i < 100; i++)
  {
    stp::FixedBits a = stp::FixedBits::createRandom(i+1,  30, rand);
    stp::FixedBits start =a;                        

    auto a_ptr = new stp::FixedBits(a);
    stp::UnsignedInterval* b_ptr = nullptr;

    c.domain.harmonise(a_ptr, b_ptr);
    
    // The interval provides no information, so sould be the same.
    ASSERT_TRUE(stp::FixedBits::equals(start,a)); 

    // Min and max should be the same
    if (a_ptr != nullptr && b_ptr != nullptr)
    {
      ASSERT_EQ(CONSTANTBV::BitVector_Compare(b_ptr->minV, a_ptr->GetMinBVConst()),0);
      ASSERT_EQ(CONSTANTBV::BitVector_Compare(b_ptr->maxV, a_ptr->GetMaxBVConst()),0);
    }

    delete a_ptr;
    delete b_ptr;
  }
}


TEST(NodeDomainAnalysis_Test, DISABLED_3)
{
  Context c;

  const auto width =2;

  stp::CBV min = CONSTANTBV::BitVector_Create(width, true);
  stp::CBV max = CONSTANTBV::BitVector_Create(width, true);
  stp::UnsignedInterval b(min,max);

  stp::FixedBits a = stp::FixedBits::fromUnsignedInt(width,3);

  auto a_ptr = &a;
  stp::UnsignedInterval* b_ptr = nullptr;

  c.domain.harmonise(a_ptr, b_ptr);
  
  ASSERT_EQ(a_ptr->isTotallyFixed(), true);
  ASSERT_EQ(b_ptr->isConstant(), true);
}

