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
#include "stp/FloatBlaster/rounding_modes.h"
#include "stp/Parser/parser.h"
#include "stp/Simplifier/constantBitP/ConstantBitPropagation.h"
#include "stp/Simplifier/constantBitP/FixedBits.h"
#include <gtest/gtest.h>


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
      std::cerr << "Pre cbitp " << n;

    simplifier::constantBitP::ConstantBitPropagation cb(
        &mgr, &simplifier, mgr.defaultNodeFactory, n);
    if (cb.isUnsatisfiable())
      n = mgr.ASTFalse;
    else
      n = cb.topLevelBothWays(n);

    if (simplifier.hasUnappliedSubstitutions())
    {
      n = simplifier.applySubstitutionMap(n);
      simplifier.haveAppliedSubstitutionMap();
    }

    std::cerr << "Post cbitp "<< n;
    return n;
    }
};

TEST(ConstantBitPropagation_Test , __LINE__)
{
    const std::string input = R"(
    (assert a )
    (assert 
        (ite 
            a 
            (= v0 (_ bv4 20))
            (= v1 (_ bv6 20))
         )
     )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(n, c.mgr.ASTTrue);
}


// Expects interior occurrences of the asserted (xor a b) to be replaced by
// true. Constant bit propagation doesn't rewrite fixed interior nodes yet,
// so this documents desired behaviour rather than current behaviour.
TEST(ConstantBitPropagation_Test , DISABLED_asserted_xor_removed_from_ite_condition)
{
    const std::string input = R"(
    (assert (xor a b) )
    (assert
        (ite
            (xor a b)
            (= v0 (_ bv4 20))
            (= v1 (_ bv6 20))
         )
     )
    )";

  Context c;
  ASTNode n = c.process(input);
  ASSERT_EQ(n, c.snf.CreateNode(stp::XOR, {c.mgr.LookupOrCreateSymbol("b"), c.mgr.LookupOrCreateSymbol("a")} ));
}

// Same limitation as above, with the fixed xor nested inside an AND.
TEST(ConstantBitPropagation_Test , DISABLED_asserted_xor_removed_from_nested_and)
{
    const std::string input = R"(
    (assert (xor a b) )
    (assert 
        (ite 
            (and c (xor a b))
            (= v0 (_ bv4 20))
            (= v1 (_ bv6 20))
         )
     )
    )";

  Context c;
  ASTNode n = c.process(input);
  
  // The xor in the ITE conditional should be removed.
  ASSERT_EQ(c.mgr.LookupOrCreateSymbol("c"), n[1][0]);
}


// A rounding mode is carried in five bits, but a fixing for one has to come
// back as a rounding-mode constant: a plain five-bit constant put in its place
// hides the sort that floating-point lowering goes by.
TEST(ConstantBitPropagation_Test, rounding_mode_fixing_is_a_rounding_mode)
{
  stp::STPMgr mgr;
  const ASTNode rm =
      mgr.CreateSourceSymbol("rm", stp::SourceSort::roundingMode());
  const ASTNode rtz = mgr.CreateRMConst(stp::symbolic_fp::ROUND_TOWARD_ZERO);

  using simplifier::constantBitP::ConstantBitPropagation;
  using simplifier::constantBitP::FixedBits;

  const ASTNode fixed = ConstantBitPropagation::bitsToNode(
      mgr.defaultNodeFactory, rm,
      FixedBits::fromUnsignedInt(5, stp::symbolic_fp::ROUND_TOWARD_ZERO));
  ASSERT_EQ(fixed, rtz);
  ASSERT_EQ(fixed.GetSourceSort(), stp::SourceSort::roundingMode());

  // Two bits set encode no mode at all, so there is no constant to give.
  ASSERT_TRUE(ConstantBitPropagation::bitsToNode(
                  mgr.defaultNodeFactory, rm, FixedBits::fromUnsignedInt(5, 3))
                  .IsNull());

  // A five-bit bit-vector is still given the plain constant.
  const ASTNode v =
      mgr.CreateSourceSymbol("v", stp::SourceSort::bitVector(5));
  const ASTNode plain = ConstantBitPropagation::bitsToNode(
      mgr.defaultNodeFactory, v, FixedBits::fromUnsignedInt(5, 8));
  ASSERT_EQ(plain, mgr.CreateBVConst(5, 8));
  ASSERT_EQ(plain.GetSourceSort(), stp::SourceSort::bitVector(5));
}

// The same through the pass: a rounding mode the formula fixes is substituted
// by the rounding-mode constant, not by its bits.
TEST(ConstantBitPropagation_Test, fixed_rounding_mode_symbol_keeps_its_sort)
{
  stp::STPMgr mgr;
  stp::SubstitutionMap substitutionMap(&mgr);
  stp::Simplifier simplifier(&mgr, &substitutionMap);

  const ASTNode rm =
      mgr.CreateSourceSymbol("rm", stp::SourceSort::roundingMode());
  const ASTNode rtz = mgr.CreateRMConst(stp::symbolic_fp::ROUND_TOWARD_ZERO);
  const ASTNode top = mgr.CreateNode(stp::EQ, rm, rtz);

  simplifier::constantBitP::ConstantBitPropagation cb(
      &mgr, &simplifier, mgr.defaultNodeFactory, top);
  cb.topLevelBothWays(top);

  ASTNode value;
  ASSERT_TRUE(simplifier.InsideSubstitutionMap(rm, value));
  ASSERT_EQ(value, rtz);
  ASSERT_EQ(value.GetSourceSort(), stp::SourceSort::roundingMode());
}
