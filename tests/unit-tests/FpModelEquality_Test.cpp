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

/*
 * Truth values the model-formula evaluator
 * (AbsRefine_CounterExample::ComputeFormulaUsingModel) gives the two float
 * equalities on the special values.
 *
 * The evaluator is a second, independent implementation of the semantics:
 * the circuit decides satisfiability, and then this walk re-derives the
 * formula's value over the model to check the counterexample. Disagreement
 * between the two is how a satisfiable query gets killed with "counterexample
 * bogus", so the special values -- the only place the two equalities differ
 * from each other -- need pinning here as well as in the circuit.
 *
 * fp-model-eval-predicates.cpp already drives every predicate kind through
 * this walk, but by construction its query is satisfiable "independent of the
 * predicate's own truth value" (its words): it proves the kinds are
 * implemented, not that they are right. These tests ask the evaluator
 * directly, through QueryFormulaAgainstModel, and assert the value.
 *
 * The model values are bound as PLAIN bitvector constants, which is how the
 * solver publishes them -- the format is stamped on by the evaluator from the
 * node, not carried by the value. That is what makes the NaN cases here real:
 * the raw payload survives into the model and reaches the operator.
 *
 * Two independent mechanisms then give `=` the right answer across payloads,
 * and this was measured rather than assumed: the stamping funnel
 * (withFormat -> CreateFPConst) interns every NaN pattern to one node, and
 * the lowered circuit recognises NaN by its exponent and significand fields.
 * Disabling either one alone leaves these tests passing; disabling both
 * fails them. So the NaN rows below are a check on the pair, not on one
 * chosen implementation -- which is the useful thing to assert, since a
 * rewrite is free to drop either mechanism but not both.
 */

#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/FloatBlaster/FpEncodingContext.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include <gtest/gtest.h>

using namespace stp;

namespace
{

// Packed binary32 patterns. Three NaNs that differ in payload and in sign:
// all denote the one SMT-LIB NaN.
const uint32_t PZERO = 0x00000000;
const uint32_t MZERO = 0x80000000;
const uint32_t PINF = 0x7F800000;
const uint32_t MINF = 0xFF800000;
const uint32_t NAN_QUIET = 0x7FC00000;
const uint32_t NAN_PAYLOAD = 0x7F800001; // quiet bit clear, payload 1
const uint32_t NAN_NEG = 0xFFC12345;     // sign set, another payload
const uint32_t ONE = 0x3F800000;
const uint32_t SUBNORMAL = 0x00000001;

class FpModelEqualityTest : public ::testing::Test
{
protected:
  STPMgr mgr;
  SubstitutionMap substitutions;
  Simplifier simplifier;
  ArrayTransformer transformer;
  FpEncodingContext encoding;
  AbsRefine_CounterExample ce;
  unsigned counter = 0;

  FpModelEqualityTest()
      : substitutions(&mgr), simplifier(&mgr, &substitutions),
        transformer(&mgr, &simplifier), encoding(&mgr),
        ce(&mgr, &simplifier, &transformer)
  {
    ce.setFpEncodingContext(&encoding);
  }

  // A Float32 variable already bound to `bits` in the model. The binding is a
  // plain 32-bit constant: the solver's model carries bits, and the evaluator
  // is what attaches the format.
  ASTNode bound(uint32_t bits)
  {
    ASTNode v =
        mgr.CreateSymbol(("f" + std::to_string(counter++)).c_str(), 0, 32);
    v.SetExpWidth(8);
    v.SetSigWidth(24);
    ce.InsertIntoCounterExampleMap(v, mgr.CreateBVConst(32, bits));
    return v;
  }

  // The evaluator's verdict on `kind` over two model-bound variables. Built
  // with the hashing factory so that the node reaching the evaluator is the
  // one asked for, with no rewrite standing in for it.
  bool eval(Kind kind, uint32_t a, uint32_t b)
  {
    const ASTVec operands = {bound(a), bound(b)};
    const ASTNode form = mgr.hashingNodeFactory->CreateNode(kind, operands);
    const ASTNode value = ce.QueryFormulaAgainstModel(form);
    EXPECT_TRUE(value == mgr.ASTTrue || value == mgr.ASTFalse)
        << "evaluator did not reduce the predicate to a Boolean";
    return value == mgr.ASTTrue;
  }
};

TEST_F(FpModelEqualityTest, EncodedTermScopeEndsBetweenModelQueries)
{
  const ASTNode one = bound(ONE);
  const ASTNode negated =
      mgr.hashingNodeFactory->CreateTerm(FP_NEG, 32, ASTVec{one});
  const ASTNode absolute =
      mgr.hashingNodeFactory->CreateTerm(FP_ABS, 32, ASTVec{negated});

  // Each source operation enters target-language evaluation while its lowered
  // DAG is live. The next independent question must enter source mode again;
  // otherwise it skips lowering and cannot interpret the FP operation.
  EXPECT_EQ(mgr.CreateBVConst(32, 0xBF800000), ce.ModelValueOfTerm(negated));
  EXPECT_EQ(mgr.CreateBVConst(32, ONE), ce.ModelValueOfTerm(absolute));
  EXPECT_EQ(mgr.CreateBVConst(32, 0xBF800000), ce.ModelValueOfTerm(negated));
}

// fp.eq is IEEE numeric equality: the two zeros are equal, NaN is equal to
// nothing, infinities agree only with the same sign.
TEST_F(FpModelEqualityTest, FpEqSpecials)
{
  // Zeros: sign is not part of the numeric value.
  EXPECT_TRUE(eval(FP_EQ, PZERO, PZERO));
  EXPECT_TRUE(eval(FP_EQ, PZERO, MZERO));
  EXPECT_TRUE(eval(FP_EQ, MZERO, PZERO));
  EXPECT_TRUE(eval(FP_EQ, MZERO, MZERO));

  // NaN, whatever payload or sign the model happens to hold, and in either
  // operand position.
  const uint32_t nans[] = {NAN_QUIET, NAN_PAYLOAD, NAN_NEG};
  for (uint32_t n : nans)
  {
    for (uint32_t m : nans)
      EXPECT_FALSE(eval(FP_EQ, n, m)) << std::hex << n << " vs " << m;
    EXPECT_FALSE(eval(FP_EQ, n, PZERO));
    EXPECT_FALSE(eval(FP_EQ, PZERO, n));
    EXPECT_FALSE(eval(FP_EQ, n, PINF));
    EXPECT_FALSE(eval(FP_EQ, n, ONE));
  }

  // Infinities.
  EXPECT_TRUE(eval(FP_EQ, PINF, PINF));
  EXPECT_TRUE(eval(FP_EQ, MINF, MINF));
  EXPECT_FALSE(eval(FP_EQ, PINF, MINF));
  EXPECT_FALSE(eval(FP_EQ, MINF, PINF));

  // Cross-class, including the subnormal that a zero-vs-finite mix-up
  // would swallow.
  EXPECT_FALSE(eval(FP_EQ, PINF, ONE));
  EXPECT_FALSE(eval(FP_EQ, PZERO, ONE));
  EXPECT_FALSE(eval(FP_EQ, PZERO, SUBNORMAL));
  EXPECT_TRUE(eval(FP_EQ, ONE, ONE));
  EXPECT_TRUE(eval(FP_EQ, SUBNORMAL, SUBNORMAL));
}

// `=` is equality on the abstract domain: the signed zeros are two values,
// and every NaN pattern is the one NaN.
TEST_F(FpModelEqualityTest, SmtEqSpecials)
{
  // Zeros are distinguishable here, which is the whole difference from fp.eq.
  EXPECT_TRUE(eval(FP_SMT_EQ, PZERO, PZERO));
  EXPECT_TRUE(eval(FP_SMT_EQ, MZERO, MZERO));
  EXPECT_FALSE(eval(FP_SMT_EQ, PZERO, MZERO));
  EXPECT_FALSE(eval(FP_SMT_EQ, MZERO, PZERO));

  // One NaN value: true between any two spellings, in either order. A model
  // that published the raw payloads, reaching an evaluator that both skipped
  // the interning funnel and compared packed bits, fails exactly here.
  const uint32_t nans[] = {NAN_QUIET, NAN_PAYLOAD, NAN_NEG};
  for (uint32_t n : nans)
    for (uint32_t m : nans)
      EXPECT_TRUE(eval(FP_SMT_EQ, n, m)) << std::hex << n << " vs " << m;

  // ... and false against everything that is not a NaN.
  for (uint32_t n : nans)
  {
    EXPECT_FALSE(eval(FP_SMT_EQ, n, PZERO));
    EXPECT_FALSE(eval(FP_SMT_EQ, PZERO, n));
    EXPECT_FALSE(eval(FP_SMT_EQ, n, PINF));
    EXPECT_FALSE(eval(FP_SMT_EQ, n, ONE));
  }

  // Infinities.
  EXPECT_TRUE(eval(FP_SMT_EQ, PINF, PINF));
  EXPECT_TRUE(eval(FP_SMT_EQ, MINF, MINF));
  EXPECT_FALSE(eval(FP_SMT_EQ, PINF, MINF));
  EXPECT_FALSE(eval(FP_SMT_EQ, MINF, PINF));

  // Cross-class.
  EXPECT_FALSE(eval(FP_SMT_EQ, PINF, ONE));
  EXPECT_FALSE(eval(FP_SMT_EQ, PZERO, ONE));
  EXPECT_FALSE(eval(FP_SMT_EQ, PZERO, SUBNORMAL));
  EXPECT_TRUE(eval(FP_SMT_EQ, ONE, ONE));
  EXPECT_TRUE(eval(FP_SMT_EQ, SUBNORMAL, SUBNORMAL));
}

// The two operators must actually differ where the semantics say they do,
// and agree everywhere else. Stated as a relation between the two verdicts
// so that an evaluator which quietly routed one kind to the other -- the
// plausible failure, given they share an arm -- cannot pass.
TEST_F(FpModelEqualityTest, TheTwoEqualitiesDifferExactlyOnZerosAndNaN)
{
  const uint32_t values[] = {PZERO, MZERO,       PINF, MINF,     NAN_QUIET,
                             NAN_PAYLOAD, NAN_NEG, ONE,  SUBNORMAL};
  for (uint32_t a : values)
    for (uint32_t b : values)
    {
      const bool ieee = eval(FP_EQ, a, b);
      const bool abstract = eval(FP_SMT_EQ, a, b);
      const bool bothNaN = (a & 0x7FFFFFFF) > 0x7F800000 &&
                           (b & 0x7FFFFFFF) > 0x7F800000;
      const bool bothZero = (a & 0x7FFFFFFF) == 0 && (b & 0x7FFFFFFF) == 0;
      const bool mixedZero = bothZero && a != b;

      if (bothNaN)
      {
        EXPECT_FALSE(ieee);
        EXPECT_TRUE(abstract);
      }
      else if (mixedZero)
      {
        EXPECT_TRUE(ieee);
        EXPECT_FALSE(abstract);
      }
      else
      {
        EXPECT_EQ(ieee, abstract)
            << "the operators must agree away from zeros and NaN: " << std::hex
            << a << " vs " << b;
      }
    }
}

} // namespace

