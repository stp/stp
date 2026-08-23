/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: Aug, 2026
 *
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
********************************************************************/

// Refining an abstracted BVMULT with an algebraic fact rather than by ruling
// out the pair of operand values the candidate holds.
//
// A blocking lemma excludes one point of a 2^(2W) space, so a multiplication
// the search has to work through can need more rounds than there are pairs
// of operands. The schemas exclude a slice each -- the product's trailing
// zeros, its low bit, and the shift a power-of-two operand turns the whole
// product into -- and BVAbstractionRefiner spends one whenever the candidate
// contradicts it, falling back on the blocking lemma when none of them does.
//
// BVMultSchema_Test covers which schema is chosen, exhaustively. What is
// left for here is the part that needs a solver: that the clauses put into
// it are sound, that the counter says which kind of lemma paid for the
// answer, and that turning the schemas off changes how the query is decided
// and not what it is decided to be.
#include "stp/c_interface.h"
#include <gtest/gtest.h>

namespace
{

// The abstraction on, at a width floor low enough that the 64-bit
// multiplication below is taken, with the schemas as the caller asked.
VC checker(int schemas)
{
  VC vc = vc_createValidityChecker();
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION, 1);
  vc_setInterfaceFlags(vc, BV_EQ_ABSTRACTION, 1);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_SCHEMAS, schemas);
  return vc;
}

Expr var(VC vc, const char* name)
{
  return vc_varExpr(vc, name, vc_bvType(vc, 64));
}

// A satisfiable factorisation the simplifier cannot settle: the product pins
// both factors and neither is a constant, so the bit-blaster runs and the
// abstraction has something to refine.
void assertFactorisation(VC vc)
{
  Expr a = var(vc, "a");
  Expr b = var(vc, "b");
  vc_assertFormula(vc, vc_eqExpr(vc, vc_bvMultExpr(vc, 64, a, b),
                                 vc_bvConstExprFromLL(vc, 64,
                                                      0x7ffffffc80000005ULL)));
  vc_assertFormula(vc, vc_bvGtExpr(vc, a, vc_bvConstExprFromInt(vc, 64, 1)));
  vc_assertFormula(vc, vc_bvGtExpr(vc, b, vc_bvConstExprFromInt(vc, 64, 1)));
}

// An unsatisfiable one that still has to be bit-blasted to be refuted.
//
// 0xfff0 is not a square modulo 2^64: it is divisible by 16 but not by 32,
// so any root is 4y with y odd, and an odd square is 1 modulo 8 while
// 0xfff0/16 is 7. Nothing in the preprocessor sees that -- constant bit
// propagation settles the easier "an even factor cannot give an odd product"
// before a single gate is built, which makes that query useless here -- so
// this one reaches the abstraction and is decided by the lemmas the
// refinement installs.
//
// Written as a product of two variables with an equality between them rather
// than as a square, so that what is abstracted is an ordinary BVMULT.
void assertANonSquare(VC vc)
{
  Expr x = var(vc, "x");
  Expr y = var(vc, "y");
  vc_assertFormula(vc, vc_eqExpr(vc, vc_bvMultExpr(vc, 64, x, y),
                                 vc_bvConstExprFromInt(vc, 64, 0xfff0)));
  vc_assertFormula(vc, vc_eqExpr(vc, x, y));
}

unsigned long long counter(VC vc, enum stp_counter_t c)
{
  return vc_getCounter(vc, c);
}

} // namespace

// The schemas engage, and they engage in place of the blocking lemmas rather
// than alongside them: a round spends one or the other. A caller that turns
// them on and reads a zero here is being told the flag did nothing, which is
// the whole reason the two counters are separate.
TEST(bv_abstraction_mult_schemas, ASchemaLemmaIsSpentOnAnAbstractedMultiply)
{
  VC vc = checker(1);
  assertFactorisation(vc);
  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc))); // satisfiable

  EXPECT_GT(counter(vc, STP_COUNTER_QUERIES_BITBLASTED), 0u);
  EXPECT_EQ(1u, counter(vc, STP_COUNTER_BV_ABSTRACTED_MULT));
  EXPECT_GT(counter(vc, STP_COUNTER_BV_SCHEMA_LEMMAS), 0u);
  vc_Destroy(vc);
}

// With them off the same query is decided by blocking lemmas alone and the
// schema counter stays at zero. Without this leg the test above would pass
// against a counter that is incremented in the wrong place.
TEST(bv_abstraction_mult_schemas, NoSchemaLemmaIsSpentWithTheFlagOff)
{
  VC vc = checker(0);
  assertFactorisation(vc);
  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  EXPECT_GT(counter(vc, STP_COUNTER_QUERIES_BITBLASTED), 0u);
  EXPECT_EQ(1u, counter(vc, STP_COUNTER_BV_ABSTRACTED_MULT));
  EXPECT_EQ(0u, counter(vc, STP_COUNTER_BV_SCHEMA_LEMMAS));
  EXPECT_GT(counter(vc, STP_COUNTER_BV_BLOCKING_LEMMAS), 0u);
  vc_Destroy(vc);
}

// The clauses are theorems about the operation, so they can only rule out
// candidates the query rules out too. A schema that was merely usually true
// would show here as a satisfiable query answered unsat -- silently, and
// only on the inputs that reach it.
TEST(bv_abstraction_mult_schemas, TheSchemasDoNotRemoveAModelTheQueryHas)
{
  VC on = checker(1);
  assertFactorisation(on);
  const int withSchemas = vc_query(on, vc_falseExpr(on));
  vc_Destroy(on);

  VC off = checker(0);
  assertFactorisation(off);
  const int withoutSchemas = vc_query(off, vc_falseExpr(off));
  vc_Destroy(off);

  EXPECT_EQ(0, withSchemas);
  EXPECT_EQ(withoutSchemas, withSchemas);
}

// ... and they do not admit one it has not. An unsatisfiable query stays
// unsatisfiable, which is the direction a too-weak lemma breaks: the
// abstraction is an over-approximation until refinement pins it, so a schema
// that says less than it claims leaves a candidate nothing contradicts.
TEST(bv_abstraction_mult_schemas, AnUnsatisfiableQueryStaysUnsatisfiable)
{
  VC on = checker(1);
  assertANonSquare(on);
  const int withSchemas = vc_query(on, vc_falseExpr(on));
  // The query really is decided down here, and not by the preprocessor:
  // without this the test would pass against a build in which the schemas
  // never ran at all.
  EXPECT_GT(counter(on, STP_COUNTER_QUERIES_BITBLASTED), 0u);
  EXPECT_EQ(1u, counter(on, STP_COUNTER_BV_ABSTRACTED_MULT));
  EXPECT_GT(counter(on, STP_COUNTER_BV_SCHEMA_LEMMAS), 0u);
  vc_Destroy(on);

  VC off = checker(0);
  assertANonSquare(off);
  const int withoutSchemas = vc_query(off, vc_falseExpr(off));
  EXPECT_EQ(0u, counter(off, STP_COUNTER_BV_SCHEMA_LEMMAS));
  vc_Destroy(off);

  EXPECT_EQ(1, withSchemas);
  EXPECT_EQ(withoutSchemas, withSchemas);
}

// Nothing is spent where nothing is abstracted. The floor is the default 64
// here and the multiplication is 32 bits wide, so the abstraction declines it
// and the refiner never runs -- a schema counted for such a query would mean
// the lemmas are being written over an operation that is already exact.
TEST(bv_abstraction_mult_schemas, NothingIsSpentBelowTheWidthFloor)
{
  VC vc = checker(1);
  Type bv = vc_bvType(vc, 32);
  Expr a = vc_varExpr(vc, "a32", bv);
  Expr b = vc_varExpr(vc, "b32", bv);
  vc_assertFormula(vc, vc_eqExpr(vc, vc_bvMultExpr(vc, 32, a, b),
                                 vc_bvConstExprFromInt(vc, 32, 3037 * 3041)));
  vc_assertFormula(vc, vc_bvGtExpr(vc, a, vc_bvConstExprFromInt(vc, 32, 1)));
  vc_assertFormula(vc, vc_bvGtExpr(vc, b, vc_bvConstExprFromInt(vc, 32, 1)));
  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  EXPECT_GT(counter(vc, STP_COUNTER_QUERIES_BITBLASTED), 0u);
  EXPECT_EQ(0u, counter(vc, STP_COUNTER_BV_ABSTRACTED_MULT));
  EXPECT_EQ(0u, counter(vc, STP_COUNTER_BV_SCHEMA_LEMMAS));
  vc_Destroy(vc);
}
