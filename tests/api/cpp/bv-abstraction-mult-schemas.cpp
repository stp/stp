/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: September, 2026
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

// bv-abstraction-mult-schemas.cpp -- refining an abstracted BVMULT with
// an algebraic fact rather than by ruling out the pair of operand values the
// candidate holds, and the statistics that say which kind of lemma paid.
//
// A blocking lemma excludes one point of a 2^(2W) space, so a multiplication
// the search has to work through can need more rounds than there are pairs
// of operands. The schemas exclude a slice each -- the product's trailing
// zeros, its low bit, zero products with an odd operand, and the shift a
// power-of-two operand turns the whole product into -- and
// BVAbstractionRefiner spends one whenever the candidate contradicts it,
// falling back on the blocking lemma when none of them does.
//
// BVMultSchema_Test covers which schema is chosen, exhaustively. What is
// left for here is the part that needs a solver: that the clauses put into
// it are sound, that the statistics say which kind of lemma paid for the
// answer, and that turning the schemas off (bv-term-abstraction-schemas)
// changes how the query is decided and not what it is decided to be.

#include "api_common.hpp"

#include <cstdint>

using namespace stp;

namespace
{

// The abstraction on, at a width floor low enough that the 64-bit
// multiplication below is taken, with the schemas as the caller asked -- and
// the engine's model self-check (check-sanity) on, as every 2.x checker had
// it, so a sat answer is also held against the assertions. The check
// evaluates the model after the refinement is done and moves none of the
// counters read below.
Options checker_options(bool schemas)
{
  Options o;
  o.set_bool("check-sanity", true);
  o.set_bool("bv-term-abstraction", true);
  o.set_bool("bv-eq-abstraction", true);
  o.set_bool("bv-term-abstraction-schemas", schemas);
  return o;
}

// A solver over a manager of its own, configured as above.
struct Checker
{
  explicit Checker(bool schemas) : s(tm, checker_options(schemas)) {}

  std::uint64_t counter(const char* name) const
  {
    return s.statistics().uint64(name);
  }

  TermManager tm;
  Solver s;
};

Term var(TermManager& tm, const char* name)
{
  return tm.declare(name, tm.mk_bv_sort(64));
}

// A satisfiable factorisation the simplifier cannot settle: the product pins
// both factors and neither is a constant, so the bit-blaster runs and the
// abstraction has something to refine.
void assert_factorisation(Checker& c)
{
  const Term a = var(c.tm, "a");
  const Term b = var(c.tm, "b");
  c.s.add(bvmul(a, b) == c.tm.mk_bv(64, 0x7ffffffc80000005ULL));
  c.s.add(bvugt(a, 1));
  c.s.add(bvugt(b, 1));
}

// An unsatisfiable one that still has to be bit-blasted to be refuted.
//
// 0x1c00 is not a square modulo 2^64: it is divisible by 2^10 but not by
// 2^11, so any root is 32y with y odd, and an odd square is 1 modulo 8 while
// 0x1c00/2^10 is 7. Nothing in the preprocessor sees that -- constant bit
// propagation is exact on a product's low eight bits, so it refutes a
// non-square whose odd part starts there (0xfff0, say) before a single gate
// is built, but here those bits are all zero -- so this one reaches the
// abstraction and is decided by the lemmas the refinement installs.
//
// Written as a product of two variables with an equality between them rather
// than as a square, so that what is abstracted is an ordinary BVMULT.
void assert_a_non_square(Checker& c)
{
  const Term x = var(c.tm, "x");
  const Term y = var(c.tm, "y");
  c.s.add(bvmul(x, y) == c.tm.mk_bv(64, 0x1c00));
  c.s.add(x == y);
}

// If b <= a < 2b, unsigned division has quotient one. Negating that theorem
// gives the DIV/MOD exact-escalation path a formula which abstraction alone
// admits but the exact circuit refutes.
void assert_impossible_quotient(Checker& c)
{
  const Term a = var(c.tm, "div_a");
  const Term b = var(c.tm, "div_b");
  const Term quotient = bvudiv(a, b);
  c.s.add(bvule(b, a));
  c.s.add(bvult(bvsub(a, b), b));
  c.s.add(!(quotient == 1));
}

} // namespace

// The schemas engage. For one inconsistent multiplication the chosen schema
// is installed in place of that multiplication's blocking lemma; a refiner
// pass can visit several operations, so the counters themselves are not a
// partition of passes. A caller that turns schemas on and reads a zero here
// is being told the option did nothing, which is why the lemma counters are
// separate.
TEST(bv_abstraction_mult_schemas, ASchemaLemmaIsSpentOnAnAbstractedMultiply)
{
  Checker c(true);
  assert_factorisation(c);
  EXPECT_TRUE(c.s.check_sat().is_sat());

  EXPECT_GT(c.counter("checks.bitblasted"), 0u);
  EXPECT_EQ(1u, c.counter("bv.abstracted.mult"));
  EXPECT_GT(c.counter("bv.schema_lemmas"), 0u);
}

// With them off the same query is decided by blocking lemmas alone and the
// schema counter stays at zero. Without this leg the test above would pass
// against a counter that is incremented in the wrong place.
TEST(bv_abstraction_mult_schemas, NoSchemaLemmaIsSpentWithTheFlagOff)
{
  Checker c(false);
  assert_factorisation(c);
  EXPECT_TRUE(c.s.check_sat().is_sat());

  EXPECT_GT(c.counter("checks.bitblasted"), 0u);
  EXPECT_EQ(1u, c.counter("bv.abstracted.mult"));
  EXPECT_EQ(0u, c.counter("bv.schema_lemmas"));
  EXPECT_GT(c.counter("bv.blocking_lemmas"), 0u);
}

// Reaching the value allowance is a different outcome from spending another
// blocking lemma. Its counters are what an embedder can use in place of the
// command-line record trace, and the operation-family split must add back to
// the total.
TEST(bv_abstraction_mult_schemas, ExactEscalationIsCountedByFamily)
{
  Checker c(false);
  c.s.options().set_uint("bv-term-abstraction-rounds", 1);
  assert_factorisation(c);
  EXPECT_TRUE(c.s.check_sat().is_sat());

  EXPECT_EQ(1u, c.counter("bv.blocking_lemmas"));
  EXPECT_EQ(1u, c.counter("bv.exact.escalations"));
  EXPECT_EQ(1u, c.counter("bv.exact.escalations_mult"));
  EXPECT_EQ(0u, c.counter("bv.exact.escalations_divmod"));
  EXPECT_GT(c.counter("bv.exact.clauses"), 0u);
  EXPECT_GT(c.counter("bv.exact.variables"), 0u);
}

TEST(bv_abstraction_mult_schemas, DivModExactEscalationIsCountedByFamily)
{
  Checker c(false);
  c.s.options().set_uint("bv-term-abstraction-divmod-value-limit", 1);
  assert_impossible_quotient(c);
  EXPECT_TRUE(c.s.check_sat().is_unsat());

  EXPECT_EQ(1u, c.counter("bv.abstracted.divmod"));
  EXPECT_EQ(1u, c.counter("bv.blocking_lemmas"));
  EXPECT_EQ(1u, c.counter("bv.exact.escalations"));
  EXPECT_EQ(0u, c.counter("bv.exact.escalations_mult"));
  EXPECT_EQ(1u, c.counter("bv.exact.escalations_divmod"));
  EXPECT_GT(c.counter("bv.exact.clauses"), 0u);
  EXPECT_GT(c.counter("bv.exact.variables"), 0u);
}

// The clauses are theorems about the operation, so they can only rule out
// candidates the query rules out too. A schema that was merely usually true
// would show here as a satisfiable query answered unsat -- silently, and
// only on the inputs that reach it.
TEST(bv_abstraction_mult_schemas, TheSchemasDoNotRemoveAModelTheQueryHas)
{
  Checker on(true);
  assert_factorisation(on);
  const Verdict withSchemas = on.s.check_sat().verdict();

  Checker off(false);
  assert_factorisation(off);
  const Verdict withoutSchemas = off.s.check_sat().verdict();

  EXPECT_EQ(Verdict::SAT, withSchemas);
  EXPECT_EQ(withoutSchemas, withSchemas);
}

// ... and they do not admit one it has not. An unsatisfiable query stays
// unsatisfiable, which is the direction a too-weak lemma breaks: the
// abstraction is an over-approximation until refinement pins it, so a schema
// that says less than it claims leaves a candidate nothing contradicts.
TEST(bv_abstraction_mult_schemas, AnUnsatisfiableQueryStaysUnsatisfiable)
{
  Checker on(true);
  assert_a_non_square(on);
  const Verdict withSchemas = on.s.check_sat().verdict();
  // The query really is decided down here, and not by the preprocessor:
  // without this the test would pass against a build in which the schemas
  // never ran at all.
  EXPECT_GT(on.counter("checks.bitblasted"), 0u);
  EXPECT_EQ(1u, on.counter("bv.abstracted.mult"));
  EXPECT_GT(on.counter("bv.schema_lemmas"), 0u);

  Checker off(false);
  assert_a_non_square(off);
  const Verdict withoutSchemas = off.s.check_sat().verdict();
  EXPECT_EQ(0u, off.counter("bv.schema_lemmas"));

  EXPECT_EQ(Verdict::UNSAT, withSchemas);
  EXPECT_EQ(withoutSchemas, withSchemas);
}

// Nothing is spent where nothing is abstracted. The floor is the default 64
// here and the multiplication is 32 bits wide, so the abstraction declines it
// and the refiner never runs -- a schema counted for such a query would mean
// the lemmas are being written over an operation that is already exact.
TEST(bv_abstraction_mult_schemas, NothingIsSpentBelowTheWidthFloor)
{
  Checker c(true);
  const Sort bv = c.tm.mk_bv_sort(32);
  const Term a = c.tm.declare("a32", bv);
  const Term b = c.tm.declare("b32", bv);
  c.s.add(bvmul(a, b) == c.tm.mk_bv(32, 3037 * 3041));
  c.s.add(bvugt(a, 1));
  c.s.add(bvugt(b, 1));
  EXPECT_TRUE(c.s.check_sat().is_sat());

  EXPECT_GT(c.counter("checks.bitblasted"), 0u);
  EXPECT_EQ(0u, c.counter("bv.abstracted.mult"));
  EXPECT_EQ(0u, c.counter("bv.schema_lemmas"));
}
