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

#ifndef BVABSTRACTIONREFINER_H
#define BVABSTRACTIONREFINER_H

// The CEGAR half of --bv-eq-abstraction and --bv-term-abstraction.
//
// The bit-blaster replaces an equality, a comparison or an arithmetic
// operation by free combinational inputs and records what it stood for.
// That is an over-approximation, so a candidate model is an assignment of
// the query only once every abstraction in it has been checked against
// the operands underneath and, where the two disagree, pinned by clauses.
// This is the party that does the checking and the pinning.
//
// It is kept apart from the lowering that mints the records because there
// are two of those -- the batch pipeline's whole-formula ToSATAIG and the
// incremental driver's persistent, per-conjunct encoder -- and only the
// resolution of a record's SAT variables differs between them. Everything
// here works from the records plus one map from node to SAT variables, and
// so is shared.
//
// Nothing it adds to the solver is retractable, and nothing needs to be:
// every clause is a definitional fact about the blasted circuit -- this
// abstraction variable means these operand bits -- which holds whatever
// else is asserted. Refining an abstraction only ever brings the encoding
// closer to the query it already stood for.

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/ToSat/BVAbstractionTypes.h"
#include "stp/ToSat/BVExactEncoder.h"
#include "stp/ToSat/ToSATBase.h"

#include <cstdint>
#include <map>
#include <vector>

namespace stp
{

// The variable a record does not have: the condition input of a family that
// carries none, or one whose input never reached the solver. It is ~0u
// rather than zero because zero is a SAT variable like any other -- the
// incremental driver has handed variable 1 to an abstraction input -- and a
// record whose variable read as absent would be skipped, which for an
// over-approximation means certified.
const unsigned BV_ABSTRACTION_NO_VAR = ~((unsigned)0);

// An equality replaced by one free Boolean. `refinedBits` counts the bit
// positions whose agreement has been encoded so far, and `defined` marks
// the point where all of them have been, after which the Boolean is the
// equality and the record is never revisited.
struct BVEQAbstraction
{
  BVAbstractionId id;
  std::vector<BVAbstractionId> dependencies;
  ASTNode eqNode;
  unsigned abstractionSATVar = BV_ABSTRACTION_NO_VAR;
  ASTNode leftSymbol;
  ASTNode rightSymbol;
  unsigned width;
  bool defined = false;
  unsigned refinedBits = 0;
  std::vector<unsigned> xnorHelpers;
};

// An operation replaced by free result bits (and, for a comparison or an
// if-then-else, a free condition variable).
// The algebraic facts about a multiplication that a refinement round may
// spend in place of ruling out the one pair of operand values the candidate
// happens to hold.
//
// A blocking lemma excludes a single point of a 2^(2W) space, so a
// multiplication the search has to work through can need more rounds than
// there are pairs of operands -- at 53 bits, one of 2^106. Each of these
// excludes a slice instead: they are theorems about every pair, not about
// the one in hand, and the candidate is read only to decide which of them
// it contradicts.
//
// The four schemas cover low-bit parity, trailing-zero preservation, and
// positive and negative powers of two.
enum class MulSchema
{
  // Nothing the candidate contradicts. The round falls through to the
  // blocking lemma and the escalation behind it.
  None,
  // t[0] = a[0] & b[0]: the product is odd exactly when both operands are.
  Odd,
  // The product carries at least as many trailing zeros as either operand,
  // written per bit: t[i] holds only if some bit of that operand at or
  // below i does. Equivalently, for operand s and product t:
  // `(bvand (bvor (bvneg s) s) t) = t`.
  TrailingZeros,
  // An operand whose value is 2^k turns the product into a shift of the
  // other one: a = 2^k -> t = b << k. The premise fixes one operand, so
  // this still rules out 2^W pairs rather than one.
  Pow2,
  // ... and an operand whose value is -2^k turns it into a shift of the
  // other one negated: a = -2^k -> t = (-b) << k.
  NegPow2
};

// Which fact to spend, over which operand. Multiplication is commutative,
// so each schema has two readings and they are separate lemmas.
struct MulSchemaChoice
{
  MulSchema schema = MulSchema::None;
  unsigned operand = 0;
  // log2 of the power of two, for the two schemas that have one.
  unsigned shift = 0;
};

// Bits of BVTermAbstraction::installedSchemas. Only the two unconditional
// facts are tracked: once installed, no candidate can contradict them
// again, so re-checking them is wasted and re-emitting them is worse.
// The two value-guarded schemas need no flag -- installing one for a given
// operand value settles that value for good, and there are only as many of
// them as there are bits.
enum
{
  MUL_SCHEMA_INSTALLED_ODD = 1u,
  MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_0 = 2u,
  MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_1 = 4u
};

// The first of the four facts above that this candidate contradicts, or
// None. Pure: the caller has already read the model, and what comes back
// depends on nothing else.
//
// `tBits` is the product bits the candidate holds, NOT the product of
// `aBits` and `bBits` -- the whole point is that the two disagree. Called
// only once they do.
DLL_PUBLIC MulSchemaChoice chooseMulSchema(const std::vector<bool>& aBits,
                                           const std::vector<bool>& bBits,
                                           const std::vector<bool>& tBits,
                                           unsigned installedSchemas);

// The algebraic facts an abstracted BVDIV or BVMOD is refined with.
//
// Division is not commutative and has no cheap unconditional fact about its
// low bits to match the multiplication schemas: the low bits of a quotient
// depend on the whole of both operands. Both facts here are value-guarded on
// the *divisor* instead. Each says what the operation is for one divisor and
// leaves the dividend free, which rules out 2^W pairs where a blocking lemma
// rules out one, and neither needs an installed-flag -- fixing a divisor
// value settles that value for good, and there are only as many of them as
// the schemas can name.
enum class DivSchema
{
  // Nothing the candidate contradicts. The round falls through to the
  // blocking lemma and the escalation behind it.
  None,
  // b = 0 -> t = ~0 for BVDIV, t = a for BVMOD. SMT-LIB totalises both and
  // the abstraction is told neither, so a candidate may divide by zero and
  // call the answer anything at all. This is the one divisor a blocking
  // lemma is worst at: it rules out the pair (a, 0) and leaves every other
  // dividend over the same zero divisor still to be found.
  DivisorZero,
  // b = 2^k -> t = a >> k for BVDIV, t = a & (2^k - 1) for BVMOD. k = 0 is
  // the useful degenerate reading: dividing by one is the dividend, and the
  // remainder over one is zero.
  Pow2Divisor,
  // The three below name no divisor at all, which is what makes them the
  // ones that fire. A candidate handed a 256-bit divisor is almost never
  // handed zero or a power of two, so the two schemas above sit idle on
  // exactly the queries the abstraction exists for -- while a bound is
  // contradicted by any candidate that overshoots, whatever the divisor is.
  //
  // Each is installed once and then never again: they are facts about every
  // pair of operands, so a second copy would say nothing new.
  //
  // r <=u a. True over a zero divisor as well, where the remainder is the
  // dividend, so this one carries no premise whatsoever.
  RemainderAtMostDividend,
  // b != 0 -> r <u b, which is what a remainder is.
  RemainderBelowDivisor,
  // b != 0 -> t <=u a. Dividing by one leaves the dividend and dividing by
  // more only shrinks it; the premise is there for the zero divisor, whose
  // totalised all-ones quotient is the one case that breaks it.
  QuotientAtMostDividend,
  // One of the DivLemma facts, named by DivSchemaChoice::lemmaIndex. They
  // are inequalities over the quotient rather than statements of what it
  // is, and several shift by a variable amount, so unlike everything above
  // they are built by the bit-blaster rather than written a clause at a
  // time.
  Lemma
};

// Bits of BVTermAbstraction::installedSchemas for the three unconditional
// division facts. They share the field with the multiplication flags, which
// is safe because an abstraction is a multiplication or a division and
// never both.
enum
{
  DIV_SCHEMA_INSTALLED_REMAINDER_AT_MOST_DIVIDEND = 8u,
  DIV_SCHEMA_INSTALLED_REMAINDER_BELOW_DIVISOR = 16u,
  DIV_SCHEMA_INSTALLED_QUOTIENT_AT_MOST_DIVIDEND = 32u,
  // ... and one apiece for the seven DivLemma facts, which are
  // unconditional for the same reason and tracked the same way. The first
  // of them is 64; `DIV_LEMMA_INSTALLED(i)` is the bit for the i'th.
  DIV_LEMMA_INSTALLED_FIRST = 64u
};

inline unsigned divLemmaInstalledBit(unsigned index)
{
  return DIV_LEMMA_INSTALLED_FIRST << index;
}

// The DivLemma facts the chooser offers, in the order it offers them, and
// how many there are. Exposed so a test can walk the same table the refiner
// does rather than keeping a second copy of it in step with this one.
DLL_PUBLIC const DivLemma* divLemmaTable(unsigned& count);

struct DivSchemaChoice
{
  DivSchema schema = DivSchema::None;
  // log2 of the divisor, for the schema that has one.
  unsigned shift = 0;
  // Set when `schema` is Lemma: which of the DivLemma facts to install, as
  // an index into the table the refiner keeps. Held as an index rather than
  // the enum so this header does not need the one that defines it.
  unsigned lemmaIndex = 0;
};

// Where each bit of the result comes from once a schema has fixed the
// divisor: a bit of the dividend, or a constant. The fact is written this
// way because it is exactly what the encoder can pin under a guard, which
// keeps what the schema claims and what it installs from drifting apart --
// and it lets a test check the claim without a solver.
enum : int
{
  DIV_SOURCE_ZERO = -1,
  DIV_SOURCE_ONE = -2
};

DLL_PUBLIC std::vector<int> divSchemaSources(Kind opKind, unsigned width,
                                             const DivSchemaChoice& choice);

// The first of the facts above that this candidate contradicts, or None.
// Pure, and called under the same conditions as chooseMulSchema: `tBits` is
// what the candidate holds for the result, already known to disagree with
// what the operands say it should be.
//
// `opKind` is BVDIV or BVMOD. The two share both schemas and differ only in
// what each one concludes.
DLL_PUBLIC DivSchemaChoice chooseDivSchema(Kind opKind,
                                           const std::vector<bool>& aBits,
                                           const std::vector<bool>& bBits,
                                           const std::vector<bool>& tBits,
                                           unsigned installedSchemas);

// A variable that holds exactly when `lv <= rv`. Shared by the comparison
// refinement, which is where it comes from, and by the division bounds,
// which are comparisons over the abstraction's own result bits.
DLL_PUBLIC unsigned encodeLessOrEqual(SATSolver& solver,
                                      const std::vector<unsigned>& lv,
                                      const std::vector<unsigned>& rv,
                                      unsigned width, bool isSigned);

// One of the three bounds, over the operand proxies and the abstraction's
// own result bits. Exposed for the same reason as the encoder above: that
// the clauses say what the schema claims is a question only a solver can
// answer.
DLL_PUBLIC void encodeDivBound(SATSolver& solver, DivSchema schema,
                               const std::vector<unsigned>& dividendVars,
                               const std::vector<unsigned>& divisorVars,
                               const std::vector<unsigned>& resultVars,
                               unsigned width);

// divisor = divisorBits -> every result bit is a constant or a bit of the
// dividend, as `source` says. Exposed for the tests: what the schema claims
// is checked by evaluating `divSchemaSources`, and that the clauses say the
// same thing is a separate question a solver has to answer.
DLL_PUBLIC void encodeDivUnderDivisorValue(
    SATSolver& solver, const std::vector<unsigned>& divisorVars,
    const std::vector<bool>& divisorBits,
    const std::vector<unsigned>& dividendVars,
    const std::vector<unsigned>& resultVars, unsigned width,
    const std::vector<int>& source);

// The blocking lemmas one abstraction of this width may spend before the
// refinement gives up on it and encodes the operation exactly.
//
// A blocking lemma rules out one pair of operand values out of 2^(2W), so
// what one is worth falls away as the operands widen and a flat allowance
// means something quite different at either end of the range. The allowance
// is a rate instead -- `width / bv_term_abstraction_value_divisor` -- held
// under the flat ceiling `bv_term_abstraction_rounds`, which keeps every
// spelling that ceiling already had: zero still never escalates, and an
// explicit count still caps.
DLL_PUBLIC unsigned valueLemmaAllowance(const UserDefinedFlags& uf,
                                        unsigned width);

struct BVTermAbstraction
{
  BVAbstractionId id;
  std::vector<BVAbstractionId> dependencies;
  ASTNode termNode;
  Kind opKind;
  ASTNode operands[3];
  unsigned numOperands;
  unsigned width;
  // Direct variables for this record's free result bits. The batch path may
  // leave this empty and use nodeToSATVar. The persistent incremental path
  // fills it so correctness does not depend on the canonical-reuse invariant:
  // if duplicate records ever arise, each still owns distinct inputs.
  std::vector<unsigned> resultSATVars;
  bool operandNegated[3] = {false, false, false};
  unsigned condSATVar = BV_ABSTRACTION_NO_VAR;
  bool defined = false;
  // Blocking lemmas spent on this one abstraction so far; see
  // bv_term_abstraction_rounds.
  unsigned blockedRounds = 0;
  // Algebraic schemas spent on it, counted separately: a schema is both
  // cheaper and stronger than a blocking lemma, so it does not eat the
  // budget that decides when to give up and encode the operation exactly.
  // It is bounded by the same number, though, because a candidate that
  // keeps landing on fresh powers of two would otherwise buy a solve for
  // each one.
  unsigned schemaRounds = 0;
  // Which of the unconditional schemas are already in the solver.
  unsigned installedSchemas = 0;
  // How far up the exact encoding has been pushed, for an escalation that
  // goes a piece at a time; see bv_term_abstraction_inc_bitblast. Zero
  // until the first piece, and equal to the width once `defined` is set.
  unsigned blastedBits = 0;
  // The bits of -operand[i], minted on first use by the NegPow2 schema and
  // kept because that schema can fire once per power of two and would
  // otherwise pay for the same negation circuit every time.
  std::vector<unsigned> negatedOperand[2];
};

class DLL_PUBLIC BVAbstractionRefiner
{
  STPMgr* bm;

  std::vector<BVEQAbstraction> eqs_;
  std::vector<BVTermAbstraction> terms_;

  struct RecordLocation
  {
    bool equality;
    size_t index;
  };
  std::map<BVAbstractionId, RecordLocation> recordOfId_;
  size_t indexedRecords_ = 0;

  // Monotone across the session, including across a clear(): a driver
  // compares it either side of a round to learn whether that round found
  // anything, and a counter that went backwards would read as no progress.
  uint64_t refinements_ = 0;

  unsigned refineEqualities(SATSolver& solver,
                            const ToSATBase::ASTNodeToSATVar& nodeToSATVar);
  unsigned refineTerms(SATSolver& solver,
                       const ToSATBase::ASTNodeToSATVar& nodeToSATVar);
  void rebuildRecordIndex();

public:
  explicit BVAbstractionRefiner(STPMgr* bm_) : bm(bm_) {}

  bool empty() const { return eqs_.empty() && terms_.empty(); }
  bool hasEqualities() const { return !eqs_.empty(); }
  bool hasTerms() const { return !terms_.empty(); }

  // The records, for whoever mints them. Everything a refinement round
  // learns is written back into them, so an owner that discards its SAT
  // solver or its bit-blast has to discard these too.
  const std::vector<BVEQAbstraction>& equalities() const { return eqs_; }
  const std::vector<BVTermAbstraction>& terms() const { return terms_; }

  // File a record. The identity a producer minted travels with it, so
  // everything downstream can name the operation a record came from rather
  // than the position it happens to occupy in these vectors.
  void appendEquality(BVEQAbstraction record);
  void appendTerm(BVTermAbstraction record);

  void clear()
  {
    eqs_.clear();
    terms_.clear();
    recordOfId_.clear();
    indexedRecords_ = 0;
  }

  uint64_t refinements() const { return refinements_; }

  // Keep a simplifying backend from eliminating anything a future lemma
  // will be written over.
  void freezeVariables(SATSolver& solver,
                       const ToSATBase::ASTNodeToSATVar& nodeToSATVar) const;

  // Check every record against the current SAT model and pin the ones the
  // model contradicts. Returns how many were pinned: zero means the
  // candidate is faithful and may be handed on.
  unsigned refine(SATSolver& solver,
                  const ToSATBase::ASTNodeToSATVar& nodeToSATVar);
};
}

#endif
