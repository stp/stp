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
#include <iosfwd>
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
// The hand-written schemas cover low-bit parity, trailing-zero preservation,
// and positive and negative powers of two. Lemma carries the ranked upstream
// registry, including MUL8's zero-product/odd-factor relationship.
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
  NegPow2,
  // One of the remaining synthesised facts, named by lemmaIndex.
  Lemma
};

// Which fact to spend, over which operand. Multiplication is commutative,
// so each schema has two readings and they are separate lemmas.
struct MulSchemaChoice
{
  MulSchema schema = MulSchema::None;
  unsigned operand = 0;
  // log2 of the power of two for the two shift schemas.
  unsigned shift = 0;
  // Set for Lemma: index in mulLemmaTable().
  unsigned lemmaIndex = 0;
  // The option family that admitted this choice. BASE is also the harmless
  // default for None and for the established schemas' aggregate initialisers.
  BVSchemaGroup group = BVSchemaGroup::BASE;
};

// Bits of BVTermAbstraction::installedSchemas. Only the unconditional facts
// are tracked: once installed, no candidate can contradict them again, so
// re-checking them is wasted and re-emitting them is worse. The two
// value-guarded schemas need no flag -- installing one for a given operand
// value settles that value for good, and there are only as many of them as
// there are bits.
enum : uint64_t
{
  MUL_SCHEMA_INSTALLED_ODD = 1ull << 0,
  MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_0 = 1ull << 1,
  MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_1 = 1ull << 2,
  // One bit per registry entry per operand reading: fifteen lemmas in two
  // readings occupy bits 3 through 32.
  MUL_LEMMA_INSTALLED_FIRST = 1ull << 3
};

constexpr uint64_t mulLemmaInstalledBit(unsigned index, unsigned operand)
{
  return MUL_LEMMA_INSTALLED_FIRST << (2 * index + operand);
}


struct AddSchemaChoice
{
  bool found = false;
  unsigned operand = 0;
  unsigned lemmaIndex = 0;
  BVSchemaGroup group = BVSchemaGroup::BASE;
};

constexpr uint64_t addLemmaInstalledBitValue(unsigned index, unsigned operand)
{
  return uint64_t{1} << (2 * index + operand);
}

inline uint64_t addLemmaInstalledBit(unsigned index, unsigned operand)
{
  return addLemmaInstalledBitValue(index, operand);
}

DLL_PUBLIC AddSchemaChoice
chooseAddSchema(const std::vector<bool>& aBits, const std::vector<bool>& bBits,
                const std::vector<bool>& tBits, uint64_t installedSchemas,
                uint32_t enabledGroups = BV_SCHEMA_GROUP_ALL);

// The first fact above that this candidate contradicts, or None. Pure: the
// caller has already read the model, and what comes back depends on nothing
// else.
//
// `tBits` is the product bits the candidate holds, NOT the product of
// `aBits` and `bBits` -- the whole point is that the two disagree. Called
// only once they do.
DLL_PUBLIC MulSchemaChoice
chooseMulSchema(const std::vector<bool>& aBits, const std::vector<bool>& bBits,
                const std::vector<bool>& tBits, uint64_t installedSchemas,
                uint32_t enabledGroups = BV_SCHEMA_GROUP_ALL);

// Whether one hand-written multiplication schema holds of these values.
//
// The registry facts get their five faces from BVLemmaCatalogue: one
// enumerator, one predicate, one circuit, one name, one group, one table row
// apiece, and an exhaustive test that reconciles the predicate with the
// circuit. The schemas here and the division ones below are not table rows --
// each is parameterised by something the candidate supplies (an operand
// reading, an exponent, a prefix length, a divisor value) and each has a
// circuit of its own shape, so a row would have to carry a different
// signature per arm. The reason the table exists applies to them unchanged
// though: what the chooser reads off a candidate and what the clauses go on
// to say have to be the same claim, and the only way to know that is to have
// one predicate and check the circuit against it.
//
// So the claim is written once, here, the chooser calls exactly these, and
// BVSchemaCircuit_Test drives the same functions against the circuits the
// refiner installs. Each is a theorem of the operation on its own -- the
// value-guarded arms carry their guard rather than assuming the caller has
// checked it -- which is what lets the same test ask both questions of them.
//
// `operand` selects the reading of the commutative operation; `shift` carries
// the exponent for Pow2 and NegPow2, and is ignored by the arms that take no
// parameter.
DLL_PUBLIC bool mulSchemaHolds(MulSchema schema, unsigned operand,
                               unsigned shift,
                               const std::vector<bool>& aBits,
                               const std::vector<bool>& bBits,
                               const std::vector<bool>& tBits);

// The circuits those schemas install, over the operand proxies and the
// abstraction's own result bits. Exposed for the same reason the division
// encoders below are: whether the clauses say what the predicate above claims
// is a question only a solver can answer.
DLL_PUBLIC void encodeMulOdd(SATSolver& solver,
                             const std::vector<unsigned>& aVars,
                             const std::vector<unsigned>& bVars,
                             const std::vector<unsigned>& resultVars);
DLL_PUBLIC void encodeMulTrailingZeros(SATSolver& solver,
                                       const std::vector<unsigned>& opVars,
                                       const std::vector<unsigned>& resultVars,
                                       unsigned width);
DLL_PUBLIC void encodeMulShiftUnderValue(
    SATSolver& solver, const std::vector<unsigned>& fixedVars,
    const std::vector<bool>& fixedBits, const std::vector<unsigned>& sourceVars,
    const std::vector<unsigned>& resultVars, unsigned width, unsigned shift);

// The bits of -x. The negated-power-of-two schema is this composed with the
// shift circuit above, so what it claims can only be checked against the two
// together.
DLL_PUBLIC std::vector<unsigned> encodeNegate(SATSolver& solver,
                                              const std::vector<unsigned>& x,
                                              unsigned width);

// What the operation really is at these operand values: the oracle the whole
// refinement rests on, since a candidate is faithful exactly when its result
// agrees with this.
//
// It is STP's own constant evaluator rather than a second implementation kept
// beside the loop -- `opKind` is BVMULT, BVDIV or BVMOD, and the two
// totalisations SMT-LIB asks for over a zero divisor come from there rather
// than from a special case written here. The one that was written here
// answered zero for a division by zero, which made a bogus candidate look
// consistent and left the loop with nothing to say about a model it had
// already rejected. Exposed so that the oracle can be checked on its own
// rather than only through the loop that depends on it.
DLL_PUBLIC std::vector<bool> bvOperationValue(Kind opKind,
                                              const std::vector<bool>& aBits,
                                              const std::vector<bool>& bBits);

// The exact low `prefixBits` bits of an addition, over the operand proxies
// and the abstraction's own result bits. `aNegated`/`bNegated` carry the
// subtraction spelling STP lowers as an addition of a complement. The whole
// addition is this with `prefixBits == width`, so the definition and any
// partial pin cannot silently disagree about polarity.
DLL_PUBLIC void encodeAddLowPrefix(
    SATSolver& solver, const std::vector<unsigned>& aVars,
    const std::vector<unsigned>& bVars,
    const std::vector<unsigned>& resultVars, unsigned width,
    unsigned prefixBits, bool aNegated = false, bool bNegated = false);

// The algebraic facts an abstracted BVDIV or BVMOD is refined with.
//
// Division is not commutative and has no cheap unconditional fact about its
// low bits to match the multiplication schemas: the low bits of a quotient
// depend on the whole of both operands. The first two facts are value-guarded
// on the *divisor*. Each says what the operation is for one divisor and
// leaves the dividend free, which rules out 2^W pairs where a blocking lemma
// rules out one. They need no installed flag: fixing a divisor value settles
// that value for good. The bounds and synthesised facts that follow apply to
// whole candidate regions and are each installed once.
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
  // The facts below name no particular divisor, which is what makes them
  // fire. A candidate handed a 256-bit divisor is almost never
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

// Bits of BVTermAbstraction::installedSchemas for the unconditional division
// or remainder facts. They share the field with the multiplication and
// addition flags, which is safe because an abstraction has only one kind.
enum : uint64_t
{
  DIV_SCHEMA_INSTALLED_REMAINDER_AT_MOST_DIVIDEND = 1ull << 0,
  DIV_SCHEMA_INSTALLED_REMAINDER_BELOW_DIVISOR = 1ull << 1,
  DIV_SCHEMA_INSTALLED_QUOTIENT_AT_MOST_DIVIDEND = 1ull << 2,
  // ... and one apiece for the DivLemma or RemLemma facts, which are
  // unconditional for the same reason and tracked the same way;
  // divLemmaInstalledBit(i) is the bit for the i'th.
  DIV_LEMMA_INSTALLED_FIRST = 1ull << 3
};

constexpr uint64_t divLemmaInstalledBitValue(unsigned index)
{
  return DIV_LEMMA_INSTALLED_FIRST << index;
}

inline uint64_t divLemmaInstalledBit(unsigned index)
{
  return divLemmaInstalledBitValue(index);
}

// The schema families whose guard is read off the candidate -- a divisor
// value, a power-of-two exponent, a magnitude band -- rather than being a
// fact about every pair of operands.
//
// An unconditional fact needs one `installedSchemas` bit: once it is in the
// solver no candidate can contradict it again. These cannot be tracked that
// way, because each fires once per distinct guard, and for several of them
// the number of distinct guards grows with the width rather than being a
// constant: a 256-bit divisor has 255 magnitudes to walk through and a
// 256-bit quotient has 255 thresholds, at a comparator apiece. Both were
// observed doing exactly that, and were patched in different ways -- one by
// reordering the chooser, one by a hard cap of two. This is that cap,
// generalised: every candidate-guarded family declares an instance budget,
// and the counters live in the high bits of the same field.
enum class BVSchemaFamily : unsigned
{
  // DivSchema::DivisorZero and DivSchema::Pow2Divisor.
  DivisorValue = 0,
  // MulSchema::Pow2 and MulSchema::NegPow2.
  MulShiftValue,
  COUNT
};

constexpr unsigned BV_SCHEMA_FAMILY_COUNT =
    static_cast<unsigned>(BVSchemaFamily::COUNT);

// Four bits apiece, above every per-lemma bit any operation uses.
constexpr unsigned BV_SCHEMA_FAMILY_COUNTER_BITS = 4;
constexpr unsigned BV_SCHEMA_FAMILY_COUNTER_FIRST = 48;
constexpr uint64_t BV_SCHEMA_FAMILY_COUNTER_MASK =
    (uint64_t{1} << BV_SCHEMA_FAMILY_COUNTER_BITS) - 1;

static_assert(BV_SCHEMA_FAMILY_COUNT * BV_SCHEMA_FAMILY_COUNTER_BITS <=
                  64 - BV_SCHEMA_FAMILY_COUNTER_FIRST,
              "the schema-family counters do not fit in installedSchemas");
// Growing a catalogue eventually runs its per-entry bits into the low-prefix
// bit above, or the family counters above that. Both are compile errors.
static_assert(mulLemmaInstalledBit(BV_MUL_LEMMA_COUNT - 1, 1) <
                  (uint64_t{1} << BV_SCHEMA_FAMILY_COUNTER_FIRST),
              "the MUL catalogue has outgrown its installed-lemma bits");
static_assert(addLemmaInstalledBitValue(BV_ADD_LEMMA_COUNT - 1, 1) <
                  (uint64_t{1} << BV_SCHEMA_FAMILY_COUNTER_FIRST),
              "the ADD catalogue has outgrown its installed-lemma bits");
static_assert(divLemmaInstalledBitValue(BV_DIV_LEMMA_COUNT - 1) <
                  (uint64_t{1} << BV_SCHEMA_FAMILY_COUNTER_FIRST),
              "the UDIV catalogue has outgrown its installed-lemma bits");
static_assert(divLemmaInstalledBitValue(BV_REM_LEMMA_COUNT - 1) <
                  (uint64_t{1} << BV_SCHEMA_FAMILY_COUNTER_FIRST),
              "the UREM catalogue has outgrown its installed-lemma bits");

// How many instances of a family one record may install; zero is no cap.
//
// Two is the number that removed the observed divisor-magnitude regression,
// and the quotient thresholds have the same failure mode with no measurement
// of their own, so they inherit it. The two value-guarded families are left
// uncapped: they are what the established profile has always done, and each
// installed instance says what the operation *is* for that operand value
// rather than bounding it, so capping them would be a policy change with no
// evidence behind it. The mechanism is here for when there is some.
constexpr unsigned bvSchemaFamilyAllowance(BVSchemaFamily)
{
  return 0u;
}

// Every allowance has to fit the nibble that counts it.
//
// Five static assertions above guard the bit *layout* -- that the catalogues
// have not outgrown their per-entry bits, that the low-prefix flags do not
// overlap the counters, that the counters fit the word. The one thing the
// counter arithmetic actually depends on was not among them, and it is the
// one the header invites changing: raise an allowance past fifteen and
// bvSchemaFamilyRecordInstance carries out of the nibble into the next
// family's, so the family it belongs to becomes uncapped -- its count wraps
// to zero and never reaches the allowance again -- while its neighbour loses
// budget it was never asked to spend. Both failures are silent.
constexpr bool bvSchemaFamilyAllowancesFit(unsigned family = 0)
{
  return family >= BV_SCHEMA_FAMILY_COUNT ||
         (bvSchemaFamilyAllowance(static_cast<BVSchemaFamily>(family)) <=
              BV_SCHEMA_FAMILY_COUNTER_MASK &&
          bvSchemaFamilyAllowancesFit(family + 1));
}

static_assert(bvSchemaFamilyAllowancesFit(),
              "a schema-family allowance does not fit its counter, so "
              "recording an instance would carry into the next family");

constexpr unsigned bvSchemaFamilyInstances(uint64_t installedSchemas,
                                           BVSchemaFamily family)
{
  return (unsigned)((installedSchemas >>
                     (BV_SCHEMA_FAMILY_COUNTER_FIRST +
                      BV_SCHEMA_FAMILY_COUNTER_BITS *
                          static_cast<unsigned>(family))) &
                    BV_SCHEMA_FAMILY_COUNTER_MASK);
}

// Whether this record may still install one of this family.
constexpr bool bvSchemaFamilyHasInstance(uint64_t installedSchemas,
                                         BVSchemaFamily family)
{
  return bvSchemaFamilyAllowance(family) == 0 ||
         bvSchemaFamilyInstances(installedSchemas, family) <
             bvSchemaFamilyAllowance(family);
}

// `installedSchemas` with one more instance of this family recorded. An
// uncapped family is not counted, so its nibble cannot wrap.
constexpr uint64_t bvSchemaFamilyRecordInstance(uint64_t installedSchemas,
                                                BVSchemaFamily family)
{
  return bvSchemaFamilyAllowance(family) == 0
             ? installedSchemas
             : installedSchemas +
                   (uint64_t{1} << (BV_SCHEMA_FAMILY_COUNTER_FIRST +
                                    BV_SCHEMA_FAMILY_COUNTER_BITS *
                                        static_cast<unsigned>(family)));
}


struct DivSchemaChoice
{
  DivSchema schema = DivSchema::None;
  // log2 of the divisor for Pow2Divisor, or the exponent used by one of the
  // two power-of-two quotient bounds.
  unsigned shift = 0;
  // Set when `schema` is Lemma: which DivLemma or RemLemma fact to install,
  // as an index into the operation's table.
  unsigned lemmaIndex = 0;
  BVSchemaGroup group = BVSchemaGroup::BASE;
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

// Whether one hand-written division or remainder schema holds of these
// values -- the same single-predicate arrangement `mulSchemaHolds` describes,
// for the arms of DivSchema that are not registry rows.
//
// Every arm here is a theorem about the operation on its own. The two that
// name a divisor carry their own guard: `DivisorZero` is vacuous over a
// nonzero divisor and `Pow2Divisor` over a divisor that is not 2^shift. The
// chooser reaches them only where the guard is already true, so asking this
// is the same question it used to ask inline -- and it is now the same
// question the circuit is checked against.
//
// `opKind` is BVDIV or BVMOD; `shift` carries the exponent for the
// parameterised arms and is ignored by the rest. `DivSchema::Lemma` is a
// registry row and belongs to `divLemmaHolds`/`remLemmaHolds`, not here.
DLL_PUBLIC bool divSchemaHolds(Kind opKind, DivSchema schema, unsigned shift,
                               const std::vector<bool>& aBits,
                               const std::vector<bool>& bBits,
                               const std::vector<bool>& tBits);

// The first of the facts above that this candidate contradicts, or None.
// Pure, and called under the same conditions as chooseMulSchema: `tBits` is
// what the candidate holds for the result, already known to disagree with
// what the operands say it should be.
//
// `opKind` is BVDIV or BVMOD. The two share both schemas and differ only in
// what each one concludes.
DLL_PUBLIC DivSchemaChoice chooseDivSchema(
    Kind opKind, const std::vector<bool>& aBits, const std::vector<bool>& bBits,
    const std::vector<bool>& tBits, uint64_t installedSchemas,
    uint32_t enabledGroups = BV_SCHEMA_GROUP_ALL);

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
// means something quite different at either end of the range. Three flags
// therefore compose into this one number, and because they compose it is
// written out here rather than left to be reassembled from three separate
// pieces of documentation:
//
//   allowance(W, op) =
//       rounds == 0            -> 0, meaning never escalate
//       otherwise              -> min(rounds,
//                                     divisor != 0 ? max(1, W / divisor) : rounds,
//                                     op is DIV/MOD && divmodLimit != 0
//                                         ? divmodLimit : rounds)
//
// where `rounds` is bv_term_abstraction_rounds, `divisor` is
// bv_term_abstraction_value_divisor and `divmodLimit` is
// bv_term_abstraction_divmod_value_limit.
//
// The zeros do not all mean the same thing, which is the part worth saying
// out loud. Zero rounds means "never escalate, enumerate without limit" --
// and, separately, that algebraic schemas are not capped either, since they
// are bounded by the same flag. Zero for the other two means "this layer is
// absent", leaving whatever the layers above it decided.
//
// Keeping the layers separate is what lets a benchmark vary value blocks
// without also changing the number of schema rounds.
DLL_PUBLIC unsigned valueLemmaAllowance(const UserDefinedFlags& uf,
                                        unsigned width);

// The operation-specific allowance -- the third line of the composition
// above. DIV/MOD may opt into the independent
// `bv_term_abstraction_divmod_value_limit`; multiplication deliberately does
// not, so a divider experiment cannot silently change a corpus's multipliers.
DLL_PUBLIC unsigned valueLemmaAllowance(const UserDefinedFlags& uf,
                                        unsigned width, Kind opKind);

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
  // Blocking lemmas spent on this one abstraction over its whole life, and
  // algebraic schemas likewise -- counted separately, because a schema is
  // both cheaper and stronger than a blocking lemma and should not bring the
  // escalation forward. These are what the diagnostics report; the two
  // below are what the budgets are spent from.
  unsigned blockedRounds = 0;
  unsigned schemaRounds = 0;
  // The same two, since this query began.
  //
  // bv_term_abstraction_rounds is a ceiling on what one abstraction may
  // spend, and the number it defaults to was calibrated a query at a time.
  // A record's life is one query in the batch pipeline -- ToSATAIG, and the
  // record vector with it, is a local of the call that solves -- but a whole
  // session under the incremental driver, where records are dropped only by
  // a rebuild. Spending the ceiling from the lifetime counts would therefore
  // mean two different things on the two drivers, and the incremental one
  // would give up on an abstraction after thirty-two blocking lemmas spread
  // over thirty-two queries rather than thirty-two within one.
  //
  // So the budgets are spent from these. BVAbstractionRefiner::beginQuery
  // advances a generation, and the first live touch resets them lazily.
  // Nothing a round bought is reset with them: installed schema bits, exact
  // encodings and `defined` are permanent, and a fact each record can receive
  // only once is still received only once, because what bounds that is its
  // installed bit and not the purse.
  unsigned blockedThisQuery = 0;
  unsigned schemasThisQuery = 0;
  // The refiner advances one generation per incremental query and resets the
  // two purses lazily when this record is actually live. Dormant historical
  // records therefore cost no per-query scan.
  uint64_t queryGeneration = 0;
  // Which of the unconditional schemas will not be offered again: the ones
  // already in the solver, and the ones the AIG node budget refused to build,
  // which there is no point offering a second time either.
  uint64_t installedSchemas = 0;
  // Set once the AIG node budget has refused this record's exact encoding.
  //
  // The budget is a memory guard, and a circuit it will not build this round
  // is one it will not build on any later round either -- so without this the
  // refinement offered the same escalation every round for the rest of the
  // session, and every query after the first pinned itself to `unknown` on it.
  // Refused, an inconsistent candidate which has exhausted its bounded value
  // allowance is unknown: enumerating the remaining operand pairs would turn
  // a memory guard into an exponential fallback.
  bool exactRefused = false;
  int exactRefusedAtNodeCount = -1;
  // How many of this operation's low bits are encoded exactly. Zero for an
  // abstraction nothing has pinned exactly yet, the width once `defined` is
  // set, and something in between for the two ways a record gets there
  // gradually: an exact low prefix, and a piece-at-a-time escalation (see
  // bv_term_abstraction_inc_bitblast).
  //
  // It used to say it was only the escalation's, and only ever zero or the
  // width -- which the low-prefix schemas broke by writing three, and which
  // the comparison, if-then-else and whole-addition definitions broke by
  // setting `defined` and leaving this at zero. reportRecords publishes it,
  // so a record could be `defined` and report `exact-bits=0`, or report
  // `partial` on a three-bit prefix with no piece ever blasted. Every path
  // that pins bits exactly writes it now, and the field says what it counts.
  unsigned blastedBits = 0;
  // Times value-pair refinement reached its allowance and installed an exact
  // circuit. Normally zero or one; incremental multiplication bit-blasting
  // may install more than one increasingly wide piece.
  unsigned exactEscalations = 0;
  // Cost paid by those exact escalations. submittedClauses() is the common,
  // monotone backend boundary, so this remains comparable when a backend's
  // own clause count is unavailable or preprocessing has removed clauses.
  // The timer covers circuit construction, CNF conversion and submission;
  // it deliberately excludes the next SAT search.
  uint64_t exactClauses = 0;
  uint64_t exactVariables = 0;
  uint64_t exactMicroseconds = 0;
  // The bits of -operand[i], minted on first use by a schema that needs the
  // semantic operand and kept so later schemas do not pay for the same
  // negation circuit again.
  std::vector<unsigned> negatedOperand[2];
  // What the blast knew about each operand's bits before the abstraction
  // replaced them with proxy inputs: -1 for a live node, 0 or 1 for a
  // constant. Carried so that an escalation can rebuild the operation over
  // the same constants the query would have blasted it with, rather than
  // over 2W free inputs; see BitBlaster::RawBVTermAbstraction for what that
  // costs when it is thrown away. Empty means nothing is known.
  std::vector<signed char> operandKnownBits[2];
};

// An explicit sparse view of the records one query semantically owns. Empty
// selected lists mean no records, while allRecords is the separate batch-mode
// spelling of every record; this avoids the old empty-means-all ambiguity.
// `complete` is false only when dependency closure named an ID for which no
// record exists, a state which must yield Unknown rather than certify a model.
struct BVAbstractionScope
{
  bool allRecords = true;
  bool complete = true;
  std::vector<size_t> equalityIndices;
  std::vector<size_t> termIndices;

  static BVAbstractionScope all() { return BVAbstractionScope(); }

  static BVAbstractionScope selected()
  {
    BVAbstractionScope scope;
    scope.allRecords = false;
    return scope;
  }
};

class DLL_PUBLIC BVAbstractionRefiner
{
  STPMgr* bm;

  // One encoder for the session. Every schema lemma and every exact
  // escalation goes through it, and it owns the scratch simplifier state
  // those blasts need, so a refinement round does not rebuild that per
  // lemma.
  BVExactEncoder exact_;

  std::vector<BVEQAbstraction> eqs_;
  std::vector<BVTermAbstraction> terms_;

  struct RecordLocation
  {
    bool equality;
    size_t index;
  };
  std::map<BVAbstractionId, RecordLocation> recordOfId_;
  size_t indexedRecords_ = 0;
  uint64_t queryGeneration_ = 1;

  // Monotone across the session, including across a clear(): a driver
  // compares it either side of a round to learn whether that round found
  // anything, and a counter that went backwards would read as no progress.
  uint64_t refinements_ = 0;

  unsigned refineEqualities(SATSolver& solver,
                            const ToSATBase::ASTNodeToSATVar& nodeToSATVar,
                            const std::vector<size_t>* selected);
  AbstractionRefinementResult
  refineTerms(SATSolver& solver,
              const ToSATBase::ASTNodeToSATVar& nodeToSATVar,
              const std::vector<size_t>* selected);
  void rebuildRecordIndex();
  void prepareTermForQuery(BVTermAbstraction& term);

public:
  explicit BVAbstractionRefiner(STPMgr* bm_) : bm(bm_), exact_(bm_) {}

  bool empty() const { return eqs_.empty() && terms_.empty(); }
  bool hasEqualities() const { return !eqs_.empty(); }
  bool hasTerms() const { return !terms_.empty(); }

  // The records, for whoever mints them. Everything a refinement round
  // learns is written back into them, so an owner that discards its SAT
  // solver or its bit-blast has to discard these too.
  const std::vector<BVEQAbstraction>& equalities() const { return eqs_; }
  const std::vector<BVTermAbstraction>& terms() const { return terms_; }

  void appendEquality(BVEQAbstraction record);
  void appendTerm(BVTermAbstraction record);

  // Fixed-point closure from direct root producers to every child producer
  // their defining records consume. The resulting indices are creation-order
  // sorted so refinement scheduling stays deterministic.
  BVAbstractionScope
  dependencyClosure(const std::vector<BVAbstractionId>& seeds);

  void clear()
  {
    eqs_.clear();
    terms_.clear();
    recordOfId_.clear();
    indexedRecords_ = 0;
  }

  // A new query begins over the same records.
  //
  // The blocking allowance and the schema ceiling are spent per record, and
  // the defaults behind them were calibrated a query at a time. A record's
  // life is one query in the batch pipeline, so there the two units coincide
  // and nothing has to call this; under the incremental driver a record
  // outlives the query that minted it, and without this the same flag would
  // mean "per session" there and "per query" here.
  //
  // The generation change is O(1); a purse is reset only when its record is
  // selected by this query's sparse scope. What a round bought is permanent
  // and stays -- installed schema bits, exact encodings, `defined` -- so this
  // cannot buy a record a second copy of a fact it already has.
  void beginQuery()
  {
    ++queryGeneration_;
    if (queryGeneration_ == 0)
    {
      queryGeneration_ = 1;
      for (BVTermAbstraction& term : terms_)
        term.queryGeneration = 0;
    }
  }

  uint64_t refinements() const { return refinements_; }

  // A stable, one-line snapshot for every term record. Quick-statistics
  // consumers use this instead of reconstructing records from free-form
  // schema diagnostics; in particular it exposes the blocking distribution
  // which an aggregate total hides.
  void reportRecords(std::ostream& out) const;

  // Keep a simplifying backend from eliminating anything a future lemma
  // will be written over.
  void freezeVariables(SATSolver& solver,
                       const ToSATBase::ASTNodeToSATVar& nodeToSATVar) const;

  // Check every record against the current SAT model and pin the ones the
  // model contradicts. Faithful is the only result which permits the
  // candidate to be handed on; Refined requires another SAT call, and Unknown
  // means a mandatory exact encoding was refused by the AIG budget.
  //
  // With no scope argument the batch pipeline checks every record, since its
  // records live exactly as long as its one query. The incremental driver
  // passes a dependency-closed sparse scope; selected-empty is a genuine
  // fixed point over no records.
  //
  // The incremental driver retains records until the encoding epoch ends, so
  // a pop leaves behind records for operations no live assertion mentions.
  // Those records are logically retired by omitting them from the sparse
  // dependency closure; a later activation of a cached owner can select them
  // again without reconstructing their refinement state.
  //
  // Passing over such a record is sound. What still mentions it is the
  // definitional encoding of the cone it was minted in, which no assumption
  // asserts and which is satisfiable whatever the record holds, and the
  // theorems earlier rounds installed over it, which are likewise
  // satisfiable. Nothing the current query asserts reaches it, so no value it
  // takes can change the answer. The safe direction is still to check too
  // much: missing owner metadata selects all records, while a dependency ID
  // with no retained record makes the result Unknown.
  AbstractionRefinementResult
  refine(SATSolver& solver,
         const ToSATBase::ASTNodeToSATVar& nodeToSATVar);
  AbstractionRefinementResult
  refine(SATSolver& solver, const ToSATBase::ASTNodeToSATVar& nodeToSATVar,
         const BVAbstractionScope& scope);
};
}

#endif
