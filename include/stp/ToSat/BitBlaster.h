/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
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

#ifndef BITBLASTNEW_H
#define BITBLASTNEW_H

#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/constantBitP/MultiplicationStats.h"
#include "stp/ToSat/BBNodeManagerAIG.h"
#include "stp/ToSat/BVAbstractionTypes.h"
#include "stp/Util/DagWalk.h"
#include <cassert>
#include <cmath>
#include <list>
#include <map>
#include <string>

namespace simplifier
{
namespace constantBitP
{
class ConstantBitPropagation;
class FixedBits;
}
}

namespace stp
{

using std::list;
using simplifier::constantBitP::MultiplicationStats;

class Simplifier;
class ASTNode;

using ASTVec = vector<ASTNode>;

// The support set a blast accumulates, insertion-ordered rather than a bare
// std::unordered_set. Its iteration order reaches the emitted formula in two
// places -- the support conjunction under --conjoin-to-top, and the
// combinational-output order BVExactEncoder gives the circuit it splices into
// a live solver -- and an unordered_set's order is a property of the standard
// library's bucket policy and of std::hash, not of the query. So the CNF
// depended on which library STP was built against. Insertion order depends on
// the blast alone.
//
// The set is small (it holds side conditions, not gates), so the vector is
// the cheap part; the hash set is only here to keep insert() a set operation.
//
// At namespace scope rather than inside the blaster because BBExactBinaryOp
// takes one and its callers are outside.
template <class BBNode> class BBNodeOrderedSet
{
  std::vector<BBNode> order_;
  std::unordered_set<BBNode> seen_;

public:
  void insert(const BBNode& n)
  {
    if (seen_.insert(n).second)
      order_.push_back(n);
  }
  size_t size() const { return order_.size(); }
  bool empty() const { return order_.empty(); }
  typename std::vector<BBNode>::const_iterator begin() const
  {
    return order_.begin();
  }
  typename std::vector<BBNode>::const_iterator end() const
  {
    return order_.end();
  }
};

enum class DivLemma;
enum class RemLemma;
enum class MulLemma;
enum class AddLemma;

// Templated over the node representation and the manager that mints them.
// One instantiation exists -- BitBlasterAIG, at the bottom of this file --
// and the parameters are here so that a second can arrive without the 6900
// lines of blasting logic learning anything about it. Nothing in this class
// may name a backend's own types: BBNodeAIG appears nowhere in the class
// body, only in the alias under it.
template <class BBNode, class BBNodeManagerT> class BitBlaster
{
  using BBNodeVec = std::vector<BBNode>;
  using BBNodeSet = BBNodeOrderedSet<BBNode>;

  BBNode BBTrue, BBFalse;

  // Memo table for bit blasted terms.  If a node has already been
  // bitblasted, it is mapped to a vector of Boolean formulas for
  // the
  std::unordered_map<ASTNode, BBNodeVec, ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual> BBTermMemo;

  // Memo table for bit blasted formulas.  If a node has already
  // been bitblasted, it is mapped to a node representing the
  // bitblasted equivalent
  std::unordered_map<ASTNode, BBNode, ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual> BBFormMemo;

  // Get vector of Boolean formulas for sum of two
  // vectors of Boolean formulas
  void BBPlus2(BBNodeVec& sum, const BBNodeVec& y, BBNode cin);

  // Increment
  BBNodeVec BBInc(const BBNodeVec& x);

  // Add one bit to a vector of bits.
  BBNodeVec BBAddOneBit(const BBNodeVec& x, BBNode cin);

  // Bitwise complement
  BBNodeVec BBNeg(const BBNodeVec& x);
  BBNodeVec BBAnd(const BBNodeVec& x, const BBNodeVec& y);
  BBNodeVec BBOr(const BBNodeVec& x, const BBNodeVec& y);
  BBNodeVec BBXor(const BBNodeVec& x, const BBNodeVec& y);
  BBNodeVec BBAdd(const BBNodeVec& x, const BBNodeVec& y);

  // Unary minus
  BBNodeVec BBUminus(const BBNodeVec& x);

  // Multiply.
  BBNodeVec BBMult(const BBNodeVec& x, const BBNodeVec& y,
                        BBNodeSet& support, const ASTNode& n);
  void mult_allPairs(const BBNodeVec& x, const BBNodeVec& y,
                     BBNodeSet& support, vector<list<BBNode>>& products);
  void mult_Booth(const BBNodeVec& x_i, const BBNodeVec& y_i,
                  BBNodeSet& support, const stp::ASTNode& xN,
                  const stp::ASTNode& yN, vector<list<BBNode>>& products,
                  const ASTNode& n);
  void mult_Booth_radix4(const BBNodeVec& x, const BBNodeVec& y,
                         vector<list<BBNode>>& products, const ASTNode& n);
  bool mult_Booth_constant(const BBNodeVec& x, const BBNodeVec& y,
                           BBNodeSet& support, vector<list<BBNode>>& products,
                           const ASTNode& n);
  BBNodeVec mult_normal(const BBNodeVec& x, const BBNodeVec& y,
                             BBNodeSet& support, const ASTNode& n);

  BBNodeVec batcher(const BBNodeVec& in);
  BBNodeVec mergeSorted(const BBNodeVec& in1,
                             const BBNodeVec& in2);
  BBNodeVec compareOddEven(const BBNodeVec& in);

  void setColumnsToZero(vector<list<BBNode>>& products, BBNodeSet& support,
                        const ASTNode& n);

  void sortingNetworkAdd(BBNodeSet& support, list<BBNode>& current,
                         BBNodeVec& currentSorted,
                         BBNodeVec& priorSorted);

  BBNodeVec v6(vector<list<BBNode>>& products, BBNodeSet& support,
                    const ASTNode& n);
  BBNodeVec v7(vector<list<BBNode>>& products, BBNodeSet& support,
                    const ASTNode& n);
  BBNodeVec v8(vector<list<BBNode>>& products, BBNodeSet& support,
                    const ASTNode& n);
  BBNodeVec v9(vector<list<BBNode>>& products, BBNodeSet& support,
                    const ASTNode& n);
  BBNodeVec v13(vector<list<BBNode>>& products, BBNodeSet& support,
                     const ASTNode& n);

  BBNodeVec multWithBounds(const ASTNode& n,
                                vector<list<BBNode>>& products,
                                BBNodeSet& toConjoinToTop);
  bool statsFound(const ASTNode& n);

  void mult_BubbleSorterWithBounds(BBNodeSet& support,
                                   list<BBNode>& currentColumn,
                                   BBNodeVec& currentSorted,
                                   BBNodeVec& priorSorted,
                                   const int minTrue = 0,
                                   const int maxTrue = ((unsigned)~0) >> 1);

  void buildAdditionNetworkResult(list<BBNode>& from, list<BBNode>& to,
                                  BBNodeSet& support, const bool top,
                                  const bool empty);
  BBNodeVec buildAdditionNetworkResult(vector<list<BBNode>>& products,
                                            BBNodeSet& support,
                                            const ASTNode& n);

  BBNodeVec BBAndBit(const BBNodeVec& y, BBNode b);

  MultiplicationStats* getMS(const ASTNode& n, int& highestZero);

  /////////// The end of the multiplication stuff..

  // Returns BBNodeVec for result - y.  This destroys "result".
  void BBSub(BBNodeVec& result, const BBNodeVec& y,
             BBNodeSet& support);

  // build ITE's (ITE cond then[i] else[i]) for each i.
  BBNodeVec BBITE(const BBNode& cond, const BBNodeVec& thn,
                       const BBNodeVec& els);

  // Build a vector of zeros.
  BBNodeVec BBfill(unsigned int width, BBNode fillval);

  // build an EQ formula
  BBNode BBEQ(const BBNodeVec& left, const BBNodeVec& right);

  // This implements a variant of binary long division.
  // q and r are "out" parameters.  rwidth puts a bound on the
  // recursion depth.   Unsigned only, for now.

  void BBDivMod(const BBNodeVec& y, const BBNodeVec& x,
                BBNodeVec& q, BBNodeVec& r, unsigned int rwidth,
                BBNodeSet& support);

  // Return formula for majority function of three formulas.
  BBNode Majority(const BBNode& a, const BBNode& b, const BBNode& c);

  // Internal bit blasting routines.
  BBNode BBBVLE(const BBNodeVec& x, const BBNodeVec& y,
                bool is_signed, bool is_bvlt = false);
  BBNode BBBVLE_variant1(const BBNodeVec& x, const BBNodeVec& y,
                         bool is_signed, bool is_bvlt = false);
  BBNode BBBVLE_variant2(const BBNodeVec& x, const BBNodeVec& y,
                         bool is_signed, bool is_bvlt = false);

  // Return bit-blasted form for BVLE, BVGE, BVGT, SBLE, etc.
  BBNode BBcompare(const ASTNode& form, BBNodeSet& support);

  // bit blast a floating-point ordering comparison (FP_GT, FP_LT, FP_GEQ,
  // FP_LEQ) over packed operands
  BBNode BBcompareFP(const ASTNode& form, BBNodeSet& support);

  // bit blast a floating-point equality (FP_EQ, FP_SMT_EQ) over packed
  // operands
  BBNode BBeqFP(const ASTNode& form, BBNodeSet& support);

  // bit blast a floating-point classification predicate (FP_ISNORMAL,
  // FP_ISSUBNORMAL, FP_ISZERO, FP_ISINFINITE, FP_ISNAN, FP_ISNEGATIVE,
  // FP_ISPOSITIVE) over a packed operand
  BBNode BBclassifyFP(const ASTNode& form, BBNodeSet& support);

  // Field tests on a packed IEEE-754 operand, shared by the comparison and
  // equality encodings. `sb` is the significand width, `w` the total width.
  BBNode BBfpIsNaN(const BBNodeVec& p, unsigned sb, unsigned w);
  BBNode BBfpIsZero(const BBNodeVec& p, unsigned w);

  struct FpNativeBounds
  {
    bool hasLower = false;
    bool hasUpper = false;
    long double lower = 0.0L;
    long double upper = 0.0L;
    bool lowerExact = false;
    bool upperExact = false;
    std::string lowerBits;
    std::string upperBits;
  };

  struct FpNativeInterval
  {
    bool known = false;
    bool exact = false;
    long double lower = 0.0L;
    long double upper = 0.0L;
    std::string lowerBits;
    std::string upperBits;
  };

  void collectFpNativeDomainFacts(const ASTNode& root);
  void collectFpNativeDomainBounds(const ASTNode& n);
  bool fpNativeBoundPredicate(const ASTNode& n, ASTNode& symbol,
                              ASTNode& constant, long double& value,
                              bool& lowerBound) const;
  bool fpNativeMagnitudeZeroPredicate(const ASTNode& n,
                                      ASTNode& term) const;
  bool fpNativeConstantZeroMagnitude(const ASTNode& n) const;
  bool fpNativeConstantValue(const ASTNode& n, long double& out) const;
  bool fpNativeConstantBits(const ASTNode& n, std::string& out) const;
  bool fpNativeMaxFiniteValue(const SourceSort& sort, long double& out) const;
  FpNativeInterval fpNativeRoundedRange(const SourceSort& sort,
                                        long double lower,
                                        long double upper) const;
  FpNativeInterval fpNativeInterval(const ASTNode& n);
  FpNativeInterval fpNativeIntervalUncached(const ASTNode& n);
  FpNativeInterval fpNativeExactRoundedRange(
      const SourceSort& sort, Kind kind, const ASTNode& roundingMode,
      const FpNativeInterval& a, const FpNativeInterval& b) const;
  bool fpNativeKnownFinite(const ASTNode& n);
  bool fpNativeKnownZeroMagnitude(const ASTNode& n);
  bool fpNativeKnownFiniteNonnegative(const ASTNode& n);
  bool fpNativeKnownFiniteNonpositive(const ASTNode& n);

  // bit blast fp.mul / fp.add / float-to-float to_fp over packed operands:
  // hand-written unpack/compute/round/pack circuits, no SymFPU
  // (--bb.fp-native-arith)
  BBNodeVec BBfpMul(const ASTNode& term, BBNodeSet& support);
  BBNodeVec BBfpAdd(const ASTNode& term, BBNodeSet& support);
  BBNode BBfpAddIsZero(const ASTNode& term, BBNodeSet& support);
  BBNodeVec BBfpToFp(const ASTNode& term, BBNodeSet& support);

  // Kept separate from the native-domain profiling counters so the stacked
  // add-isZero optimization retains its standalone statistics contract.
  size_t fpNativeAddIsZeroFusions = 0;

  // A packed operand split for the native arithmetic circuits: fields,
  // classification, and the significand with its hidden bit made explicit
  // but NOT normalised (0 for subnormals) -- normalisation is deferred to
  // the operation's result, so consuming a packed operand is only wiring.
  struct FpOperand
  {
    BBNode sign, isZero, isInf, isNaN;
    BBNodeVec msig; // sb bits, hidden bit at msig[sb-1]
    BBNodeVec eUnb; // E bits, signed, unbiased (subnormals read exp as 1)
  };
  FpOperand BBfpUnpack(const BBNodeVec& p, unsigned sb, unsigned w,
                       unsigned E, BBNodeSet& support,
                       bool knownFinite = false,
                       bool knownZeroMagnitude = false);

  // The shared tail of the native arithmetic circuits: denormalise into
  // the subnormal range when the biased exponent be is <= 0, round rsig
  // (with its guard and sticky) per the one-hot mode rm, saturate
  // overflow per mode, and pack the finite result. NaN/infinity/zero
  // specials are the caller's to mux over the top.
  BBNodeVec BBfpRoundPack(const BBNodeVec& rm, const BBNode& sgn,
                          const BBNodeVec& rsig, const BBNode& guard,
                          const BBNode& sticky, const BBNodeVec& be,
                          unsigned sb, unsigned eb, BBNodeSet& support,
                          bool resultKnownFinite = false);

  // Width of the internal signed exponent for format (eb, sb): eb+2
  // widened until the subnormal shift distance (up to bias + 2sb + 3,
  // counting fp.add's alignment headroom) cannot overflow it.
  static unsigned BBfpExpWidth(unsigned eb, unsigned sb);

  // Helpers for the native floating-point arithmetic circuits.
  // Count of leading zeros of v (from the MSB down) as an unsigned binary
  // vector of `countWidth` bits; an all-zero v counts v.size().
  BBNodeVec BBfpCLZ(const BBNodeVec& v, unsigned countWidth);
  // Right shift v by `amt`, ORing every shifted-out bit into `sticky`.
  BBNodeVec BBfpShiftRightSticky(const BBNodeVec& v, const BBNodeVec& amt,
                                 BBNode& sticky);
  // v + inc (a single carry-in bit), one bit wider than v.
  BBNodeVec BBfpIncrement(const BBNodeVec& v, const BBNode& inc);

  // Return bit-blasted form for the overflow predicates BVUADDO, BVSADDO,
  // BVUMULO, BVSMULO, BVUSUBO, BVSSUBO.
  BBNode BBOverflow(const ASTNode& form, BBNodeSet& support);

  void BBLShift(BBNodeVec& x, unsigned int shift);
  void BBRShift(BBNodeVec& x, unsigned int shift);

  // Checks for constants.
  void commonCheck(const ASTNode& n);
  void check(const BBNode& x, const ASTNode& n);
  void check(const BBNodeVec& x, const ASTNode& n);

  bool update(const ASTNode& n, const int i,
              simplifier::constantBitP::FixedBits* b, BBNode& bb,
              BBNodeSet& support);
  void updateTerm(const ASTNode& n, BBNodeVec& bb, BBNodeSet& support);
  void updateForm(const ASTNode& n, BBNode& bb, BBNodeSet& support);

  const BBNode BBForm(const ASTNode& form, BBNodeSet& support);
  const BBNode BBForm(const ASTNode& form, BBNodeSet& support,
                      bool knownMissing);
  const BBNodeVec BBTerm(const ASTNode& term, BBNodeSet& support,
                         bool knownMissing);

  // BBForm and BBTerm both blast a node's operands by calling themselves, so
  // input nested deeply enough takes the stack with it. Shallow inputs keep
  // the ordinary recursive path: starting an extra walk at their root costs
  // more than the stack it saves. Once the shared formula/term recursion
  // budget is exhausted, primeMemos fills both memos below that point and the
  // bounded recursive prefix unwinds normally. One walk covers both memos
  // because the two functions reach each other. See DeepDag_Test.cpp.
  void primeMemos(const ASTNode& n, BBNodeSet& support);
  static constexpr size_t unprimedDepthLimit = 512;
  size_t unprimedDepth = 0;

  // How many primeMemos walks are on the stack. Normally 0 or 1, but a walk's
  // visit can reach a node built after the walk ran (simplify_during_bb
  // replacing a term), and blasting that node primes below it first -- a
  // nested session, so a count rather than a flag.
  size_t priming = 0;

  // Debug-only: the deliberately recursive prefix plus the small amount of
  // recursion used while processing nodes created during priming. Empty and
  // free in a build with NDEBUG. The suffix itself must still answer from one
  // of the two memos rather than nesting with the input.
  PrimeAudit memoAudit{"BitBlaster", unprimedDepthLimit + 32};

  bool isConstant(const BBNodeVec& v);
  ASTNode getConstant(const BBNodeVec& v, const ASTNode& n);

  // Nodes in this set can be replaced by their constant values, without being
  // conjoined to the top..
  ASTNodeSet fixedFromBottom;
  ASTNodeSet fpNativeFiniteTerms;
  ASTNodeSet fpNativeZeroMagnitudeFacts;
  ASTNodeSet fpNativeZeroMagnitudeTerms;
  // Negative lookup cache only: membership means "not currently proven
  // zero", not that the term is known nonzero.
  ASTNodeSet fpNativeUnknownZeroMagnitudeTerms;
  ASTNodeSet fpNativeFiniteNonnegativeTerms;
  // As above, this is a proof-failure cache, not a proof that a term is
  // negative or non-finite.
  ASTNodeSet fpNativeUnknownFiniteNonnegativeTerms;
  ASTNodeSet fpNativeFiniteNonpositiveTerms;
  // As above, this records only failure to prove semantic nonpositivity.
  ASTNodeSet fpNativeUnknownFiniteNonpositiveTerms;
  std::unordered_map<ASTNode, FpNativeBounds, ASTNode::ASTNodeHasher,
                     ASTNode::ASTNodeEqual>
      fpNativeBounds;
  std::unordered_map<ASTNode, FpNativeInterval, ASTNode::ASTNodeHasher,
                     ASTNode::ASTNodeEqual>
      fpNativeIntervals;
  std::unordered_map<ASTNode, size_t, ASTNode::ASTNodeHasher,
                     ASTNode::ASTNodeEqual>
      fpNativeParentUses;
  ASTNode fpNativeDomainRoot;
  size_t fpNativeFiniteCmpOperands = 0;
  size_t fpNativeFiniteEqOperands = 0;
  size_t fpNativeFiniteClassifications = 0;
  size_t fpNativeFiniteArithOperands = 0;
  size_t fpNativeFiniteRoundPacks = 0;
  size_t fpNativeZeroCmpOperands = 0;
  size_t fpNativeZeroEqOperands = 0;
  size_t fpNativeZeroClassifications = 0;
  size_t fpNativeIsZeroPredicates = 0;
  size_t fpNativeIsZeroAddPredicates = 0;
  size_t fpNativeIsZeroAddFusedPredicates = 0;
  size_t fpNativeIsZeroAddExclusiveResults = 0;
  size_t fpNativeIsZeroAddMemoizedResults = 0;
  size_t fpNativeIsZeroAddKnownZeroResults = 0;
  size_t fpNativeIsZeroAddBothFiniteOperands = 0;
  size_t fpNativeIsZeroAddKnownSameSignOperands = 0;
  size_t fpNativeIsZeroAddKnownOppositeSignOperands = 0;
  size_t fpNativeIsZeroAddOneKnownSignOperand = 0;
  size_t fpNativeZeroAddFastPaths = 0;
  size_t fpNativeZeroMulFastPaths = 0;
  size_t fpNativeZeroToFpFastPaths = 0;
  size_t fpNativeKnownPositiveAddPaths = 0;
  size_t fpNativeKnownNegativeAddPaths = 0;
  size_t fpNativeKnownPositiveMulPaths = 0;
  size_t fpNativeKnownNegativeMulPaths = 0;
  UserDefinedFlags* uf;
  const bool allowAbstraction_ = true;
  NodeFactory* ASTNF;
  Simplifier* simp;
  BBNodeManagerT* nf;

  ASTNodeSet booth_recoded; // Nodes that have been recoded.

public:
  // The two result shapes are deliberately different types. An entry in one
  // of these registries is proof that the returned AIG input was minted by an
  // abstraction, and carries the producer identity with it; symbolToBBNode is
  // still the general symbol/proxy compatibility registry and is not such
  // proof.
  struct BooleanAbstractionResult
  {
    BVAbstractionId producer;
    BBNode bit;
  };

  struct BitVectorAbstractionResult
  {
    BVAbstractionId producer;
    BBNodeVec bits;
  };

  struct RawBVEQAbstraction
  {
    BVAbstractionId id;
    std::vector<BVAbstractionId> dependencies;
    ASTNode eqNode;
    BBNode abstractionCI;
    ASTNode leftSymbol;
    ASTNode rightSymbol;
  };

private:
  std::vector<RawBVEQAbstraction> abstractedEQs_;

public:
  const std::vector<RawBVEQAbstraction>& abstractedEQs() const
  {
    return abstractedEQs_;
  }

  struct RawBVTermAbstraction
  {
    BVAbstractionId id;
    std::vector<BVAbstractionId> dependencies;
    ASTNode termNode;
    Kind opKind;
    ASTNode operands[3];
    unsigned numOperands;
    unsigned width;
    bool operandNegated[3] = {false, false, false};
    int condCISymbolIndex = -1;
    // The result inputs belonging to this record. Canonical reuse normally
    // prevents duplicate records for one term, but ownership here keeps the
    // lowering sound if another producer or a future memo boundary creates
    // them: symbolToBBNode can identify only the latest registered vector.
    std::vector<int> resultCISymbolIndices;
    // What the blast already knew about each operand's bits: -1 where the bit
    // is a live circuit node, 0 or 1 where it had folded to a constant.
    //
    // Kept because the abstraction throws it away and the exact escalation
    // needs it back. An operand whose vector holds any constant bit fails
    // allBBNodesAreCIs, so ensureProxyCIs replaces the whole vector with fresh
    // proxy inputs -- correct, since a refinement clause has to name solver
    // variables, and each proxy is pinned to its bit by a side constraint. But
    // BVExactEncoder then rebuilds the operation over free inputs, and every
    // constant shortcut in the multiplier reads the bit vector rather than the
    // AST, so none of them fires. A 64-bit multiply against a literal of
    // popcount 8 built 64 adder rows instead of 8: 33,968 clauses where the
    // unabstracted blast of the whole query was 12,380.
    //
    // Empty means nothing is known, which is what an all-symbolic operand and
    // every family that does not escalate leave behind.
    std::vector<signed char> operandKnownBits[2];
  };

private:
  std::vector<RawBVTermAbstraction> abstractedTerms_;
  // The Boolean each abstracted equality and comparison was replaced by, so
  // that a second occurrence of the same predicate reuses it.
  //
  // The term families get this from symbolToBBNode, which the node manager
  // owns and which outlives a piece; a predicate is one Boolean rather than a
  // vector and has no place there, so it has its own map. It is kept for the
  // same reason and the reason is the incremental driver: BBForm clears its
  // memo on every new root, so two conjuncts sharing a predicate ask for it
  // independently, and minting a second Boolean for the second ask leaves two
  // records over two inputs that are free to disagree. A predicate has one
  // truth value wherever it occurs.
  //
  // Not cleared by ClearAllTables, which is deliberate and is what the raw
  // record vectors beside it do: the abstraction state outlives the memos and
  // is dropped only when the blaster is.
  std::unordered_map<ASTNode, BooleanAbstractionResult,
                     ASTNode::ASTNodeHasher,
                     ASTNode::ASTNodeEqual>
      abstractedFormulas_;
  // Nodes whose blasted vector IS an abstraction's own result inputs.
  //
  // Constant-bit propagation must not rewrite one of these. The record was
  // filed against those inputs and resolves them through the registry, while
  // updateTerm rewrites the term MEMO -- so a bit it replaced with a constant
  // would leave every parent that reads the term using a bit the record does
  // not name, and the refinement pinning an input nothing reads.
  //
  // Nothing is lost by declining. Refinement pins the abstraction to the
  // operands underneath it, which is a stronger statement than any single bit
  // constant-bit propagation could fix, and the operands keep their own
  // propagation either way.
  std::unordered_map<ASTNode, BitVectorAbstractionResult,
                     ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual>
      abstractedResults_;

  // Provenance is attached to AIG inputs because those are what survive all
  // of the lowering's generated ASTs, memo aliases and proxy boundaries. An
  // abstraction result input names exactly its producer. A proxy input names
  // the producers reachable in the AIG bit it aliases. Internal-node results
  // are memoised after an iterative walk; CI provenance never changes after
  // that input is exposed to a parent.
  uint64_t nextAbstractionId_ = 1;
  // Both are indexed by AIG node id, which is dense and never reused within a
  // manager, so a vector beats a hash map: the second is walked once per
  // abstracted bit, and this removes a hash from every node of every visit.
  // An empty entry means "nothing recorded", which is the same answer the
  // maps gave by not finding the key.
  std::vector<std::vector<BVAbstractionId>> ciAbstractionSources_;
  std::vector<std::vector<BVAbstractionId>> aigAbstractionSourcesMemo_;
  // "this id's union has been computed", which an empty entry cannot say on
  // its own -- and a node whose cone holds no abstraction has an empty union,
  // which is the common case because abstraction is off by default. Keeping
  // this separate from the memo is what stops those cones being re-walked on
  // every visit. It must live here rather than in the walk: the walk recurses
  // into itself for the fanins, so a local marker is void at each descent.
  std::vector<bool> aigAbstractionSourcesComputed_;

  // Grow-on-demand accessors for the two above; `at` returns the empty vector
  // for an id past the end rather than resizing, so a read never allocates.
  static const std::vector<BVAbstractionId>& noSources();
  static const std::vector<BVAbstractionId>&
  sourcesAt(const std::vector<std::vector<BVAbstractionId>>& table, unsigned id)
  {
    return id < table.size() ? table[id] : noSources();
  }
  static void setSourcesAt(std::vector<std::vector<BVAbstractionId>>& table,
                           unsigned id, std::vector<BVAbstractionId> sources)
  {
    if (id >= table.size())
      table.resize(id + 1);
    table[id] = std::move(sources);
  }
  bool aigSourcesComputed(unsigned id) const
  {
    return id < aigAbstractionSourcesComputed_.size() &&
           aigAbstractionSourcesComputed_[id];
  }
  void markAigSourcesComputed(unsigned id)
  {
    if (id >= aigAbstractionSourcesComputed_.size())
      aigAbstractionSourcesComputed_.resize(id + 1, false);
    aigAbstractionSourcesComputed_[id] = true;
  }

  BVAbstractionId newAbstractionId();
  void tagAbstractionSources(const BBNode& ci,
                             const std::vector<BVAbstractionId>& sources);
  BBNodeVec ensureProxyCIs(const ASTNode& node, const BBNodeVec& bits);
  bool reuseRegisteredTerm(const ASTNode& term, unsigned width,
                           BBNodeVec& reused) const;
  // Operations already counted as abstraction candidates.
  //
  // bv_candidates says it counts operations reaching the bit-blaster at or
  // above the width floor, and exists so that a flag which reached nothing
  // eligible can be told from a flag that is broken. It was counted at the top
  // of each abstraction arm, which is a bit-blaster VISIT: the incremental
  // driver clears its term memo on every new root, so one operation is
  // re-entered once per check-sat while bv_abstracted -- correctly -- counts
  // the one record. Ten solves over one multiplication read mult=10->1, which
  // says the abstraction took a tenth of what it could have.
  //
  // Counted once per node, so the ratio means what it is documented to mean
  // and abstracted can never exceed candidates. In the batch pipeline the
  // blaster lives for one query with one root, so nothing there moves.
  std::unordered_set<ASTNode, ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual>
      countedCandidates_;
  std::vector<BBNode> sideConstraints_;

public:
  const std::vector<RawBVTermAbstraction>& abstractedTerms() const
  {
    return abstractedTerms_;
  }
  const std::vector<BBNode>& sideConstraints() const
  {
    return sideConstraints_;
  }

  // Direct producer IDs reachable from an AIG result. Walking the committed
  // root gives assertion ownership; walking the operands before a new result
  // is tagged gives that producer's parent-to-child dependencies.
  std::vector<BVAbstractionId> abstractionSourcesOf(const BBNode& root);
  std::vector<BVAbstractionId> abstractionSourcesOf(const BBNodeVec& bits);
  BitBlaster& operator=(const BitBlaster& other) = delete;
  BitBlaster(const BitBlaster& other) = delete;
  ~BitBlaster() { ClearAllTables(); }

  simplifier::constantBitP::ConstantBitPropagation* cb;

  // Bit blast a bitvector term.  The term must have a kind for a
  // bitvector term.  Result is a ref to a vector of formula nodes
  // representing the boolean formula.
  const BBNodeVec BBTerm(const ASTNode& term, BBNodeSet& support);

  // The exact circuit for one of the three operations --bv-term-abstraction
  // replaces by free result bits, over operand bits the caller supplies
  // rather than the ones under `term`.
  //
  // This is what BBTerm builds when the abstraction declines a node, and it
  // is the same code: the refiner reaches it to encode an operation it has
  // given up on abstracting, and "the answer it would have given had the
  // term never been abstracted" is only true of an encoding that is the
  // same one. Two copies of a divider that agree today are two copies that
  // can stop agreeing.
  //
  // `term` is the operation's own node; `x` and `y` stand in for its
  // operands. What the node supplies is the kind, the width and the operand
  // order -- not the operand *values*. Constant detection and Booth recoding
  // read the bit vectors: mult_normal skips a false multiplier bit, Booth
  // classifies through convert(), and Aig_And folds a constant argument
  // structurally, all of them off `x` and `y`. So a caller that hands over
  // free inputs where the query's own blast had constants gets the fully
  // symbolic circuit however constant `term`'s children look, which is why
  // BVExactEncoder::encode carries the known bits separately.
  //
  // Anything the circuit needs conjoined to the top is added to `support`,
  // as everywhere else here.
  BBNodeVec BBExactBinaryOp(const ASTNode& term, const BBNodeVec& x,
                            const BBNodeVec& y, BBNodeSet& support);

  // The circuit for one algebraic fact about `t = x udiv s`, returned as the
  // single node that must hold.
  //
  // Here rather than in BVExactEncoder, which is what asks for it, because
  // the facts are built out of BBEQ, BBBVLE, BBUminus and the rest, and
  // those are this class's own. It is the same reason BBExactBinaryOp is
  // here: the caller has the AIG manager and the splice, and this has the
  // parts.
  BBNode BBDivLemma(DivLemma lemma, const BBNodeVec& x, const BBNodeVec& s,
                    const BBNodeVec& t, BBNodeSet& support);
  BBNode BBRemLemma(RemLemma lemma, const BBNodeVec& x, const BBNodeVec& s,
                    const BBNodeVec& t, BBNodeSet& support);
  BBNode BBMulLemma(MulLemma lemma, const BBNodeVec& x, const BBNodeVec& s,
                    const BBNodeVec& t, BBNodeSet& support);
  BBNode BBAddLemma(AddLemma lemma, const BBNodeVec& x, const BBNodeVec& s,
                    const BBNodeVec& t, BBNodeSet& support);

  // The full modular recomposition theorem over a quotient/remainder pair:
  // x = q*s+r. `product` is a BVMULT node standing for q*s and supplies the
  // multiplier with the same AST metadata it receives on the exact path.
  BBNode BBDivRemIdentity(const ASTNode& product, const BBNodeVec& x,
                          const BBNodeVec& s, const BBNodeVec& q,
                          const BBNodeVec& r, BBNodeSet& support);

  // Logical shifts by a variable amount. Both are logarithmic barrel
  // shifters, and any represented amount at or above the value width clears
  // the vector as SMT-LIB requires.
  BBNodeVec BBShiftLeftByVariable(const BBNodeVec& value,
                                  const BBNodeVec& amount);
  BBNodeVec BBShiftRightByVariable(const BBNodeVec& value,
                                   const BBNodeVec& amount, unsigned width);
  // Shared premise for the quotient/remainder exact-one-band registry facts.
  BBNode BBFitsExactlyOnce(const BBNodeVec& dividend,
                           const BBNodeVec& divisor);

  typename std::unordered_map<ASTNode, BBNodeVec, ASTNode::ASTNodeHasher,
                              ASTNode::ASTNodeEqual>::iterator
  simplify_during_bb(ASTNode& term, BBNodeSet& support);

  // `allowAbstraction` is false for a blast whose circuit is itself the
  // answer to an abstraction -- an exact escalation, or a lemma spliced onto
  // an abstraction's own variables. Such a blast must not abstract anything:
  // the record it minted would be against an AIG thrown away at the end of
  // the call, so nothing could ever refine it. This used to be done by
  // clearing the flags on the shared UserDefinedFlags for the duration, which
  // meant one blast could see another's policy.
  BitBlaster(BBNodeManagerT* bnm, Simplifier* _simp, NodeFactory* astNodeF,
             UserDefinedFlags* _uf,
             simplifier::constantBitP::ConstantBitPropagation* cb_ = NULL,
             bool allowAbstraction = true)
      : uf(_uf), allowAbstraction_(allowAbstraction)
  {
    nf = bnm;
    cb = cb_;
    BBTrue = nf->getTrue();
    BBFalse = nf->getFalse();
    simp = _simp;
    ASTNF = astNodeF;
  }

  // Whether this blast may replace a term or an equality with free inputs.
  // Whether this operation has not been counted as a candidate before; see
  // countedCandidates_.
  bool firstCandidateSighting(const ASTNode& n)
  {
    return countedCandidates_.insert(n).second;
  }

  bool termAbstractionAllowed() const
  {
    return allowAbstraction_ && uf->bv_term_abstraction;
  }
  bool eqAbstractionAllowed() const
  {
    return allowAbstraction_ && uf->bv_eq_abstraction;
  }

  void ClearAllTables()
  {
    BBTermMemo.clear();
    BBFormMemo.clear();
    fpNativeFiniteTerms.clear();
    fpNativeZeroMagnitudeFacts.clear();
    fpNativeZeroMagnitudeTerms.clear();
    fpNativeUnknownZeroMagnitudeTerms.clear();
    fpNativeFiniteNonnegativeTerms.clear();
    fpNativeUnknownFiniteNonnegativeTerms.clear();
    fpNativeFiniteNonpositiveTerms.clear();
    fpNativeUnknownFiniteNonpositiveTerms.clear();
    fpNativeBounds.clear();
    fpNativeIntervals.clear();
    fpNativeParentUses.clear();
    fpNativeDomainRoot = ASTNode();
    fpNativeAddIsZeroFusions = 0;
    fpNativeFiniteCmpOperands = 0;
    fpNativeFiniteEqOperands = 0;
    fpNativeFiniteClassifications = 0;
    fpNativeFiniteArithOperands = 0;
    fpNativeFiniteRoundPacks = 0;
    fpNativeZeroCmpOperands = 0;
    fpNativeZeroEqOperands = 0;
    fpNativeZeroClassifications = 0;
    fpNativeIsZeroPredicates = 0;
    fpNativeIsZeroAddPredicates = 0;
    fpNativeIsZeroAddFusedPredicates = 0;
    fpNativeIsZeroAddExclusiveResults = 0;
    fpNativeIsZeroAddMemoizedResults = 0;
    fpNativeIsZeroAddKnownZeroResults = 0;
    fpNativeIsZeroAddBothFiniteOperands = 0;
    fpNativeIsZeroAddKnownSameSignOperands = 0;
    fpNativeIsZeroAddKnownOppositeSignOperands = 0;
    fpNativeIsZeroAddOneKnownSignOperand = 0;
    fpNativeZeroAddFastPaths = 0;
    fpNativeZeroMulFastPaths = 0;
    fpNativeZeroToFpFastPaths = 0;
    fpNativeKnownPositiveAddPaths = 0;
    fpNativeKnownNegativeAddPaths = 0;
    fpNativeKnownPositiveMulPaths = 0;
    fpNativeKnownNegativeMulPaths = 0;
  }

  // Bitblast a formula
  const BBNode BBForm(const ASTNode& form);

  void getConsts(const ASTNode& n, ASTNodeMap& fromTo, ASTNodeMap& equivs);
};

// The one instantiation the tree has, and the name everything outside the
// blaster uses. A second backend adds an alias beside this one rather than an
// edit at every use.
using BitBlasterAIG = BitBlaster<BBNodeAIG, BBNodeManagerAIG>;
using BBNodeVecAIG = std::vector<BBNodeAIG>;
using BBNodeSetAIG = BBNodeOrderedSet<BBNodeAIG>;

} // end of namespace

#endif
