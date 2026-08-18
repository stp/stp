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
#include "stp/Util/DagWalk.h"
#include <cassert>
#include <cmath>
#include <list>
#include <map>

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

// BitBlaster used to be a template over the node representation and its
// manager. The AIG backend is the only one that remains, so these are the
// only types it is ever used with.
using BBNode = BBNodeAIG;
using BBNodeVec = std::vector<BBNodeAIG>;

class BitBlaster
{
  using BBNodeSet = std::unordered_set<BBNode>;

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

  void checkFixed(const BBNodeVec& v, const ASTNode& n);

  // AND each bit of vector y with single bit b and return the result.
  // (used in BBMult)
  // BBNodeVec BBAndBit(const BBNodeVec& y, ASTNode b);

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

  // bit blast fp.mul / fp.add / float-to-float to_fp over packed operands:
  // hand-written unpack/compute/round/pack circuits, no SymFPU
  // (--bb.fp-native-arith)
  BBNodeVec BBfpMul(const ASTNode& term, BBNodeSet& support);
  BBNodeVec BBfpAdd(const ASTNode& term, BBNodeSet& support);
  BBNodeVec BBfpToFp(const ASTNode& term, BBNodeSet& support);

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
                       unsigned E, BBNodeSet& support);

  // The shared tail of the native arithmetic circuits: denormalise into
  // the subnormal range when the biased exponent be is <= 0, round rsig
  // (with its guard and sticky) per the one-hot mode rm, saturate
  // overflow per mode, and pack the finite result. NaN/infinity/zero
  // specials are the caller's to mux over the top.
  BBNodeVec BBfpRoundPack(const BBNodeVec& rm, const BBNode& sgn,
                          const BBNodeVec& rsig, const BBNode& guard,
                          const BBNode& sticky, const BBNodeVec& be,
                          unsigned sb, unsigned eb, BBNodeSet& support);

  // Width of the internal signed exponent for format (eb, sb): eb+2
  // widened until the subnormal shift distance (up to bias + 2sb + 3,
  // counting fp.add's alignment headroom) cannot overflow it.
  static unsigned BBfpExpWidth(unsigned eb, unsigned sb);

  // Helpers for the native floating-point arithmetic circuits.
  // Count of leading zeros of v (from the MSB down) as an unsigned binary
  // vector of `countWidth` bits; an all-zero v counts v.size().
  BBNodeVec BBfpCLZ(const BBNodeVec& v, unsigned countWidth);
  // Left shift v by the unsigned binary amount `amt` (zero fill).
  BBNodeVec BBfpShiftLeft(const BBNodeVec& v, const BBNodeVec& amt);
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

  UserDefinedFlags* uf;
  NodeFactory* ASTNF;
  Simplifier* simp;
  BBNodeManagerAIG* nf;

  ASTNodeSet booth_recoded; // Nodes that have been recoded.

public:
  BitBlaster& operator=(const BitBlaster& other) = delete;
  BitBlaster(const BitBlaster& other) = delete;
  ~BitBlaster() { ClearAllTables(); }

  simplifier::constantBitP::ConstantBitPropagation* cb;

  // Bit blast a bitvector term.  The term must have a kind for a
  // bitvector term.  Result is a ref to a vector of formula nodes
  // representing the boolean formula.
  const BBNodeVec BBTerm(const ASTNode& term, BBNodeSet& support);

  std::unordered_map<ASTNode, BBNodeVec, ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual>::iterator
  simplify_during_bb(ASTNode& term, BBNodeSet& support);

  BitBlaster(BBNodeManagerAIG* bnm, Simplifier* _simp, NodeFactory* astNodeF,
             UserDefinedFlags* _uf,
             simplifier::constantBitP::ConstantBitPropagation* cb_ = NULL)
      : uf(_uf)
  {
    nf = bnm;
    cb = cb_;
    BBTrue = nf->getTrue();
    BBFalse = nf->getFalse();
    simp = _simp;
    ASTNF = astNodeF;
  }

  void ClearAllTables()
  {
    BBTermMemo.clear();
    BBFormMemo.clear();
  }

  // Bitblast a formula
  const BBNode BBForm(const ASTNode& form);

  void getConsts(const ASTNode& n, ASTNodeMap& fromTo, ASTNodeMap& equivs);
};

} // end of namespace

#endif
