/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: July, 2026
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

/*
 * The achievable image of a chain of operations applied to a completely
 * free bit-vector variable x, where every other operand is a constant.
 *
 * This is an UNDER-approximation: every value the image reports is
 * guaranteed attainable by some choice of x (with a concrete witness),
 * the reverse of the over-approximating ValueSetAnalysis /
 * UnsignedIntervalAnalysis. RemoveUnconstrained uses it to collapse a
 * predicate over such a chain -- e.g. ((x mod 100) + 7 >u 50) -- to a
 * fresh boolean, recording x := ITE(v, w_true, w_false).
 *
 * The image is tracked exactly as a contiguous unsigned interval while
 * the operations allow it, and degrades to a small set of
 * (x-witness, value) samples when they don't. Only a collapse whose two
 * witnesses re-evaluate to the two polarities is ever reported, so a
 * bug in a transfer or inversion rule is a missed optimisation, never
 * unsoundness.
 */

#ifndef ACHIEVABLEIMAGE_H_
#define ACHIEVABLEIMAGE_H_

#include "stp/AST/AST.h"
#include <vector>

namespace stp
{

class STPMgr;

// One term on the path from x up to the predicate: the path enters
// through operand `pathIndex`; `constants` holds the other operands in
// order. n-ary kinds must be pre-folded to one constant; BVEXTRACT
// keeps its two index constants; BVSX/BVZX store no constant (the
// evaluator takes the new width from outWidth).
//
// samePathAllOperands marks a binary node whose operands are BOTH the
// path -- (bvmul t t), squaring being the common case. Still a unary
// function of the path value; `constants` is empty and the value is
// placed in every operand slot.
struct GroundStep
{
  Kind kind;
  unsigned outWidth;
  unsigned inWidth;
  size_t pathIndex;
  bool samePathAllOperands = false;
  ASTVec constants;
};

class AchievableImage
{
public:
  struct Decision
  {
    bool collapse = false;
    ASTNode witnessTrue;  // BVCONST at x's width; set iff collapse.
    ASTNode witnessFalse;
  };

  AchievableImage(STPMgr& bm, unsigned varWidth);
  ~AchievableImage();
  AchievableImage(const AchievableImage&) = delete;
  AchievableImage& operator=(const AchievableImage&) = delete;

  // Flow the image up through one more operation. Returns false when
  // the kind isn't handled -- the caller should give up.
  bool apply(const GroundStep& step);

  // Seed hint: a value the caller expects to matter at the top of the
  // chain (typically the predicate's constant). When the image degrades
  // to samples, the hints (width-adapted) are tried as members first --
  // e.g. (x & 0x55) == 0x41 only finds the true-witness x = 0x41 this
  // way. Call before apply()ing the steps.

  // Back-propagate the predicate constant `k` through the whole
  // collected path with a per-operator heuristic preimage, recording a
  // hint at every level it survives to. A degrade deep in the chain
  // then has a same-width hint instead of a truncated top-level one --
  // e.g. (extract[15:0] (bvadd C (zx x))) == k recovers x = k' exactly.
  // The backward map is only a seed heuristic; witnesses are still
  // validated forward. Call before apply()ing the steps.
  void addHintChain(const std::vector<GroundStep>& steps, const ASTNode& k);

  // Whether the predicate `pred` between the chain's result and the
  // constant `k` can be made both true and false by choice of x. When
  // it can, returns validated witnesses for x.
  Decision decide(Kind pred, bool pathIsFirstOperand, const ASTNode& k);

  static bool handledKind(Kind k);
  static bool predicateKind(Kind k);

  // Evaluate one step at a concrete path value. Returns a fresh CBV.
  // Shared with RemoveUnconstrained's symbolic-side collapse, which
  // needs forward evaluation of a chain outside any image object.
  static CBV evalStep(const GroundStep& step, const CBV in);

  // Whether the image is still tracked as an exact interval (rather
  // than under-approximating samples). Tests use this to know when
  // decide() must be complete, not just sound.
  bool isExact() const { return rep == Rep::Exact; }

  static const unsigned MAX_PATH = 32;
  static const size_t MAX_SAMPLES = 24;

private:
  enum class Rep
  {
    Exact,  // the image is exactly the unsigned interval [lo, hi].
    Samples // each sample's value is attainable, via its witness.
  };

  struct Sample
  {
    CBV witness; // at varWidth
    CBV value;   // at curWidth
  };

  STPMgr& bm;
  const unsigned varWidth;
  Rep rep;
  CBV lo, hi; // owned; meaningful when rep == Rep::Exact.
  unsigned curWidth;

  // Every step applied, for the forward validation of witnesses.
  std::vector<GroundStep> allSteps;
  // Input interval of allSteps[i], recorded while still exact; used to
  // invert an image value back to an x value.
  std::vector<std::pair<CBV, CBV>> exactBounds;
  std::vector<Sample> samples;
  std::vector<CBV> hints; // owned; see addHintChain

  bool applyExact(const GroundStep& step);
  void applyToSamples(const GroundStep& step);
  void degradeToSamples(const GroundStep& degradingStep);
  void addSample(CBV witness, CBV value);

  CBV invertPrefix(CBV value); // takes and returns ownership
  CBV invertStep(const GroundStep& step, const CBV inLo, const CBV inHi,
                 const CBV value);
  bool evalPredicate(Kind pred, bool pathIsFirstOperand, const CBV member,
                     const CBV k);
  bool validate(const CBV xWitness, Kind pred, bool pathIsFirstOperand,
                const CBV k, bool expected);

  void setExact(CBV newLo, CBV newHi, unsigned newWidth);
  bool isFull() const;
};
}

#endif
