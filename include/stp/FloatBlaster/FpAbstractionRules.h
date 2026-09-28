/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: August, 2026
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

#ifndef FPABSTRACTIONRULES_H
#define FPABSTRACTIONRULES_H

// The refinement rules of the floating-point abstraction: sound facts about
// t = op(rm, x, y, ...) stated over the packed bits of the operands and the
// surrogate, without the operation's datapath.
//
// FpAbstractionRuleList.h assigns stable schema IDs and names the
// verification group that checks each one. Those checks are finite:
// FpAbstraction_Test.cpp asserts exact AND NOT rule unsatisfiable at
// explicit formats, rounding modes and parameters, and no finite sweep
// proves a schema for arbitrary format parameters.
//
// The vocabulary is deliberately what is free on a packed value: the class
// (from the exponent and fraction fields), the sign bit, the biased exponent
// field E and the fraction field F, small signed arithmetic on the unbiased
// exponent e = E - bias (read only under a normal-class guard; a subnormal
// or zero is given emin - 1 as an upper bound, a special emax + 1), the
// native ordering predicates, and SMT equality with constants. No counters:
// the trailing-exponent facts are model-instantiated with a concrete
// threshold and become a variable mask (fpRuleTrailingExponentAtLeast).
//
// Tiers, cumulative:
//   0  class/sign constraints: some exact characterisations and some
//      necessary conditions; these do not determine every special outcome;
//   1  order: |y| >= 1 -> |x*y| >= |x| and its kin, from the monotonicity
//      of rounding over a representable endpoint;
//   2  exponent bands and overflow/underflow selection: e(x)+e(y) <= e(t)
//      <= e(x)+e(y)+1 for normals with the boundary rows split out, and the
//      rounding mode's choice between infinity and the largest finite;
//   3  identities: x * 1 = x, x / x = 1, sqrt(4^k) = 2^k, ...

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"

#include <cstdint>
#include <vector>

namespace stp
{

enum class FpRuleId
{
  None,
#define FP_RULE(token, name, operations, family, verification, selection)     \
  token,
#include "stp/FloatBlaster/FpAbstractionRuleList.h"
#undef FP_RULE
  Count
};

struct FpRuleInfo
{
  const char* name;
  const char* operations;
  const char* family;
  const char* verification;
  const char* selection;
};

const FpRuleInfo& fpRuleInfo(FpRuleId id);
inline const char* fpRuleName(FpRuleId id)
{
  return fpRuleInfo(id).name;
}

// What a rule may mention about one abstracted application.
struct FpRuleContext
{
  STPMgr* bm = nullptr;
  Kind kind = UNDEFINED;
  unsigned eb = 0;
  unsigned sb = 0;
  // The rounding mode when constant: one of symbolic_fp::rounding_modes; 0
  // for an operation with a symbolic mode (then `rmTerm` is its RM-sorted
  // symbol) or with no mode at all (fp.rem).
  unsigned rm = 0;
  ASTNode rmTerm;
  // The floating-point operands in operation order (the mode excluded): as
  // float-sorted views, and as the packed bits those views are of. A
  // constant operand is its float constant and its bit-vector constant.
  std::vector<ASTNode> view;
  std::vector<ASTNode> bits;
  // Significand bits of the reduced-precision bands (the flag
  // --fp-abstraction-significand-bits); 0 emits none.
  unsigned bandBits = 0;
  // The surrogate: its float view and its bit-vector symbol. For the
  // integer conversions the result is a plain bit-vector: `tb` is the
  // surrogate at the target width and `t` is null.
  ASTNode t;
  ASTNode tb;
  // The integer conversions (fp.to_sbv/fp.to_ubv) only: the target width,
  // and the proxy of the totalised unspecified value the result takes on
  // NaN, the infinities and out-of-range. Zero and null otherwise.
  unsigned targetWidth = 0;
  ASTNode undefBits;
};

// Append the rule conjuncts of every tier up to `tiers` to `out`. Returns
// how many were appended. If supplied, ids receives one schema ID per
// appended conjunct, in the same order. Omitted/trivial rules append neither.
unsigned emitFpAbstractionRules(const FpRuleContext& context, unsigned tiers,
                                std::vector<ASTNode>& out,
                                std::vector<FpRuleId>* ids = nullptr);

// Facts between one fused multiply-add and other abstracted applications
// over the same operands under the same mode: the product of its two
// factors (`product`, t = fma(x, y, z) against p = mul(x, y)), and the sum
// of one factor with the addend (`sumWithX` is add(x, z), the partner when
// y = 1; `sumWithY` is add(y, z), the partner when x = 1). Each partner may
// be null. The facts are universal and relate surrogates only, so they are
// emitted with the rules rather than chosen by a candidate. Returns how
// many were appended.
unsigned emitFpAbstractionCrossRules(const FpRuleContext& fma,
                                     const FpRuleContext* product,
                                     const FpRuleContext* sumWithX,
                                     const FpRuleContext* sumWithY,
                                     std::vector<ASTNode>& out,
                                     std::vector<FpRuleId>* ids = nullptr);

// Concrete views of a packed constant, for the model-driven lemmas.
struct FpPackedValue
{
  enum Class
  {
    NaN,
    Inf,
    Zero,
    Subnormal,
    Normal
  };
  Class cls = NaN;
  bool negative = false;
  // e as the rules define it: E - bias for a normal, emin - 1 for a
  // subnormal or zero, emax + 1 for a special.
  int64_t e = 0;
  // The trailing exponent: v = M * 2^f with M odd. Meaningful for a nonzero
  // finite value only.
  int64_t f = 0;
};
FpPackedValue decodeFpPackedValue(const ASTNode& packedConstant, unsigned eb,
                                  unsigned sb);

// Whether two packed constants are one value under SMT-LIB equality: every
// NaN is one value, the two zeros are two.
bool fpPackedSmtEqual(const ASTNode& a, const ASTNode& b, unsigned eb,
                      unsigned sb);

// fp.leq over two packed constants: false when either is NaN, true for any
// two zeros.
bool fpPackedLeq(const ASTNode& a, const ASTNode& b, unsigned eb, unsigned sb);

// A fact relating two applications of one operation under one rounding
// mode, chosen because the candidate violates it. First congruence: operands
// equal under SMT-LIB equality in the candidate (the product's factors in
// either order) and results that are not, for any operation. Then
// monotonicity, for applications that share every operand but one (or, for
// the square root and the rounding to an integer, nothing): "a smaller free
// operand gives a smaller result", or a larger one, guarded by the sign of
// the shared operand where the direction depends on it. Every fact is
// universally valid. Given the candidate's operand values (mode excluded,
// in operation order) and surrogate values of the two applications; null
// when the pair offers nothing the candidate violates.
ASTNode fpAbstractionRelationalLemma(const FpRuleContext& a,
                                     const std::vector<ASTNode>& aValues,
                                     const ASTNode& aResult,
                                     const FpRuleContext& b,
                                     const std::vector<ASTNode>& bValues,
                                     const ASTNode& bResult,
                                     FpRuleId* id = nullptr);

// "bits is a multiple of 2^threshold" (true for zero, false for a special),
// as a formula over the packed bits `bits` of a (eb, sb) value.
ASTNode fpRuleTrailingExponentAtLeast(STPMgr* bm, const ASTNode& bits,
                                      unsigned eb, unsigned sb,
                                      int64_t threshold);

// The model-instantiated exactness lemma for one application, given the
// candidate's operand and surrogate values, or null when the candidate does
// not violate one. For multiplication: trailing exponents add; for addition,
// subtraction and remainder: the result is a multiple of the smaller
// quantum; for FMA: of min(f(x)+f(y), f(z)) -- each guarded away from
// overflow, where saturation to the largest finite breaks them.
ASTNode fpAbstractionShapeLemma(const FpRuleContext& context,
                                const std::vector<ASTNode>& operandValues,
                                const ASTNode& surrogateValue,
                                FpRuleId* id = nullptr);

} // namespace stp

#endif
