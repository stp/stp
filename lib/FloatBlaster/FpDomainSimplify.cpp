/********************************************************************
 * Experimental floating-point domain simplification.
 ********************************************************************/
#include "stp/FloatBlaster/FpDomainSimplify.h"

#include "stp/FloatBlaster/DecimalLiteral.h"
#include "stp/FloatBlaster/rounding_modes.h"

#include "extlib-constbv/constantbv.h"

#include <algorithm>
#include <cassert>
#include <cmath>
#include <iostream>
#include <limits>
#include <unordered_map>
#include <vector>

namespace stp
{
namespace
{

struct Bounds
{
  bool hasLower = false;
  bool hasUpper = false;
  bool lowerStrict = false;
  bool upperStrict = false;
  long double lower = 0.0L;
  long double upper = 0.0L;
  ASTNode lowerConst;
  ASTNode upperConst;
  std::string lowerBits;
  std::string upperBits;
  bool lowerExact = false;
  bool upperExact = false;
};

struct Interval
{
  bool known = false;
  bool finite = false;
  bool exact = false;
  long double lower = 0.0L;
  long double upper = 0.0L;
  std::string lowerBits;
  std::string upperBits;

  static Interval unknown() { return Interval(); }

  static Interval finiteRange(long double lo, long double hi)
  {
    Interval out;
    out.known = true;
    out.finite = true;
    out.lower = lo;
    out.upper = hi;
    return out;
  }

  static Interval exactFiniteRange(long double lo, long double hi,
                                   const std::string& loBits,
                                   const std::string& hiBits)
  {
    Interval out = finiteRange(lo, hi);
    out.exact = true;
    out.lowerBits = loBits;
    out.upperBits = hiBits;
    return out;
  }
};

using BoundsMap =
    std::unordered_map<ASTNode, Bounds, ASTNode::ASTNodeHasher,
                       ASTNode::ASTNodeEqual>;
using IntervalMap =
    std::unordered_map<ASTNode, Interval, ASTNode::ASTNodeHasher,
                       ASTNode::ASTNodeEqual>;

using SignedTerms = std::vector<std::pair<ASTNode, int>>;

bool fpSort(const ASTNode& n)
{
  return n.GetSourceSort().kind() == SourceSort::Kind::FloatingPoint;
}

bool bit(const ASTNode& c, unsigned i)
{
  return CONSTANTBV::BitVector_bit_test(c.GetBVConst(), i);
}

bool fpConstantValue(const ASTNode& c, long double& out)
{
  if (c.GetKind() != BVCONST || c.GetSourceSort().kind() !=
                                    SourceSort::Kind::FloatingPoint)
    return false;

  const unsigned eb = c.GetExpWidth();
  const unsigned sb = c.GetSigWidth();
  if (eb < 2 || sb < 2 || eb >= 31 ||
      sb > static_cast<unsigned>(std::numeric_limits<long double>::digits))
    return false;

  const unsigned w = eb + sb;
  const bool negative = bit(c, w - 1);

  unsigned exponent = 0;
  for (unsigned i = 0; i < eb; i++)
    if (bit(c, sb - 1 + i))
      exponent |= 1u << i;

  const unsigned maxExponent = (1u << eb) - 1;
  if (exponent == maxExponent)
    return false; // NaN or infinity.

  long double significand = 0.0L;
  for (unsigned i = 0; i + 1 < sb; i++)
    if (bit(c, i))
      significand += std::ldexp(1.0L, static_cast<int>(i));

  const int bias = static_cast<int>((1u << (eb - 1)) - 1);
  if (exponent == 0)
  {
    out = std::ldexp(significand,
                     static_cast<int>(1 - bias - (sb - 1)));
  }
  else
  {
    significand += std::ldexp(1.0L, static_cast<int>(sb - 1));
    out = std::ldexp(significand,
                     static_cast<int>(exponent) - bias -
                         static_cast<int>(sb - 1));
  }

  if (negative)
    out = -out;
  return std::isfinite(out) &&
         (out != 0.0L || (exponent == 0 && significand == 0.0L));
}

bool fpConstantBits(const ASTNode& c, std::string& out)
{
  if (c.GetKind() != BVCONST ||
      c.GetSourceSort().kind() != SourceSort::Kind::FloatingPoint)
    return false;

  const unsigned width = c.GetValueWidth();
  out.resize(width);
  for (unsigned i = 0; i < width; i++)
    out[width - 1 - i] = bit(c, i) ? '1' : '0';
  return true;
}

bool fpPackedValue(const SourceSort& sort, const std::string& bits,
                   long double& out)
{
  if (sort.kind() != SourceSort::Kind::FloatingPoint)
    return false;
  const unsigned eb = sort.exponentWidth();
  const unsigned sb = sort.significandWidth();
  if (bits.size() != eb + sb || eb < 2 || sb < 2 || eb >= 31 ||
      sb > static_cast<unsigned>(std::numeric_limits<long double>::digits))
    return false;

  unsigned exponent = 0;
  for (unsigned i = 0; i < eb; i++)
    exponent = (exponent << 1) |
               static_cast<unsigned>(bits[1 + i] == '1');
  if (exponent == (1u << eb) - 1)
    return false;

  long double significand = 0.0L;
  for (unsigned i = 0; i + 1 < sb; i++)
    if (bits[1 + eb + i] == '1')
      significand += std::ldexp(
          1.0L, static_cast<int>(sb - 2 - i));

  const int bias = static_cast<int>((1u << (eb - 1)) - 1);
  if (exponent == 0)
    out = std::ldexp(significand,
                     1 - bias - static_cast<int>(sb - 1));
  else
  {
    significand += std::ldexp(1.0L, static_cast<int>(sb - 1));
    out = std::ldexp(significand,
                     static_cast<int>(exponent) - bias -
                         static_cast<int>(sb - 1));
  }
  if (bits[0] == '1')
    out = -out;
  return std::isfinite(out);
}

bool packedFinite(const std::string& bits, unsigned eb)
{
  if (bits.size() <= eb)
    return false;
  for (unsigned i = 0; i < eb; i++)
    if (bits[1 + i] != '1')
      return true;
  return false;
}

bool packedZeroMagnitude(const std::string& bits)
{
  for (size_t i = 1; i < bits.size(); i++)
    if (bits[i] != '0')
      return false;
  return !bits.empty();
}

// Numeric ordering for finite packed IEEE values. Signed zeros compare equal;
// all other values use sign-magnitude order, reversed on the negative side.
int packedCompare(const std::string& a, const std::string& b)
{
  assert(a.size() == b.size() && !a.empty());
  if (packedZeroMagnitude(a) && packedZeroMagnitude(b))
    return 0;
  if (a[0] != b[0])
    return a[0] == '1' ? -1 : 1;
  const int magnitude = a.substr(1).compare(b.substr(1));
  if (magnitude == 0)
    return 0;
  const int ordered = magnitude < 0 ? -1 : 1;
  return a[0] == '1' ? -ordered : ordered;
}

std::string packedNegate(std::string bits)
{
  assert(!bits.empty());
  bits[0] = bits[0] == '1' ? '0' : '1';
  return bits;
}

std::string packedAbs(std::string bits)
{
  assert(!bits.empty());
  bits[0] = '0';
  return bits;
}

bool fixedRoundingMode(const ASTNode& n, unsigned& mode)
{
  if (n.GetKind() != BVCONST || n.GetValueWidth() != 5)
    return false;
  mode = static_cast<unsigned>(n.GetUnsignedConst());
  switch (mode)
  {
    case symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN:
    case symbolic_fp::ROUND_NEAREST_TIES_TO_AWAY:
    case symbolic_fp::ROUND_TOWARD_POSITIVE:
    case symbolic_fp::ROUND_TOWARD_NEGATIVE:
    case symbolic_fp::ROUND_TOWARD_ZERO: return true;
    default: return false;
  }
}

bool exactBinaryEndpoint(const SourceSort& sort, Kind kind,
                         const std::string& left,
                         const std::string& right, unsigned mode,
                         std::string& result)
{
  PackedFpBinaryOp operation;
  switch (kind)
  {
    case FP_ADD: operation = PackedFpBinaryOp::Add; break;
    case FP_SUB: operation = PackedFpBinaryOp::Subtract; break;
    case FP_MUL: operation = PackedFpBinaryOp::Multiply; break;
    default: return false;
  }

  std::string error;
  if (!packedFPBinaryOp(left, right, sort.exponentWidth(),
                        sort.significandWidth(), mode, operation, result,
                        error))
    return false;
  return packedFinite(result, sort.exponentWidth());
}

bool maxFiniteValue(const SourceSort& sort, long double& out)
{
  if (sort.kind() != SourceSort::Kind::FloatingPoint)
    return false;

  const unsigned eb = sort.exponentWidth();
  const unsigned sb = sort.significandWidth();
  if (eb < 2 || sb < 2 || eb >= 31 || sb > 113)
    return false;

  const int bias = static_cast<int>((1u << (eb - 1)) - 1);
  const int maxExp = static_cast<int>((1u << eb) - 2) - bias;
  const long double sig =
      2.0L - std::ldexp(1.0L, -static_cast<int>(sb - 1));
  out = std::ldexp(sig, maxExp);
  return std::isfinite(out);
}

bool maxUlpValue(const SourceSort& sort, long double& out)
{
  if (sort.kind() != SourceSort::Kind::FloatingPoint)
    return false;

  const unsigned eb = sort.exponentWidth();
  const unsigned sb = sort.significandWidth();
  if (eb < 2 || sb < 2 || eb >= 31 || sb > 113)
    return false;

  const int bias = static_cast<int>((1u << (eb - 1)) - 1);
  const int maxExp = static_cast<int>((1u << eb) - 2) - bias;
  out = std::ldexp(1.0L, maxExp - static_cast<int>(sb - 1));
  return std::isfinite(out) && out > 0.0L;
}

Interval roundedRange(const SourceSort& sort, long double lo, long double hi)
{
  if (!std::isfinite(lo) || !std::isfinite(hi))
    return Interval::unknown();

  long double maxFinite = 0.0L;
  if (!maxFiniteValue(sort, maxFinite))
    return Interval::unknown();

  if (lo < -maxFinite || hi > maxFinite)
    return Interval::unknown();
  long double maxUlp = 0.0L;
  if (!maxUlpValue(sort, maxUlp))
    return Interval::unknown();
  lo = std::max(-maxFinite, lo - maxUlp);
  hi = std::min(maxFinite, hi + maxUlp);
  return Interval::finiteRange(lo, hi);
}

Interval exactRoundedRange(const SourceSort& sort, Kind kind,
                           const ASTNode& roundingMode, const Interval& a,
                           const Interval& b)
{
  if (!a.exact || !b.exact)
    return Interval::unknown();

  unsigned fixedMode = 0;
  const bool fixed = fixedRoundingMode(roundingMode, fixedMode);
  const unsigned lowerMode =
      fixed ? fixedMode
            : static_cast<unsigned>(symbolic_fp::ROUND_TOWARD_NEGATIVE);
  const unsigned upperMode =
      fixed ? fixedMode
            : static_cast<unsigned>(symbolic_fp::ROUND_TOWARD_POSITIVE);

  using EndpointPair = std::pair<std::string, std::string>;
  std::vector<EndpointPair> lowerInputs;
  std::vector<EndpointPair> upperInputs;
  if (kind == FP_ADD)
  {
    lowerInputs.emplace_back(a.lowerBits, b.lowerBits);
    upperInputs.emplace_back(a.upperBits, b.upperBits);
  }
  else if (kind == FP_SUB)
  {
    lowerInputs.emplace_back(a.lowerBits, b.upperBits);
    upperInputs.emplace_back(a.upperBits, b.lowerBits);
  }
  else if (kind == FP_MUL)
  {
    const std::string as[2] = {a.lowerBits, a.upperBits};
    const std::string bs[2] = {b.lowerBits, b.upperBits};
    for (const std::string& av : as)
      for (const std::string& bv : bs)
      {
        lowerInputs.emplace_back(av, bv);
        upperInputs.emplace_back(av, bv);
      }
  }
  else
    return Interval::unknown();

  std::string lower;
  for (const EndpointPair& input : lowerInputs)
  {
    std::string value;
    if (!exactBinaryEndpoint(sort, kind, input.first, input.second,
                             lowerMode, value))
      return Interval::unknown();
    if (lower.empty() || packedCompare(value, lower) < 0)
      lower = value;
  }

  std::string upper;
  for (const EndpointPair& input : upperInputs)
  {
    std::string value;
    if (!exactBinaryEndpoint(sort, kind, input.first, input.second,
                             upperMode, value))
      return Interval::unknown();
    if (upper.empty() || packedCompare(value, upper) > 0)
      upper = value;
  }

  long double lo = 0.0L;
  long double hi = 0.0L;
  if (lower.empty() || upper.empty() || packedCompare(lower, upper) > 0 ||
      !fpPackedValue(sort, lower, lo) ||
      !fpPackedValue(sort, upper, hi))
    return Interval::unknown();
  return Interval::exactFiniteRange(lo, hi, lower, upper);
}

bool isOrderedComparison(Kind k)
{
  return k == FP_LT || k == FP_LEQ || k == FP_GT || k == FP_GEQ;
}

bool isFpZero(const ASTNode& n)
{
  long double value = 0.0L;
  return fpConstantValue(n, value) && value == 0.0L;
}

bool relationAsLeq(const ASTNode& n, ASTNode& left, ASTNode& right)
{
  switch (n.GetKind())
  {
    case FP_LEQ:
    case FP_LT:
      left = n[0];
      right = n[1];
      return true;
    case FP_GEQ:
    case FP_GT:
      left = n[1];
      right = n[0];
      return true;
    default:
      return false;
  }
}

bool boundPredicate(const ASTNode& n, ASTNode& symbol, ASTNode& constant,
                    long double& value, bool& lowerBound, bool& strict)
{
  if (!isOrderedComparison(n.GetKind()) || n.Degree() != 2)
    return false;

  strict = n.GetKind() == FP_LT || n.GetKind() == FP_GT;

  ASTNode left;
  ASTNode right;
  if (!relationAsLeq(n, left, right))
    return false;

  if (left.GetKind() == SYMBOL && fpSort(left) && fpConstantValue(right, value))
  {
    symbol = left;
    constant = right;
    lowerBound = false;
    return true;
  }

  if (right.GetKind() == SYMBOL && fpSort(right) && fpConstantValue(left, value))
  {
    symbol = right;
    constant = left;
    lowerBound = true;
    return true;
  }

  return false;
}

ASTNode rebuild(NodeFactory* nf, const ASTNode& n, const ASTVec& children)
{
  if (n.GetType() == BOOLEAN_TYPE)
    return nf->CreateNode(n.GetKind(), children);
  if (n.GetIndexWidth() > 0)
    return nf->CreateArrayTerm(n.GetKind(), n.GetIndexWidth(),
                               n.GetValueWidth(), children);
  return nf->CreateTerm(n.GetKind(), n.GetValueWidth(), children);
}

class DomainPass
{
public:
  DomainPass(STPMgr* bm_, NodeFactory* nf_,
             FpDomainSimplify::Statistics& stats_)
      : bm(bm_), nf(nf_), stats(stats_)
  {
  }

  ASTNode run(const ASTNode& root)
  {
    collectConjunctiveBounds(root);
    for (const auto& entry : bounds)
      if (entry.second.hasLower && entry.second.hasUpper &&
          entry.second.lower <= entry.second.upper)
        boxed.insert(entry.first);

    stats.boxed_symbols = boxed.size();

    if (bm->UserFlags.fp_domain_sound_zero_facts)
      inferSoundZeroRows(root);

    ASTNode out = rewrite(root);
    if (!soundZeroSymbols.empty())
    {
      ASTVec conjuncts;
      conjuncts.push_back(out);
      for (const ASTNode& term : soundZeroSymbols)
      {
        assert(term.GetKind() == SYMBOL);
        conjuncts.push_back(magnitudeZero(term));
      }
      out = nf->CreateNode(AND, conjuncts);
    }
    return out;
  }

private:
  void collectConjunctiveBounds(const ASTNode& n)
  {
    if (n.GetKind() == AND)
    {
      for (const ASTNode& child : n)
        collectConjunctiveBounds(child);
      return;
    }

    ASTNode symbol;
    ASTNode constant;
    long double value = 0.0L;
    bool lowerBound = false;
    bool strict = false;
    if (!boundPredicate(n, symbol, constant, value, lowerBound, strict))
      return;

    // These predicates are both the proof source for this pass and the facts
    // consumed later by native lowering. Do not fold them away merely because
    // the interval assembled from the complete conjunction proves them.
    boxPredicates.insert(n);
    Bounds& b = bounds[symbol];
    if (lowerBound)
    {
      if (!b.hasLower || value >= b.lower)
      {
        b.lower = value;
        b.lowerConst = constant;
        b.lowerStrict = strict;
        b.lowerExact = fpConstantBits(constant, b.lowerBits);
      }
      b.hasLower = true;
    }
    else
    {
      if (!b.hasUpper || value <= b.upper)
      {
        b.upper = value;
        b.upperConst = constant;
        b.upperStrict = strict;
        b.upperExact = fpConstantBits(constant, b.upperBits);
      }
      b.hasUpper = true;
    }
  }

  Interval interval(const ASTNode& n)
  {
    const IntervalMap::const_iterator cached = intervals.find(n);
    if (cached != intervals.end())
      return cached->second;

    Interval out = intervalUncached(n);
    intervals.emplace(n, out);
    return out;
  }

  Interval intervalUncached(const ASTNode& n)
  {
    long double value = 0.0L;
    if (fpConstantValue(n, value))
    {
      std::string bits;
      if (fpConstantBits(n, bits))
        return Interval::exactFiniteRange(value, value, bits, bits);
      return Interval::finiteRange(value, value);
    }

    if (n.GetKind() == SYMBOL && fpSort(n))
    {
      const BoundsMap::const_iterator it = bounds.find(n);
      if (it == bounds.end() || !it->second.hasLower || !it->second.hasUpper)
        return Interval::unknown();
      if (it->second.lower > it->second.upper)
        return Interval::unknown();
      if (it->second.lowerExact && it->second.upperExact)
        return Interval::exactFiniteRange(
            it->second.lower, it->second.upper, it->second.lowerBits,
            it->second.upperBits);
      return Interval::finiteRange(it->second.lower, it->second.upper);
    }

    switch (n.GetKind())
    {
      case ITE:
      {
        if (n.Degree() != 3 || !fpSort(n))
          return Interval::unknown();
        const Interval t = interval(n[1]);
        const Interval e = interval(n[2]);
        if (!t.known || !e.known || !t.finite || !e.finite)
          return Interval::unknown();
        const long double lower = std::min(t.lower, e.lower);
        const long double upper = std::max(t.upper, e.upper);
        if (t.exact && e.exact)
        {
          const std::string& lowerBits =
              packedCompare(t.lowerBits, e.lowerBits) <= 0 ? t.lowerBits
                                                           : e.lowerBits;
          const std::string& upperBits =
              packedCompare(t.upperBits, e.upperBits) >= 0 ? t.upperBits
                                                           : e.upperBits;
          return Interval::exactFiniteRange(lower, upper, lowerBits,
                                            upperBits);
        }
        return Interval::finiteRange(lower, upper);
      }

      case FP_ABS:
      {
        const Interval x = interval(n[0]);
        if (!x.known || !x.finite)
          return Interval::unknown();
        if (x.lower >= 0.0L)
        {
          if (!x.exact)
            return x;
          return Interval::exactFiniteRange(
              x.lower, x.upper, packedAbs(x.lowerBits),
              packedAbs(x.upperBits));
        }
        if (x.upper <= 0.0L)
        {
          if (x.exact)
            return Interval::exactFiniteRange(
                -x.upper, -x.lower, packedAbs(x.upperBits),
                packedAbs(x.lowerBits));
          return Interval::finiteRange(-x.upper, -x.lower);
        }
        const long double upper = std::max(-x.lower, x.upper);
        if (x.exact)
        {
          std::string zero = x.lowerBits;
          std::fill(zero.begin(), zero.end(), '0');
          const std::string negativeMagnitude = packedAbs(x.lowerBits);
          const std::string positiveMagnitude = packedAbs(x.upperBits);
          const std::string& upperBits =
              packedCompare(negativeMagnitude, positiveMagnitude) >= 0
                  ? negativeMagnitude
                  : positiveMagnitude;
          return Interval::exactFiniteRange(0.0L, upper, zero, upperBits);
        }
        return Interval::finiteRange(0.0L, upper);
      }

      case FP_NEG:
      {
        const Interval x = interval(n[0]);
        if (!x.known || !x.finite)
          return Interval::unknown();
        if (x.exact)
          return Interval::exactFiniteRange(
              -x.upper, -x.lower, packedNegate(x.upperBits),
              packedNegate(x.lowerBits));
        return Interval::finiteRange(-x.upper, -x.lower);
      }

      case FP_ADD:
      case FP_SUB:
      case FP_MUL:
      {
        if (n.Degree() != 3)
          return Interval::unknown();
        const Interval a = interval(n[1]);
        const Interval b = interval(n[2]);
        if (!a.known || !b.known || !a.finite || !b.finite)
          return Interval::unknown();

        const Interval exact =
            exactRoundedRange(n.GetSourceSort(), n.GetKind(), n[0], a, b);
        if (exact.known)
          return exact;

        if (n.GetKind() == FP_ADD)
          return roundedRange(n.GetSourceSort(), a.lower + b.lower,
                              a.upper + b.upper);
        if (n.GetKind() == FP_SUB)
          return roundedRange(n.GetSourceSort(), a.lower - b.upper,
                              a.upper - b.lower);

        long double vals[4] = {a.lower * b.lower, a.lower * b.upper,
                               a.upper * b.lower, a.upper * b.upper};
        return roundedRange(n.GetSourceSort(),
                            *std::min_element(vals, vals + 4),
                            *std::max_element(vals, vals + 4));
      }

      default:
        return Interval::unknown();
    }
  }

  bool knownFinite(const ASTNode& n)
  {
    const Interval x = interval(n);
    return x.known && x.finite;
  }

  bool knownNonnegativeFinite(const ASTNode& n)
  {
    const Interval x = interval(n);
    if (!x.known || !x.finite)
      return false;
    if (x.exact)
      return x.lowerBits[0] == '0' || packedZeroMagnitude(x.lowerBits);
    return x.lower >= 0.0L;
  }

  // Recognise the same restricted linear-row language as the former
  // coefficient/error model, but do not flatten it. The actual endpoint
  // evaluation below follows every FP operation in its original AST
  // association and rounds after each operation in the target format.
  bool linearRowExpression(const ASTNode& n)
  {
    long double value = 0.0L;
    if (fpConstantValue(n, value))
      return true;

    if (n.GetKind() == SYMBOL && knownFinite(n))
      return true;

    if (n.GetKind() == FP_NEG)
      return n.Degree() == 1 && linearRowExpression(n[0]);

    if ((n.GetKind() == FP_ADD || n.GetKind() == FP_SUB) && n.Degree() == 3)
      return linearRowExpression(n[1]) && linearRowExpression(n[2]);

    if (n.GetKind() == FP_MUL && n.Degree() == 3)
    {
      long double c = 0.0L;
      if (fpConstantValue(n[1], c) && n[2].GetKind() == SYMBOL &&
          knownFinite(n[2]))
        return true;
      return fpConstantValue(n[2], c) && n[1].GetKind() == SYMBOL &&
             knownFinite(n[1]);
    }

    return false;
  }

  ASTNode rowBoundZeroRewrite(const ASTNode& expr)
  {
    if (!bm->UserFlags.fp_domain_row_bounds)
      return ASTNode();

    if (!linearRowExpression(expr))
      return ASTNode();

    const Interval row = interval(expr);
    if (!row.known || !row.finite)
      return ASTNode();

    ++stats.row_bound_rows;
    bool excludesZero = row.lower > 0.0L || row.upper < 0.0L;
    if (row.exact)
    {
      assert(row.lowerBits.size() == row.upperBits.size());
      const std::string zero(row.lowerBits.size(), '0');
      excludesZero = packedCompare(row.lowerBits, zero) > 0 ||
                     packedCompare(row.upperBits, zero) < 0;
    }
    if (excludesZero)
    {
      ++stats.row_bound_false;
      return bm->ASTFalse;
    }
    return ASTNode();
  }

  ASTNode magnitudeZero(const ASTNode& n)
  {
    const SourceSort sort = n.GetSourceSort();
    if (sort.kind() != SourceSort::Kind::FloatingPoint)
      return ASTNode();

    const unsigned width = sort.packedWidth();
    if (width <= 1)
      return ASTNode();

    const ASTNode high = bm->CreateBVConst(32, width - 2);
    const ASTNode low = bm->CreateBVConst(32, 0);
    const ASTNode magnitude =
        nf->CreateTerm(BVEXTRACT, width - 1, n, high, low);
    return nf->CreateNode(EQ, magnitude, bm->CreateZeroConst(width - 1));
  }

  ASTNode zeroTest(const ASTNode& n)
  {
    if (bm->UserFlags.fp_domain_sound_zero_facts && n.GetKind() == SYMBOL &&
        knownNonnegativeFinite(n))
    {
      const ASTNode zero = magnitudeZero(n);
      if (!zero.IsNull())
        return zero;
    }

    return nf->CreateNode(FP_ISZERO, n);
  }

  bool parseSignedSymbolSum(const ASTNode& n, int sign, SignedTerms& terms)
  {
    if (n.GetKind() == FP_ADD && n.Degree() == 3)
    {
      return parseSignedSymbolSum(n[1], sign, terms) &&
             parseSignedSymbolSum(n[2], sign, terms);
    }

    if (n.GetKind() == FP_SUB && n.Degree() == 3)
    {
      return parseSignedSymbolSum(n[1], sign, terms) &&
             parseSignedSymbolSum(n[2], -sign, terms);
    }

    if (n.GetKind() == FP_NEG)
      return parseSignedSymbolSum(n[0], -sign, terms);

    if (isFpZero(n))
      return true;

    if (n.GetKind() != SYMBOL || !knownNonnegativeFinite(n))
      return false;

    terms.push_back(std::make_pair(n, sign));
    return true;
  }

  bool parseSoundZeroRow(const ASTNode& n, SignedTerms& terms)
  {
    ASTNode expr;
    if (n.GetKind() == FP_ISZERO && n.Degree() == 1)
      expr = n[0];
    else if (n.GetKind() == FP_EQ && n.Degree() == 2)
    {
      if (isFpZero(n[0]))
        expr = n[1];
      else if (isFpZero(n[1]))
        expr = n[0];
      else
        return false;
    }
    else
      return false;

    return parseSignedSymbolSum(expr, 1, terms) && !terms.empty();
  }

  ASTNode soundRep(const ASTNode& n)
  {
    ASTNodeMap::iterator it = soundParent.find(n);
    if (it == soundParent.end())
    {
      soundParent[n] = n;
      return n;
    }
    if (it->second == n)
      return n;
    const ASTNode rep = soundRep(it->second);
    it->second = rep;
    return rep;
  }

  bool uniteSound(const ASTNode& a, const ASTNode& b)
  {
    ASTNode ra = soundRep(a);
    ASTNode rb = soundRep(b);
    if (ra == rb)
      return false;
    if (rb.GetNodeNum() < ra.GetNodeNum())
      std::swap(ra, rb);
    soundParent[rb] = ra;
    return true;
  }

  bool markSoundZero(const ASTNode& n)
  {
    const ASTNode rep = soundRep(n);
    if (!soundZeroReps.insert(rep).second)
      return false;
    return true;
  }

  void collectSoundRows(const ASTNode& n)
  {
    if (n.GetKind() == AND)
    {
      for (const ASTNode& child : n)
        collectSoundRows(child);
      return;
    }

    SignedTerms terms;
    if (parseSoundZeroRow(n, terms))
      soundRows.push_back(terms);
  }

  void normalizeSoundZeros()
  {
    ASTNodeSet normalized;
    for (const ASTNode& z : soundZeroReps)
      normalized.insert(soundRep(z));
    soundZeroReps.swap(normalized);
  }

  void inferSoundZeroRows(const ASTNode& root)
  {
    collectSoundRows(root);
    stats.sound_zero_rows = soundRows.size();
    if (soundRows.empty())
      return;

    for (const SignedTerms& row : soundRows)
      for (const auto& term : row)
        soundRep(term.first);

    bool changed = true;
    unsigned rounds = 0;
    while (changed && rounds++ < soundRows.size() + 1)
    {
      changed = false;
      normalizeSoundZeros();

      for (const SignedTerms& row : soundRows)
      {
        SignedTerms active;
        for (const auto& term : row)
        {
          const ASTNode rep = soundRep(term.first);
          if (soundZeroReps.find(rep) != soundZeroReps.end())
            continue;
          active.push_back(term);
        }

        if (active.empty())
          continue;

        bool allPositive = true;
        bool allNegative = true;
        for (const auto& term : active)
        {
          allPositive = allPositive && term.second > 0;
          allNegative = allNegative && term.second < 0;
        }

        // A rounded sum of finite terms with one mathematical sign has zero
        // magnitude only when every term has zero magnitude. Association and
        // rounding cannot cancel a nonzero same-sign term.
        if (allPositive || allNegative)
        {
          for (const auto& term : active)
            changed = markSoundZero(term.first) || changed;
          continue;
        }

        // For two representable operands, a rounded difference can have zero
        // magnitude only when the operands have the same FP value. Keep that
        // equality for propagating an independently established zero fact.
        // Do not cancel equal/opposite terms inside a larger row: in
        // (x + tiny) - x, `tiny` may be lost to rounding even though it is
        // nonzero.
        if (active.size() == 2 &&
            active[0].second + active[1].second == 0)
          changed = uniteSound(active[0].first, active[1].first) || changed;
      }
    }

    normalizeSoundZeros();
    for (const auto& entry : soundParent)
      if (soundZeroReps.find(soundRep(entry.first)) != soundZeroReps.end())
        soundZeroSymbols.insert(entry.first);
    stats.sound_zero_facts = soundZeroSymbols.size();
  }

  bool differenceFromZero(const ASTNode& n, ASTNode& left, ASTNode& right)
  {
    if (n.GetKind() != FP_ADD || n.Degree() != 3)
      return false;

    if (n[1].GetKind() == FP_NEG)
    {
      left = n[2];
      right = n[1][0];
      return knownFinite(left) && knownFinite(right);
    }

    if (n[2].GetKind() == FP_NEG)
    {
      left = n[1];
      right = n[2][0];
      return knownFinite(left) && knownFinite(right);
    }

    return false;
  }

  void collectAddends(const ASTNode& n, ASTVec& out)
  {
    if (n.GetKind() == FP_ADD && n.Degree() == 3)
    {
      collectAddends(n[1], out);
      collectAddends(n[2], out);
      return;
    }
    out.push_back(n);
  }

  ASTNode zeroEqualityRewrite(const ASTNode& expr, const ASTNode& zero)
  {
    if (expr.GetKind() == FP_NEG)
    {
      ++stats.difference_zero_equalities;
      return nf->CreateNode(FP_EQ, expr[0], zero);
    }

    ASTNode left;
    ASTNode right;
    if (differenceFromZero(expr, left, right))
    {
      ++stats.difference_zero_equalities;
      return nf->CreateNode(FP_EQ, left, right);
    }

    ASTVec addends;
    collectAddends(expr, addends);
    if (addends.size() < 2)
      return ASTNode();

    for (const ASTNode& addend : addends)
      if (!knownNonnegativeFinite(addend))
        return ASTNode();

    ASTVec conjuncts;
    conjuncts.reserve(addends.size());
    for (const ASTNode& addend : addends)
      conjuncts.push_back(nf->CreateNode(FP_EQ, addend, zero));
    ++stats.nonnegative_zero_sums;
    return nf->CreateNode(AND, conjuncts);
  }

  ASTNode zeroPredicateRewrite(const ASTNode& expr)
  {
    if (expr.GetKind() == FP_NEG)
    {
      ++stats.difference_zero_equalities;
      return zeroTest(expr[0]);
    }

    ASTNode left;
    ASTNode right;
    if (differenceFromZero(expr, left, right))
    {
      ++stats.difference_zero_equalities;
      return nf->CreateNode(FP_EQ, left, right);
    }

    ASTVec addends;
    collectAddends(expr, addends);
    if (addends.size() < 2)
      return ASTNode();

    for (const ASTNode& addend : addends)
      if (!knownNonnegativeFinite(addend))
        return ASTNode();

    ASTVec conjuncts;
    conjuncts.reserve(addends.size());
    for (const ASTNode& addend : addends)
      conjuncts.push_back(zeroTest(addend));
    ++stats.nonnegative_zero_sums;
    return nf->CreateNode(AND, conjuncts);
  }

  ASTNode rewrite(const ASTNode& n)
  {
    const ASTNodeMap::const_iterator cached = rewriteCache.find(n);
    if (cached != rewriteCache.end())
      return cached->second;

    ASTNode out;
    if (boxPredicates.find(n) != boxPredicates.end())
      out = n;
    else if (n.GetKind() == FP_ISZERO)
    {
      out = rowBoundZeroRewrite(n[0]);
      if (out.IsNull())
        out = zeroPredicateRewrite(n[0]);
    }
    else if (n.GetKind() == FP_ISNAN || n.GetKind() == FP_ISINFINITE)
    {
      const Interval x = interval(n[0]);
      if (x.known && x.finite)
      {
        ++stats.classifier_false;
        out = bm->ASTFalse;
      }
    }
    else if (isOrderedComparison(n.GetKind()) && n.Degree() == 2)
    {
      const Interval a = interval(n[0]);
      const Interval b = interval(n[1]);
      if (a.known && b.known && a.finite && b.finite)
      {
        const bool strict = n.GetKind() == FP_LT || n.GetKind() == FP_GT;
        const auto compareEndpoints = [](const Interval& left,
                                         bool leftUpper,
                                         const Interval& right,
                                         bool rightUpper) {
          if (left.exact && right.exact)
          {
            const std::string& l =
                leftUpper ? left.upperBits : left.lowerBits;
            const std::string& r =
                rightUpper ? right.upperBits : right.lowerBits;
            return packedCompare(l, r);
          }
          const long double l = leftUpper ? left.upper : left.lower;
          const long double r = rightUpper ? right.upper : right.lower;
          return l < r ? -1 : (l > r ? 1 : 0);
        };
        const int upperLower =
            compareEndpoints(a, true, b, false);
        const int lowerUpper =
            compareEndpoints(a, false, b, true);
        bool decided = false;
        bool value = false;
        if (n.GetKind() == FP_LT || n.GetKind() == FP_LEQ)
        {
          if (strict ? upperLower < 0 : upperLower <= 0)
          {
            decided = true;
            value = true;
          }
          else if (strict ? lowerUpper >= 0 : lowerUpper > 0)
          {
            decided = true;
            value = false;
          }
        }
        else
        {
          if (strict ? lowerUpper > 0 : lowerUpper >= 0)
          {
            decided = true;
            value = true;
          }
          else if (strict ? upperLower <= 0 : upperLower < 0)
          {
            decided = true;
            value = false;
          }
        }

        if (decided)
        {
          if (value)
            ++stats.interval_true;
          else
            ++stats.interval_false;
          out = value ? bm->ASTTrue : bm->ASTFalse;
        }
      }
    }
    else if (n.GetKind() == FP_EQ && n.Degree() == 2)
    {
      if (isFpZero(n[0]))
      {
        out = rowBoundZeroRewrite(n[1]);
        if (out.IsNull())
          out = zeroEqualityRewrite(n[1], n[0]);
      }
      else if (isFpZero(n[1]))
      {
        out = rowBoundZeroRewrite(n[0]);
        if (out.IsNull())
          out = zeroEqualityRewrite(n[0], n[1]);
      }
    }

    if (out.IsNull())
    {
      if (n.Degree() == 0)
        out = n;
      else
      {
        ASTVec children;
        children.reserve(n.Degree());
        bool changed = false;
        for (const ASTNode& child : n)
        {
          const ASTNode r = rewrite(child);
          changed = changed || r != child;
          children.push_back(r);
        }
        out = changed ? rebuild(nf, n, children) : n;
      }
    }

    rewriteCache[n] = out;
    return out;
  }

  STPMgr* bm;
  NodeFactory* nf;
  FpDomainSimplify::Statistics& stats;
  BoundsMap bounds;
  std::vector<SignedTerms> soundRows;
  ASTNodeSet boxed;
  ASTNodeSet boxPredicates;
  ASTNodeSet soundZeroReps;
  ASTNodeSet soundZeroSymbols;
  ASTNodeMap soundParent;
  IntervalMap intervals;
  ASTNodeMap rewriteCache;
};

} // namespace

FpDomainSimplify::FpDomainSimplify(STPMgr* bm_)
    : bm(bm_), node_factory(bm_->defaultNodeFactory)
{
}

ASTNode FpDomainSimplify::topLevel(const ASTNode& source)
{
  if (bm->defaultNodeFactory != node_factory)
    FatalError("FpDomainSimplify reused after the node factory changed");

  stats = Statistics();
  DomainPass pass(bm, node_factory, stats);
  return pass.run(source);
}

} // namespace stp
