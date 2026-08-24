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

struct RelationalBound
{
  ASTNode symbol;
  ASTNode expression;
  bool lower = false;
  bool strict = false;
};

struct SelectorDomain
{
  ASTNode zero;
  ASTNode one;
  Interval zeroValue;
  Interval oneValue;
};

using BoundsMap =
    std::unordered_map<ASTNode, Bounds, ASTNode::ASTNodeHasher,
                       ASTNode::ASTNodeEqual>;
using IntervalMap =
    std::unordered_map<ASTNode, Interval, ASTNode::ASTNodeHasher,
                       ASTNode::ASTNodeEqual>;
using SelectorDomainMap =
    std::unordered_map<ASTNode, SelectorDomain, ASTNode::ASTNodeHasher,
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

template <typename Visitor>
void forEachConjunct(const ASTNode& root, Visitor visitor)
{
  ASTVec pending(1, root);
  while (!pending.empty())
  {
    const ASTNode current = pending.back();
    pending.pop_back();
    if (current.GetKind() == AND)
    {
      // Reverse-push to preserve recursive left-to-right visitation order.
      for (auto it = current.end(); it != current.begin();)
        pending.push_back(*--it);
      continue;
    }
    visitor(current);
  }
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

    // Keep the default zero-fact pass dependent only on the literal boxes it
    // has always consumed. The derived-bound experiment below is deliberately
    // decision-only: when it cannot decide an assertion, enabling it must not
    // alter the circuit by feeding extra facts into another optimization.
    if (bm->UserFlags.fp_domain_sound_zero_facts)
      inferSoundZeroRows(root);

    if (bm->UserFlags.fp_domain_derived_bounds)
    {
      intervals.clear();
      collectDerivedBounds(root);
      propagateDerivedBounds();
    }

    rebuildBoxed();
    stats.boxed_symbols = boxed.size();

    if (bm->UserFlags.fp_domain_derived_bounds && contradictoryBox())
      return bm->ASTFalse;

    if (bm->UserFlags.fp_domain_extremal_selectors)
    {
      collectSelectorDomains(root);
      intervals.clear();
      collectExtremalRewrites(root);
    }

    // Zero-fact extraction is an independent strengthening. Enabling it must
    // not also select the general domain-rewrite prepass. The inferred facts
    // are conjoined below with the original formula unless one of the rewrite
    // passes was explicitly requested as well.
    ASTNode out = root;
    if (bm->UserFlags.fp_domain_simplify ||
        bm->UserFlags.fp_domain_derived_bounds ||
        bm->UserFlags.fp_domain_extremal_selectors ||
        bm->UserFlags.fp_domain_row_bounds)
      out = rewrite(root);
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
  int compareEndpoint(long double value, const std::string& bits, bool exact,
                      long double oldValue, const std::string& oldBits,
                      bool oldExact) const
  {
    if (exact && oldExact && bits.size() == oldBits.size())
      return packedCompare(bits, oldBits);
    return value < oldValue ? -1 : (value > oldValue ? 1 : 0);
  }

  bool updateBound(const ASTNode& symbol, bool lower, long double value,
                   const std::string& bits, bool exact, bool strict)
  {
    assert(symbol.GetKind() == SYMBOL && fpSort(symbol));
    Bounds& b = bounds[symbol];
    bool& present = lower ? b.hasLower : b.hasUpper;
    long double& oldValue = lower ? b.lower : b.upper;
    std::string& oldBits = lower ? b.lowerBits : b.upperBits;
    bool& oldExact = lower ? b.lowerExact : b.upperExact;
    bool& oldStrict = lower ? b.lowerStrict : b.upperStrict;

    bool replace = !present;
    bool strengthenStrictness = false;
    if (present)
    {
      const int comparison =
          compareEndpoint(value, bits, exact, oldValue, oldBits, oldExact);
      replace = lower ? comparison > 0 : comparison < 0;
      strengthenStrictness = comparison == 0 && strict && !oldStrict;
    }

    if (!replace && !strengthenStrictness)
      return false;

    present = true;
    if (replace)
    {
      oldValue = value;
      oldBits = bits;
      oldExact = exact;
      oldStrict = strict;
    }
    else
      oldStrict = true;
    return true;
  }

  void collectConjunctiveBounds(const ASTNode& root)
  {
    forEachConjunct(root, [&](const ASTNode& n) {
      ASTNode symbol;
      ASTNode constant;
      long double value = 0.0L;
      bool lowerBound = false;
      bool strict = false;
      if (!boundPredicate(n, symbol, constant, value, lowerBound, strict))
        return;

      // These predicates are both the proof source for this pass and the
      // facts consumed later by native lowering. Do not fold them away merely
      // because the interval assembled from the complete conjunction proves
      // them.
      boxPredicates.insert(n);
      std::string bits;
      const bool exact = fpConstantBits(constant, bits);
      if (updateBound(symbol, lowerBound, value, bits, exact, strict))
      {
        Bounds& b = bounds[symbol];
        if (lowerBound)
          b.lowerConst = constant;
        else
          b.upperConst = constant;
      }
    });
  }

  bool zeroRelationExpression(const ASTNode& n, ASTNode& expression) const
  {
    if (n.GetKind() == FP_ISZERO && n.Degree() == 1)
    {
      expression = n[0];
      return true;
    }
    if (n.GetKind() != FP_EQ || n.Degree() != 2)
      return false;
    if (isFpZero(n[0]))
      expression = n[1];
    else if (isFpZero(n[1]))
      expression = n[0];
    else
      return false;
    return true;
  }

  void collectDerivedBounds(const ASTNode& root)
  {
    forEachConjunct(root, [&](const ASTNode& n) {
      if (isOrderedComparison(n.GetKind()) && n.Degree() == 2)
      {
        derivedDecisionPredicates.insert(n);
        ASTNode left;
        ASTNode right;
        if (!relationAsLeq(n, left, right))
          return;

        long double ignored = 0.0L;
        bool used = false;
        const bool strict = n.GetKind() == FP_LT || n.GetKind() == FP_GT;
        if (left.GetKind() == SYMBOL && fpSort(left) && left != right &&
            !fpConstantValue(right, ignored))
        {
          relationalBounds.push_back({left, right, false, strict});
          used = true;
        }
        if (right.GetKind() == SYMBOL && fpSort(right) && left != right &&
            !fpConstantValue(left, ignored))
        {
          relationalBounds.push_back({right, left, true, strict});
          used = true;
        }
        if (used)
        {
          boxPredicates.insert(n);
          ++stats.derived_relations;
        }
      }

      ASTNode expression;
      if (zeroRelationExpression(n, expression) &&
          expression.GetKind() == FP_ADD && expression.Degree() == 3)
        zeroAddRelations.push_back(expression);
    });
  }

  bool numericAliasSymbol(const ASTNode& n, ASTNode& symbol,
                          bool& negated) const
  {
    ASTNode current = n;
    negated = false;
    while (true)
    {
      if (current.GetKind() == SYMBOL && fpSort(current))
      {
        symbol = current;
        return true;
      }
      if (current.GetKind() == FP_NEG && current.Degree() == 1)
      {
        negated = !negated;
        current = current[0];
        continue;
      }
      if (current.GetKind() != FP_ADD || current.Degree() != 3)
        return false;
      if (isFpZero(current[1]))
        current = current[2];
      else if (isFpZero(current[2]))
        current = current[1];
      else
        return false;
    }
  }

  Interval negateInterval(const Interval& x) const
  {
    if (!x.known || !x.finite)
      return Interval::unknown();
    if (x.exact)
      return Interval::exactFiniteRange(
          -x.upper, -x.lower, packedNegate(x.upperBits),
          packedNegate(x.lowerBits));
    return Interval::finiteRange(-x.upper, -x.lower);
  }

  bool applyIntervalBound(const ASTNode& symbol, const Interval& value,
                          bool lower, bool strict)
  {
    if (!value.known || !value.finite)
      return false;
    const long double endpoint = lower ? value.lower : value.upper;
    const std::string bits =
        value.exact ? (lower ? value.lowerBits : value.upperBits)
                    : std::string();
    return updateBound(symbol, lower, endpoint, bits, value.exact, strict);
  }

  bool deriveRelationalBound(const RelationalBound& relation)
  {
    const Interval expression = interval(relation.expression);
    if (!expression.known || !expression.finite)
      return false;
    if (applyIntervalBound(relation.symbol, expression, relation.lower,
                           relation.strict))
    {
      ++stats.derived_bounds;
      return true;
    }
    return false;
  }

  bool deriveZeroAddBound(const ASTNode& expression)
  {
    assert(expression.GetKind() == FP_ADD && expression.Degree() == 3);
    bool changed = false;
    for (unsigned aliasIndex = 1; aliasIndex <= 2; ++aliasIndex)
    {
      ASTNode symbol;
      bool aliasNegated = false;
      if (!numericAliasSymbol(expression[aliasIndex], symbol, aliasNegated))
        continue;

      const unsigned otherIndex = aliasIndex == 1 ? 2 : 1;
      Interval value = negateInterval(interval(expression[otherIndex]));
      if (aliasNegated)
        value = negateInterval(value);
      if (!value.known || !value.finite)
        continue;

      if (applyIntervalBound(symbol, value, true, false))
      {
        ++stats.zero_add_bounds;
        changed = true;
      }
      if (applyIntervalBound(symbol, value, false, false))
      {
        ++stats.zero_add_bounds;
        changed = true;
      }
    }
    return changed;
  }

  void propagateDerivedBounds()
  {
    const size_t maxRounds =
        2 * (relationalBounds.size() + zeroAddRelations.size() +
             bounds.size() + 1);
    for (size_t round = 0; round < maxRounds; ++round)
    {
      bool changed = false;
      for (const RelationalBound& relation : relationalBounds)
        changed = deriveRelationalBound(relation) || changed;
      for (const ASTNode& expression : zeroAddRelations)
        changed = deriveZeroAddBound(expression) || changed;
      intervals.clear();
      if (!changed)
        break;
    }
  }

  int compareBounds(const Bounds& b) const
  {
    assert(b.hasLower && b.hasUpper);
    return compareEndpoint(b.lower, b.lowerBits, b.lowerExact, b.upper,
                           b.upperBits, b.upperExact);
  }

  void rebuildBoxed()
  {
    boxed.clear();
    for (const auto& entry : bounds)
      if (entry.second.hasLower && entry.second.hasUpper &&
          compareBounds(entry.second) <= 0)
        boxed.insert(entry.first);
  }

  bool contradictoryBox()
  {
    for (const auto& entry : bounds)
    {
      const Bounds& b = entry.second;
      if (!b.hasLower || !b.hasUpper)
        continue;
      const int comparison = compareBounds(b);
      if (comparison > 0 ||
          (comparison == 0 && (b.lowerStrict || b.upperStrict)))
      {
        ++stats.inconsistent_boxes;
        return true;
      }
    }
    return false;
  }

  bool selectorEquality(const ASTNode& n, ASTNode& symbol,
                        ASTNode& constant, bool& one)
  {
    // The simplifying factory canonicalises fp.eq(x, +/-0) to isZero(x),
    // and fp.eq(x, nonzero-constant) to structural FP equality. Recover that
    // source-level semantic {0, 1} disjunction here. Structural equality is
    // sound for the one endpoint; it is deliberately not used for zero.
    if (n.GetKind() == FP_ISZERO && n.Degree() == 1 &&
        n[0].GetKind() == SYMBOL && fpSort(n[0]))
    {
      symbol = n[0];
      const SourceSort sort = symbol.GetSourceSort();
      constant = bm->CreateFPSpecialConst(
          FPSpecial::PlusZero, sort.exponentWidth(), sort.significandWidth());
      one = false;
      return true;
    }

    if ((n.GetKind() != FP_EQ && n.GetKind() != FP_SMT_EQ) ||
        n.Degree() != 2)
      return false;

    if (n[0].GetKind() == SYMBOL && fpSort(n[0]))
    {
      symbol = n[0];
      constant = n[1];
    }
    else if (n[1].GetKind() == SYMBOL && fpSort(n[1]))
    {
      symbol = n[1];
      constant = n[0];
    }
    else
      return false;

    long double value = 0.0L;
    if (!fpConstantValue(constant, value))
      return false;
    if (value == 0.0L)
    {
      if (n.GetKind() == FP_SMT_EQ)
        return false;
      one = false;
      return true;
    }
    if (value == 1.0L)
    {
      one = true;
      return true;
    }
    return false;
  }

  void collectSelectorDomains(const ASTNode& root)
  {
    forEachConjunct(root, [&](const ASTNode& n) {
      if (n.GetKind() != OR || n.Degree() != 2)
        return;

      ASTNode firstSymbol;
      ASTNode firstConstant;
      ASTNode secondSymbol;
      ASTNode secondConstant;
      bool firstOne = false;
      bool secondOne = false;
      if (!selectorEquality(n[0], firstSymbol, firstConstant, firstOne) ||
          !selectorEquality(n[1], secondSymbol, secondConstant, secondOne) ||
          firstSymbol != secondSymbol || firstOne == secondOne)
        return;

      SelectorDomain domain;
      domain.zero = firstOne ? secondConstant : firstConstant;
      domain.one = firstOne ? firstConstant : secondConstant;
      domain.zeroValue = interval(domain.zero);
      domain.oneValue = interval(domain.one);
      if (!domain.zeroValue.known || !domain.zeroValue.finite ||
          !domain.zeroValue.exact || !domain.oneValue.known ||
          !domain.oneValue.finite || !domain.oneValue.exact)
        return;
      selectorDomains[firstSymbol] = domain;
      stats.extremal_selector_domains = selectorDomains.size();
    });
  }

  void collectPredicateSelectors(const ASTNode& predicate,
                                 ASTNodeSet& selectors) const
  {
    ASTVec pending(1, predicate);
    ASTNodeSet visited;
    while (!pending.empty())
    {
      const ASTNode current = pending.back();
      pending.pop_back();
      if (!visited.insert(current).second)
        continue;
      if (selectorDomains.find(current) != selectorDomains.end())
      {
        selectors.insert(current);
        continue;
      }
      for (const ASTNode& child : current)
        pending.push_back(child);
    }
  }

  int compareIntervalEndpoints(const Interval& left, bool leftUpper,
                               const Interval& right,
                               bool rightUpper) const
  {
    if (left.exact && right.exact)
    {
      const std::string& l = leftUpper ? left.upperBits : left.lowerBits;
      const std::string& r = rightUpper ? right.upperBits : right.lowerBits;
      return packedCompare(l, r);
    }
    const long double l = leftUpper ? left.upper : left.lower;
    const long double r = rightUpper ? right.upper : right.lower;
    return l < r ? -1 : (l > r ? 1 : 0);
  }

  bool predicateDecision(const ASTNode& predicate, bool& value)
  {
    if (predicate.Degree() != 2 ||
        (!isOrderedComparison(predicate.GetKind()) &&
         predicate.GetKind() != FP_EQ &&
         predicate.GetKind() != FP_SMT_EQ))
      return false;

    const Interval left = interval(predicate[0]);
    const Interval right = interval(predicate[1]);
    if (!left.known || !right.known || !left.finite || !right.finite)
      return false;

    const int upperLower =
        compareIntervalEndpoints(left, true, right, false);
    const int lowerUpper =
        compareIntervalEndpoints(left, false, right, true);
    if (predicate.GetKind() == FP_EQ || predicate.GetKind() == FP_SMT_EQ)
    {
      if (upperLower < 0 || lowerUpper > 0)
      {
        value = false;
        return true;
      }
      const bool leftSingleton =
          compareIntervalEndpoints(left, false, left, true) == 0;
      const bool rightSingleton =
          compareIntervalEndpoints(right, false, right, true) == 0;
      if (leftSingleton && rightSingleton && lowerUpper == 0)
      {
        value = true;
        return true;
      }
      return false;
    }

    const bool strict =
        predicate.GetKind() == FP_LT || predicate.GetKind() == FP_GT;
    if (predicate.GetKind() == FP_LT || predicate.GetKind() == FP_LEQ)
    {
      if (strict ? upperLower < 0 : upperLower <= 0)
      {
        value = true;
        return true;
      }
      if (strict ? lowerUpper >= 0 : lowerUpper > 0)
      {
        value = false;
        return true;
      }
      return false;
    }

    if (strict ? lowerUpper > 0 : lowerUpper >= 0)
    {
      value = true;
      return true;
    }
    if (strict ? upperLower <= 0 : upperLower < 0)
    {
      value = false;
      return true;
    }
    return false;
  }

  bool objectivePredicate(const ASTNode& n) const
  {
    if (n.Degree() != 2 ||
        (!isOrderedComparison(n.GetKind()) && n.GetKind() != FP_EQ &&
         n.GetKind() != FP_SMT_EQ))
      return false;

    long double target = 0.0L;
    const bool leftConstant = fpConstantValue(n[0], target);
    long double rightTarget = 0.0L;
    const bool rightConstant = fpConstantValue(n[1], rightTarget);
    if (leftConstant == rightConstant)
      return false;
    if (!leftConstant)
      target = rightTarget;

    // Zero-result predicates have separate signed-zero-sensitive machinery.
    // Keeping this experiment to nonzero extrema also prevents it from
    // consuming a bound derived from the predicate it is considering.
    return target != 0.0L;
  }

  void setSelectorOverride(const ASTNode& symbol, bool one)
  {
    const SelectorDomainMap::const_iterator it = selectorDomains.find(symbol);
    assert(it != selectorDomains.end());
    selectorOverrides[symbol] = one ? it->second.oneValue
                                    : it->second.zeroValue;
    intervals.clear();
  }

  void clearSelectorOverrides()
  {
    selectorOverrides.clear();
    intervals.clear();
  }

  void collectExtremalRewrites(const ASTNode& root)
  {
    forEachConjunct(root, [&](const ASTNode& predicate) {
      if (!objectivePredicate(predicate) ||
          boxPredicates.find(predicate) != boxPredicates.end())
        return;

      ASTNodeSet selectors;
      collectPredicateSelectors(predicate, selectors);
      if (selectors.empty())
        return;
      ++stats.extremal_selector_predicates;

      std::vector<std::pair<ASTNode, bool>> forced;
      for (const ASTNode& selector : selectors)
      {
        setSelectorOverride(selector, false);
        bool zeroValue = false;
        const bool zeroDecided = predicateDecision(predicate, zeroValue);
        clearSelectorOverrides();

        setSelectorOverride(selector, true);
        bool oneValue = false;
        const bool oneDecided = predicateDecision(predicate, oneValue);
        clearSelectorOverrides();

        const bool zeroImpossible = zeroDecided && !zeroValue;
        const bool oneImpossible = oneDecided && !oneValue;
        if (zeroImpossible != oneImpossible)
          forced.push_back(std::make_pair(selector, zeroImpossible));
      }
      if (forced.empty())
        return;

      for (const auto& fact : forced)
        setSelectorOverride(fact.first, fact.second);
      bool sufficientValue = false;
      const bool sufficient =
          predicateDecision(predicate, sufficientValue) && sufficientValue;
      clearSelectorOverrides();
      if (!sufficient)
        return;

      ASTVec facts;
      facts.reserve(forced.size());
      for (const auto& fact : forced)
      {
        const SelectorDomain& domain = selectorDomains.at(fact.first);
        facts.push_back(nf->CreateNode(FP_EQ, fact.first,
                                       fact.second ? domain.one : domain.zero));
      }
      extremalRewrites[predicate] = nf->CreateNode(AND, facts);
      stats.extremal_selector_facts += facts.size();
      ++stats.extremal_selector_rewrites;
    });
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
      const IntervalMap::const_iterator overridden = selectorOverrides.find(n);
      if (overridden != selectorOverrides.end())
        return overridden->second;

      const BoundsMap::const_iterator it = bounds.find(n);
      if (it != bounds.end() && it->second.hasLower && it->second.hasUpper)
      {
        if (compareBounds(it->second) > 0)
          return Interval::unknown();
        if (it->second.lowerExact && it->second.upperExact)
          return Interval::exactFiniteRange(
              it->second.lower, it->second.upper, it->second.lowerBits,
              it->second.upperBits);
        return Interval::finiteRange(it->second.lower, it->second.upper);
      }

      const SelectorDomainMap::const_iterator selector =
          selectorDomains.find(n);
      if (selector != selectorDomains.end())
        return Interval::exactFiniteRange(
            selector->second.zeroValue.lower,
            selector->second.oneValue.upper,
            selector->second.zeroValue.lowerBits,
            selector->second.oneValue.upperBits);
      return Interval::unknown();
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

  void collectSoundRows(const ASTNode& root)
  {
    forEachConjunct(root, [&](const ASTNode& n) {
      SignedTerms terms;
      if (parseSoundZeroRow(n, terms))
        soundRows.push_back(terms);
    });
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
    const bool legacyRewrite = bm->UserFlags.fp_domain_simplify ||
                               bm->UserFlags.fp_domain_row_bounds;
    const ASTNodeMap::const_iterator extremal = extremalRewrites.find(n);
    if (extremal != extremalRewrites.end())
      out = extremal->second;
    else if (boxPredicates.find(n) != boxPredicates.end())
      out = n;
    else if (n.GetKind() == FP_ISZERO && legacyRewrite)
    {
      out = rowBoundZeroRewrite(n[0]);
      if (out.IsNull())
        out = zeroPredicateRewrite(n[0]);
    }
    else if (legacyRewrite &&
             (n.GetKind() == FP_ISNAN || n.GetKind() == FP_ISINFINITE))
    {
      const Interval x = interval(n[0]);
      if (x.known && x.finite)
      {
        ++stats.classifier_false;
        out = bm->ASTFalse;
      }
    }
    else if ((legacyRewrite ||
              (bm->UserFlags.fp_domain_derived_bounds &&
               derivedDecisionPredicates.find(n) !=
                   derivedDecisionPredicates.end())) &&
             isOrderedComparison(n.GetKind()) && n.Degree() == 2)
    {
      bool value = false;
      if (predicateDecision(n, value))
      {
        if (value)
          ++stats.interval_true;
        else
          ++stats.interval_false;
        out = value ? bm->ASTTrue : bm->ASTFalse;
      }
    }
    else if (legacyRewrite && n.GetKind() == FP_EQ && n.Degree() == 2)
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
  std::vector<RelationalBound> relationalBounds;
  ASTVec zeroAddRelations;
  ASTNodeSet derivedDecisionPredicates;
  SelectorDomainMap selectorDomains;
  IntervalMap selectorOverrides;
  std::vector<SignedTerms> soundRows;
  ASTNodeSet boxed;
  ASTNodeSet boxPredicates;
  ASTNodeSet soundZeroReps;
  ASTNodeSet soundZeroSymbols;
  ASTNodeMap soundParent;
  IntervalMap intervals;
  ASTNodeMap extremalRewrites;
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
