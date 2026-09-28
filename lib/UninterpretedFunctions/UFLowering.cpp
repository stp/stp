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

#include "stp/UninterpretedFunctions/UFLowering.h"
#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/Globals/Globals.h"
#include "stp/STPManager/STPManager.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/UninterpretedFunctions/UFModel.h"
#include "stp/Util/DagWalk.h"
#include <algorithm>
#include <cerrno>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <map>
#include <string>
#include <unordered_map>
#include <utility>

namespace stp
{

namespace
{

unsigned bitsForDistinct(unsigned n)
{
  if (n <= 1)
    return 1;
  unsigned bits = 0;
  unsigned v = n;
  while (v > 0)
  {
    bits++;
    v >>= 1;
  }
  if (n == (1u << (bits - 1)))
    return bits - 1;
  return bits;
}

struct NarrowAnalysis
{
  std::map<const UFDecl*, unsigned> applicationCount;
  std::set<const UFDecl*> nonNarrowable;
};

NarrowAnalysis analyzeNarrowability(const ASTNode& root, UFContext* context,
                                    PreparationPoller& poll)
{
  NarrowAnalysis result;
  ASTNodeSet visited;
  walkPreOrder(root, [&](const ASTNode& n) -> bool {
    poll();
    if (!visited.insert(n).second)
      return false;

    if (n.GetKind() == UF_APPLY)
    {
      const UFDecl* decl = context->lookupIdentity(n[0]);
      if (decl)
        result.applicationCount[decl]++;
    }

    for (size_t i = 0; i < n.Degree(); i++)
    {
      poll();
      if (n[i].GetKind() != UF_APPLY)
        continue;
      const UFDecl* childDecl = context->lookupIdentity(n[i][0]);
      if (!childDecl)
        continue;

      if (n.GetKind() != EQ)
      {
        result.nonNarrowable.insert(childDecl);
        continue;
      }
      size_t other = (i == 0) ? 1 : 0;
      if (other >= n.Degree() || n[other].GetKind() != UF_APPLY)
      {
        result.nonNarrowable.insert(childDecl);
        continue;
      }
      const UFDecl* otherDecl = context->lookupIdentity(n[other][0]);
      if (otherDecl != childDecl)
      {
        result.nonNarrowable.insert(childDecl);
        result.nonNarrowable.insert(otherDecl);
      }
    }
    return true;
  });
  return result;
}

bool isLeafActual(const ASTNode& actual)
{
  return actual.GetKind() == SYMBOL || actual.isConstant();
}

ASTNode rebuildWithChildren(const ASTNode& original,
                            const ASTVec& loweredChildren, STPMgr* manager)
{
  assert(original.Degree() == loweredChildren.size());
  const ASTNode rebuilt =
      rebuildNodeWithChildren(manager, original, loweredChildren);
  if (rebuilt.GetSourceSort() != original.GetSourceSort())
    FatalError("UF lowering rebuilt a node at the wrong SourceSort", rebuilt);
  return rebuilt;
}

} // namespace

ASTNode
LoweredApplicationView::semanticRootWithDefinitions(STPMgr* manager) const
{
  assert(manager != NULL);
  if (namingDefinitions.empty() && sortConstraints.empty() &&
      congruenceConstraints.empty())
    return semanticRoot;
  ASTVec conjuncts;
  conjuncts.reserve(namingDefinitions.size() + sortConstraints.size() +
                    congruenceConstraints.size() + 1);
  conjuncts.push_back(semanticRoot);
  conjuncts.insert(conjuncts.end(), namingDefinitions.begin(),
                   namingDefinitions.end());
  conjuncts.insert(conjuncts.end(), sortConstraints.begin(),
                   sortConstraints.end());
  conjuncts.insert(conjuncts.end(), congruenceConstraints.begin(),
                   congruenceConstraints.end());
  return manager->defaultNodeFactory->CreateNode(AND, conjuncts);
}

UFLowering::UFLowering(STPMgr* manager) : manager_(manager)
{
  assert(manager_ != NULL);
}

namespace
{

bool allActualsConstant(const LoweredApplicationRecord& record)
{
  for (const ASTNode& actual : record.namedActuals)
    if (!actual.isConstant())
      return false;
  return true;
}

// C(n, 2) without overflowing on an absurd application count.
uint64_t pairsAmong(const uint64_t n)
{
  return n < 2 ? 0 : (n % 2 == 0 ? (n / 2) * (n - 1) : n * ((n - 1) / 2));
}

bool hasFloatingPointPosition(const UFSignature& signature)
{
  if (signature.codomain().kind() == SourceSort::Kind::FloatingPoint)
    return true;
  for (const SourceSort& sort : signature.domain())
    if (sort.kind() == SourceSort::Kind::FloatingPoint)
      return true;
  return false;
}

// One declaration's applications, partitioned so that only pairs drawn from
// the same part can ever be congruent, together with what those parts cost.
//
// The partition is z3's reduce_args grouping: a position at which *every*
// application holds a constant splits them by the value there, and two
// applications in different parts differ at a position where the pair loop
// sees two unequal constants and drops the pair. So the parts are both what
// to charge for and what to walk. Charging C(n, 2) over the whole declaration
// instead pushes it past a budget it fits inside -- measured, a declaration
// with a literal tag in one position was charged 4950 where it installs 450 --
// and walking the whole declaration instead spends time on pairs that can
// produce nothing.
//
// The estimate must be an upper bound on what the loop emits, never under it,
// or a declaration would spend budget it was not billed for. Within a part it
// is the established count: pairs among the applications with a symbolic
// actual somewhere, plus each all-constant application against each of those.
// Two all-constant applications are never charged, in a part or out of one,
// because they are either the same hash-consed handle or differ somewhere and
// are dropped.
//
// That last sentence is why a part carries its symbolic records first and says
// where they end. Being charged nothing is only half of it -- such a pair must
// not be *walked* either, and skipping it has to mean not iterating it, since a
// test still costs a loop step and these counts reach billions. Ordering the
// part is what lets the emit loop take the symbolic prefix as its outer range
// and get C(symbolic, 2) + constant * symbolic exactly, the estimate term for
// term.
struct CongruencePart
{
  std::vector<const LoweredApplicationRecord*> records;
  size_t symbolic = 0;
};

struct CongruenceGroups
{
  std::vector<CongruencePart> parts;
  uint64_t estimate = 0;
};

CongruenceGroups
groupForCongruence(const std::vector<const LoweredApplicationRecord*>& records)
{
  CongruenceGroups grouped;
  if (records.size() < 2)
    return grouped;
  const size_t arity = records.front()->loweredActuals.size();

  // Positions at which *every* application holds a constant. The quantifier
  // has to be "every", not "here": "these two cannot be shown distinct" is
  // not a transitive relation -- for arity two, (1,x), (1,2) and (3,2) relate
  // the first to the second and the second to the third but not the first to
  // the third -- so no partition models it. Restricting to positions that are
  // constant throughout is what makes it an equivalence, and is the same
  // restriction z3's reduce_args makes for the same reason.
  std::vector<bool> constantEverywhere(arity, true);
  for (const LoweredApplicationRecord* record : records)
    for (size_t i = 0; i < arity; ++i)
      if (!record->loweredActuals[i].isConstant())
        constantEverywhere[i] = false;

  std::map<ASTVec, size_t> partIndex;
  for (const LoweredApplicationRecord* record : records)
  {
    ASTVec key;
    for (size_t i = 0; i < arity; ++i)
      if (constantEverywhere[i])
        key.push_back(record->loweredActuals[i]);
    const auto found = partIndex.find(key);
    if (found == partIndex.end())
    {
      partIndex.emplace(key, grouped.parts.size());
      grouped.parts.push_back(CongruencePart());
      grouped.parts.back().records.push_back(record);
    }
    else
      grouped.parts[found->second].records.push_back(record);
  }

  for (CongruencePart& part : grouped.parts)
  {
    // Symbolic first, all-constant after, and the charge read off the same
    // split the walk will use. Written as one stable partition rather than
    // two counts so the two cannot drift: whatever ends up before `symbolic`
    // is exactly what the emit loop takes as its outer range.
    const auto boundary = std::stable_partition(
        part.records.begin(), part.records.end(),
        [](const LoweredApplicationRecord* record) {
          return !allActualsConstant(*record);
        });
    part.symbolic = (size_t)(boundary - part.records.begin());
    const uint64_t constantArgued = part.records.size() - part.symbolic;
    grouped.estimate +=
        pairsAmong(part.symbolic) + constantArgued * part.symbolic;
  }
  return grouped;
}

// What one argument position of a candidate pair contributes to the premise.
enum class PositionVerdict
{
  Distinct,  // the two actuals can never be equal: the pair needs no constraint
  Identical, // they always are: the premise atom is true and drops
  Unknown    // the premise atom has to be built
};

// A rational in two machine words, invalidated the moment anything overflows.
// It serves a pruner, and a pruner is free to give up: invalid means "cannot
// tell", which costs a pair that could have been dropped and can never produce
// a wrong answer. That is why none of this reaches for ExactRational, which
// would need a live NumberOperationScope and would charge the solve's
// arithmetic budget to decide a question whose wrong answer is only a missed
// optimisation.
struct SmallRational
{
  std::int64_t numerator;
  std::int64_t denominator;
  bool valid;
};

SmallRational smallRational(std::int64_t numerator)
{
  SmallRational value;
  value.numerator = numerator;
  value.denominator = 1;
  value.valid = true;
  return value;
}

SmallRational invalidRational()
{
  SmallRational value;
  value.numerator = 0;
  value.denominator = 1;
  value.valid = false;
  return value;
}

bool checkedAdd(std::int64_t left, std::int64_t right, std::int64_t& out)
{
  if (right > 0 && left > std::numeric_limits<std::int64_t>::max() - right)
    return false;
  if (right < 0 && left < std::numeric_limits<std::int64_t>::min() - right)
    return false;
  out = left + right;
  return true;
}

bool checkedMultiply(std::int64_t left, std::int64_t right, std::int64_t& out)
{
  if (left == 0 || right == 0)
  {
    out = 0;
    return true;
  }
  // Taking the magnitude of the minimum is itself the overflow, so refuse both
  // rather than reason about which of their products happen to fit.
  if (left == std::numeric_limits<std::int64_t>::min() ||
      right == std::numeric_limits<std::int64_t>::min())
    return false;
  const std::int64_t leftSize = left < 0 ? -left : left;
  const std::int64_t rightSize = right < 0 ? -right : right;
  if (leftSize > std::numeric_limits<std::int64_t>::max() / rightSize)
    return false;
  out = left * right;
  return true;
}

std::int64_t greatestCommonDivisor(std::int64_t left, std::int64_t right)
{
  while (right != 0)
  {
    const std::int64_t remainder = left % right;
    left = right;
    right = remainder;
  }
  return left < 0 ? -left : left;
}

// Lowest terms with a positive denominator, so that two equal values hold
// identical fields and compare equal field by field.
void reduce(SmallRational& value)
{
  if (!value.valid)
    return;
  if (value.denominator == 0 ||
      value.numerator == std::numeric_limits<std::int64_t>::min() ||
      value.denominator == std::numeric_limits<std::int64_t>::min())
  {
    value.valid = false;
    return;
  }
  if (value.numerator == 0)
  {
    value.denominator = 1;
    return;
  }
  const std::int64_t divisor =
      greatestCommonDivisor(value.numerator, value.denominator);
  if (divisor > 1)
  {
    value.numerator /= divisor;
    value.denominator /= divisor;
  }
  if (value.denominator < 0)
  {
    value.numerator = -value.numerator;
    value.denominator = -value.denominator;
  }
}

SmallRational addRational(const SmallRational& left, const SmallRational& right)
{
  SmallRational result = smallRational(0);
  std::int64_t leftScaled = 0;
  std::int64_t rightScaled = 0;
  if (!left.valid || !right.valid ||
      !checkedMultiply(left.numerator, right.denominator, leftScaled) ||
      !checkedMultiply(right.numerator, left.denominator, rightScaled) ||
      !checkedAdd(leftScaled, rightScaled, result.numerator) ||
      !checkedMultiply(left.denominator, right.denominator,
                       result.denominator))
    return invalidRational();
  reduce(result);
  return result;
}

SmallRational multiplyRational(const SmallRational& left,
                               const SmallRational& right)
{
  SmallRational result = smallRational(0);
  if (!left.valid || !right.valid ||
      !checkedMultiply(left.numerator, right.numerator, result.numerator) ||
      !checkedMultiply(left.denominator, right.denominator,
                       result.denominator))
    return invalidRational();
  reduce(result);
  return result;
}

SmallRational reciprocalRational(const SmallRational& value)
{
  if (!value.valid || value.numerator == 0)
    return invalidRational();
  SmallRational result;
  result.numerator = value.denominator;
  result.denominator = value.numerator;
  result.valid = true;
  reduce(result);
  return result;
}

bool sameRational(const SmallRational& left, const SmallRational& right)
{
  return left.valid && right.valid && left.numerator == right.numerator &&
         left.denominator == right.denominator;
}

bool parseDecimal(const std::string& text, std::int64_t& out)
{
  if (text.empty())
    return false;
  errno = 0;
  char* end = NULL;
  const long long parsed = std::strtoll(text.c_str(), &end, 10);
  if (errno != 0 || end == NULL || *end != '\0' || end == text.c_str())
    return false;
  out = static_cast<std::int64_t>(parsed);
  return true;
}

// The exact constant, if it fits two machine words. Its text is already the
// reduced canonical form the value table stores.
SmallRational readRealConstant(const ASTNode& node)
{
  SmallRational value;
  value.valid = true;
  if (!parseDecimal(node.GetRealNumerator(), value.numerator) ||
      !parseDecimal(node.GetRealDenominator(), value.denominator))
    return invalidRational();
  reduce(value);
  return value;
}

// One side of a candidate pair as coefficient * term + ... + constant. The map
// is keyed by interned node number, so equal keys are the identical term and
// two forms with equal maps differ by exactly their constants.
struct AffineForm
{
  std::map<std::uint64_t, SmallRational> terms;
  SmallRational constant;
  bool valid;

  AffineForm() : constant(smallRational(0)), valid(true) {}
};

void addAtom(AffineForm& form, const ASTNode& term,
             const SmallRational& coefficient)
{
  const std::uint64_t key = term.GetNodeNum();
  std::map<std::uint64_t, SmallRational>::iterator position =
      form.terms.find(key);
  if (position == form.terms.end())
  {
    form.terms.insert(std::make_pair(key, coefficient));
    return;
  }
  position->second = addRational(position->second, coefficient);
  if (!position->second.valid)
    form.valid = false;
}

// Linearise a Real term. Anything that is not Real arithmetic becomes an
// opaque atom, which is sound: a pair is pruned only when the two forms carry
// the *same* atoms with the same coefficients, so a term this walk cannot see
// into has to appear identically on both sides before it can affect a verdict.
//
// The fuel bounds the walk. A deep term spends its budget and reports Unknown,
// which is the same answer the walk would give for anything non-affine.
void linearise(const ASTNode& term, const SmallRational& scale,
               AffineForm& form, unsigned& fuel)
{
  if (!form.valid || !scale.valid)
  {
    form.valid = false;
    return;
  }
  if (fuel == 0)
  {
    form.valid = false;
    return;
  }
  --fuel;

  switch (term.GetKind())
  {
    case REAL_CONST:
      form.constant = addRational(form.constant,
                                  multiplyRational(readRealConstant(term),
                                                   scale));
      if (!form.constant.valid)
        form.valid = false;
      return;

    case REAL_ADD:
      for (size_t i = 0; i < term.Degree(); ++i)
        linearise(term[i], scale, form, fuel);
      return;

    case REAL_SUB:
    {
      // Degree one is negation, exactly as the exact frontend reads it.
      const SmallRational negated =
          multiplyRational(scale, smallRational(-1));
      if (term.Degree() == 1)
      {
        linearise(term[0], negated, form, fuel);
        return;
      }
      linearise(term[0], scale, form, fuel);
      for (size_t i = 1; i < term.Degree(); ++i)
        linearise(term[i], negated, form, fuel);
      return;
    }

    case REAL_NEG:
      linearise(term[0], multiplyRational(scale, smallRational(-1)), form,
                fuel);
      return;

    case REAL_MUL:
    {
      // The type check admits exactly one concrete operand.
      const bool leftConcrete = term[0].GetKind() == REAL_CONST;
      const ASTNode& concrete = leftConcrete ? term[0] : term[1];
      const ASTNode& symbolic = leftConcrete ? term[1] : term[0];
      if (concrete.GetKind() != REAL_CONST)
      {
        form.valid = false;
        return;
      }
      linearise(symbolic,
                multiplyRational(scale, readRealConstant(concrete)), form,
                fuel);
      return;
    }

    case REAL_DIV:
    {
      // The type check admits only a concrete non-zero divisor.
      if (term[1].GetKind() != REAL_CONST)
      {
        form.valid = false;
        return;
      }
      linearise(term[0],
                multiplyRational(scale,
                                 reciprocalRational(readRealConstant(term[1]))),
                form, fuel);
      return;
    }

    default:
      addAtom(form, term, scale);
      return;
  }
}

// Drop the atoms whose coefficients cancelled, and report whether every
// surviving coefficient is representable.
bool significantTerms(const AffineForm& form,
                      std::map<std::uint64_t, SmallRational>& out)
{
  for (std::map<std::uint64_t, SmallRational>::const_iterator entry =
           form.terms.begin();
       entry != form.terms.end(); ++entry)
  {
    if (!entry->second.valid)
      return false;
    if (entry->second.numerator != 0)
      out.insert(*entry);
  }
  return true;
}

// A half-line or segment of the reals, with each end open, closed or absent.
struct SmallInterval
{
  SmallRational lo;
  SmallRational hi;
  bool lo_inf;
  bool hi_inf;
  bool lo_open;
  bool hi_open;
};

SmallInterval wholeLine()
{
  SmallInterval interval;
  interval.lo = smallRational(0);
  interval.hi = smallRational(0);
  interval.lo_inf = true;
  interval.hi_inf = true;
  interval.lo_open = false;
  interval.hi_open = false;
  return interval;
}

// a < b, when the machine words can say.
bool rationalLess(const SmallRational& a, const SmallRational& b, bool& less)
{
  std::int64_t left = 0;
  std::int64_t right = 0;
  if (!a.valid || !b.valid ||
      !checkedMultiply(a.numerator, b.denominator, left) ||
      !checkedMultiply(b.numerator, a.denominator, right))
    return false;
  less = left < right;
  return true;
}

// What the query's top-level conjuncts say about each symbol on its own:
// x < c, x <= c, c < x, x = c and their negations, tightened together.
using UnitBounds = std::map<std::uint64_t, SmallInterval>;

void tightenLower(SmallInterval& interval, const SmallRational& value,
                  bool open)
{
  bool higher = false;
  if (interval.lo_inf ||
      (rationalLess(interval.lo, value, higher) && higher) ||
      (sameRational(interval.lo, value) && open))
  {
    interval.lo = value;
    interval.lo_inf = false;
    interval.lo_open = open;
  }
}

void tightenUpper(SmallInterval& interval, const SmallRational& value,
                  bool open)
{
  bool lower = false;
  if (interval.hi_inf ||
      (rationalLess(value, interval.hi, lower) && lower) ||
      (sameRational(interval.hi, value) && open))
  {
    interval.hi = value;
    interval.hi_inf = false;
    interval.hi_open = open;
  }
}

// One relation between a symbol and a constant, oriented as symbol REL
// constant, possibly under a negation.
void noteRelation(UnitBounds& bounds, Kind relation, bool negated,
                  const ASTNode& symbol, const ASTNode& constant)
{
  const SmallRational value = readRealConstant(constant);
  if (!value.valid)
    return;
  SmallInterval& interval =
      bounds.emplace(symbol.GetNodeNum(), wholeLine()).first->second;
  // Negating flips the relation and its openness: not (x < c) is x >= c.
  Kind effective = relation;
  if (negated)
    effective = relation == REAL_LT   ? REAL_GE
                : relation == REAL_LE ? REAL_GT
                : relation == REAL_GT ? REAL_LE
                                      : REAL_LT;
  switch (effective)
  {
    case REAL_LT: tightenUpper(interval, value, true); break;
    case REAL_LE: tightenUpper(interval, value, false); break;
    case REAL_GT: tightenLower(interval, value, true); break;
    case REAL_GE: tightenLower(interval, value, false); break;
    default: break;
  }
}

UnitBounds collectUnitBounds(const ASTNode& root)
{
  UnitBounds bounds;
  std::vector<ASTNode> pending;
  pending.push_back(root);
  while (!pending.empty())
  {
    ASTNode conjunct = pending.back();
    pending.pop_back();
    if (conjunct.GetKind() == AND)
    {
      for (size_t i = 0; i < conjunct.Degree(); ++i)
        pending.push_back(conjunct[i]);
      continue;
    }
    bool negated = false;
    if (conjunct.GetKind() == NOT)
    {
      negated = true;
      conjunct = conjunct[0];
    }
    const Kind kind = conjunct.GetKind();
    if (conjunct.Degree() != 2)
      continue;
    const ASTNode& a = conjunct[0];
    const ASTNode& b = conjunct[1];
    if (kind == REAL_LT || kind == REAL_LE || kind == REAL_GT ||
        kind == REAL_GE)
    {
      if (a.GetKind() == SYMBOL && b.GetKind() == REAL_CONST)
        noteRelation(bounds, kind, negated, a, b);
      else if (a.GetKind() == REAL_CONST && b.GetKind() == SYMBOL)
        // c < x is x > c: mirror the relation.
        noteRelation(bounds,
                     kind == REAL_LT   ? REAL_GT
                     : kind == REAL_LE ? REAL_GE
                     : kind == REAL_GT ? REAL_LT
                                       : REAL_LE,
                     negated, b, a);
    }
    else if (kind == EQ && !negated)
    {
      // x = c pins x; x != c says nothing an interval can hold.
      if (a.GetKind() == SYMBOL && b.GetKind() == REAL_CONST)
      {
        noteRelation(bounds, REAL_LE, false, a, b);
        noteRelation(bounds, REAL_GE, false, a, b);
      }
      else if (a.GetKind() == REAL_CONST && b.GetKind() == SYMBOL)
      {
        noteRelation(bounds, REAL_LE, false, b, a);
        noteRelation(bounds, REAL_GE, false, b, a);
      }
    }
  }
  return bounds;
}

// The interval a linear form ranges over, from the unit bounds on its atoms.
// An atom with no bound, or arithmetic that overflows, makes the whole line.
SmallInterval intervalOf(const std::map<std::uint64_t, SmallRational>& terms,
                         const SmallRational& constant, const UnitBounds& bounds)
{
  SmallInterval result = wholeLine();
  result.lo = constant;
  result.hi = constant;
  result.lo_inf = false;
  result.hi_inf = false;
  for (const auto& term : terms)
  {
    const auto found = bounds.find(term.first);
    if (found == bounds.end())
      return wholeLine();
    SmallInterval scaled = found->second;
    const SmallRational& coefficient = term.second;
    if (coefficient.numerator < 0)
    {
      std::swap(scaled.lo, scaled.hi);
      std::swap(scaled.lo_inf, scaled.hi_inf);
      std::swap(scaled.lo_open, scaled.hi_open);
    }
    if (!scaled.lo_inf)
      scaled.lo = multiplyRational(scaled.lo, coefficient);
    if (!scaled.hi_inf)
      scaled.hi = multiplyRational(scaled.hi, coefficient);
    result.lo_inf = result.lo_inf || scaled.lo_inf;
    result.hi_inf = result.hi_inf || scaled.hi_inf;
    if (!result.lo_inf)
      result.lo = addRational(result.lo, scaled.lo);
    if (!result.hi_inf)
      result.hi = addRational(result.hi, scaled.hi);
    result.lo_open = result.lo_open || scaled.lo_open;
    result.hi_open = result.hi_open || scaled.hi_open;
    if ((!result.lo_inf && !result.lo.valid) ||
        (!result.hi_inf && !result.hi.valid))
      return wholeLine();
  }
  return result;
}

// Whether every point of `a` lies strictly before every point of `b`.
bool entirelyBefore(const SmallInterval& a, const SmallInterval& b)
{
  if (a.hi_inf || b.lo_inf)
    return false;
  bool less = false;
  if (!rationalLess(a.hi, b.lo, less))
    return false;
  if (less)
    return true;
  return sameRational(a.hi, b.lo) && (a.hi_open || b.lo_open);
}

// Decide a Real argument position by linear arithmetic instead of asking the
// node factory, which holds no Real rewrites at all: every symbolic Real pair
// reaches it as Unknown, so f(i) against f(i+1) used to cost an atom and a
// constraint whose premise is unsatisfiable. Two forms over the same atoms
// with the same coefficients differ by exactly their constants, which settles
// the sliding-offset shape without building anything.
PositionVerdict compareRealPosition(const ASTNode& left, const ASTNode& right,
                                    const UnitBounds* bounds)
{
  unsigned fuel = 256;
  AffineForm leftForm;
  AffineForm rightForm;
  linearise(left, smallRational(1), leftForm, fuel);
  linearise(right, smallRational(1), rightForm, fuel);
  if (!leftForm.valid || !rightForm.valid || !leftForm.constant.valid ||
      !rightForm.constant.valid)
    return PositionVerdict::Unknown;

  std::map<std::uint64_t, SmallRational> leftTerms;
  std::map<std::uint64_t, SmallRational> rightTerms;
  if (!significantTerms(leftForm, leftTerms) ||
      !significantTerms(rightForm, rightTerms))
    return PositionVerdict::Unknown;
  bool sameTerms = leftTerms.size() == rightTerms.size();
  if (sameTerms)
  {
    std::map<std::uint64_t, SmallRational>::const_iterator leftEntry =
        leftTerms.begin();
    std::map<std::uint64_t, SmallRational>::const_iterator rightEntry =
        rightTerms.begin();
    for (; leftEntry != leftTerms.end(); ++leftEntry, ++rightEntry)
      if (leftEntry->first != rightEntry->first ||
          !sameRational(leftEntry->second, rightEntry->second))
      {
        sameTerms = false;
        break;
      }
  }
  if (sameTerms)
    return sameRational(leftForm.constant, rightForm.constant)
               ? PositionVerdict::Identical
               : PositionVerdict::Distinct;

  // Different terms. The query's own unit bounds may still keep the two
  // apart: a pair whose ranges do not meet can never be equal, and a pair
  // pinned to one and the same point always is. A range that touches at a
  // closed end is not apart -- that point is where they can meet.
  if (bounds == NULL)
    return PositionVerdict::Unknown;
  const SmallInterval a = intervalOf(leftTerms, leftForm.constant, *bounds);
  const SmallInterval b = intervalOf(rightTerms, rightForm.constant, *bounds);
  if (entirelyBefore(a, b) || entirelyBefore(b, a))
    return PositionVerdict::Distinct;
  if (!a.lo_inf && !a.hi_inf && !b.lo_inf && !b.hi_inf &&
      !a.lo_open && !a.hi_open && !b.lo_open && !b.hi_open &&
      sameRational(a.lo, a.hi) && sameRational(b.lo, b.hi) &&
      sameRational(a.lo, b.lo))
    return PositionVerdict::Identical;
  return PositionVerdict::Unknown;
}

// Ask the *lowered* actuals, not the named ones. A compound actual is named by
// a fresh symbol, so asking the names can only ever catch two literal
// constants -- which is why a function applied at a sliding offset, f(i),
// f(i+1), ..., got a full C(n,2) set of constraints whose premises are all
// unsatisfiable. The lowered terms hand the question to the node factory,
// which already cancels a common addend out of two BVPLUSes and folds
// (= (bvadd i 1) (bvadd i 2)) to false on its own.
//
// Whatever the factory cannot decide stays Unknown, so a factory without those
// rewrites (the C API's default hashing factory) simply prunes nothing. The
// premise is still stated over the named actuals: only the *test* moves.
PositionVerdict comparePosition(NodeFactory* factory, const ASTNode& left,
                                const ASTNode& right, const SourceSort& sort,
                                const UnitBounds* bounds)
{
  // Interning makes equal constants one node, so the first two tests are
  // exact and hold whatever factory is installed -- the C API leaves the
  // plain hashing factory in place, and it folds nothing.
  if (left == right)
    return PositionVerdict::Identical;
  if (left.isConstant() && right.isConstant())
    return PositionVerdict::Distinct;
  // Real is asked by linear arithmetic first: the factory has no Real
  // rewrites, so it can only ever answer Unknown here. A verdict it cannot
  // reach still falls through to it, so this only ever adds power.
  if (sort.kind() == SourceSort::Kind::Real)
  {
    const PositionVerdict linear = compareRealPosition(left, right, bounds);
    if (linear != PositionVerdict::Unknown)
      return linear;
  }
  const ASTNode folded = factory->CreateNode(
      sort.kind() == SourceSort::Kind::Bool ? IFF : EQ, left, right);
  if (folded.GetKind() == TRUE)
    return PositionVerdict::Identical;
  if (folded.GetKind() == FALSE)
    return PositionVerdict::Distinct;
  return PositionVerdict::Unknown;
}

} // namespace

// Optional eager congruence. The policy may select every declaration or a
// cost-bounded subset, while the dynamic checker remains available to catch
// any missed conflict. The constraints are built as AST and conjoined to the
// semantic root rather than encoded straight to CNF, which buys three things:
// both solve modes pick them up through the one function that already attaches
// naming definitions, a persistent block inherits its guard with no new guard
// logic, and ordinary preprocessing gets to simplify or delete constraints
// whose results nothing constrains.
// A signature the value-based checker cannot police: its Real positions have
// no bits for it to compare. Such a declaration is decided by the lazy round
// from the arithmetic's model (isLazyCongruenceSignature below), or, where a
// float position rules that out, its constraints have to be installed here,
// whatever the policy would otherwise have decided about cost.
static bool hasRealPosition(const stp::UFSignature& signature)
{
  if (signature.codomain().kind() == stp::SourceSort::Kind::Real)
    return true;
  for (size_t i = 0; i < signature.domain().size(); ++i)
    if (signature.domain()[i].kind() == stp::SourceSort::Kind::Real)
      return true;
  return false;
}

// A signature whose congruence is decided from a committed model rather than
// stated in advance. Any position with a Real in it qualifies the signature,
// because that is the position the value-based checker cannot police; what
// the lazy round then needs is a value for every position, and a committed
// model has one for each: the arithmetic's exact rational for a Real, the
// counterexample's constant for a bit-vector or a Boolean, or for a sort that
// lowers to a bit-vector carrier. Stating congruence in advance would cost an
// equality atom per pair, which is a row and a slack variable in the tableau
// before the search has run once.
//
// A float position keeps the signature eager. Its carrier's bit-equality is
// not its equality -- one NaN is many patterns, and two zeros are one value
// -- so grouping applications by carrier value would decide the wrong thing.
static bool isLazyCongruenceSignature(const stp::UFSignature& signature)
{
  return hasRealPosition(signature) && !hasFloatingPointPosition(signature);
}

// A solve scalar is a symbol the checker reads out of the SAT model, bit by
// bit. A Real has no bits: its value is an exact rational the arithmetic
// holds, and the SAT model says nothing about it. Such a symbol is still
// protected from preprocessing -- lemmas name it -- but it is never
// registered for bit-level readback, and congruence over it is decided from
// the arithmetic's exact value instead of from a bit pattern.
static bool isBitReadableScalar(const stp::ASTNode& symbol)
{
  return symbol.GetSourceSort().kind() != stp::SourceSort::Kind::Real;
}

void UFLowering::installEagerCongruence(
    LoweredApplicationView& view, const std::set<const UFDecl*>& injectable,
    const ASTNode& guard) const
{
  PreparationPoller poll(manager_->preparation_control, PreparationStage::UFLowering);
  typedef UserDefinedFlags::UFEagerMode Mode;
  const Mode mode = manager_->UserFlags.uf_eager_mode;
  view.eagerStats.budget = manager_->UserFlags.uf_eager_budget;
  // A Real signature the lazy round cannot decide -- one with a float
  // position -- is not the policy's to decline: the checker cannot see its
  // values, so anything not installed here is simply not enforced. Run
  // whenever one is present, even with the policy off.
  bool anyRealSignature = false;
  for (const LoweredApplicationRecord& record : view.applications)
    if (hasRealPosition(record.declaration->signature()) &&
        !isLazyCongruenceSignature(record.declaration->signature()))
      anyRealSignature = true;
  if ((mode == Mode::OFF && !anyRealSignature) || view.applications.empty())
    return;
  view.eagerStats.policyRan = true;

  std::map<const UFDecl*, std::vector<const LoweredApplicationRecord*>>
      byDeclaration;
  for (const LoweredApplicationRecord& record : view.applications)
  {
    poll();
    // A record with no readable argument tuple belongs to a declaration with
    // one application, which has no pairs to constrain anyway.
    if (!record.observableArguments)
      continue;
    // A declaration the lazy round can decide is decided from committed
    // models instead, one earned pair at a time, unless eager was asked for
    // by name.
    if (mode != Mode::ON &&
        isLazyCongruenceSignature(record.declaration->signature()))
      continue;
    byDeclaration[record.declaration].push_back(&record);
  }

  // Cost of each candidate declaration, cheapest first: two applications
  // whose actuals are all constants are either the same durable handle or
  // differ in some position, so they never need a constraint between them.
  std::vector<std::pair<uint64_t, const UFDecl*>> selection;
  std::map<const UFDecl*, size_t> statIndex;
  std::map<const UFDecl*, CongruenceGroups> groupsByDeclaration;
  for (const auto& entry : byDeclaration)
  {
    poll();
    const CongruenceGroups grouped = groupForCongruence(entry.second);
    const uint64_t cost = grouped.estimate;
    groupsByDeclaration.emplace(entry.first, grouped);

    UFEagerDeclarationStat stat;
    stat.name = entry.first->name();
    stat.applications = entry.second.size();
    stat.estimatedPairs = cost;
    stat.outcome = UFEagerDeclarationStat::Outcome::NoComparablePairs;
    statIndex[entry.first] = view.eagerStats.declarations.size();
    view.eagerStats.declarations.push_back(stat);

    if (cost != 0)
      selection.push_back(std::make_pair(cost, entry.first));
  }
  // Cheapest first, but every floating-point signature after every
  // bit-vector one whatever they cost.
  //
  // A float pair is worth less than a bit-vector pair of the same count: the
  // query's own (= a b) over bit-vectors is a substitutable equality, so
  // equality propagation collapses the actuals and the constraints dissolve
  // before SAT, while over floats it is FP_SMT_EQ, a predicate, and every
  // constraint is paid in full. Sorting floats last is what that difference
  // buys them -- they take whatever budget is left rather than competing for
  // it, so the declarations a pure bit-vector query selects are exactly the
  // ones it selected when floats were refused outright, and a cheap float
  // declaration can no longer push an expensive bit-vector one over the line.
  std::sort(selection.begin(), selection.end(),
            [](const std::pair<uint64_t, const UFDecl*>& left,
               const std::pair<uint64_t, const UFDecl*>& right) {
              const bool leftFloat =
                  hasFloatingPointPosition(left.second->signature());
              const bool rightFloat =
                  hasFloatingPointPosition(right.second->signature());
              if (leftFloat != rightFloat)
                return rightFloat;
              if (left.first != right.first)
                return left.first < right.first;
              return left.second->id() < right.second->id();
            });

  NodeFactory* const factory = manager_->defaultNodeFactory;
  const UnitBounds unitBounds = collectUnitBounds(view.semanticRoot);
  uint64_t budget = manager_->UserFlags.uf_eager_budget;
  for (const std::pair<uint64_t, const UFDecl*>& candidate : selection)
  {
    poll();
    UFEagerDeclarationStat& stat =
        view.eagerStats.declarations[statIndex[candidate.second]];
    if (mode == Mode::AUTO && !hasRealPosition(candidate.second->signature()))
    {
      // A float pair is worth less than a bit-vector pair of the same
      // count, which is why the ordering above puts every float signature
      // after every bit-vector one: they take what is left rather than
      // competing for it. Where the actuals are bit-vectors the query's own
      // (= a b) is a substitutable equality, so equality propagation
      // collapses them and the constraints dissolve before SAT; where they
      // are floats it is FP_SMT_EQ, a predicate, and every constraint is paid
      // in full.
      //
      // They used to be refused outright, which was right while the budget
      // was 4096: that admitted a float declaration of up to 91 applications,
      // and the shape the refusal was reasoned from -- actuals asserted
      // equal, results distinct -- costs eager 1.6s and climbing at that
      // size. At 256 the budget admits at most 23 float applications, and
      // measured across that whole band the refusal costs more than it saves:
      // the shape it protected loses 0.04s at the top of the band, while free
      // float arguments with distinct results gain 0.52s, and a float
      // codomain over a bit-vector domain, a NaN-heavy query and compound
      // float actuals are each within 0.1s or favour selecting. The budget,
      // not a veto, is what keeps the bad shape cheap now, and it truncates
      // that shape before its superlinear part begins.
      if (candidate.first > budget)
      {
        // Pass over this one and keep going. Stopping here would be right if
        // the order were cheapest-first throughout, but it is cheapest-first
        // within the bit-vector signatures and then again within the float
        // ones, so a bit-vector declaration that does not fit says nothing
        // about the floats queued behind every bit-vector one. Stopping was
        // what made "floats take what is left" untrue: a float declaration of
        // ten pairs was passed over because a bit-vector declaration of three
        // hundred came first, while the same ten-pair declaration was selected
        // when its signature was bit-vectors. It also left the float one
        // labelled as having had no comparable pairs on a line that reported
        // ten.
        stat.outcome = UFEagerDeclarationStat::Outcome::DeclinedBudget;
        continue;
      }
      budget -= candidate.first;
      view.eagerStats.budgetSpent += candidate.first;
    }
    stat.outcome = UFEagerDeclarationStat::Outcome::Selected;

    // Walk exactly what was charged for, and nothing else. Two kinds of pair
    // are charged nothing because they can produce nothing, and each has to be
    // skipped by not being iterated rather than by being tested and dropped --
    // a test still costs a loop step, and the counts here reach billions.
    //
    // Across parts: the pair differs at a position where both hold constants.
    // Within a part, between two all-constant applications: they are either
    // the same durable handle or they differ somewhere, and where they differ
    // both hold constants again. The outer range is therefore the part's
    // symbolic prefix, which makes the walk C(symbolic, 2) + constant *
    // symbolic -- the estimate, term for term.
    //
    // Counting them instead is not a small waste. One part of 60 000
    // all-constant applications is charged one pair and was enumerated
    // 1 799 970 001 times, 20.5 s against 1.5 s with the policy off, and it
    // grew quadratically from there.
    const UFSignature& signature = candidate.second->signature();
    for (const CongruencePart& part : groupsByDeclaration[candidate.second].parts)
    {
      poll();
    const std::vector<const LoweredApplicationRecord*>& records = part.records;
    for (size_t i = 0; i < part.symbolic; ++i)
      for (size_t j = i + 1; j < records.size(); ++j)
      {
        poll();
        const LoweredApplicationRecord& left = *records[i];
        const LoweredApplicationRecord& right = *records[j];
        stat.enumeratedPairs++;
        ASTVec premise;
        bool impossible = false;
        for (size_t k = 0; k < signature.arity() && !impossible; ++k)
        {
          poll();
          const SourceSort solved =
              UFSignature::loweringSort(signature.domain()[k]);
          switch (comparePosition(factory, left.loweredActuals[k],
                                  right.loweredActuals[k], solved,
                                  &unitBounds))
          {
            case PositionVerdict::Identical:
              continue; // the premise atom is true and drops
            case PositionVerdict::Distinct:
              // These two can never be congruent, so the pair needs no
              // constraint at all.
              impossible = true;
              continue;
            case PositionVerdict::Unknown:
              break;
          }
          premise.push_back(factory->CreateNode(
              solved.kind() == SourceSort::Kind::Bool ? IFF : EQ,
              left.namedActuals[k], right.namedActuals[k]));
        }
        if (impossible)
        {
          stat.skippedImpossiblePairs++;
          continue;
        }
        stat.emittedConstraints++;

        const ASTNode conclusion = factory->CreateNode(
            signature.codomain().kind() == SourceSort::Kind::Bool ? IFF : EQ,
            left.resultSymbol, right.resultSymbol);
        const ASTNode premiseConj =
            premise.empty()
                ? ASTNode()
                : premise.size() == 1
                      ? premise[0]
                      : factory->CreateNode(AND, premise);
        manager_->UserFlags.coverage.uf_constraints_installed++;
        view.congruenceConstraints.push_back(
            premise.empty()
                ? conclusion
                : factory->CreateNode(IMPLIES, premiseConj, conclusion));

        if (!premise.empty() &&
            injectable.count(candidate.second) != 0)
        {
          // The converse of congruence, and the one constraint here that is
          // not entailed by the query: it says this declaration is injective
          // on the pair, which the caller never asserted. It goes in behind
          // the activation symbol so that a refutation resting on it can be
          // taken back rather than reported -- see
          // STPMgr::solveRetractingInjectivity. Counted separately, because
          // the guard is only sound if every one of them is behind it, and a
          // driver with no way to assume the guard has to know that these
          // exist at all.
          stat.emittedInjectivity++;
          const ASTNode converse =
              factory->CreateNode(IMPLIES, conclusion, premiseConj);
          manager_->UserFlags.coverage.uf_constraints_installed++;
          view.congruenceConstraints.push_back(
              guard.IsNull() ? converse
                             : factory->CreateNode(IMPLIES, guard, converse));
        }
      }
    }
  }
}

// Observability for the eager policy. Without this the only way to tell a
// declined declaration from one that had nothing to install is to edit a flag
// and compare wall clock, which is how every calibration of this policy has
// had to be done. One line per declaration that had pairs to consider, plus a
// total; nothing is printed when the policy did not run.
void UFLowering::reportEagerCongruence(const LoweredApplicationView& view) const
{
  if (!manager_->UserFlags.stats_flag)
    return;
  const UFEagerStats& stats = view.eagerStats;
  if (!stats.policyRan)
  {
    if (!view.applications.empty())
      std::cerr << "UF: eager congruence policy off, "
                << view.applications.size() << " application(s) left to the "
                << "refinement loop" << std::endl;
    return;
  }
  // By name, not in the order the declarations were collected: that order is
  // the address order of the declaration records, so it varies between two
  // runs of the same query and between two queries of the same shape. A
  // fixture that reads one line after another was pinning the allocator.
  std::vector<const UFEagerDeclarationStat*> ordered;
  ordered.reserve(stats.declarations.size());
  for (const UFEagerDeclarationStat& stat : stats.declarations)
    ordered.push_back(&stat);
  std::stable_sort(ordered.begin(), ordered.end(),
                   [](const UFEagerDeclarationStat* left,
                      const UFEagerDeclarationStat* right) {
                     return left->name < right->name;
                   });
  for (const UFEagerDeclarationStat* entry : ordered)
  {
    const UFEagerDeclarationStat& stat = *entry;
    if (stat.estimatedPairs == 0)
      continue;
    std::cerr << "UF: eager " << stat.outcomeName() << " " << stat.name << " ("
              << stat.applications << " applications, " << stat.estimatedPairs
              << " pairs estimated";
    if (stat.outcome == UFEagerDeclarationStat::Outcome::Selected)
      std::cerr << ", " << stat.enumeratedPairs << " enumerated, "
                << stat.skippedImpossiblePairs << " impossible, "
                << stat.emittedConstraints << " constraints";
    std::cerr << ")" << std::endl;
  }
  std::cerr << "UF: eager total " << stats.selectedDeclarations() << "/"
            << stats.declarations.size() << " declarations, "
            << stats.emittedConstraints() << " constraints, budget "
            << stats.budgetSpent << "/" << stats.budget << " spent"
            << std::endl;
  if (stats.emittedInjectivity() != 0)
    std::cerr << "UF: eager " << stats.emittedInjectivity()
              << " of those assume injectivity (--uf-inject-args), behind one "
              << "guard the search can be asked about and withdraw"
              << std::endl;
}

LoweredApplicationView
UFLowering::lowerCompletedRoot(const ASTNode& publicRoot,
                               const UFSolveScope& scope) const
{
  PreparationPoller poll(manager_->preparation_control, PreparationStage::UFLowering);
  if (publicRoot.IsNull() || !publicRoot.IsOwnedBy(manager_))
    FatalError("UF lowering requires a completed root owned by its context");

  LoweredApplicationView view;
  view.scope = scope;
  view.publicRoot = publicRoot;
  view.semanticRoot = publicRoot;

  UFContext* context = manager_->getUFContextIfAny();
  if (!manager_->UserFlags.enable_uninterpreted_functions)
  {
    if (context != NULL)
      context->releaseSolveProtection();
    return view;
  }

  if (context == NULL)
  {
    if (containsKind(publicRoot, UF_APPLY))
      FatalError("UF lowering found UF_APPLY without a manager context",
                 publicRoot);
    return view;
  }
  context->beginSolveProtection();

  // Pre-analysis: detect UF declarations whose results are used only for
  // equality with other results of the same declaration. Their result sort
  // can be narrowed from the declared width to ceil(log2(N+1)) bits,
  // cutting the AIG cost of every congruence constraint from O(width) to
  // O(log N).
  NarrowAnalysis narrowing;
  if (manager_->UserFlags.uf_narrow_results ||
      manager_->UserFlags.uf_inject_args)
    narrowing = analyzeNarrowability(publicRoot, context, poll);

  // A name is canonical per lowered expression, matching the reference
  // oracle. This both avoids redundant definitions and makes an identical
  // persistent block reconstruct the identical semantic root.
  ASTNodeMap scalarNames;

  // Pin every RoundingMode scalar this lowering makes the checker's authority
  // for -- introduced results, introduced argument names, and the leaf
  // symbols it registers as solve scalars in their own right. The sort has
  // five values and its carrier thirty-two, so an unpinned one lets a model
  // name no mode at all: the generated define-fun would print a term of no
  // sort, and model evaluation could hand an illegal mode to an enclosing
  // floating-point operation as a constant operand.
  //
  // FpTotalise pins the same symbols out of the semantic root when it runs,
  // and an OR of five equalities is idempotent, so at worst this adds a
  // duplicate conjunct. What it buys is that the pin arrives with the symbol
  // instead of with a later pass: the persistent path decides whether to run
  // that pass from the *raw* block, and reset-assertions can retract a
  // declaration's own pin while keeping the declaration.
  //
  // Pins are appended in walk order rather than collected from
  // view.solveScalars, so that an identical block rebuilds an identical
  // conjunction without depending on a hash set's iteration order.
  ASTNodeSet pinnedRoundingModes;
  const auto pinIfRoundingMode = [&](const ASTNode& scalar) {
    if (!manager_->isRoundingModeSymbol(scalar) ||
        !pinnedRoundingModes.insert(scalar).second)
      return;
    view.sortConstraints.push_back(
        manager_->roundingModeValidConstraint(scalar));
  };

  // An actual, as the checker will compare it. Only a float moves: it becomes
  // its canonical packed bits, which is the sort's own equality rather than
  // the carrier's, so two NaNs of different payloads compare equal and the
  // two zeros stay apart. A constant takes the same boundary as everything
  // else -- it needs no special case, because a float constant is already
  // interned canonically (STPMgr::CreateFPConst quotients NaN) and the
  // boundary folds over it rather than building a circuit.
  const auto canonicalActual = [&](const ASTNode& lowered,
                                   const SourceSort& declared) -> ASTNode {
    if (declared.kind() != SourceSort::Kind::FloatingPoint)
      return lowered;
    return manager_->defaultNodeFactory->CreateTerm(
        FP_TO_IEEE_BV, declared.packedWidth(), lowered);
  };

  // A result, as the formula that replaces the application will see it. The
  // exact inverse of canonicalActual: the three-child to_fp reinterprets the
  // solved bits at the declared format.
  const auto theoryResult = [&](const ASTNode& result,
                                const SourceSort& declared) -> ASTNode {
    if (declared.kind() != SourceSort::Kind::FloatingPoint)
      return result;
    const ASTNode reinterpreted = manager_->defaultNodeFactory->CreateTerm(
        FP_TOFP, declared.packedWidth(),
        manager_->CreateBVConst(32, declared.exponentWidth()),
        manager_->CreateBVConst(32, declared.significandWidth()), result);
    if (reinterpreted.GetSourceSort() != declared)
      FatalError("UF lowering rebuilt a float result at the wrong SourceSort",
                 reinterpreted);
    return reinterpreted;
  };

  std::set<const UFDecl*> reportedNarrow;

  // A compound actual cannot be named while the walk is running: whether the
  // name is needed depends on how many applications its declaration turns out
  // to have, and the last of them may not have been reached yet. Each one is
  // parked here against the slot it will fill.
  struct PendingName
  {
    size_t record;
    size_t argument;
    ASTNode lowered;
    SourceSort sort;
  };
  std::vector<PendingName> pendingNames;

  // Rewrite the completed root once, bottom-up. The explicit walk keeps its
  // frames on the heap (input controls AST depth), visits each shared DAG node
  // once, and guarantees that a nested UF application has become its scalar
  // result before an enclosing application's actual is recorded.
  DenseNodeMap rewritten;
  view.semanticRoot = postOrderRebuild(
      publicRoot, rewritten,
      [&](const ASTNode& application, const ASTVec& loweredChildren) -> ASTNode
      {
        if (application.GetKind() != UF_APPLY)
          return rebuildWithChildren(application, loweredChildren, manager_);

        std::string diagnostic;
        if (!context->isRegisteredApplication(application) ||
            !context->validateApplicationChildren(application.GetChildren(),
                                                  &diagnostic))
          FatalError(("UF lowering rejected a malformed durable application: " +
                      diagnostic)
                         .c_str(),
                     application);
        if (!context->isActiveApplication(application))
          FatalError("UF lowering rejected a stale or inactive durable "
                     "application",
                     application);

        const UFDecl* declaration = context->lookupIdentity(application[0]);
        if (declaration == NULL)
          FatalError("UF lowering could not recover declaration identity",
                     application);
        if (loweredChildren.size() != application.Degree() ||
            loweredChildren.empty() || loweredChildren[0] != application[0])
          FatalError("UF lowering rewrote a declaration identity", application);

        LoweredApplicationRecord record;
        record.durableHandle = application;
        record.declaration = declaration;
        record.scope = scope;
        record.stableOrder = view.applications.size();
        record.loweredActuals.reserve(application.Degree() - 1);
        record.namedActuals.reserve(application.Degree() - 1);

        for (size_t i = 1; i < loweredChildren.size(); ++i)
        {
          poll();
          const ASTNode& lowered = loweredChildren[i];
          const SourceSort& expected = declaration->signature().domain()[i - 1];
          if (application[i].GetSourceSort() != expected ||
              lowered.GetSourceSort() != expected)
            FatalError("UF lowering crossed a SourceSort boundary",
                       application);

          // From here down the record speaks the lowering sort. For every
          // sort but FloatingPoint that is the declared sort unchanged; a
          // float crosses into its canonical packed carrier here and does not
          // cross back until the model boundary.
          const SourceSort solved = UFSignature::loweringSort(expected);
          const ASTNode scalar = canonicalActual(lowered, expected);
          if (scalar.GetSourceSort() != solved)
            FatalError("UF lowering produced an actual at the wrong lowering "
                       "sort",
                       scalar);
          record.loweredActuals.push_back(scalar);

          if (isLeafActual(scalar))
          {
            record.namedActuals.push_back(scalar);
            // A source symbol is already its own canonical scalar name, but it
            // still participates in future direct-CNF lemmas. Protect/register it
            // exactly like an introduced name so ordinary preprocessing cannot
            // substitute it away and leave the lemma talking about an unlinked
            // fresh SAT value. Constants need no mapping or protection.
            if (scalar.GetKind() == SYMBOL)
            {
              view.protectedSymbols.insert(scalar);
              if (isBitReadableScalar(scalar))
                view.solveScalars.insert(scalar);
              pinIfRoundingMode(scalar);
            }
            continue;
          }

          PendingName pending;
          pending.record = record.stableOrder;
          pending.argument = record.namedActuals.size();
          pending.lowered = scalar;
          pending.sort = solved;
          pendingNames.push_back(pending);
          record.namedActuals.push_back(ASTNode());
        }

        const SourceSort& codomain = declaration->signature().codomain();
        if (application.GetSourceSort() != codomain)
          FatalError("UF lowering found a durable result with the wrong "
                     "SourceSort",
                     application);
        SourceSort solvedCodomain = UFSignature::loweringSort(codomain);
        // The name a narrowed result gets has to say how wide it is. The
        // deterministic namespace keys a symbol on the application alone, and
        // its contract is that the key settles the sort -- one key, one
        // symbol, one sort, so that an identical block rebuilds an identical
        // root. A narrowed width does not keep that bargain: it is read off
        // how many applications the *current* root has, and the same durable
        // application is lowered again in the next solve with a different
        // count behind it. Two applications of f under a push, three after
        // the pop, and the same handle wants one bit and then two.
        //
        // So the width joins the key rather than silently disagreeing with
        // it. Only a result that was actually narrowed is tagged, which
        // leaves every unnarrowed name exactly as it was -- including the
        // rounding-mode results a persistent block has to rebuild and re-pin
        // by name.
        std::string resultPrefix = "uf_result";
        if (manager_->UserFlags.uf_narrow_results &&
            solvedCodomain.kind() == SourceSort::Kind::BitVector &&
            narrowing.nonNarrowable.count(declaration) == 0)
        {
          auto it = narrowing.applicationCount.find(declaration);
          if (it != narrowing.applicationCount.end())
          {
            const unsigned narrowWidth =
                bitsForDistinct(it->second);
            if (narrowWidth < solvedCodomain.bitVectorWidth())
            {
              solvedCodomain = SourceSort::bitVector(narrowWidth);
              resultPrefix += "_w" + std::to_string(narrowWidth);
              if (manager_->UserFlags.stats_flag &&
                  reportedNarrow.insert(declaration).second)
                std::cerr << "UF: narrowing result of "
                          << declaration->name() << " from "
                          << codomain.bitVectorWidth() << " to "
                          << narrowWidth << " bits (" << it->second
                          << " applications)" << std::endl;
            }
          }
        }
        record.resultSymbol = manager_->CreateDeterministicSourceVariable(
            solvedCodomain, resultPrefix, application);
        if (record.resultSymbol.GetSourceSort() != solvedCodomain)
          FatalError("UF lowering allocated a result at the wrong SourceSort",
                     record.resultSymbol);
        view.protectedSymbols.insert(record.resultSymbol);
        if (isBitReadableScalar(record.resultSymbol))
          view.solveScalars.insert(record.resultSymbol);
        pinIfRoundingMode(record.resultSymbol);
        view.handleToResult.insert(
            std::make_pair(application, record.resultSymbol));
        view.applications.push_back(record);
        manager_->UserFlags.coverage.uf_applications_lowered++;
        // A float result is solved as a packed bit-vector but the formula it
        // replaces expects a float, so it goes back in through the exact
        // inverse of the boundary its arguments came through: the three-child
        // "reinterpret these bits" to_fp. Every other sort is returned as
        // itself.
        return theoryResult(record.resultSymbol, codomain);
      }, [&poll] { poll(); });

  // Only a declaration with two or more lowered applications can ever produce
  // a congruence lemma, and a name for a compound actual exists solely so that
  // such a lemma has a scalar to equate. Naming one for a lone application
  // costs a protected symbol and a defining equality that drag the whole
  // argument expression into the bit-blast, where nothing can observe it.
  //
  // Two rounds, so that the decision does not depend on the order the walk
  // reached things: every name a comparable record needs is created first, and
  // a lone application sharing one of those terms then reuses it and stays
  // readable for free. Only an actual left without a name after both rounds
  // makes its record unobservable.
  std::map<const UFDecl*, size_t> applicationsPerDeclaration;
  for (const LoweredApplicationRecord& record : view.applications)
  {
    poll();
    applicationsPerDeclaration[record.declaration]++;
  }

  const auto comparable = [&](const PendingName& pending) {
    return applicationsPerDeclaration[view.applications[pending.record]
                                          .declaration] > 1;
  };

  for (const PendingName& pending : pendingNames)
  {
    poll();
    if (!comparable(pending))
      continue;
    ASTNode name;
    const ASTNodeMap::const_iterator found = scalarNames.find(pending.lowered);
    if (found != scalarNames.end())
      name = found->second;
    else
    {
      name = manager_->CreateDeterministicSourceVariable(pending.sort, "uf_arg",
                                                         pending.lowered);
      if (name.GetSourceSort() != pending.sort)
        FatalError("UF lowering allocated an argument name at the wrong "
                   "SourceSort",
                   name);
      scalarNames.insert(std::make_pair(pending.lowered, name));
      view.nameToTerm.insert(std::make_pair(name, pending.lowered));
      view.protectedSymbols.insert(name);
      if (isBitReadableScalar(name))
        view.solveScalars.insert(name);
      pinIfRoundingMode(name);
      view.namingDefinitions.push_back(
          manager_->defaultNodeFactory->CreateNode(
              pending.sort.kind() == SourceSort::Kind::Bool ? IFF : EQ, name,
              pending.lowered));
    }
    view.applications[pending.record].namedActuals[pending.argument] = name;
  }

  for (const PendingName& pending : pendingNames)
  {
    poll();
    if (comparable(pending))
      continue;
    LoweredApplicationRecord& record = view.applications[pending.record];
    const ASTNodeMap::const_iterator found = scalarNames.find(pending.lowered);
    if (found != scalarNames.end())
      record.namedActuals[pending.argument] = found->second;
    else
      record.observableArguments = false;
  }

  // An unobservable record keeps its durable handle, its result symbol and its
  // lowered actuals; what it does not keep is a half-filled scalar tuple that
  // no checker round may read.
  for (LoweredApplicationRecord& record : view.applications)
    if (!record.observableArguments)
      record.namedActuals.clear();

  std::set<const UFDecl*> injectable;
  ASTNode injectivityGuard;
  if (manager_->UserFlags.uf_inject_args)
  {
    for (const auto& entry : narrowing.applicationCount)
      if (narrowing.nonNarrowable.count(entry.first) == 0)
        injectable.insert(entry.first);

    // Minted before the pair loop rather than on first use, so that every
    // converse implication of this lowering is behind the same symbol and
    // withdrawing it withdraws all of them. Keyed on the root being lowered,
    // which is what makes an identical persistent block rebuild an identical
    // guard along with an identical semantic root.
    if (!injectable.empty())
      injectivityGuard = manager_->CreateDeterministicSourceVariable(
          SourceSort::boolean(), "uf_inject_guard", publicRoot);
  }

  installEagerCongruence(view, injectable, injectivityGuard);
  reportEagerCongruence(view);

  // Tell the driver what this lowering assumed, and how to take it back. It is
  // the driver that holds the verdict, and this is the one thing installed
  // here that the verdict depends on: everything else in the encoding is
  // entailed by the query, so only these implications can turn a satisfiable
  // query unsatisfiable.
  //
  // The guard is registered as protected only when it is actually load-bearing.
  // A lowering that installed no converse implication has nothing to retract
  // and must not leave a free symbol behind for the simplifier to carry.
  if (view.eagerStats.emittedInjectivity() != 0)
  {
    view.injectivityGuard = injectivityGuard;
    // Without this the simplifier is free to do exactly what the guard was
    // built to allow -- observe that nothing constrains it, set it false, and
    // delete every implication behind it. That is sound, but it silently
    // turns the flag off. RemoveUnconstrained and SubstitutionMap both honour
    // this set.
    view.protectedSymbols.insert(injectivityGuard);
  }
  manager_->noteInjectivityAssumed(view.eagerStats.emittedInjectivity(),
                                   view.eagerStats.injectiveDeclarations(),
                                   view.injectivityGuard);

  // This checks the whole barrier once, including the naming definitions.
  // Scanning every progressively larger actual separately would turn a
  // linear post-order rewrite back into a quadratic algorithm on shared
  // nested DAGs.
  if (containsKind(view.semanticRootWithDefinitions(manager_), UF_APPLY))
    FatalError("UF_APPLY crossed the completed-root lowering barrier",
               view.semanticRoot);

  poll.check();
  context->installSolveProtection(view.protectedSymbols, view.solveScalars);
  return view;
}

namespace
{

// Declarations in one lowering view share a context, whose IDs are unique
// and follow declaration order. Addresses depend on unrelated allocations
// (including CLI parsing); using them to order lemma construction changes
// the SAT clauses and arithmetic rows installed by the next refinement.
struct DeclarationIdLess
{
  bool operator()(const UFDecl* left, const UFDecl* right) const
  {
    return left->id() < right->id();
  }
};

// One pair's congruence: the arguments agreeing forces the results to agree.
// A Boolean position is stated as an equivalence; every other is an equality,
// which the arithmetic owns for a Real and bit-blasting for the rest.
ASTNode congruenceForPair(NodeFactory* factory,
                          const LoweredApplicationRecord& left,
                          const LoweredApplicationRecord& right)
{
  const UFSignature& signature = left.declaration->signature();
  auto equalityKind = [](const SourceSort& sort) {
    return sort.kind() == SourceSort::Kind::Bool ? IFF : EQ;
  };
  const ASTNode conclusion = factory->CreateNode(
      equalityKind(signature.codomain()), left.resultSymbol,
      right.resultSymbol);
  if (left.namedActuals.empty())
    return conclusion;
  ASTVec premise;
  premise.reserve(left.namedActuals.size());
  for (size_t k = 0; k < left.namedActuals.size(); ++k)
    premise.push_back(factory->CreateNode(
        equalityKind(UFSignature::loweringSort(signature.domain()[k])),
        left.namedActuals[k], right.namedActuals[k]));
  return factory->CreateNode(IMPLIES,
                             premise.size() == 1
                                 ? premise[0]
                                 : factory->CreateNode(AND, premise),
                             conclusion);
}

// The fallback for a model that cannot be read: state the whole relation for
// this declaration rather than pass judgement on values that are not there.
// It costs what eager expansion costs, which is the point -- it is correct,
// and reaching it at all means something upstream did not value a symbol it
// was supposed to.
ASTVec congruenceForAllPairs(
    NodeFactory* factory,
    const std::vector<const LoweredApplicationRecord*>& records)
{
  ASTVec lemmas;
  for (size_t i = 0; i < records.size(); ++i)
    for (size_t j = i + 1; j < records.size(); ++j)
      lemmas.push_back(congruenceForPair(factory, *records[i], *records[j]));
  return lemmas;
}

} // namespace

namespace
{

// The same interpretation used to complete applications in public queries.
bool modelKey(STPMgr* manager, AbsRefine_CounterExample* counterexample,
              const ASTNode& scalar, const SourceSort& sort, std::string& key)
{
  return UFModel::scalarModelKey(manager, counterexample, scalar, sort, key);
}

} // namespace

ASTVec lazyCongruenceLemmasFromModel(STPMgr* manager,
                                     AbsRefine_CounterExample* counterexample,
                                     const LoweredApplicationView& view,
                                     std::set<const UFDecl*>* broken)
{
  ASTVec lemmas;
  if (manager == NULL || !manager->HasRealModel())
    return lemmas;
  NodeFactory* const factory = manager->defaultNodeFactory;

  std::map<const UFDecl*, std::vector<const LoweredApplicationRecord*>,
           DeclarationIdLess>
      byDeclaration;
  for (const LoweredApplicationRecord& record : view.applications)
    if (record.observableArguments && record.declaration != NULL &&
        isLazyCongruenceSignature(record.declaration->signature()))
      byDeclaration[record.declaration].push_back(&record);

  for (const auto& entry : byDeclaration)
  {
    const UFSignature& signature = entry.first->signature();
    std::map<std::vector<std::string>,
             std::vector<const LoweredApplicationRecord*>>
        atSamePoint;
    for (const LoweredApplicationRecord* record : entry.second)
    {
      std::vector<std::string> point;
      bool readable = true;
      for (size_t k = 0; k < record->namedActuals.size() && readable; ++k)
      {
        std::string key;
        readable = modelKey(manager, counterexample, record->namedActuals[k],
                            signature.domain()[k],
                            key);
        point.push_back(key);
      }
      // A model that does not value one of this declaration's arguments
      // cannot be judged here. Saying nothing would report the query
      // satisfiable on an unchecked application, so refuse the shortcut and
      // let the pairs be stated.
      if (!readable)
        return congruenceForAllPairs(factory, entry.second);
      atSamePoint[point].push_back(record);
    }

    for (const auto& group : atSamePoint)
    {
      const std::vector<const LoweredApplicationRecord*>& together =
          group.second;
      if (together.size() < 2)
        continue;
      std::vector<std::string> results;
      results.reserve(together.size());
      for (const LoweredApplicationRecord* record : together)
      {
        std::string key;
        if (!modelKey(manager, counterexample, record->resultSymbol,
                      signature.codomain(), key))
          return congruenceForAllPairs(factory, entry.second);
        results.push_back(key);
      }
      auto emit = [&](size_t i, size_t j) {
        if (results[i] == results[j])
          return;
        lemmas.push_back(congruenceForPair(factory, *together[i],
                                           *together[j]));
        manager->UserFlags.coverage.uf_constraints_installed++;
        if (broken != NULL)
          broken->insert(entry.first);
      };
      // Which of the group's pairs to state. Relating every member to the
      // first is enough for *this* model, since equality is transitive, but
      // the next model is free to move the first away and leave the rest
      // standing together with nothing said between them -- which is a round
      // spent re-discovering a collision that was already in view. A small
      // group states every disagreeing pair, so that no way of splitting it
      // is left unsaid. A large one cannot afford the square: it keeps the
      // star and adds a chain through the members, so that the anchor
      // leaving still leaves every neighbouring pair related.
      const size_t clique_limit = 8;
      if (together.size() <= clique_limit)
      {
        for (size_t i = 0; i < together.size(); ++i)
          for (size_t j = i + 1; j < together.size(); ++j)
            emit(i, j);
      }
      else
      {
        for (size_t i = 1; i < together.size(); ++i)
        {
          emit(0, i);
          if (i + 1 < together.size())
            emit(i, i + 1);
        }
      }
    }
  }
  return lemmas;
}

ASTVec congruenceClosureLemmasFromModel(STPMgr* manager,
                                        AbsRefine_CounterExample* counterexample,
                                        const LoweredApplicationView& view,
                                        std::set<const UFDecl*>* broken,
                                        const std::set<const UFDecl*>* onlyFor)
{
  ASTVec lemmas;
  if (manager == NULL || !manager->HasRealModel())
    return lemmas;
  // When onlyFor is set, state only the predictive (cross-cell) pairs: the
  // value-grouping pass has already stated the pairs the model directly
  // breaks, and re-stating them here would only duplicate them under the
  // caller's dedup and double the statistics.
  const bool predictiveOnly = (onlyFor != NULL);
  NodeFactory* const factory = manager->defaultNodeFactory;

  // The same population the value-grouping path decides.
  std::map<const UFDecl*, std::vector<const LoweredApplicationRecord*>,
           DeclarationIdLess>
      byDeclaration;
  for (const LoweredApplicationRecord& record : view.applications)
    if (record.observableArguments && record.declaration != NULL &&
        isLazyCongruenceSignature(record.declaration->signature()))
      byDeclaration[record.declaration].push_back(&record);
  if (byDeclaration.empty())
    return lemmas;

  // Intern every term an application names -- each argument and each result --
  // reading its committed value once, in a fixed order so the class ids below
  // are deterministic. A term the model does not value leaves the closure
  // unable to seed a class it needs; the whole round then defers to the
  // value-grouping path, which carries its own fallback for that case.
  std::unordered_map<ASTNode, unsigned, ASTNode::ASTNodeHasher,
                     ASTNode::ASTNodeEqual>
      idOf;
  std::vector<std::string> valueKey;
  bool readable = true;
  auto intern = [&](const ASTNode& term, const SourceSort& sort) -> unsigned {
    auto found = idOf.find(term);
    if (found != idOf.end())
      return found->second;
    std::string key;
    if (!modelKey(manager, counterexample, term, sort, key))
    {
      readable = false;
      return 0;
    }
    const unsigned id = static_cast<unsigned>(valueKey.size());
    idOf.emplace(term, id);
    valueKey.push_back(key);
    return id;
  };

  // Per record: the interned ids of its arguments and its result, kept in
  // step with byDeclaration so emission can zip the two.
  struct AppIds
  {
    std::vector<unsigned> args;
    unsigned result = 0;
  };
  std::map<const UFDecl*, std::vector<AppIds>, DeclarationIdLess> ids;
  for (const auto& entry : byDeclaration)
  {
    const UFSignature& signature = entry.first->signature();
    std::vector<AppIds>& list = ids[entry.first];
    list.reserve(entry.second.size());
    for (const LoweredApplicationRecord* record : entry.second)
    {
      AppIds a;
      a.args.reserve(record->namedActuals.size());
      for (size_t k = 0; k < record->namedActuals.size() && readable; ++k)
        a.args.push_back(intern(
            record->namedActuals[k],
            signature.domain()[k]));
      if (readable)
        a.result = intern(record->resultSymbol, signature.codomain());
      if (!readable)
        break;
      list.push_back(std::move(a));
    }
    if (!readable)
      break;
  }
  if (!readable)
    return lazyCongruenceLemmasFromModel(manager, counterexample, view, broken);

  const unsigned n = static_cast<unsigned>(valueKey.size());
  std::vector<unsigned> parent(n);
  std::vector<unsigned> rank(n, 0);
  for (unsigned i = 0; i < n; ++i)
    parent[i] = i;
  auto find = [&](unsigned x) {
    while (parent[x] != x)
    {
      parent[x] = parent[parent[x]];
      x = parent[x];
    }
    return x;
  };
  auto unite = [&](unsigned x, unsigned y) -> bool {
    x = find(x);
    y = find(y);
    if (x == y)
      return false;
    if (rank[x] < rank[y])
      std::swap(x, y);
    parent[y] = x;
    if (rank[x] == rank[y])
      rank[x]++;
    return true;
  };

  // Seed: terms the model gives one value stand at one point.
  {
    std::unordered_map<std::string, unsigned> firstWithValue;
    for (unsigned i = 0; i < n; ++i)
    {
      auto it = firstWithValue.find(valueKey[i]);
      if (it == firstWithValue.end())
        firstWithValue.emplace(valueKey[i], i);
      else
        unite(i, it->second);
    }
  }

  // Congruence to a fixpoint: applications whose arguments are pairwise in one
  // class carry equal results, so merge their result terms and repeat until a
  // pass merges nothing. This is what carries an equality up through a nested
  // application in one model read rather than one layer per round.
  bool changed = true;
  while (changed)
  {
    changed = false;
    for (const auto& entry : ids)
    {
      std::map<std::vector<unsigned>, unsigned> resultForArgs;
      for (const AppIds& a : entry.second)
      {
        std::vector<unsigned> classArgs;
        classArgs.reserve(a.args.size());
        for (unsigned arg : a.args)
          classArgs.push_back(find(arg));
        auto it = resultForArgs.find(classArgs);
        if (it == resultForArgs.end())
          resultForArgs.emplace(std::move(classArgs), a.result);
        else if (unite(it->second, a.result))
          changed = true;
      }
    }
  }

  for (const auto& entry : byDeclaration)
  {
    if (onlyFor != NULL && onlyFor->find(entry.first) == onlyFor->end())
      continue;
    const std::vector<const LoweredApplicationRecord*>& records = entry.second;
    const std::vector<AppIds>& appIds = ids[entry.first];

    // Group by the closure class of the argument tuple, then within that by
    // the raw argument value. Applications sharing a raw value are the pairs
    // the model directly breaks; cells the closure merged but the raw values
    // separate are congruent only through an equality this model has not yet
    // forced.
    std::map<std::vector<unsigned>,
             std::map<std::vector<std::string>, std::vector<size_t>>>
        buckets;
    for (size_t i = 0; i < records.size(); ++i)
    {
      std::vector<unsigned> classKey;
      std::vector<std::string> valueTuple;
      classKey.reserve(appIds[i].args.size());
      valueTuple.reserve(appIds[i].args.size());
      for (unsigned arg : appIds[i].args)
      {
        classKey.push_back(find(arg));
        valueTuple.push_back(valueKey[arg]);
      }
      buckets[std::move(classKey)][std::move(valueTuple)].push_back(i);
    }

    auto emitPair = [&](size_t i, size_t j) {
      if (valueKey[appIds[i].result] == valueKey[appIds[j].result])
        return;
      lemmas.push_back(congruenceForPair(factory, *records[i], *records[j]));
      manager->UserFlags.coverage.uf_constraints_installed++;
      if (broken != NULL)
        broken->insert(entry.first);
    };
    // Relate every disagreeing pair of a small set; a large one keeps the
    // star and adds a chain, exactly as the value-grouping path does, so the
    // two are compared on lemma shape and differ only in which sets they form.
    auto relate = [&](const std::vector<size_t>& members) {
      const size_t clique_limit = 8;
      if (members.size() <= clique_limit)
      {
        for (size_t i = 0; i < members.size(); ++i)
          for (size_t j = i + 1; j < members.size(); ++j)
            emitPair(members[i], members[j]);
      }
      else
      {
        for (size_t i = 1; i < members.size(); ++i)
        {
          emitPair(members[0], members[i]);
          if (i + 1 < members.size())
            emitPair(members[i], members[i + 1]);
        }
      }
    };

    for (const auto& bucket : buckets)
    {
      std::vector<size_t> cellReps;
      cellReps.reserve(bucket.second.size());
      for (const auto& cell : bucket.second)
      {
        if (!predictiveOnly && cell.second.size() >= 2)
          relate(cell.second); // pairs the model breaks now
        cellReps.push_back(cell.second.front());
      }
      if (cellReps.size() >= 2)
        relate(cellReps); // pairs a nested equality will break next round
    }
  }
  return lemmas;
}

namespace {
// Observable applications of one declaration -- the set fullLazyCongruence
// would pair up.
size_t observableApplicationCount(const LoweredApplicationView& view,
                                  const UFDecl* declaration)
{
  size_t n = 0;
  for (const LoweredApplicationRecord& record : view.applications)
    if (record.observableArguments && record.declaration == declaration)
      ++n;
  return n;
}
} // namespace

ASTVec nextLazyCongruenceRound(STPMgr* manager,
                               AbsRefine_CounterExample* counterexample,
                               const LoweredApplicationView& view,
                               LazyCongruenceState& state)
{
  std::set<const UFDecl*> brokenDeclarations;
  // The base every round: state the pairs the committed model directly breaks.
  ASTVec broken = lazyCongruenceLemmasFromModel(manager, counterexample, view,
                                                &brokenDeclarations);
  const UserDefinedFlags::OptionMode closureMode =
      manager->UserFlags.uf_congruence_closure;
  const unsigned closureMinApps =
      manager->UserFlags.uf_congruence_closure_min_apps;
  // A declaration that keeps breaking, round after round, is paying for a
  // whole round each time to learn a few pairs. Past the limit, state every
  // pair it has left and let this be the last round it costs.
  // The public output set above records membership; expansion order must
  // use the same stable identity order as ordinary conflict generation.
  std::vector<const UFDecl*> ordered(brokenDeclarations.begin(),
                                     brokenDeclarations.end());
  std::sort(ordered.begin(), ordered.end(), DeclarationIdLess{});
  // Large stuck declarations to escalate to the congruence closure this round,
  // instead of the O(n^2) full expansion that would stall the SAT solver.
  std::set<const UFDecl*> closureDeclarations;
  for (const UFDecl* declaration : ordered)
  {
    if (++state.brokenRounds[declaration] <
        manager->UserFlags.uf_lazy_round_limit)
      continue;
    const size_t n = observableApplicationCount(view, declaration);
    const unsigned long long pairs =
        static_cast<unsigned long long>(n) * (n - 1) / 2;
    if (n < 2)
      continue;
    if (pairs <= manager->UserFlags.uf_lazy_full_expansion_pairs)
    {
      // Small enough to state the whole relation in one round, once.
      if (state.expanded.insert(declaration).second)
      {
        const ASTVec whole = fullLazyCongruence(manager, view, declaration);
        broken.insert(broken.end(), whole.begin(), whole.end());
      }
    }
    else
    {
      // Too large to Ackermannise; escalate to the closure, which states the
      // congruences a nested equality will break next round rather than
      // waiting a round each to re-discover them. This is what the size gate
      // otherwise leaves purely lazy -- the case the closure exists for. ON
      // escalates every such declaration; AUTO only the very large ones, where
      // the win is robust; OFF none.
      const bool escalate =
          closureMode == UserDefinedFlags::OptionMode::ON ||
          (closureMode == UserDefinedFlags::OptionMode::AUTO &&
           n >= closureMinApps);
      if (escalate)
      {
        closureDeclarations.insert(declaration);
        state.expanded.insert(declaration); // reported under -s
      }
    }
  }
  if (!closureDeclarations.empty())
  {
    const ASTVec predicted = congruenceClosureLemmasFromModel(
        manager, counterexample, view, &brokenDeclarations,
        &closureDeclarations);
    broken.insert(broken.end(), predicted.begin(), predicted.end());
  }
  // Only what is new counts. A constraint already stated was satisfied by
  // the model just returned, so seeing it again means the round learned
  // nothing -- which cannot happen from a broken pair, but can from the
  // fallback that states a whole declaration when a model cannot be read.
  ASTVec fresh;
  for (const ASTNode& lemma : broken)
    if (state.earned.insert(lemma).second)
      fresh.push_back(lemma);
  state.lemmas += fresh.size();
  return fresh;
}

ASTVec fullLazyCongruence(STPMgr* manager, const LoweredApplicationView& view,
                          const UFDecl* declaration)
{
  ASTVec lemmas;
  if (manager == NULL || declaration == NULL)
    return lemmas;
  NodeFactory* const factory = manager->defaultNodeFactory;
  std::vector<const LoweredApplicationRecord*> records;
  for (const LoweredApplicationRecord& record : view.applications)
    if (record.observableArguments && record.declaration == declaration)
      records.push_back(&record);
  const UFSignature& signature = declaration->signature();
  const UnitBounds unitBounds = collectUnitBounds(view.semanticRoot);
  for (size_t i = 0; i < records.size(); ++i)
    for (size_t j = i + 1; j < records.size(); ++j)
    {
      // The same tests eager applies: a pair whose actuals can never agree
      // at some position needs nothing.
      bool impossible = false;
      for (size_t k = 0; k < signature.arity() && !impossible; ++k)
        impossible = comparePosition(factory, records[i]->loweredActuals[k],
                                     records[j]->loweredActuals[k],
                                     UFSignature::loweringSort(
                                         signature.domain()[k]),
                                     &unitBounds) ==
                     PositionVerdict::Distinct;
      if (impossible)
        continue;
      lemmas.push_back(congruenceForPair(factory, *records[i], *records[j]));
      manager->UserFlags.coverage.uf_constraints_installed++;
    }
  return lemmas;
}

} // namespace stp
