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

#include "stp/UninterpretedFunctions/UFPreLowering.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/SkeletonPreproc.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/Util/DagWalk.h"
#include <iostream>
#include <vector>

namespace stp
{

namespace
{

// The conjuncts of a root, left to right, with nested conjunctions opened.
// A conjunct that is itself an AND has no fact of its own to offer; its
// children do.
void collectConjuncts(const ASTNode& root, ASTVec& out)
{
  std::vector<ASTNode> pending;
  pending.push_back(root);
  // Depth-first from the left, so a right-nested conjunction is read in the
  // order it was written.
  while (!pending.empty())
  {
    const ASTNode n = pending.back();
    pending.pop_back();
    if (n.GetKind() == AND)
    {
      for (size_t i = n.Degree(); i > 0; --i)
        pending.push_back(n[i - 1]);
      continue;
    }
    out.push_back(n);
  }
}

// Whether `node` occurs anywhere in `term`. Every rewrite below is only sound
// if what a symbol is replaced by does not mention that symbol, so this is
// asked before every insertion; the walk is memoised per call and the terms
// it sees are the small right-hand sides of top-level equalities.
bool occursIn(const ASTNode& node, const ASTNode& term)
{
  bool found = false;
  ASTNodeSet visited;
  walkPreOrder(term, [&](const ASTNode& n) -> bool {
    if (found || !visited.insert(n).second)
      return false;
    if (n == node)
    {
      found = true;
      return false;
    }
    return true;
  });
  return found;
}

bool isScalarSymbol(const ASTNode& n)
{
  // Arrays are equated through ARRAY_EQ, never EQ, so an array symbol does
  // not reach here from an EQ; the width test keeps it that way for any
  // other route.
  return n.GetKind() == SYMBOL && n.GetIndexWidth() == 0;
}

bool isApplication(const ASTNode& n)
{
  return n.GetKind() == UF_APPLY;
}

// One fact read off a conjunct: `key` may be replaced by `value` everywhere
// else. `conjunct` is the index it was read from, which is the conjunct the
// rewrite keeps as the key's definition.
struct Candidate
{
  ASTNode key;
  ASTNode value;
  size_t conjunct = 0;
};

// Constants first, then symbols, then everything else: a chain x = y, y = 5
// resolves to x = 5 only if 5 is in the map before y is asked about, and a
// symbol equated with two things keeps the cheaper one.
int rank(const ASTNode& value)
{
  if (value.isConstant())
    return 0;
  if (value.GetKind() == SYMBOL)
    return 1;
  return 2;
}

void addSymbolCandidate(std::vector<Candidate>& out, const ASTNode& symbol,
                        const ASTNode& value, size_t conjunct)
{
  if (symbol == value)
    return;
  Candidate c;
  c.key = symbol;
  c.value = value;
  c.conjunct = conjunct;
  out.push_back(c);
}

void readCandidates(const ASTNode& conjunct, size_t index,
                    const ASTNode& astTrue, const ASTNode& astFalse,
                    std::vector<Candidate>& out)
{
  const Kind k = conjunct.GetKind();

  // A Boolean asserted outright, or its negation.
  if (isScalarSymbol(conjunct) || isApplication(conjunct))
  {
    addSymbolCandidate(out, conjunct, astTrue, index);
    return;
  }
  if (k == NOT && (isScalarSymbol(conjunct[0]) || isApplication(conjunct[0])))
  {
    addSymbolCandidate(out, conjunct[0], astFalse, index);
    return;
  }

  if ((k != EQ && k != IFF) || conjunct.Degree() != 2)
    return;

  const ASTNode& a = conjunct[0];
  const ASTNode& b = conjunct[1];

  if (isScalarSymbol(a) && isScalarSymbol(b))
  {
    // Either orientation is sound; the later symbol is the one that goes,
    // so that the choice is a function of the query alone.
    if (a.GetNodeNum() > b.GetNodeNum())
      addSymbolCandidate(out, a, b, index);
    else
      addSymbolCandidate(out, b, a, index);
    return;
  }
  if (isScalarSymbol(a))
  {
    addSymbolCandidate(out, a, b, index);
    return;
  }
  if (isScalarSymbol(b))
  {
    addSymbolCandidate(out, b, a, index);
    return;
  }

  // An application pinned to a constant. An application equated with a
  // non-constant term is left alone: replacing it by that term would move
  // the application into the equality alone and buy nothing, while the
  // symbol case above already covers `(f x) = a` by sending `a` to `(f x)`.
  if (isApplication(a) && b.isConstant())
    addSymbolCandidate(out, a, b, index);
  else if (isApplication(b) && a.isConstant())
    addSymbolCandidate(out, b, a, index);
}

// Rebuild an application over rewritten arguments without rewriting the
// application itself, which the map may send to a constant. The declaration
// identity in child 0 is a symbol no fact ever equates, so it survives
// replace() unchanged and is passed through untouched here as well.
ASTNode rewriteArguments(const ASTNode& application, ASTNodeMap& fromTo,
                         NodeFactory* factory)
{
  ASTVec children;
  children.reserve(application.Degree());
  children.push_back(application[0]);
  bool changed = false;
  for (size_t i = 1; i < application.Degree(); ++i)
  {
    ASTNodeMap cache;
    const ASTNode rewritten =
        SubstitutionMap::replace(application[i], fromTo, cache, factory);
    changed = changed || rewritten != application[i];
    children.push_back(rewritten);
  }
  if (!changed)
    return application;
  if (application.GetType() == BOOLEAN_TYPE)
    return factory->CreateNode(UF_APPLY, children);
  return factory->CreateTerm(UF_APPLY, application.GetValueWidth(),
                             children);
}

// Every distinct application in `root`, in the order the walk meets them.
void collectApplications(const ASTNode& root, ASTVec& out)
{
  ASTNodeSet visited;
  walkPreOrder(root, [&](const ASTNode& n) -> bool {
    if (!visited.insert(n).second)
      return false;
    if (n.GetKind() == UF_APPLY)
      out.push_back(n);
    return true;
  });
}

size_t countApplications(const ASTNode& root)
{
  ASTVec applications;
  collectApplications(root, applications);
  return applications.size();
}

} // namespace

UFPreLowering::UFPreLowering(STPMgr* manager) : manager_(manager)
{
  assert(manager_ != NULL);
}

ASTNode UFPreLowering::propagate(const ASTNode& root, UFPreLoweringStats* stats,
                                 bool skeleton, ASTNodeMap* handleAliases)
{
  UFPreLoweringStats local;
  UFPreLoweringStats& s = stats != NULL ? *stats : local;
  s = UFPreLoweringStats();
  if (handleAliases != NULL)
    handleAliases->clear();

  NodeFactory* const factory = manager_->defaultNodeFactory;
  ASTNode current = root;

  // The applications the caller's root holds, and what each has become so
  // far. An application is followed by rewriting its arguments -- never by
  // the constant it may be pinned to -- so that the image is the application
  // lowering will meet, whatever else the pass did with it.
  ASTVec originalApplications;
  ASTNodeMap image;
  if (handleAliases != NULL)
  {
    collectApplications(root, originalApplications);
    for (const ASTNode& application : originalApplications)
      image.insert(std::make_pair(application, application));
  }

  if (skeleton && !current.isConstant())
  {
    SkeletonPreproc structure(manager_);
    bool unsat = false;
    ASTVec facts = structure.derive(current, unsat);
    if (unsat)
    {
      s.skeletonUnsat = true;
      return manager_->ASTFalse;
    }
    if (!facts.empty())
    {
      s.skeletonFacts = facts.size();
      facts.push_back(current);
      current = factory->CreateNode(AND, facts);
    }
  }

  // A round reads the facts of the current root and rewrites under them. A
  // rewrite can expose a fact the previous round could not read -- `(f y)`
  // becomes `(f 3)` and a conjunct `(f 3) = 0` elsewhere now matches it --
  // so run until the root stops moving. Each round is one linear pass, and
  // the bound is a guard against a pathological chain rather than a limit
  // any real query reaches.
  const size_t maxRounds = 8;
  // A later round re-reads the definitions an earlier one left in place;
  // only a key not seen before is a new substitution.
  ASTNodeSet substituted;
  for (size_t round = 0; round < maxRounds; ++round)
  {
    if (current.GetKind() != AND && current.GetKind() != EQ &&
        current.GetKind() != IFF)
      break;

    ASTVec conjuncts;
    collectConjuncts(current, conjuncts);
    if (conjuncts.size() < 2)
      break;

    std::vector<Candidate> candidates;
    for (size_t i = 0; i < conjuncts.size(); ++i)
      readCandidates(conjuncts[i], i, manager_->ASTTrue, manager_->ASTFalse,
                     candidates);
    if (candidates.empty())
      break;

    std::stable_sort(candidates.begin(), candidates.end(),
                     [](const Candidate& left, const Candidate& right) {
                       return rank(left.value) < rank(right.value);
                     });

    ASTNodeMap fromTo;
    // Which conjunct defines each key that made it into the map. Those
    // conjuncts are rebuilt as `key = value` rather than rewritten, so the
    // fact survives for the symbol it was used on.
    std::vector<bool> defines(conjuncts.size(), false);
    std::vector<ASTNode> definedKey(conjuncts.size());
    size_t symbolSubstitutions = 0;
    size_t applicationSubstitutions = 0;

    for (const Candidate& candidate : candidates)
    {
      if (fromTo.find(candidate.key) != fromTo.end())
        continue;
      if (defines[candidate.conjunct])
        continue;

      // What the value is once everything already in the map has been
      // applied to it: a chain x = y, y = 5 gives x = 5, and the occurs
      // check below then sees the resolved term rather than the written one.
      ASTNode value = candidate.value;
      if (!value.isConstant())
      {
        ASTNodeMap cache;
        value = SubstitutionMap::replace(value, fromTo, cache, factory);
      }
      if (value == candidate.key || occursIn(candidate.key, value))
        continue;

      fromTo.insert(std::make_pair(candidate.key, value));
      defines[candidate.conjunct] = true;
      definedKey[candidate.conjunct] = candidate.key;
      if (!substituted.insert(candidate.key).second)
        continue;
      if (isApplication(candidate.key))
        applicationSubstitutions++;
      else
        symbolSubstitutions++;
    }

    if (fromTo.empty())
      break;

    for (const ASTNode& application : originalApplications)
    {
      ASTNode& current_image = image.find(application)->second;
      current_image = rewriteArguments(current_image, fromTo, factory);
    }

    ASTVec rewritten;
    rewritten.reserve(conjuncts.size());
    ASTNodeMap cache;
    for (size_t i = 0; i < conjuncts.size(); ++i)
    {
      if (!defines[i])
      {
        rewritten.push_back(
            SubstitutionMap::replace(conjuncts[i], fromTo, cache, factory));
        continue;
      }

      // The defining conjunct, restated as the key against its resolved
      // value. An application key keeps its own arguments current so that
      // it stays the one application every other occurrence merged into.
      const ASTNode& key = definedKey[i];
      const ASTNode& value = fromTo.find(key)->second;
      ASTNode keptKey = key;
      if (isApplication(key))
        keptKey = rewriteArguments(key, fromTo, factory);
      if (value == manager_->ASTTrue)
        rewritten.push_back(keptKey);
      else if (value == manager_->ASTFalse)
        rewritten.push_back(factory->CreateNode(NOT, keptKey));
      else
        rewritten.push_back(factory->CreateNode(
            keptKey.GetType() == BOOLEAN_TYPE ? IFF : EQ, keptKey, value));
    }

    const ASTNode next = rewritten.size() == 1
                             ? rewritten[0]
                             : factory->CreateNode(AND, rewritten);
    s.symbolSubstitutions += symbolSubstitutions;
    s.applicationSubstitutions += applicationSubstitutions;
    if (next == current)
      break;
    s.rounds++;
    current = next;
    if (current.isConstant())
      break;
  }

  if (handleAliases != NULL)
    for (const ASTNode& application : originalApplications)
    {
      const ASTNode& final_image = image.find(application)->second;
      if (final_image != application)
        handleAliases->insert(std::make_pair(application, final_image));
    }

  s.applicationsRemaining = countApplications(current);
  return current;
}

void UFPreLowering::report(const UFPreLoweringStats& stats) const
{
  if (!manager_->UserFlags.stats_flag)
    return;
  if (stats.skeletonUnsat)
  {
    std::cerr << "UF: pre-lowering: the Boolean skeleton refutes the query"
              << std::endl;
    return;
  }
  std::cerr << "UF: pre-lowering substituted " << stats.symbolSubstitutions
            << " symbol(s) and " << stats.applicationSubstitutions
            << " application(s) in " << stats.rounds << " round(s)";
  if (stats.skeletonFacts != 0)
    std::cerr << " using " << stats.skeletonFacts << " skeleton fact(s)";
  std::cerr << ", " << stats.applicationsRemaining
            << " application(s) remain" << std::endl;
}

} // namespace stp
