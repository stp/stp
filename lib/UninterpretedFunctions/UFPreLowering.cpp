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

// The order the candidates are tried in, which decides what a conjunct that
// could be read two ways is used for. A symbol equated with a constant, with
// another symbol, or with an application is a definition worth applying: it
// folds constants, merges applications and removes the symbol from every
// argument position. Only then is a conjunct read as an asserted atom, sent
// to true wherever else it occurs. A symbol equated with any other term is
// left as that atom: pushing a wide division into every argument position
// that named it makes each congruence premise a comparison of dividers
// where it was a comparison of symbols, and the ordinary preprocessing that
// follows lowering substitutes the symbol anyway wherever no application
// protects it. Within a class, constants come first so that a chain x = y,
// y = 5 resolves to x = 5 before y is asked about.
int rank(const Candidate& candidate)
{
  const bool definition = isScalarSymbol(candidate.key) ||
                          isApplication(candidate.key);
  if (definition && candidate.value.isConstant())
    return 0;
  if (definition && candidate.value.GetKind() == SYMBOL)
    return 1;
  if (definition && isApplication(candidate.value))
    return 2;
  if (!definition)
    return 3;
  return 4;
}

void addCandidate(std::vector<Candidate>& out, const ASTNode& key,
                  const ASTNode& value, size_t conjunct)
{
  if (key == value)
    return;
  Candidate c;
  c.key = key;
  c.value = value;
  c.conjunct = conjunct;
  out.push_back(c);
}

void readCandidates(const ASTNode& conjunct, size_t index,
                    const ASTNode& astTrue, const ASTNode& astFalse,
                    std::vector<Candidate>& out)
{
  const Kind k = conjunct.GetKind();
  if (conjunct.isConstant())
    return;

  // What an equality says about its sides comes first, so that `x = 5`
  // sends x to 5 rather than merely the atom to true; the atom then folds
  // wherever it recurs.
  if ((k == EQ || k == IFF) && conjunct.Degree() == 2)
  {
    const ASTNode& a = conjunct[0];
    const ASTNode& b = conjunct[1];

    if (isScalarSymbol(a) && isScalarSymbol(b))
    {
      // Either orientation is sound; the later symbol is the one that goes,
      // so that the choice is a function of the query alone.
      if (a.GetNodeNum() > b.GetNodeNum())
        addCandidate(out, a, b, index);
      else
        addCandidate(out, b, a, index);
    }
    else if (isScalarSymbol(a))
      addCandidate(out, a, b, index);
    else if (isScalarSymbol(b))
      addCandidate(out, b, a, index);
    // An application pinned to a constant. An application equated with a
    // non-constant term is left alone: replacing it by that term would move
    // the application into the equality alone and buy nothing, while the
    // symbol case above already covers `(f x) = a` by sending `a` to
    // `(f x)`.
    else if (isApplication(a) && b.isConstant())
      addCandidate(out, a, b, index);
    else if (isApplication(b) && a.isConstant())
      addCandidate(out, b, a, index);
  }

  // Whatever the conjunct is, it holds: every other occurrence of it is
  // true, and every other occurrence of what it negates is false. This is
  // the embedded-constraints rewrite, over the structure the query has
  // before its applications are hidden. A Boolean symbol or application
  // asserted outright is the same rule with the atom as its own key.
  if (k == NOT)
    addCandidate(out, conjunct[0], astFalse, index);
  else
    addCandidate(out, conjunct, astTrue, index);
}

// Rebuild a node over rewritten children without rewriting the node itself,
// which the map may send elsewhere: an application pinned to a constant, or
// an asserted atom sent to true. An application's declaration identity in
// child 0 is a symbol no fact ever equates, so it is passed through as is.
ASTNode rewriteChildren(const ASTNode& node, ASTNodeMap& fromTo,
                        NodeFactory* factory)
{
  if (node.Degree() == 0)
    return node;
  ASTVec children;
  children.reserve(node.Degree());
  bool changed = false;
  for (size_t i = 0; i < node.Degree(); ++i)
  {
    if (i == 0 && isApplication(node))
    {
      children.push_back(node[0]);
      continue;
    }
    ASTNodeMap cache;
    const ASTNode rewritten =
        SubstitutionMap::replace(node[i], fromTo, cache, factory);
    changed = changed || rewritten != node[i];
    children.push_back(rewritten);
  }
  if (!changed)
    return node;
  if (node.GetType() == BOOLEAN_TYPE)
    return factory->CreateNode(node.GetKind(), children);
  return factory->CreateArrayTerm(node.GetKind(), node.GetIndexWidth(),
                                  node.GetValueWidth(), children);
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
                       return rank(left) < rank(right);
                     });

    ASTNodeMap fromTo;
    // Which conjunct defines each key that made it into the map. Those
    // conjuncts are rebuilt as `key = value` rather than rewritten, so the
    // fact survives for the symbol it was used on.
    std::vector<bool> defines(conjuncts.size(), false);
    std::vector<ASTNode> definedKey(conjuncts.size());
    size_t symbolSubstitutions = 0;
    size_t applicationSubstitutions = 0;
    size_t atomSubstitutions = 0;

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
      else if (candidate.key.GetKind() == SYMBOL)
        symbolSubstitutions++;
      else
        atomSubstitutions++;
    }

    if (fromTo.empty())
      break;

    for (const ASTNode& application : originalApplications)
    {
      ASTNode& current_image = image.find(application)->second;
      current_image = rewriteChildren(current_image, fromTo, factory);
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
      // value. The key keeps its own children current -- an application
      // stays the one application every other occurrence merged into, an
      // atom reads what the other definitions say about its operands --
      // without being sent where the map sends its other occurrences.
      const ASTNode& key = definedKey[i];
      const ASTNode& value = fromTo.find(key)->second;
      const ASTNode keptKey = rewriteChildren(key, fromTo, factory);
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
    s.atomSubstitutions += atomSubstitutions;
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
            << " application(s) and " << stats.atomSubstitutions
            << " asserted atom(s) in " << stats.rounds << " round(s)";
  if (stats.skeletonFacts != 0)
    std::cerr << " using " << stats.skeletonFacts << " skeleton fact(s)";
  std::cerr << ", " << stats.applicationsRemaining
            << " application(s) remain" << std::endl;
}

} // namespace stp
