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
#include <algorithm>
#include <unordered_map>
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

// Visited marks for the walks below, keyed by node number rather than
// hashed. A round walks tens of thousands of small values -- one per
// candidate for the occurs check, one for the wide-arithmetic test, one
// for the cycle pass -- and a hash set allocated and filled for each was
// half the pass's time on a hardware query defining sixteen thousand state
// variables. Node numbers are dense, so a stamp per number and a
// generation per walk make a visit one load and one store.
class NodeMarks
{
public:
  void next()
  {
    if (++generation_ == 0)
    {
      std::fill(stamp_.begin(), stamp_.end(), 0);
      generation_ = 1;
    }
  }

  // Whether this is the first visit to `n` in the current walk.
  bool first(const ASTNode& n)
  {
    const uint64_t num = n.GetNodeNum();
    if (num >= stamp_.size())
      stamp_.resize(num + 1024, 0);
    if (stamp_[num] == generation_)
      return false;
    stamp_[num] = generation_;
    return true;
  }

private:
  std::vector<uint32_t> stamp_;
  uint32_t generation_ = 0;
};

// Whether `node` occurs anywhere in `term`. Every rewrite below is only sound
// if what a symbol is replaced by does not mention that symbol, so this is
// asked before every insertion; the terms it sees are the right-hand sides
// of top-level equalities.
bool occursIn(const ASTNode& node, const ASTNode& term, NodeMarks& marks)
{
  marks.next();
  ASTVec stack(1, term);
  while (!stack.empty())
  {
    const ASTNode current = stack.back();
    stack.pop_back();
    if (!marks.first(current))
      continue;
    if (current == node)
      return true;
    for (size_t i = 0; i < current.Degree(); ++i)
      stack.push_back(current[i]);
  }
  return false;
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
  // Whether the value holds a multiplication, division or remainder at or
  // above the abstraction width: the one kind of term a symbol is not sent
  // to, see rank().
  bool wideValue = false;
};

// Whether `term` holds an operation the abstraction would take at `width`
// bits or more. The same test the abstraction policy makes of the query.
bool holdsWideArithmetic(const ASTNode& term, unsigned width, NodeMarks& marks)
{
  marks.next();
  ASTVec stack(1, term);
  while (!stack.empty())
  {
    const ASTNode n = stack.back();
    stack.pop_back();
    if (!marks.first(n))
      continue;
    switch (n.GetKind())
    {
      case BVMULT:
      case BVDIV:
      case BVMOD:
      case SBVDIV:
      case SBVREM:
      case SBVMOD:
        if (n.GetValueWidth() >= width)
          return true;
        break;
      default:
        break;
    }
    for (size_t i = 0; i < n.Degree(); ++i)
      stack.push_back(n[i]);
  }
  return false;
}

// The order the candidates are tried in, which decides what a conjunct that
// could be read two ways is used for. A symbol equated with a constant, with
// another symbol, with an application, or with any other term free of wide
// arithmetic is a definition worth applying: it folds constants, merges
// applications, removes the symbol from every argument position, and lets a
// fact stated about the symbol meet the term it names. A definition is the
// stronger reading of an equality: once the symbol is sent to the term,
// every other occurrence of the equality folds to true of itself. Only
// then is a conjunct read as an asserted atom, sent to true wherever else
// it occurs. A symbol equated with a term holding a wide multiplication or
// division is left as that atom: pushing a wide division into every
// argument position that named it makes each congruence premise a
// comparison of dividers where it was a comparison of symbols, and the
// ordinary preprocessing that follows lowering substitutes the symbol
// anyway wherever no application protects it. Within a class, constants
// come first so that a chain x = y, y = 5 resolves to x = 5 before y is
// asked about.
//
// The term-valued definitions were once all left as atoms, which on 0208 of
// the Certora queries left `x = a + b` standing beside `x <= y` while the
// skeleton had forced `a + b > y` under another name: the contradiction
// Bitwuzla's variable substitution makes syntactic cost a 5.3M-clause CNF
// and thirty seconds of solving here.
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
  if (definition && !candidate.wideValue)
    return 3;
  if (!definition)
    return 4;
  return 5;
}

void addCandidate(std::vector<Candidate>& out, const ASTNode& key,
                  const ASTNode& value, size_t conjunct, unsigned wideWidth,
                  NodeMarks& marks)
{
  if (key == value)
    return;
  Candidate c;
  c.key = key;
  c.value = value;
  c.conjunct = conjunct;
  c.wideValue =
      value.Degree() != 0 && holdsWideArithmetic(value, wideWidth, marks);
  out.push_back(c);
}

void readCandidates(const ASTNode& conjunct, size_t index,
                    const ASTNode& astTrue, const ASTNode& astFalse,
                    unsigned wideWidth, NodeMarks& marks,
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
        addCandidate(out, a, b, index, wideWidth, marks);
      else
        addCandidate(out, b, a, index, wideWidth, marks);
    }
    else if (isScalarSymbol(a))
      addCandidate(out, a, b, index, wideWidth, marks);
    else if (isScalarSymbol(b))
      addCandidate(out, b, a, index, wideWidth, marks);
    // Two applications equated: the later goes, as for two symbols. Every
    // term built on either is then one term built on the survivor, which
    // is what a verification query needs when it computes the same value
    // through two accessors and takes their difference: with each side its
    // own application the difference is two wide products of two wide
    // quotients, which an abstraction refines round after round, and with
    // one application it is a term less itself. The equality is kept, so
    // the application that goes is still one the congruence checker sees,
    // its result pinned to the survivor's, its arguments still meeting
    // every other application of its declaration. An application equated
    // with any other non-constant term is left alone: replacing it by that
    // term would move the application into the equality alone and buy
    // nothing, while the symbol case above already covers `(f x) = a` by
    // sending `a` to `(f x)`.
    else if (isApplication(a) && isApplication(b))
    {
      if (a.GetNodeNum() > b.GetNodeNum())
        addCandidate(out, a, b, index, wideWidth, marks);
      else
        addCandidate(out, b, a, index, wideWidth, marks);
    }
    // An application pinned to a constant.
    else if (isApplication(a) && b.isConstant())
      addCandidate(out, a, b, index, wideWidth, marks);
    else if (isApplication(b) && a.isConstant())
      addCandidate(out, b, a, index, wideWidth, marks);
  }

  // Whatever the conjunct is, it holds: every other occurrence of it is
  // true, and every other occurrence of what it negates is false. This is
  // the embedded-constraints rewrite, over the structure the query has
  // before its applications are hidden. A Boolean symbol or application
  // asserted outright is the same rule with the atom as its own key.
  if (k == NOT)
    addCandidate(out, conjunct[0], astFalse, index, wideWidth, marks);
  else
    addCandidate(out, conjunct, astTrue, index, wideWidth, marks);
}

// Rebuild a node over rewritten children without rewriting the node itself,
// which the map may send elsewhere: an application pinned to a constant, or
// an asserted atom sent to true. An application's declaration identity in
// child 0 is a symbol no fact ever equates, so it is passed through as is.
//
// `cache` memoises replace() under `fromTo`, which does not change while a
// round is being applied, so one cache serves every rewrite of the round: a
// subterm shared by thousands of conjuncts is rewritten once, not once per
// conjunct.
ASTNode rewriteChildren(const ASTNode& node, ASTNodeMap& fromTo,
                        ASTNodeMap& cache, NodeFactory* factory)
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
  NodeMarks marks;
  for (size_t round = 0; round < maxRounds; ++round)
  {
    // The Boolean structure is asked what it forces at the start of every
    // round, not once up front: a round's rewrite changes what the atoms
    // are -- a symbol sent to another renames every predicate over it --
    // and folds connectives, so a guard the structure could not see
    // through before the round is one it resolves after it. On 0208 of the
    // Certora queries the facts that decide the query sit under a Boolean
    // symbol's definition that only the second round's substitution opens;
    // asked once, the structure never saw them and the query cost a
    // 5.3M-clause CNF. The call is CaDiCaL's preprocessing on a CNF the
    // size of the skeleton, a few milliseconds on a query of thousands of
    // assertions, and it is made only while the root is still moving.
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
      // A top-level conjunct is trivially forced, and comes back as a fact;
      // only what the structure derived beyond the conjuncts themselves is
      // worth conjoining. A query of fifteen thousand assertions otherwise
      // doubles in size for nothing, and pays for it in every round below.
      ASTVec conjuncts;
      collectConjuncts(current, conjuncts);
      const ASTNodeSet present(conjuncts.begin(), conjuncts.end());
      ASTVec fresh;
      for (const ASTNode& fact : facts)
        if (present.find(fact) == present.end())
          fresh.push_back(fact);
      if (!fresh.empty())
      {
        s.skeletonFacts += fresh.size();
        fresh.push_back(current);
        current = factory->CreateNode(AND, fresh);
      }
    }

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
                     manager_->UserFlags.bv_abstraction_width, marks,
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

    // Selection inserts each value as written. What a value resolves to
    // once every other definition has been applied is left to the rewrite
    // below, whose replace follows a chain x = y, y = 5 to 5 itself and
    // memoises the walk across the whole round. Resolving at insertion
    // instead, each candidate through the map as it then stood with a
    // cache of its own, was quadratic in the length of a chain: a hardware
    // query defining sixteen thousand state variables, each in terms of the
    // last, spent six seconds here on a solve that otherwise takes half a
    // second. An acyclic map is what makes the chain-following rewrite
    // terminate, so the cycles are found once, on the map as a whole, after
    // selection.
    std::vector<Candidate> chosen;
    for (const Candidate& candidate : candidates)
    {
      if (fromTo.find(candidate.key) != fromTo.end())
        continue;
      if (defines[candidate.conjunct])
        continue;
      if (candidate.value == candidate.key ||
          occursIn(candidate.key, candidate.value, marks))
        continue;

      fromTo.insert(std::make_pair(candidate.key, candidate.value));
      defines[candidate.conjunct] = true;
      definedKey[candidate.conjunct] = candidate.key;
      chosen.push_back(candidate);
    }

    // A key's value may mention other keys, and following those may come
    // back to the key: x = f(y), y = g(x) each pass the direct occurs check
    // above and together would send the rewrite round in circles. The keys
    // are the vertices, a value's mention of a key an edge, and Kahn's peel
    // finds whether anything is left on a cycle; when it is, the lowest
    // ranked definition still standing among the leftovers is withdrawn and
    // the peel run again. The walk of a value stops at a key it meets,
    // since the rewrite replaces that key whole and never looks inside it.
    {
      std::unordered_map<ASTNode, size_t, ASTNode::ASTNodeHasher,
                         ASTNode::ASTNodeEqual>
          indexOf;
      for (size_t i = 0; i < chosen.size(); ++i)
        indexOf[chosen[i].key] = i;
      std::vector<std::vector<size_t>> mentions(chosen.size());
      for (size_t i = 0; i < chosen.size(); ++i)
      {
        marks.next();
        ASTVec stack(1, chosen[i].value);
        while (!stack.empty())
        {
          const ASTNode node = stack.back();
          stack.pop_back();
          if (!marks.first(node))
            continue;
          const auto it = indexOf.find(node);
          if (it != indexOf.end())
          {
            mentions[i].push_back(it->second);
            continue;
          }
          for (size_t c = 0; c < node.Degree(); ++c)
            stack.push_back(node[c]);
        }
      }

      std::vector<bool> alive(chosen.size(), true);
      for (;;)
      {
        std::vector<size_t> indegree(chosen.size(), 0);
        for (size_t i = 0; i < chosen.size(); ++i)
          if (alive[i])
            for (const size_t j : mentions[i])
              if (alive[j])
                indegree[j]++;
        std::vector<size_t> ready;
        for (size_t i = 0; i < chosen.size(); ++i)
          if (alive[i] && indegree[i] == 0)
            ready.push_back(i);
        size_t peeled = 0;
        while (!ready.empty())
        {
          const size_t i = ready.back();
          ready.pop_back();
          peeled++;
          for (const size_t j : mentions[i])
            if (alive[j] && --indegree[j] == 0)
              ready.push_back(j);
        }
        size_t standing = 0;
        for (size_t i = 0; i < chosen.size(); ++i)
          if (alive[i])
            standing++;
        if (peeled == standing)
          break;
        // Everything not peeled is on a cycle or downstream of one; the
        // last of them in rank order goes.
        size_t drop = chosen.size();
        for (size_t i = 0; i < chosen.size(); ++i)
          if (alive[i] && indegree[i] != 0)
            drop = i;
        assert(drop != chosen.size());
        alive[drop] = false;
        fromTo.erase(chosen[drop].key);
        defines[chosen[drop].conjunct] = false;
        definedKey[chosen[drop].conjunct] = ASTNode();
      }

      std::vector<Candidate> kept;
      kept.reserve(chosen.size());
      for (size_t i = 0; i < chosen.size(); ++i)
        if (alive[i])
          kept.push_back(chosen[i]);
      chosen.swap(kept);
    }

    for (const Candidate& candidate : chosen)
    {
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

    ASTNodeMap cache;
    for (const ASTNode& application : originalApplications)
    {
      ASTNode& current_image = image.find(application)->second;
      current_image = rewriteChildren(current_image, fromTo, cache, factory);
    }

    ASTVec rewritten;
    rewritten.reserve(conjuncts.size());
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
      const ASTNode value =
          SubstitutionMap::replace(fromTo.find(key)->second, fromTo, cache,
                                   factory);
      const ASTNode keptKey = rewriteChildren(key, fromTo, cache, factory);
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
