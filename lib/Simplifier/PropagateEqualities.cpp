/********************************************************************
 *
 * BEGIN DATE: April, 2022
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

#include "stp/Simplifier/PropagateEqualities.h"
#include "stp/Util/DagWalk.h"
#include <string>
#include <utility>
#include <queue>

namespace stp
{

typedef PropagateEqualities::IdSet IdSet;
typedef ankerl::unordered_dense::map<uint64_t, uint64_t> IdToId;
typedef ankerl::unordered_dense::map<uint64_t, IdSet> IdToIdSet;
// Safe as a dense set: only inserted into, then copied out and sorted by
// expression number -- its iteration order never reaches a decision.
typedef ankerl::unordered_dense::set<ASTNode, ASTNode::ASTNodeHasher,
                                     ASTNode::ASTNodeEqual> DenseNodeSet;
// Values must stay pointer-stable: the priority queue and update() hold
// pointers/references into the map while it is queried, so this stays a
// node-based std::unordered_map (mapped is never inserted into after build).
typedef PropagateEqualities::MapToNodeSet MapToNodeSet;

void tagNodes(const ASTNode& n, const uint64_t tag, IdToId& nodeToTag, DenseNodeSet& shared)
{
  if (n.Degree() == 0)
    return; 

  const auto n_id = n.GetNodeNum();

  const auto it = nodeToTag.find(n_id);
  if (it != nodeToTag.end())
  {
    if (it->second != tag)
      shared.insert(n); // Two or more nodes share this node.

    return; // already tagged
  }

  nodeToTag[n_id] = tag;

  for (const auto & c : n)
    tagNodes(c, tag, nodeToTag, shared);
}

// Take the intersection of the symbols in n, and the symbols in "candidates", putting the result into "variablers"
void intersection(const ASTNode& n, IdSet& visited, IdSet& variables, const IdSet& candidates, IdToIdSet& cache)
{
  const auto n_id = n.GetNodeNum();
  
  if (!visited.insert(n_id).second)
    return;

  const auto cit = cache.find(n_id);
  if (cit != cache.end())
  {
    variables.insert(cit->second.begin(), cit->second.end());
    return;
  }
 
  if (SYMBOL == n.GetKind() && candidates.find(n_id) != candidates.end())
  {
    variables.insert(n_id);
    return;
  }

  for (const auto & c : n)
    intersection(c, visited, variables, candidates, cache);
}

MapToNodeSet PropagateEqualities::buildMapOfLHStoVariablesInRHS(const IdSet& allLhsVariables)
{
  DenseNodeSet shared;
  {
    IdToId tags;
    uint64_t tag = 0;

    for (const auto& e: candidates)  
        tagNodes(e.second, tag++, tags, shared);
  }

  IdToIdSet cache;
  {
    ASTVec orderedByExprNum(shared.begin(), shared.end());
    SortByExprNum(orderedByExprNum);

    // Prime the cache.
    for (const auto& n : orderedByExprNum )
    {
      IdSet visited;
      IdSet variables;
      intersection(n,visited,variables, allLhsVariables, cache);
      cache.insert(std::make_pair(n.GetNodeNum(),variables));
    }
  }

  // Without the id field, which we sort the priority queue on, the order that the rules were applied
  // was not deterministic, giving diffent CNF.
  MapToNodeSet mapped;
  mapped.reserve(candidates.size());
  int id =0;

  for (const auto& e: candidates)
  {
    IdSet visited;
    IdSet variables;
    intersection(e.second, visited, variables, allLhsVariables, cache);
    mapped.insert(std::make_pair(
        e.first.GetNodeNum(),
        PropagateEqualities::CandidateInfo{e.first, e.second,
                                          std::move(variables), id++, 0}));
  }

  return mapped;
}

// Bring candidate `start`'s variable set up to date with the replacements
// performed so far. Each candidate remembers how many replacements it has
// already folded in (upTo), so only the newly replaced variables need
// checking. Invariant: a replaced variable still present in a set must have
// been replaced after that set's upTo, and an up-to-date set contains no
// replaced variables at all -- which is why folding a dependency's set in
// cannot re-introduce work, and why the fold order doesn't matter.
static void update(const uint64_t start, MapToNodeSet& m,
                   const std::vector<uint64_t>& replacedOrder,
                   const IdToId& replacedIndex)
{
  const size_t now = replacedOrder.size();

  struct Frame
  {
    uint64_t n;
    std::vector<uint64_t> deps;
    bool expanded = false;
  };
  std::vector<Frame> stack;
  stack.push_back({start, {}, false});

  while (!stack.empty())
  {
    Frame& f = stack.back();
    assert(m.find(f.n) != m.end());
    PropagateEqualities::CandidateInfo& ci = m.find(f.n)->second;

    if (!f.expanded)
    {
      f.expanded = true;

      // Find the replaced variables in ci.vars, probing whichever side is
      // smaller: the pending replacements, or the set itself.
      if (now - ci.upTo < ci.vars.size())
      {
        for (size_t i = ci.upTo; i < now; i++)
          if (ci.vars.count(replacedOrder[i]) != 0)
            f.deps.push_back(replacedOrder[i]);
      }
      else
      {
        for (const auto v : ci.vars)
        {
          const auto it = replacedIndex.find(v);
          if (it != replacedIndex.end() && it->second >= ci.upTo)
            f.deps.push_back(v);
        }
      }

      bool pushed = false;
      for (const auto v : f.deps)
        if (m.find(v)->second.upTo != now)
        {
          stack.push_back({v, {}, false});
          pushed = true;
        }
      if (pushed)
        continue; // fold once the dependencies are up to date themselves
    }

    for (const auto v : f.deps)
    {
      ci.vars.erase(v);
      const IdSet& add = m.find(v)->second.vars;
      ci.vars.insert(add.begin(), add.end());
    }
    ci.upTo = now;
    stack.pop_back();
  }
}

void PropagateEqualities::processCandidates()
{
  assert(!simp->hasUnappliedSubstitutions());

  // Make a list of the variables on the LHS. We can ignore all others in the RHSs.
  IdSet allLhsVariables;
  for (const auto& e: candidates)  
  {
    assert(e.first.GetKind() == SYMBOL);
    allLhsVariables.insert(e.first.GetNodeNum()); 
  }

  //Map from the node number of the LHS to:
  //(1) the LHS ASTNode, (2) the RHS ASTNode, (3) The symbols in the RHS ASTNode.
  MapToNodeSet mapped;
  mapped = buildMapOfLHStoVariablesInRHS(allLhsVariables);

  typedef const CandidateInfo* qType;
  auto cmp = [](qType left, qType right)
    {
      if (left->vars.size() > right->vars.size())
          return true;
      if (left->vars.size() == right->vars.size())
          return left->id > right->id;
      return false;
    };
  // Fill the backing vector first and heapify once, rather than pushing
  // into an empty queue element by element: that is O(n) instead of
  // O(n log n), and the pop order is unchanged because cmp is a total order
  // (equal variable counts are broken by the unique id).
  //
  // It also sidesteps a GCC false positive. Move-constructing the queue from
  // an *empty* reserved vector runs make_heap over a range GCC cannot see is
  // empty, and it then derives an absurd trip count and reports
  // -Waggressive-loop-optimizations, which is fatal under -Werror in a
  // release build.
  vector<qType> qStore;
  qStore.reserve(mapped.size());

  for (const auto& e: mapped)
    qStore.push_back(&e.second);

  std::priority_queue<qType, vector<qType>, decltype(cmp)> q(
      cmp, std::move(qStore));

  std::vector<uint64_t> replacedOrder;
  replacedOrder.reserve(mapped.size());
  IdToId replacedIndex;
  replacedIndex.reserve(mapped.size());

  while (!q.empty())
  {
    const CandidateInfo* e = q.top();
    q.pop();

    const ASTNode& lhs = e->lhs;
    const uint64_t lhs_id = lhs.GetNodeNum();

    const ASTNode& rhs = e->rhs;
    const IdSet& rhsVariables = e->vars;

    assert(SYMBOL == lhs.GetKind());


    if (rhsVariables.find(lhs_id) != rhsVariables.end())
      continue; // Loops already, so no more processing.

    if (replacedIndex.find(lhs_id) != replacedIndex.end())
      continue; // already replaced.

    update(lhs_id, mapped, replacedOrder, replacedIndex);

    if (!q.empty() && 5* q.top()->vars.size() < rhsVariables.size())
    {
      // The priority queue doesn't automatically update as the priorties change.
      // If the next item in the priority queue is much smaller, loop.
      q.push(e);
      continue;
    }

    if (rhsVariables.find(lhs_id) == rhsVariables.end())
    {
      simp->UpdateSubstitutionMapFewChecks(lhs, rhs);
      replacedIndex.emplace(lhs_id, replacedOrder.size());
      replacedOrder.push_back(lhs_id);
    }
  }

  if (bm->UserFlags.stats_flag)
    std::cerr <<  "{PropagateEqualities} Applied:" << replacedOrder.size() << std::endl;

  candidates.clear();
}

ASTNode PropagateEqualities::topLevel(const ASTNode& a)
{
  assert (bm->UserFlags.propagate_equalities);
  todo=0;

  ASTNode result = a;

  // Needs there to be no unapplied substititions.
  result = simp->applySubstitutionMapAtTopLevel(result);
 
  bm->GetRunTimes()->start(RunTimes::PropagateEqualities);

  buildCandidateList(result);
  
  if (bm->UserFlags.stats_flag)
  {
    std::cerr <<  "{PropagateEqualities} TODO:" << todo << std::endl;
    if (candidates.size() != 0)
      std::cerr <<  "{PropagateEqualities} Candidates:" << candidates.size() << std::endl;
  }

  processCandidates();

  bm->GetRunTimes()->stop(RunTimes::PropagateEqualities);

  result = simp->applySubstitutionMapAtTopLevel(result);

  return result;
}


void PropagateEqualities::addCandidate(const ASTNode a, const ASTNode b)
{
  candidates.push_back(std::make_pair(a,b));

  if (SYMBOL == b.GetKind())
    candidates.push_back(std::make_pair(b,a));
}

// FP constant folding is deferred solver-wide, so a float literal usually
// arrives as to_fp's three-child reinterpret form over constant bits
// rather than as an interned constant. Resolve that form through the
// canonicalising funnel (CreateFPConst) -- the same lookthrough
// RemoveUnconstrained's comparison rule and FloatBlast's native-comparison
// gate use -- so the substitution installs an interned constant that folds
// at every use site. Anything else is returned unchanged.
ASTNode PropagateEqualities::resolveFpLiteral(const ASTNode& n)
{
  if (n.GetKind() == FP_TOFP && n.Degree() == 3 && n[2].GetKind() == BVCONST)
  {
    const SourceSort sort = n.GetSourceSort();
    if (sort.kind() == SourceSort::Kind::FloatingPoint)
      return bm->CreateFPConst(n[2], sort.exponentWidth(),
                               sort.significandWidth());
  }
  return n;
}

void PropagateEqualities::buildXORCandidates(const ASTNode a, bool negated)
{
   if (a[0].GetKind() == EQ && a[0][0].GetValueWidth() == 1 &&
             a[0][1].GetKind() == SYMBOL)
    {
      // XOR ((= 1 v) ... )

      const ASTNode& symbol = a[0][1];
      ASTNode newN = nf->CreateTerm(
          ITE, 1, a[1], nf->CreateTerm(BVNOT, 1, a[0][0]), a[0][0]);

      if (negated)
        newN = nf->CreateTerm(BVNOT, 1, newN);

      addCandidate(symbol, newN);
    }

    if (a[0].GetKind() == EQ && a[0][0].GetValueWidth() == 1 &&
             a[0][0].GetKind() == SYMBOL)
    {
      // XOR ((= v 1) ... )

      const ASTNode& symbol = a[0][0];
      ASTNode newN = nf->CreateTerm(
          ITE, 1, a[1], nf->CreateTerm(BVNOT, 1, a[0][1]), a[0][1]);

      if (negated)
        newN = nf->CreateTerm(BVNOT, 1, newN);

      addCandidate(symbol, newN);
    }


    if (a[1].GetKind() == EQ && a[1][0].GetValueWidth() == 1 &&
             a[1][0].GetKind() == SYMBOL)
    {
      // XOR ( ... (= v 1) )
      const ASTNode& symbol = a[1][0];
      ASTNode newN = nf->CreateTerm(
          ITE, 1, a[0], nf->CreateTerm(BVNOT, 1, a[1][1]), a[1][1]);

      if (negated)
        newN = nf->CreateTerm(BVNOT, 1, newN);

      addCandidate(symbol, newN);
    }
   
    if (a[1].GetKind() == EQ && a[1][0].GetValueWidth() == 1 &&
             a[1][1].GetKind() == SYMBOL)
    {
      // XOR ( ... (= 1 v) )
      const ASTNode& symbol = a[1][1];
      ASTNode newN = nf->CreateTerm(
          ITE, 1, a[0], nf->CreateTerm(BVNOT, 1, a[1][0]), a[1][0]);

      if (negated)
        newN = nf->CreateTerm(BVNOT, 1, newN);

      addCandidate(symbol, newN);
    }

   if (a[0].GetKind() == SYMBOL)
    {
      // (XOR a t )
      const ASTNode& symbol = a[0];
      ASTNode newN = nf->CreateNode(NOT, a[1]);

      if (negated)
        newN = nf->CreateNode(NOT, newN);

      addCandidate(symbol, newN);
    }

   if (a[1].GetKind() == SYMBOL)
    {
      // (XOR t a )
      const ASTNode& symbol = a[1];
      ASTNode newN = nf->CreateNode(NOT, a[0]);

      if (negated)
        newN = nf->CreateNode(NOT, newN);

      addCandidate(symbol, newN);
    }
}

bool PropagateEqualities::isSymbol(ASTNode c)
{
    if (c.GetKind() == BVUMINUS || c.GetKind() == BVNOT)
      return isSymbol(c[0]);

    if (c.GetKind() == BVMULT && c.Degree() ==2 && c[0].isConstant() && simp->BVConstIsOdd(c[0]))
      return isSymbol(c[1]);

    return (c.GetKind() == SYMBOL);
}

// Sent one side of an equals.
void PropagateEqualities::countToDo(ASTNode n)
{
  if (isSymbol(n))
    todo++;

  if ((n.GetKind() == BVPLUS || n.GetKind() == BVXOR) && n.Degree() ==2)
  {
    if (isSymbol(n[0]))
      todo++;
    if (isSymbol(n[1]))
      todo++;
  }
}

// The AND arm below is the only place this reaches another node. Walk its
// spine with suspended ancestors so both deeply nested and very wide
// conjunctions have bounded auxiliary memory. See DeepDag_Test.cpp.
void PropagateEqualities::buildCandidateList(const ASTNode& a)
{
  walkPreOrder(a, [&](const ASTNode& current) {
    return buildCandidateListNode(current);
  });
}

bool PropagateEqualities::buildCandidateListNode(const ASTNode& a)
{

  if (!alreadyVisited.insert(a.GetNodeNum()).second)
    return false;

  const Kind k = a.GetKind();

  if (NOT == k && SYMBOL == a[0].GetKind())
  {
    assert(BOOLEAN_TYPE == a.GetType());
    addCandidate(a[0], ASTFalse);
  }
  else if (SYMBOL == k )
  {
    assert (BOOLEAN_TYPE == a.GetType());
    addCandidate(a, ASTTrue);
  }
  else if (NOT == k && a[0].GetKind() == XOR && a[0].Degree() == 2)
  {
    buildXORCandidates(a[0], true);
  }
  else if (XOR == k && a.Degree() == 2)
  {
    buildXORCandidates(a, false);
  }
  else if (IFF == k || EQ == k)
  {
    const ASTChildren c = a.GetChildren();
    const auto width = c[0].GetValueWidth();
    bool added = false;


    if (SYMBOL == c[0].GetKind())
    {
      addCandidate(c[0],c[1]);
      added = true;
    }
    else if (speculative && c[0].GetKind() == BVUMINUS && c[0][0].GetKind() == SYMBOL)
    {
      addCandidate(c[0][0], nf->CreateTerm(BVUMINUS, width, c[1]));
      added = true;
    }
    else if (c[0].GetKind() == BVNOT && c[0][0].GetKind() == SYMBOL)
    {
      addCandidate(c[0][0], nf->CreateTerm(BVNOT, width, c[1]));
      added = true;
    }
    else if (speculative && c[0].GetKind() == BVPLUS && c[0].Degree() == 2 && c[0][0].GetKind() == SYMBOL )
    {
      ASTNode rep = nf->CreateTerm(BVPLUS, width, c[1], nf->CreateTerm(BVUMINUS, width, c[0][1]));
      addCandidate(c[0][0], rep);
      added = true;
    }

    if (SYMBOL == c[1].GetKind() && SYMBOL != c[0].GetKind()) // addCandidate swaps over arguments, so will have already been added.
    {
      addCandidate(c[1],c[0]);
      added = true;
    }
    else if (speculative && c[1].GetKind() == BVUMINUS && c[1][0].GetKind() == SYMBOL)
    {
      addCandidate(c[1][0], nf->CreateTerm(BVUMINUS, width, c[0]));
      added = true;
    }
    else if (c[1].GetKind() == BVNOT && c[1][0].GetKind() == SYMBOL )
    {
      addCandidate(c[1][0], nf->CreateTerm(BVNOT, width, c[0]));
      added = true;
    }
    else if (speculative && c[1].GetKind() == BVPLUS && c[1].Degree() == 2 && c[1][0].GetKind() == SYMBOL )
    {
      ASTNode rep = nf->CreateTerm(BVPLUS, width, c[0], nf->CreateTerm(BVUMINUS, width, c[1][1]));
      addCandidate(c[1][0], rep);
      added = true;
    }

    if (!added && bm->UserFlags.stats_flag)
    {
      [[maybe_unused]] const auto old = todo;
      countToDo(c[0]);
      countToDo(c[1]);
      //if (todo != old)
        //std::cerr << a;
    }

  }
  else if (FP_SMT_EQ == k)
  {
    // SMT `=` on floats is true equality on the abstract domain (one NaN,
    // two distinct zeros), so substituting one side for the other is sound
    // in every context. fp.eq (FP_EQ) must NEVER be propagated: it
    // identifies +0 with -0, which fp.isNegative, division etc.
    // distinguish. Kept separate from the EQ arm above so the bitvector
    // inverse rewrites (BVNOT/BVUMINUS/BVPLUS) can't see float operands.
    const ASTNode left = resolveFpLiteral(a[0]);
    const ASTNode right = resolveFpLiteral(a[1]);
    if (SYMBOL == left.GetKind())
      addCandidate(left, right);
    else if (SYMBOL == right.GetKind())
      addCandidate(right, left);
  }
  else if (ARRAY_EQ == k &&
           !a[0].GetSourceSort().usesFloatingPointTheory())
  {
    // Whole-array `=` asserted at the top level is true equality on the
    // array domain, so a symbol operand substitutes away exactly like
    // the bitvector EQ case (the occurs check in processCandidates
    // rejects A = store(A, i, v)). Kept separate from the EQ arm above
    // so the bitvector inverse rewrites (BVNOT/BVUMINUS/BVPLUS) can't
    // see array operands. Float- or RoundingMode-sorted arrays are left
    // to abstraction: the model machinery that reconstructs a
    // substituted symbol's cells reads them as plain bits, which is
    // wrong under NaN's many packings and float index canonicalisation.
    if (SYMBOL == a[0].GetKind())
      addCandidate(a[0], a[1]);
    else if (SYMBOL == a[1].GetKind())
      addCandidate(a[1], a[0]);
  }
  return AND == k;
}



}
