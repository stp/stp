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
#include <string>
#include <utility>
#include <queue>

namespace stp
{

void log(std::string s)
{
#if 0
  std::cerr << ">>" << s;
#endif
}

typedef std::unordered_set<uint64_t> IdSet;
typedef std::unordered_map<uint64_t, uint64_t> IdToId;
typedef std::unordered_map<uint64_t, IdSet> IdToIdSet;
typedef std::unordered_map<uint64_t, std::tuple <ASTNode, ASTNode, IdSet > > MapToNodeSet;

void tagNodes(const ASTNode& n, const uint64_t tag, IdToId& nodeToTag, ASTNodeSet& shared)
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

  if (cache.find(n_id) != cache.end())
  {
    const auto& item = cache.find(n_id)->second;
    variables.insert(item.begin(), item.end());
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
  ASTNodeSet shared;
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

  MapToNodeSet mapped;

  for (const auto& e: candidates)
  {
    IdSet visited;
    IdSet variables;
    intersection(e.second, visited, variables, allLhsVariables, cache);
    mapped.insert(std::make_pair(e.first.GetNodeNum(), std::make_tuple(e.first, e.second, variables)));
  }

  return mapped;
}

void update(const uint64_t n, MapToNodeSet& m, const IdSet& replaced)
{
    auto& variables = std::get<2>(m[n]);
    vector<uint64_t> toRemove;
    vector<IdSet*> toAdd;

    // all the variables that get inserted have already been updated.
    for (const auto& v: variables)
    {
      if (replaced.find(v) != replaced.end())
      {
          // It's been replaced.
          update(v,m,replaced);
          toRemove.push_back(v);
          toAdd.push_back(&std::get<2>(m.find(v)->second));
      }
    }
    for (const auto& e: toRemove)
      variables.erase(e);

    for (const auto& e: toAdd)
      variables.insert(e->begin(), e->end()); 
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

  typedef std::tuple<ASTNode, ASTNode, const IdSet*> qType;
  auto cmp = [](qType left, qType right) 
    { return std::get<2>(left)->size() > std::get<2>(right)->size(); };  
  std::priority_queue < qType, vector<qType>, decltype(cmp) > q(cmp);

  for (const auto& e: mapped)
  {
    const ASTNode& lhs = std::get<0>(e.second);
    const ASTNode& rhs = std::get<1>(e.second);
    const IdSet* varsInRHS = &(std::get<2>(e.second));
    auto d = std::make_tuple(lhs,rhs,varsInRHS);
    q.push(d);
  }

  IdSet variablesReplacedAlready;

  while (!q.empty())
  {
    auto e = q.top();
    q.pop();

    const ASTNode& lhs = std::get<0>(e);
    const uint64_t lhs_id = lhs.GetNodeNum();

    const ASTNode& rhs = std::get<1>(e);
    const IdSet& rhsVariables = *std::get<2>(e);

    assert(SYMBOL == lhs.GetKind());


    if (rhsVariables.find(lhs_id) != rhsVariables.end())
      continue; // Loops already, so no more processing.

    if (variablesReplacedAlready.find(lhs_id) != variablesReplacedAlready.end())
      continue; // already replaced.

    update(lhs.GetNodeNum(), mapped, variablesReplacedAlready);
    
    if (!q.empty() && 5* std::get<2>(q.top())->size() < rhsVariables.size())
    {
      // The priority queue doesn't automatically update as the priorties change.
      // If the next item in the priority queue is much smaller, loop.
      q.push(e);
      continue;
    }
 
    if (rhsVariables.find(lhs_id) == rhsVariables.end())
    {
      simp->UpdateSubstitutionMapFewChecks(lhs, rhs);
      variablesReplacedAlready.insert(lhs_id);
    }
  }

  if (bm->UserFlags.stats_flag)
    std::cerr <<  "{PropagateEqualities} Applied:" << variablesReplacedAlready.size() << std::endl;

  candidates.clear();
}

ASTNode PropagateEqualities::topLevel(const ASTNode& a)
{
  assert (bm->UserFlags.propagate_equalities);
  todo=0;

  ASTNode result = a;

  // Needs there to be no unapplied substititions.
  if (simp->hasUnappliedSubstitutions())
  {
    result = simp->applySubstitutionMap(result);
    simp->haveAppliedSubstitutionMap();
  }

  bm->GetRunTimes()->start(RunTimes::PropagateEqualities);
  
  //if (AND == a.GetKind())
    //result = AndPropagate(result, at);
    // TODO should write the substitutions through?
  buildCandidateList(result);
  
  if (bm->UserFlags.stats_flag)
  {
    std::cerr <<  "{PropagateEqualities} TODO:" << todo << std::endl;
    if (candidates.size() != 0)
      std::cerr <<  "{PropagateEqualities} Candidates:" << candidates.size() << std::endl;
  }

  processCandidates();

  bm->GetRunTimes()->stop(RunTimes::PropagateEqualities);

  return result;
}


void PropagateEqualities::addCandidate(const ASTNode a, const ASTNode b)
{
  candidates.push_back(std::make_pair(a,b));

  if (SYMBOL == b.GetKind())
    candidates.push_back(std::make_pair(b,a));    
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

#if 0
ASTNode PropagateEqualities::AndPropagate(const ASTNode& input, ArrayTransformer* at)
{
  assert(input.GetKind() == AND);
  ASTVec c = FlattenKind(AND, input.GetChildren());
  
  ASTVec result;

  bool different = false;
  for (const auto& it : c)
  {
    ASTNode changed = it;
    const Kind k = changed.GetKind();
    assert(k != AND); // Should have been flattened out already.

    if (NOT == k && SYMBOL == it[0].GetKind()) // (NOT a)
        changed = propagate(it,at);
    else if (SYMBOL == k) // (a)
        changed = propagate(it,at);
    else if ((IFF == k || EQ == k) && (it[0].GetKind() == SYMBOL && it[1].GetChildren().size() == 0)) // (= x y), (= x 55)
        changed = propagate(it,at);
    else if ((IFF == k || EQ == k) && (it[0].GetKind() == SYMBOL && it[1].Degree() == 0 && it[1][0].GetKind() == SYMBOL))  // (= x (bvnot y)), 
        changed = propagate(it,at);
    else if (XOR == k && it.Degree() == 2 && it[0].GetKind() == SYMBOL && it[1].Degree() == 0) 
        changed = propagate(it,at);
    else if (NOT == k && XOR == it[0].GetKind() && it[0].Degree() == 2 && it[0][0].GetKind() == SYMBOL && it[0][1].Degree() == 0)
        changed = propagate(it,at);
  
    if (!different && it != changed) 
    {
        different = true;
        result.reserve(c.size());
        for (ASTVec::iterator it1 = c.begin(); *it1 != it; it1++)
           result.push_back(*it1);
    }

    if (changed != ASTTrue)
       result.push_back(changed);

     alreadyVisited.insert(it.GetNodeNum());
  }

  if (!different)
    return input;

  ASTNode output;
  if (result.size() == 0)
    output = ASTTrue;
  else if (result.size() == 1)
    output = result[0];
  else 
    output = nf->CreateNode(AND, result);

  return output;
}
#endif

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

void PropagateEqualities::buildCandidateList(const ASTNode& a)
{

  if (!alreadyVisited.insert(a.GetNodeNum()).second)
    return;

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
    const ASTVec& c = a.GetChildren();
    const auto width = c[0].GetValueWidth();
    bool added = false;


    if (SYMBOL == c[0].GetKind())
    {
      addCandidate(c[0],c[1]);
      added = true;
    }
    else if (c[0].GetKind() == BVUMINUS && c[0][0].GetKind() == SYMBOL)
    {
      addCandidate(c[0][0], nf->CreateTerm(BVUMINUS, width, c[1]));
      added = true;
    }
    else if (c[0].GetKind() == BVNOT && c[0][0].GetKind() == SYMBOL)
    {
      addCandidate(c[0][0], nf->CreateTerm(BVNOT, width, c[1]));
      added = true;
    }
    else if (c[0].GetKind() == BVPLUS && c[0].Degree() == 2 && c[0][0].GetKind() == SYMBOL )
    {
      ASTNode rep = nf->CreateTerm(BVPLUS, width, c[1], nf->CreateTerm(BVUMINUS, width, c[0][1]));
      addCandidate(c[0][0], rep);
      added = true;
    }

    if (SYMBOL == c[1].GetKind())
    {
      addCandidate(c[1],c[0]);
      added = true;
    }
    else if (c[1].GetKind() == BVUMINUS && c[1][0].GetKind() == SYMBOL)
    {
      addCandidate(c[1][0], nf->CreateTerm(BVUMINUS, width, c[0]));
      added = true;
    }
    else if (c[1].GetKind() == BVNOT && c[1][0].GetKind() == SYMBOL )
    {
      addCandidate(c[1][0], nf->CreateTerm(BVNOT, width, c[0]));
      added = true;
    }
    else if (c[1].GetKind() == BVPLUS && c[1].Degree() == 2 && c[1][0].GetKind() == SYMBOL )
    {
      ASTNode rep = nf->CreateTerm(BVPLUS, width, c[0], nf->CreateTerm(BVUMINUS, width, c[1][1]));
      addCandidate(c[1][0], rep);
      added = true;
    }

    if (!added && bm->UserFlags.stats_flag)
    {
      const auto old = todo;
      countToDo(c[0]);
      countToDo(c[1]);
      //if (todo != old)
        //std::cerr << a;
    }

  }
  else if (AND == k)
  {
    for (const auto& it : a)
    {
      if (always_true)
        simp->UpdateAlwaysTrueFormSet(it);
      
      buildCandidateList(it);
    }
  }
}



}