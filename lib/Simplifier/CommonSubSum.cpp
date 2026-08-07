/********************************************************************
 * AUTHORS: Trevor Hansen
 *
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

#include "stp/Simplifier/CommonSubSum.h"
#include <algorithm>

namespace stp
{
namespace
{
// Stop enumerating pairs once a round would visit this many, so a query with
// very wide additions can't make the search quadratically expensive.
const long PAIR_VISIT_LIMIT = 40000000;

// Each round removes at least one adder, so this only bounds pathological
// inputs, not ordinary ones.
const long ROUND_LIMIT = 2000;

bool byNodeNum(const ASTNode& a, const ASTNode& b)
{
  return a.GetNodeNum() < b.GetNodeNum();
}
}

void CommonSubSum::collect(const ASTNode& n, ASTNodeSet& seen,
                           ASTVec& plusNodes)
{
  ASTVec stack(1, n);
  while (!stack.empty())
  {
    const ASTNode current = stack.back();
    stack.pop_back();
    if (!seen.insert(current).second)
      continue;
    if (current.GetKind() == BVPLUS && current.Degree() >= 2)
      plusNodes.push_back(current);
    for (unsigned i = 0; i < current.Degree(); i++)
      stack.push_back(current[i]);
  }
}

// Finds the operand pair shared by the most additions and pulls it out into
// its own node. Returns false once no pair is shared, or a guard fires.
bool CommonSubSum::extractOnePair()
{
  std::map<std::pair<uint64_t, uint64_t>, std::vector<uint64_t>> occurrences;

  long visited = 0;
  for (const auto& sum : operands)
  {
    const ASTVec& v = sum.second;

    // A two-operand addition already *is* its own pair; extracting from it
    // would leave a one-child BVPLUS that rebuilds to itself.
    if (v.size() < 3)
      continue;

    visited += (long)v.size() * (long)v.size();
    if (visited > PAIR_VISIT_LIMIT)
    {
      truncated = true;
      return false;
    }

    for (size_t i = 0; i < v.size(); i++)
      for (size_t j = i + 1; j < v.size(); j++)
        occurrences[{v[i].GetNodeNum(), v[j].GetNodeNum()}].push_back(
            sum.first);
  }

  size_t best = 0;
  std::pair<uint64_t, uint64_t> bestPair;
  for (const auto& entry : occurrences)
    if (entry.second.size() > best)
    {
      best = entry.second.size();
      bestPair = entry.first;
    }

  if (best < 2)
    return false;

  // Both operands are addends of a common addition, so they share its width.
  const ASTNode first = byNum[bestPair.first];
  const ASTNode second = byNum[bestPair.second];
  const ASTNode shared =
      nf->CreateTerm(BVPLUS, first.GetValueWidth(), first, second);
  byNum[shared.GetNodeNum()] = shared;

  const std::vector<uint64_t> hits = occurrences[bestPair];
  for (uint64_t sum : hits)
  {
    ASTVec& v = operands[sum];
    for (unsigned which = 0; which < 2; which++)
    {
      const uint64_t wanted = (which == 0) ? bestPair.first : bestPair.second;
      for (size_t i = 0; i < v.size(); i++)
        if (v[i].GetNodeNum() == wanted)
        {
          v.erase(v.begin() + i);
          break;
        }
    }
    v.push_back(shared);
    std::sort(v.begin(), v.end(), byNodeNum);
  }

  saved += (long)hits.size() - 1;
  return true;
}

// Rebuilds the DAG with the new operand lists. A replacement's children are
// themselves rebuilt, so a shared sub-sum that refers to a rewritten
// addition stays consistent.
ASTNode CommonSubSum::rebuild(const ASTNode& n,
                              const std::map<uint64_t, ASTVec>& changed,
                              ASTNodeMap& cache)
{
  if (n.Degree() == 0)
    return n;

  const ASTNodeMap::const_iterator cached = cache.find(n);
  if (cached != cache.end())
    return cached->second;

  ASTNode result;
  const auto replacement = changed.find(n.GetNodeNum());
  if (replacement != changed.end())
  {
    ASTVec kids;
    kids.reserve(replacement->second.size());
    for (const auto& k : replacement->second)
      kids.push_back(rebuild(k, changed, cache));
    result = nf->CreateTerm(BVPLUS, n.GetValueWidth(), kids);
  }
  else
  {
    ASTVec kids;
    kids.reserve(n.Degree());
    bool unchanged = true;
    for (unsigned i = 0; i < n.Degree(); i++)
    {
      const ASTNode k = rebuild(n[i], changed, cache);
      if (k != n[i])
        unchanged = false;
      kids.push_back(k);
    }

    if (unchanged)
      result = n;
    else if (n.GetType() == BOOLEAN_TYPE)
      result = nf->CreateNode(n.GetKind(), kids);
    else
      result = nf->CreateArrayTerm(n.GetKind(), n.GetIndexWidth(),
                                   n.GetValueWidth(), kids);
  }

  cache.insert({n, result});
  return result;
}

ASTNode CommonSubSum::topLevel(const ASTNode& n)
{
  stpMgr->GetRunTimes()->start(RunTimes::CommonSubSum);

  saved = 0;
  truncated = false;
  operands.clear();
  byNum.clear();

  ASTNodeSet seen;
  ASTVec plusNodes;
  collect(n, seen, plusNodes);

  ASTNode result = n;
  if (plusNodes.size() >= 2)
  {
    for (const auto& p : plusNodes)
    {
      ASTVec v(p.GetChildren().begin(), p.GetChildren().end());
      std::sort(v.begin(), v.end(), byNodeNum);
      operands[p.GetNodeNum()] = v;
      byNum[p.GetNodeNum()] = p;
      for (const auto& k : v)
        byNum[k.GetNodeNum()] = k;
    }

    for (long round = 0; round < ROUND_LIMIT && extractOnePair(); round++)
      ;

    if (saved > 0)
    {
      std::map<uint64_t, ASTVec> changed;
      for (const auto& p : plusNodes)
      {
        const ASTVec& v = operands[p.GetNodeNum()];
        if (v.size() != p.Degree())
          changed[p.GetNodeNum()] = v;
      }

      if (!changed.empty())
      {
        ASTNodeMap cache;
        result = rebuild(n, changed, cache);
      }
    }
  }

  if (stpMgr->UserFlags.stats_flag)
    std::cerr << "{CommonSubSum} Adders saved:" << saved
              << " Truncated:" << (truncated ? 1 : 0) << std::endl;

  operands.clear();
  byNum.clear();

  stpMgr->GetRunTimes()->stop(RunTimes::CommonSubSum);
  return result;
}
}
