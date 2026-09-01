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
#include <cassert>

namespace stp
{
namespace
{
// Give up once the tally holds this many pairs, so a query with very wide
// additions can't make the search quadratically expensive. An entry costs
// about thirty bytes, so this is a cap of roughly a hundred megabytes -- the
// bound is written in the units that actually run out.
const size_t PAIR_ENTRY_LIMIT = 4000000;

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
    if (current.GetKind() == kind && current.Degree() >= 2)
      plusNodes.push_back(current);
    for (unsigned i = 0; i < current.Degree(); i++)
      stack.push_back(current[i]);
  }
}

// Which operands are worth enumerating pairs of. An addition never gains an
// operand it didn't start with -- a substitution only removes two and adds
// the node built from them -- so an operand in one addition now is in one
// addition for the rest of the pass, and no pair it belongs to can ever be
// shared. Deciding this once is exact and costs a single walk.
void CommonSubSum::markShareable()
{
  ankerl::unordered_dense::map<uint64_t, uint32_t> holders;

  for (const auto& sum : sums)
  {
    const ASTVec& v = sum.ops;

    // A two-operand addition already *is* its own pair; extracting from it
    // would leave a one-child BVPLUS that rebuilds to itself. It is not a
    // holder, because pairs are never enumerated over it.
    if (v.size() < 3)
      continue;

    for (size_t i = 0; i < v.size(); i++)
      if (i == 0 || v[i] != v[i - 1])
        holders[v[i].GetNodeNum()]++;
  }

  for (const auto& h : holders)
    if (h.second >= 2)
      shareable.insert(h.first);
}

// The operands of one addition that pairs are enumerated over: sorted, with
// each repeat and each operand not worth pairing dropped.
//
// The list is already sorted by node number, so an operand repeated k times
// sits in one run and taking each run once records every distinct pair once.
// Counting the C(k,2) copies separately would both overstate the sharing
// and, worse, make the substitution run repeatedly on one addition -- after
// the first pass its operands are gone, so the later passes would add the
// shared node without removing anything and change the addition's value.
void CommonSubSum::eligibleOf(const ASTVec& v, std::vector<uint64_t>& out) const
{
  out.clear();

  // A two-operand addition already *is* its own pair; extracting from it
  // would leave a one-child BVPLUS that rebuilds to itself.
  if (v.size() < 3)
    return;

  for (size_t i = 0; i < v.size(); i++)
  {
    if (i > 0 && v[i] == v[i - 1])
      continue;
    const uint64_t num = v[i].GetNodeNum();
    if (shareable.count(num) != 0)
      out.push_back(num);
  }
}

bool CommonSubSum::bump(uint64_t a, uint64_t b)
{
  const NodePair key = (a < b) ? packPair(a, b) : packPair(b, a);

  // Checked only at the cap, so the ordinary path pays one lookup, not two.
  if (occurrences.size() >= PAIR_ENTRY_LIMIT &&
      occurrences.find(key) == occurrences.end())
    return false;

  const uint32_t now = ++occurrences[key];

  // A tally of one can't win, so its snapshot would only be heap churn.
  // The initial build pushes nothing: it is heapified whole afterwards.
  if (now >= 2 && !tallying)
    candidates.push({now, key});
  return true;
}

void CommonSubSum::drop(uint64_t a, uint64_t b)
{
  const NodePair key = (a < b) ? packPair(a, b) : packPair(b, a);
  const auto it = occurrences.find(key);

  assert(it != occurrences.end() && it->second > 0);
  if (it != occurrences.end() && --it->second == 0)
    occurrences.erase(it);
}

// One addition's whole contribution to the tally.
bool CommonSubSum::addPairs(const ASTVec& v)
{
  std::vector<uint64_t> eligible;
  eligibleOf(v, eligible);

  for (size_t i = 0; i < eligible.size(); i++)
    for (size_t j = i + 1; j < eligible.size(); j++)
      if (!bump(eligible[i], eligible[j]))
        return false;

  return true;
}

// Moves the tally from one addition's operand list to its replacement.
//
// A substitution takes two operands out and puts one in, so all but a
// handful of the addition's pairs are the same on both sides and only the
// ones touching a departing or arriving operand need touching. Removing the
// old list's pairs and adding the new list's would be quadratic in the
// addition's width for a change that is linear in it -- which is what made a
// query of overlapping sums quadratic in the number of rounds.
bool CommonSubSum::repair(const ASTVec& before, const ASTVec& after)
{
  std::vector<uint64_t> was, now, gone, arrived, kept;
  eligibleOf(before, was);
  eligibleOf(after, now);

  std::set_difference(was.begin(), was.end(), now.begin(), now.end(),
                      std::back_inserter(gone));
  std::set_difference(now.begin(), now.end(), was.begin(), was.end(),
                      std::back_inserter(arrived));
  std::set_intersection(was.begin(), was.end(), now.begin(), now.end(),
                        std::back_inserter(kept));

  // A pair of one departing and one arriving operand is in neither list's
  // pair set, so it needs nothing.
  for (size_t i = 0; i < gone.size(); i++)
  {
    for (size_t j = i + 1; j < gone.size(); j++)
      drop(gone[i], gone[j]);
    for (const uint64_t k : kept)
      drop(gone[i], k);
  }

  for (size_t i = 0; i < arrived.size(); i++)
  {
    for (size_t j = i + 1; j < arrived.size(); j++)
      if (!bump(arrived[i], arrived[j]))
        return false;
    for (const uint64_t k : kept)
      if (!bump(arrived[i], k))
        return false;
  }

  return true;
}

// A node this pass builds can turn out, through hash-consing, to be an
// operand the query already had and that wasn't worth pairing. Making it
// eligible now leaves every addition already holding it short of the pairs
// it forms there, so those are added before anything reads the tally again.
bool CommonSubSum::promote(const ASTNode& n)
{
  const uint64_t num = n.GetNodeNum();
  if (!shareable.insert(num).second)
    return true;

  std::vector<uint64_t> eligible;
  for (const auto& sum : sums)
  {
    const ASTVec& v = sum.ops;
    if (!std::binary_search(v.begin(), v.end(), n, byNodeNum))
      continue;

    eligibleOf(v, eligible);
    for (const uint64_t other : eligible)
      if (other != num && !bump(num, other))
        return false;
  }

  return true;
}

// The tally over every addition, built once. Later rounds patch it.
bool CommonSubSum::buildOccurrences()
{
  tallying = true;
  for (const auto& sum : sums)
    if (!addPairs(sum.ops))
    {
      tallying = false;
      return false;
    }
  tallying = false;

  // One live snapshot per pair. Heap layout doesn't reach the result: the
  // comparator is a total order, so the sequence of pops is the same
  // whatever order this vector arrives in.
  std::vector<Candidate> live;
  for (const auto& entry : occurrences)
    if (entry.second >= 2)
      live.push_back({entry.second, entry.first});
  candidates = decltype(candidates)(CandidateOrder(), std::move(live));

  return true;
}

// Finds the operand pair shared by the most additions and pulls it out into
// its own node. Returns false once no pair is shared, or a guard fires.
bool CommonSubSum::extractOnePair()
{
  // Ties go to the lowest-numbered pair -- the heap's order, not the hash
  // table's layout, decides, so the formula handed to the bit-blaster is
  // deterministic. Stale snapshots are discarded on sight; a pair whose
  // live tally is >=2 always has a live snapshot, because the increment
  // that set the tally pushed one and only a winning pop consumes it.
  uint32_t best = 0;
  NodePair bestPair = 0;
  while (!candidates.empty())
  {
    const Candidate top = candidates.top();
    candidates.pop();
    const auto live = occurrences.find(top.pair);
    if (live == occurrences.end())
      continue;
    if (live->second == top.count)
    {
      best = top.count;
      bestPair = top.pair;
      break;
    }
    // Stale, and the pair may hold no other snapshot: a tally that rose
    // pushed one per step, but a tally that fell pushed nothing on the way
    // down. Restore the live value or the pair goes invisible. Strictly
    // smaller than what was discarded, so the loop makes progress.
    if (live->second >= 2 && live->second < top.count)
      candidates.push({live->second, top.pair});
  }

  if (best < 2)
    return false;

  // Both operands sit in a common application, so they share its width.
  const ASTNode first = byNum[bestPair >> 32];
  const ASTNode second = byNum[bestPair & 0xffffffffu];
  const ASTNode shared =
      booleanKind() ? nf->CreateNode(kind, first, second)
                    : nf->CreateTerm(kind, first.GetValueWidth(), first,
                                     second);
  byNum[shared.GetNodeNum()] = shared;

  // Before any operand list moves, so that the two stay in step.
  if (!promote(shared))
  {
    truncated = true;
    return false;
  }

  std::vector<uint32_t> hits;
  for (uint32_t i = 0; i < sums.size(); i++)
  {
    const ASTVec& v = sums[i].ops;
    if (v.size() >= 3 &&
        std::binary_search(v.begin(), v.end(), first, byNodeNum) &&
        std::binary_search(v.begin(), v.end(), second, byNodeNum))
      hits.push_back(i);
  }

  long applied = 0;
  for (uint32_t sum : hits)
  {
    ASTVec& v = sums[sum].ops;

    // Locate both operands before removing either, so that a sum which
    // somehow lacks one of them is left untouched rather than rewritten
    // into a different value.
    bool found = true;
    ASTVec scratch = v;
    for (unsigned which = 0; which < 2 && found; which++)
    {
      const uint64_t wanted =
          (which == 0) ? (bestPair >> 32) : (bestPair & 0xffffffffu);
      found = false;
      for (size_t i = 0; i < scratch.size(); i++)
        if (scratch[i].GetNodeNum() == wanted)
        {
          scratch.erase(scratch.begin() + i);
          found = true;
          break;
        }
    }
    if (!found)
      continue;

    scratch.push_back(shared);
    std::sort(scratch.begin(), scratch.end(), byNodeNum);

    // Only this addition's pairs moved, so only this addition's contribution
    // is patched; every other pair's tally is still right.
    const bool room = repair(v, scratch);
    v.swap(scratch);
    applied++;
    if (!room)
    {
      truncated = true;
      break;
    }
  }

  // The winner's own snapshot was consumed above. Should its tally still be
  // live -- a hit skipped, or the pair also held by untouched additions --
  // restore the snapshot so the invariant on the heap keeps holding.
  const auto still = occurrences.find(bestPair);
  if (still != occurrences.end() && still->second >= 2)
    candidates.push({still->second, bestPair});

  if (applied < 2)
    return false;

  saved += applied - 1;
  return !truncated;
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
    if (booleanKind())
      result = nf->CreateNode(kind, kids);
    else
      result = nf->CreateTerm(kind, n.GetValueWidth(), kids);
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
  sums.clear();
  sumIndex.clear();
  byNum.clear();
  occurrences.clear();
  shareable.clear();
  candidates = decltype(candidates)();

  ASTNodeSet seen;
  ASTVec plusNodes;
  collect(n, seen, plusNodes);

  ASTNode result = n;
  if (plusNodes.size() >= 2)
  {
    sums.reserve(plusNodes.size());
    for (const auto& p : plusNodes)
    {
      ASTVec v(p.GetChildren().begin(), p.GetChildren().end());
      std::sort(v.begin(), v.end(), byNodeNum);
      byNum[p.GetNodeNum()] = p;
      for (const auto& k : v)
        byNum[k.GetNodeNum()] = k;
      sums.push_back({p.GetNodeNum(), std::move(v)});
    }

    // Ascending node number, so iteration order -- and with it what lands
    // in a capped tally -- doesn't depend on the walk.
    std::sort(sums.begin(), sums.end(),
              [](const SumEntry& a, const SumEntry& b) { return a.num < b.num; });
    for (uint32_t i = 0; i < sums.size(); i++)
      sumIndex[sums[i].num] = i;

    markShareable();

    // A pair needs two shareable operands, so fewer than two shareable
    // operands means no round can fire.
    if (shareable.size() >= 2)
    {
      if (!buildOccurrences())
        truncated = true;
      else
      {
        long round = 0;
        for (; round < ROUND_LIMIT && extractOnePair(); round++)
          ;

        // Rounds are what bounds the greedy loop, not what it converges on:
        // exhausting them leaves shared pairs behind just as the size guard
        // does, so say so rather than report a fixed point.
        if (round == ROUND_LIMIT)
          truncated = true;
      }
    }

    if (saved > 0)
    {
      std::map<uint64_t, ASTVec> changed;
      for (const auto& p : plusNodes)
      {
        const ASTVec& v = sums[sumIndex[p.GetNodeNum()]].ops;
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
    std::cerr << "{CommonSubSum} " << _kind_names[kind]
              << " applications saved:" << saved
              << " Truncated:" << (truncated ? 1 : 0) << std::endl;

  sums.clear();
  sumIndex.clear();
  byNum.clear();
  occurrences.clear();
  shareable.clear();
  candidates = decltype(candidates)();

  stpMgr->GetRunTimes()->stop(RunTimes::CommonSubSum);
  return result;
}
}
