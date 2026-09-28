/********************************************************************
 * AUTHORS: Trevor Hansen
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

#include "stp/Simplifier/CommonFactor.h"
#include "stp/Util/DagWalk.h"
#include <algorithm>
#include <cassert>
#include <deque>
#include <iostream>
#include <vector>

namespace stp
{

// Occurrences of each node, which for everything below the root is how many
// places hold it.
//
// Iterative for the reason Rewriting::buildShareCount is: the input decides
// how deep it goes, so a call per level exhausts the stack.
void CommonFactor::buildRefs(const ASTNode& n)
{
  walkPreOrder(n, [&](const ASTNode& current) {
    if (current.Degree() == 0)
      return false;

    return refs[current.GetNodeNum()]++ == 0;
  });
}

// The larger of what the input held this node in and what the rewrite has
// put into it so far. A node can be both -- a product this pass builds can
// hash-cons onto one of the input's, whose own holders have not been walked
// yet -- and the guard wants the count that misses no holder.
uint32_t CommonFactor::references(const ASTNode& n) const
{
  uint32_t most = 1;

  const auto before = refs.find(n.GetNodeNum());
  if (before != refs.end())
    most = std::max(most, before->second);

  const auto after = rewrittenRefs.find(n.GetNodeNum());
  if (after != rewrittenRefs.end())
    most = std::max(most, after->second);

  return most;
}

bool CommonFactor::productOf(const ASTNode& addend, Addend& out) const
{
  const bool negated = addend.GetKind() == BVUMINUS;

  // The negation dies with the product it wraps, so both have to.
  if (negated && references(addend) > 1)
    return false;

  const ASTNode& product = negated ? addend[0] : addend;
  if (product.GetKind() != BVMULT || references(product) > 1)
    return false;

  out.negated = negated;
  out.product = product;
  return true;
}

// The addend with one occurrence of the factor taken out of its product,
// keeping the negation the addend arrived with.
ASTNode CommonFactor::without(const Addend& a, const ASTNode& factor,
                              unsigned width)
{
  ASTVec kept;
  kept.reserve(a.product.Degree() - 1);

  bool dropped = false;
  for (const ASTNode& operand : a.product)
  {
    if (!dropped && operand == factor)
    {
      dropped = true;
      continue;
    }
    kept.push_back(operand);
  }
  assert(dropped);

  ASTNode result =
      kept.size() == 1 ? kept[0] : nf->CreateTerm(BVMULT, width, kept);

  if (a.negated)
    result = nf->CreateTerm(BVUMINUS, width, result);

  return result;
}

ASTNode CommonFactor::sumOf(const ASTVec& addends, unsigned width)
{
  assert(!addends.empty());
  if (addends.size() == 1)
    return addends[0];
  return nf->CreateTerm(BVPLUS, width, addends);
}

bool CommonFactor::extractOne(ASTVec& addends, unsigned width)
{
  // Two products at least, or there is nothing an operand can be shared
  // between. Most sums fail this, and it is the whole cost of them.
  size_t candidates = 0;
  for (const ASTNode& a : addends)
    if (a.GetKind() == BVMULT ||
        (a.GetKind() == BVUMINUS && a[0].GetKind() == BVMULT))
      candidates++;

  if (candidates < 2)
    return false;

  std::vector<Addend> products;
  products.reserve(addends.size());

  size_t reducible = 0;
  for (const ASTNode& a : addends)
  {
    Addend p;
    if (productOf(a, p))
      reducible++;
    products.push_back(p);
  }

  // The share guard may have ruled enough of them out.
  if (reducible < 2)
    return false;

  // How many of the products each operand appears in. Ordered by node
  // number, so the operand the scan below settles on doesn't depend on the
  // order the addends arrived in.
  std::map<uint64_t, uint32_t> tally;
  std::map<uint64_t, ASTNode> byNum;

  for (const Addend& p : products)
  {
    if (p.product.IsNull())
      continue;

    // An operand a product repeats is still one operand of it to give up.
    ankerl::unordered_dense::set<uint64_t> counted;
    for (const ASTNode& operand : p.product)
      if (counted.insert(operand.GetNodeNum()).second)
      {
        tally[operand.GetNodeNum()]++;
        byNum.insert({operand.GetNodeNum(), operand});
      }
  }

  uint32_t best = 1;
  uint64_t chosen = 0;
  for (const auto& entry : tally)
    if (entry.second > best)
    {
      best = entry.second;
      chosen = entry.first;
    }

  // One product holding an operand is the operand it already multiplies by:
  // taking it out builds the same multiplication somewhere else.
  if (best < 2)
    return false;

  const ASTNode factor = byNum.find(chosen)->second;

  ASTVec inner, kept;
  inner.reserve(best);
  kept.reserve(addends.size() - best + 1);

  for (size_t i = 0; i < addends.size(); i++)
  {
    const Addend& p = products[i];
    const bool holds =
        !p.product.IsNull() &&
        std::find(p.product.begin(), p.product.end(), factor) !=
            p.product.end();

    if (holds)
      inner.push_back(without(p, factor, width));
    else
      kept.push_back(addends[i]);
  }
  assert(inner.size() == static_cast<size_t>(best));

  // The remainders can share a factor of their own: the two operands the
  // products of (x*y*a + x*y*b) have in common come out one after the
  // other, and the second is only visible once the first is gone.
  extract(inner, width);

  kept.push_back(nf->CreateTerm(BVMULT, width, factor, sumOf(inner, width)));
  addends.swap(kept);

  saved += best - 1;
  return true;
}

bool CommonFactor::extract(ASTVec& addends, unsigned width)
{
  bool changed = false;

  // Each round replaces the products holding the factor -- two of them at
  // least, each costing a multiplication -- with one multiplication, so
  // what the round counts strictly falls and the loop ends.
  while (extractOne(addends, width))
    changed = true;

  return changed;
}

// Bottom-up, once per node of the input: the operands of a sum are whatever
// they rewrote to before the sum is looked at.
//
// Iterative for the reason the share count is, and with the same shape: a
// frame per suspended ancestor, the answers in a map the frames read.
ASTNode CommonFactor::rewrite(const ASTNode& top)
{
  struct Frame
  {
    ASTNode n;
    size_t i = 0;
    ASTVec kids;
    explicit Frame(const ASTNode& n_) : n(n_) {}
  };

  ASTNodeMap done;

  // A deque, so descending into a child never moves the frames above it.
  std::deque<Frame> stack;
  stack.emplace_back(top);

  while (true)
  {
    Frame& current = stack.back();

    if (current.i < current.n.Degree())
    {
      const ASTNode& child = current.n[current.i];

      // A leaf rewrites to itself, which is not worth a frame or a map
      // entry: the input is mostly leaves.
      if (child.Degree() == 0)
      {
        current.kids.push_back(child);
        current.i++;
        continue;
      }

      const ASTNodeMap::const_iterator known = done.find(child);
      if (known == done.end())
      {
        stack.emplace_back(child);
        continue;
      }

      current.kids.push_back(known->second);
      current.i++;
      continue;
    }

    const ASTNode& n = current.n;
    ASTVec& kids = current.kids;

    bool changed = false;
    for (size_t i = 0; i < kids.size(); i++)
      if (kids[i] != n[i])
        changed = true;

    if (n.GetKind() == BVPLUS && extract(kids, n.GetValueWidth()))
      changed = true;

    ASTNode result = n;
    if (changed)
    {
      if (n.GetKind() == BVPLUS)
        result = sumOf(kids, n.GetValueWidth());
      else if (n.GetType() == BOOLEAN_TYPE)
        result = nf->CreateNode(n.GetKind(), kids);
      else
        result = nf->CreateArrayTerm(n.GetKind(), n.GetIndexWidth(),
                                     n.GetValueWidth(), kids);
    }

    // What the input held this node in now holds its replacement, which is
    // what the share guard reads. Two nodes that rewrite to one are held by
    // the places that held either.
    const auto held = refs.find(n.GetNodeNum());
    rewrittenRefs[result.GetNodeNum()] +=
        held == refs.end() ? 1 : held->second;

    done.insert({n, result});
    stack.pop_back();

    if (stack.empty())
      return result;
  }
}

ASTNode CommonFactor::topLevel(const ASTNode& n)
{
  stpMgr->GetRunTimes()->start(RunTimes::CommonFactor);

  saved = 0;
  refs.clear();
  rewrittenRefs.clear();

  buildRefs(n);
  const ASTNode result = rewrite(n);

  if (stpMgr->UserFlags.stats_flag)
    std::cerr << "{CommonFactor} Multiplications saved:" << saved << std::endl;

  refs.clear();
  rewrittenRefs.clear();

  stpMgr->GetRunTimes()->stop(RunTimes::CommonFactor);
  return result;
}
}
