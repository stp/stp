/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: Aug, 2026
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

#include "stp/ToSat/BVEQCongruenceClosure.h"

namespace stp
{

void BVEQCongruenceClosure::init(unsigned n)
{
  parent_.assign(n, 0);
  rank_.assign(n, 0);
  proofParent_.assign(n, 0);
  proofEdge_.assign(n, -1);
  for (unsigned i = 0; i < n; ++i)
  {
    parent_[i] = i;
    proofParent_[i] = i;
  }
}

unsigned BVEQCongruenceClosure::find(unsigned x)
{
  while (parent_[x] != x)
    x = parent_[x];
  return x;
}

void BVEQCongruenceClosure::reroot(unsigned x)
{
  // Walk to the root first, then relink on the way back: rewriting the links
  // in place while following them would lose the rest of the path.
  std::vector<unsigned> nodes;
  std::vector<int> edges;
  unsigned cur = x;
  while (proofParent_[cur] != cur)
  {
    nodes.push_back(cur);
    edges.push_back(proofEdge_[cur]);
    cur = proofParent_[cur];
  }
  nodes.push_back(cur);

  for (size_t i = nodes.size(); i-- > 1;)
  {
    proofParent_[nodes[i]] = nodes[i - 1];
    proofEdge_[nodes[i]] = edges[i - 1];
  }
  proofParent_[x] = x;
  proofEdge_[x] = -1;
}

void BVEQCongruenceClosure::unite(unsigned x, unsigned y, unsigned eqIdx)
{
  unsigned rx = find(x);
  unsigned ry = find(y);
  if (rx == ry)
    return;

  // The proof edge goes between the equality's own two sides, not between
  // the class representatives -- that is the whole point of keeping it apart
  // from the union-find below.
  reroot(x);
  proofParent_[x] = y;
  proofEdge_[x] = static_cast<int>(eqIdx);

  if (rank_[rx] < rank_[ry])
  {
    parent_[rx] = ry;
  }
  else if (rank_[rx] > rank_[ry])
  {
    parent_[ry] = rx;
  }
  else
  {
    parent_[ry] = rx;
    rank_[rx]++;
  }
}

void BVEQCongruenceClosure::explain(unsigned x, unsigned y,
                                    std::vector<unsigned>& edges)
{
  std::vector<unsigned> px, py;
  for (unsigned cur = x;; cur = proofParent_[cur])
  {
    px.push_back(cur);
    if (proofParent_[cur] == cur)
      break;
  }
  for (unsigned cur = y;; cur = proofParent_[cur])
  {
    py.push_back(cur);
    if (proofParent_[cur] == cur)
      break;
  }

  // Both paths end at the root of the shared proof tree. Dropping the common
  // suffix leaves the two halves that meet at the deepest shared ancestor,
  // which together are the path from x to y.
  size_t i = px.size();
  size_t j = py.size();
  while (i > 0 && j > 0 && px[i - 1] == py[j - 1])
  {
    --i;
    --j;
  }

  for (size_t k = 0; k < i; ++k)
    edges.push_back(static_cast<unsigned>(proofEdge_[px[k]]));
  for (size_t k = 0; k < j; ++k)
    edges.push_back(static_cast<unsigned>(proofEdge_[py[k]]));
}

unsigned BVEQCongruenceClosure::check(
    const std::vector<EqInfo>& equalities, SATSolver& solver)
{
  if (equalities.empty())
    return 0;

  unsigned maxNode = 0;
  for (const auto& eq : equalities)
  {
    if (eq.left > maxNode) maxNode = eq.left;
    if (eq.right > maxNode) maxNode = eq.right;
  }
  init(maxNode + 1);

  for (unsigned i = 0; i < equalities.size(); ++i)
  {
    if (equalities[i].modelTrue)
      unite(equalities[i].left, equalities[i].right, i);
  }

  unsigned conflicts = 0;
  for (unsigned i = 0; i < equalities.size(); ++i)
  {
    if (equalities[i].modelTrue)
      continue;

    unsigned rl = find(equalities[i].left);
    unsigned rr = find(equalities[i].right);
    if (rl != rr)
      continue;

    std::vector<unsigned> path;
    explain(equalities[i].left, equalities[i].right, path);

    SATSolver::vec_literals cl;
    for (unsigned idx : path)
      cl.push(SATSolver::mkLit(equalities[idx].satVar, true));
    cl.push(SATSolver::mkLit(equalities[i].satVar, false));
    solver.addClause(cl);

    conflicts++;
  }
  return conflicts;
}

} // namespace stp
