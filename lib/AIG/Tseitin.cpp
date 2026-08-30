/********************************************************************
 * AUTHORS: Trevor Hansen
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

#include "stp/AIG/Tseitin.h"

#include <limits>
#include <stdexcept>

namespace stp
{
namespace aig
{

bool matchIte(const Manager& m, Node n, Lit& c, Lit& t, Lit& e)
{
  if (!m.isAnd(n))
    return false;
  const Lit f0 = m.fanin0(n), f1 = m.fanin1(n);
  if (!isNeg(f0) || !isNeg(f1))
    return false;
  const Node u = nodeOf(f0), v = nodeOf(f1);
  if (!m.isAnd(u) || !m.isAnd(v))
    return false;

  const Lit a = m.fanin0(u), b = m.fanin1(u);
  const Lit cc = m.fanin0(v), d = m.fanin1(v);

  if (a == neg(cc))
  {
    c = a;
    t = neg(b);
    e = neg(d);
  }
  else if (a == neg(d))
  {
    c = a;
    t = neg(b);
    e = neg(cc);
  }
  else if (b == neg(cc))
  {
    c = b;
    t = neg(a);
    e = neg(d);
  }
  else if (b == neg(d))
  {
    c = b;
    t = neg(a);
    e = neg(cc);
  }
  else
    return false;
  return true;
}

void collectAndLeaves(const Manager& m, Node n,
                      const std::vector<uint64_t>& absorbed,
                      std::vector<Lit>& into, std::vector<Lit>& stack)
{
  stack.clear();
  stack.push_back(m.fanin1(n));
  stack.push_back(m.fanin0(n));
  while (!stack.empty())
  {
    const Lit f = stack.back();
    stack.pop_back();
    const Node x = nodeOf(f);
    if (!isNeg(f) && ((absorbed[x >> 6] >> (x & 63)) & 1u))
    {
      stack.push_back(m.fanin1(x));
      stack.push_back(m.fanin0(x));
    }
    else
      into.push_back(f);
  }
}

Cone::Cone(const Manager& m, unsigned namedOutputs, Recover recover)
{
  const uint32_t nCo = m.outputCount();
  assert(namedOutputs <= nCo);

  nCi_ = m.ciCount();
  nNamed_ = namedOutputs;
  firstNamed_ = nCo - namedOutputs;

  const uint64_t nNodes = m.nodeCount();
  const size_t words = static_cast<size_t>((nNodes + 63) / 64);
  live_.assign(words, 0);
  pattern_.assign(words, 0);
  absorbed_.assign(words, 0);

  // A pattern is only taken when it removes its two intermediates outright,
  // which needs to know whether anything else uses them. Nothing does if they
  // have one reference apiece, and that is what this first sweep counts --
  // over the plain cone, before any pattern is taken.
  //
  // Counting on the plain cone rather than the final one over-counts, since
  // taking a pattern only ever removes references. Over-counting can lose an
  // opportunity; it cannot take one that does not pay. Deciding it exactly
  // would be a fixed point, and the reason it cannot be decided in one sweep
  // is that a node's references are not all above the node that would absorb
  // it -- they are only all above the node itself.
  //
  // One byte each, saturating at two, and it is gone when this constructor
  // returns.
  const bool matchPatterns = recover != Recover::Nothing;
  const bool collapseAnds = recover == Recover::PatternsAndAnds;

  std::vector<uint8_t> refs;
  if (matchPatterns)
  {
    refs.assign(nNodes, 0);
    const auto bump = [&refs](Node x) {
      if (x != 0 && refs[x] < 2)
        refs[x]++;
    };
    for (uint32_t i = 0; i < nCo; i++)
      bump(nodeOf(m.output(i)));
    for (Node n = static_cast<Node>(nNodes); n-- > 1;)
    {
      if (refs[n] == 0 || !m.isAnd(n))
        continue;
      bump(nodeOf(m.fanin0(n)));
      bump(nodeOf(m.fanin1(n)));
    }
  }

  for (uint32_t i = 0; i < nCo; i++)
    if (!isConst(m.output(i)))
      setLive(nodeOf(m.output(i)));

  // Would this node be folded as an ITE?  Asked in two places -- of the node
  // being decided, and of a fanin about to be absorbed -- so it is written
  // once. An ITE-shaped node must not be absorbed into its parent's
  // conjunction: absorbing it saves the parent two clauses, while folding it
  // saves five by removing both of its intermediates, and the two are
  // mutually exclusive.
  const auto wouldPattern = [&](Node x) {
    Lit c, t, e;
    return matchPatterns && m.isAnd(x) &&
           refs[nodeOf(m.fanin0(x))] == 1 && refs[nodeOf(m.fanin1(x))] == 1 &&
           matchIte(m, x, c, t, e);
  };

  for (Node n = static_cast<Node>(nNodes); n-- > 1;)
  {
    if (!live(n) || !m.isAnd(n))
      continue;

    Lit c, t, e;
    if (wouldPattern(n))
    {
      const bool matched = matchIte(m, n, c, t, e);
      assert(matched);
      (void)matched;
      setPatterned(n);
      setLive(nodeOf(c));
      setLive(nodeOf(t));
      setLive(nodeOf(e));
      continue;
    }

    // Otherwise this is an AND, and each uncomplemented fanin that nothing
    // else needs folds into it. Marking the fanin absorbed rather than only
    // live is what makes the collection transitive: the sweep reaches that
    // fanin later, finds it absorbed, and marks *its* private fanins in
    // turn, so a whole chain collapses in one descending pass.
    for (const Lit f : {m.fanin0(n), m.fanin1(n)})
    {
      const Node x = nodeOf(f);
      setLive(x);
      if (collapseAnds && !isNeg(f) && m.isAnd(x) && refs[x] == 1 &&
          !wouldPattern(x))
        setAbsorbed(x);
    }
  }

  // Now price it. Absorbed nodes cost nothing; every other live AND node is
  // either an ITE or the root of an n-ary AND whose leaves have to be
  // counted, and counted the same way pass B will collect them.
  std::vector<Lit> leaves, stack;
  for (Node n = 1; n < nNodes; ++n)
  {
    if (!live(n) || !m.isAnd(n) || absorbed(n))
      continue;
    ++nAnds_;
    if (patterned(n))
    {
      nClauses_ += 4;
      nLiterals_ += 12;
      continue;
    }
    leaves.clear();
    collectAndLeaves(m, n, absorbed_, leaves, stack);
    const uint64_t k = leaves.size();
    nClauses_ += k + 1;      // one big clause, and k implications
    nLiterals_ += 3 * k + 1; // (k+1) + 2k
  }

  for (uint32_t i = 0; i < nCo; i++)
  {
    const Lit o = m.output(i);
    if (i < firstNamed_)
    {
      if (o == LIT_TRUE)
        continue; // asserting true says nothing
      nClauses_ += 1;
      if (o != LIT_FALSE)
        nLiterals_ += 1; // asserting false is the empty clause
    }
    else if (isConst(o))
    {
      nClauses_ += 1;
      nLiterals_ += 1;
    }
    else
    {
      nClauses_ += 2;
      nLiterals_ += 4;
    }
  }

  // Counted in 64 bits and narrowed here, which is the check ABC does not
  // do: Cnf_DeriveSimple computes 1 + 7*nodes + ... in an int, and overflows
  // silently at around 306M AND nodes.
  const uint64_t vars = 1ull + nCi_ + nNamed_ + nAnds_;
  if (vars > static_cast<uint64_t>(std::numeric_limits<int>::max()) / 2)
    throw std::overflow_error("CNF variable space exhausted");
  nVars_ = static_cast<uint32_t>(vars);
}

CNF deriveTseitin(const Manager& m, unsigned namedOutputs, Recover recover)
{
  const Cone cone(m, namedOutputs, recover);
  CNF cnf;
  writeTseitin(m, cone, cnf);
  return cnf;
}

} // namespace aig
} // namespace stp
