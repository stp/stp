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

#include "stp/AIG/Manager.h"

namespace stp
{
namespace aig
{

void Manager::reset()
{
  nodes_.clear();
  cis_.clear();
  outputs_.clear();
  nAnds_ = 0;
  occupied_ = 0;
  strashLive_ = true;
  // Node 0 is the constant. Both slots sentinel, like a CI: nothing may read
  // children it does not have.
  nodes_.push_back({LIT_NULL, LIT_NULL});
  setTableSize(1024);
}

void Manager::setTableSize(uint64_t slots)
{
  table_.assign(slots, 0);
  mask_ = slots - 1;
  // 0.7 -- linear probing degrades sharply past that, and Robin Hood buys
  // back the tail rather than the average.
  capacityLimit_ = (slots * 7) / 10;
}

void Manager::reserveNodes(uint64_t expectedAnds)
{
  const uint64_t wanted = expectedAnds + cis_.size() + 1;
  if (wanted < nodes_.size())
    return;
  nodes_.reserve(wanted);

  // Enough slots that the load factor is not reached, rounded up to a power
  // of two because the index is a mask rather than a modulo.
  uint64_t slots = 1024;
  while ((slots * 7) / 10 < expectedAnds)
    slots *= 2;
  if (slots <= table_.size())
    return;

  std::vector<uint64_t> next(slots, 0);
  const uint64_t m = slots - 1;
  for (size_t n = 1; n < nodes_.size(); ++n)
  {
    const Lit l0 = nodes_[n].f0;
    if (l0 == LIT_NULL)
      continue;
    const uint64_t h = mixKey(l0, nodes_[n].f1);
    uint64_t carry = probeHead(h) | static_cast<uint32_t>(n);
    uint64_t i = h & m;
    for (;;)
    {
      const uint64_t slot = next[i];
      if (slot == 0) { next[i] = carry; break; }
      if ((slot >> 56) < (carry >> 56)) { next[i] = carry; carry = slot; }
      i = (i + 1) & m;
      carry += DIST_ONE;
    }
  }
  table_.swap(next);
  mask_ = m;
  capacityLimit_ = (slots * 7) / 10;
}

Lit Manager::createCi()
{
  if (nodes_.size() >= MAX_NODES)
    throw BudgetExhausted(nodes_.size());
  const Node n = static_cast<Node>(nodes_.size());
  nodes_.push_back({LIT_NULL, LIT_NULL});
  cis_.push_back(n);
  return litOf(n);
}

void Manager::freeStrash()
{
  std::vector<uint64_t> empty;
  table_.swap(empty);
  mask_ = 0;
  capacityLimit_ = 0;
  strashLive_ = false;
}

Node Manager::newAnd(Lit l0, Lit l1)
{
  if (nodes_.size() >= MAX_NODES)
    throw BudgetExhausted(nodes_.size());
  const Node n = static_cast<Node>(nodes_.size());
  nodes_.push_back({l0, l1});
  ++nAnds_;
  if (nodeBudget >= 0 && nAnds_ > static_cast<uint64_t>(nodeBudget))
    throw BudgetExhausted(nAnds_);
  return n;
}

void Manager::growTable()
{
  const uint64_t slots = table_.size() * 2;
  std::vector<uint64_t> next(slots, 0);
  const uint64_t m = slots - 1;

  // Sweep the nodes ascending rather than the old table: the hash has to be
  // recomputed from each node's fanins either way, and this makes those reads
  // sequential, leaving only the table writes scattered.
  for (size_t n = 1; n < nodes_.size(); ++n)
  {
    const Lit l0 = nodes_[n].f0;
    if (l0 == LIT_NULL)
      continue; // a CI: never in the table
    const uint64_t h = mixKey(l0, nodes_[n].f1);
    uint64_t carry = probeHead(h) | static_cast<uint32_t>(n);
    uint64_t i = h & m;
    for (;;)
    {
      const uint64_t slot = next[i];
      if (slot == 0)
      {
        next[i] = carry;
        break;
      }
      if ((slot >> 56) < (carry >> 56))
      {
        next[i] = carry;
        carry = slot;
      }
      i = (i + 1) & m;
      carry += DIST_ONE;
    }
  }
  table_.swap(next);
  mask_ = m;
  capacityLimit_ = (slots * 7) / 10;
}

Lit Manager::lookupOrCreate(Lit l0, Lit l1)
{
  assert(strashLive_ && "And() after freeStrash()");
  assert(l0 < l1);

  const uint64_t h = mixKey(l0, l1);
  uint64_t probe = probeHead(h);
  uint64_t i = h & mask_;

  for (;;)
  {
    const uint64_t slot = table_[i];
    if (slot == 0)
      break; // empty: not present
    if ((slot >> 56) < (probe >> 56))
      break; // closer to home than we are, so we would have displaced it
    if ((slot >> 32) == (probe >> 32))
    {
      // Distance and fingerprint agree; only now is it worth a node read.
      const Node n = static_cast<Node>(slot);
      if (nodes_[n].f0 == l0 && nodes_[n].f1 == l1)
        return litOf(n);
    }
    i = (i + 1) & mask_;
    probe += DIST_ONE;
  }

  if (occupied_ + 1 > capacityLimit_)
  {
    growTable();
    return lookupOrCreate(l0, l1);
  }
  ++occupied_;

  // Capture the index before displacing: `carry` ends up holding the last
  // entry moved, which is somebody else's.
  const Node n = newAnd(l0, l1);
  uint64_t carry = probe | n;
  for (;;)
  {
    const uint64_t slot = table_[i];
    if (slot == 0)
    {
      table_[i] = carry;
      break;
    }
    if ((slot >> 56) < (carry >> 56))
    {
      table_[i] = carry;
      carry = slot;
    }
    i = (i + 1) & mask_;
    carry += DIST_ONE;
  }
  return litOf(n);
}

// Local two-level minimisation, Brummayer and Biere, MEMICS'06. Ported from
// ABC's Aig_And (aigOper.c), which STP already runs with fAddStrash on, so
// this is parity rather than a new optimisation.
//
// Every rewriting case in ABC recurses into Aig_And; here they assign to the
// operands and let the caller loop, which is the same thing without the
// frames. Termination: each rewrite replaces an operand by one of its own
// grandchildren, so the operand ids strictly decrease.
bool Manager::twoLevel(Lit& p0, Lit& p1, Lit& out) const
{
  out = LIT_NULL;
  const Node n0 = nodeOf(p0), n1 = nodeOf(p1);
  const Lit A = nodes_[n0].f0, B = nodes_[n0].f1;
  const Lit C = nodes_[n1].f0, D = nodes_[n1].f1;

  // ABC's guard, and it is doing real work. With both operands childless the
  // grandchildren are all LIT_NULL, and the cross comparisons below are
  // between one operand's children and the other's -- so they would all
  // match and the block would return an answer built from the sentinel.
  if (A == LIT_NULL && C == LIT_NULL)
    return false;

  const bool c0 = isNeg(p0), c1 = isNeg(p1);

  if (c0)
  {
    if (A == neg(p1) || B == neg(p1)) { out = p1; return false; }
    if (B == p1) { p0 = neg(A); p1 = B; return true; }
    if (A == p1) { p0 = neg(B); p1 = A; return true; }
  }
  else
  {
    if (A == neg(p1) || B == neg(p1)) { out = LIT_FALSE; return false; }
    if (A == p1 || B == p1) { out = p0; return false; }
  }

  if (c1)
  {
    if (C == neg(p0) || D == neg(p0)) { out = p0; return false; }
    if (D == p0) { p0 = neg(C); p1 = D; return true; }
    if (C == p0) { p0 = neg(D); p1 = C; return true; }
  }
  else
  {
    if (C == neg(p0) || D == neg(p0)) { out = LIT_FALSE; return false; }
    if (C == p0 || D == p0) { out = p1; return false; }
  }

  if (!c0 && !c1)
  {
    if (A == neg(C) || A == neg(D) || B == neg(C) || B == neg(D))
    { out = LIT_FALSE; return false; }
    if (A == C || B == C) { p1 = D; return true; }
    if (B == C || B == D) { p0 = A; return true; }
    if (A == D || B == D) { p1 = C; return true; }
    if (A == C || A == D) { p0 = B; return true; }
  }
  else if (c0 && !c1)
  {
    if (A == neg(C) || A == neg(D) || B == neg(C) || B == neg(D))
    { out = p1; return false; }
    if (B == C || B == D) { p0 = neg(A); return true; }
    if (A == C || A == D) { p0 = neg(B); return true; }
  }
  else if (!c0 && c1)
  {
    if (C == neg(A) || C == neg(B) || D == neg(A) || D == neg(B))
    { out = p0; return false; }
    if (D == A || D == B) { p1 = p0; p0 = neg(C); return true; }
    if (C == A || C == B) { p1 = p0; p0 = neg(D); return true; }
  }
  else
  {
    if (A == D && B == neg(C)) { out = neg(A); return false; }
    if (B == C && A == neg(D)) { out = neg(B); return false; }
    if (A == C && B == neg(D)) { out = neg(A); return false; }
    if (B == D && A == neg(C)) { out = neg(B); return false; }
  }
  return false;
}

Lit Manager::And(Lit p0, Lit p1)
{
  for (;;)
  {
    // One level, always. Because the inverting bit is part of the literal,
    // each of these is a single comparison and covers both phases.
    if (p0 == p1)
      return p0;
    if (p0 == neg(p1))
      return LIT_FALSE;
    if (isConst(p0))
      return p0 == LIT_TRUE ? p1 : LIT_FALSE;
    if (isConst(p1))
      return p1 == LIT_TRUE ? p0 : LIT_FALSE;

    Lit out = LIT_NULL;
    if (twoLevel(p0, p1, out))
      continue;
    if (out != LIT_NULL)
      return out;

    // Canonical order. Sorting by literal is sorting by (id, phase), and the
    // ids are distinct here because the equal cases folded above.
    return p0 < p1 ? lookupOrCreate(p0, p1) : lookupOrCreate(p1, p0);
  }
}

Lit Manager::Xor(Lit a, Lit b)
{
  if (a == b)
    return LIT_FALSE;
  if (a == neg(b))
    return LIT_TRUE;
  if (isConst(a))
    return a == LIT_TRUE ? neg(b) : b;
  if (isConst(b))
    return b == LIT_TRUE ? neg(a) : a;

  const Lit positive = And(a, neg(b));
  const Lit negative = And(neg(a), b);
  return Or(positive, negative);
}

Lit Manager::Mux(Lit c, Lit t, Lit e)
{
  const Lit then_ = And(c, t);
  const Lit else_ = And(neg(c), e);
  return Or(then_, else_);
}

bool Manager::check() const
{
  if (nodes_.empty() || nodes_[0].f0 != LIT_NULL || nodes_[0].f1 != LIT_NULL)
    return false;

  uint64_t ands = 0;
  for (size_t n = 1; n < nodes_.size(); ++n)
  {
    const Lit l0 = nodes_[n].f0, l1 = nodes_[n].f1;
    if (l0 == LIT_NULL)
    {
      if (l1 != LIT_NULL)
        return false; // half a sentinel is not a CI
      continue;
    }
    ++ands;
    if (l0 >= l1)
      return false; // not canonically ordered, or a folded case survived
    if (nodeOf(l1) >= n)
      return false; // a fanin at or above its own node breaks the sweep order
  }
  if (ands != nAnds_)
    return false;

  for (Node ci : cis_)
    if (ci == 0 || ci >= nodes_.size() || nodes_[ci].f0 != LIT_NULL)
      return false;

  for (Lit o : outputs_)
    if (nodeOf(o) >= nodes_.size())
      return false;

  return true;
}

} // namespace aig
} // namespace stp
