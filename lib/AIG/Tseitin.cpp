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

namespace
{

// n = !(p & q) ... no: n = !p' & !q' with q's fanins the complements of p's --
// the AIG spelling of an exclusive-or over p's fanins. Returns the two fanin
// nodes; which of them conjoins the operands positively is for the caller to
// settle, since XOR(u,v) == XOR(!u,!v).
bool xorShape(const Manager& m, Node n, Node& p, Node& q)
{
  if (!m.isAnd(n))
    return false;
  const Lit f0 = m.fanin0(n), f1 = m.fanin1(n);
  if (!isNeg(f0) || !isNeg(f1))
    return false;
  p = nodeOf(f0);
  q = nodeOf(f1);
  if (!m.isAnd(p) || !m.isAnd(q))
    return false;
  const Lit pa = m.fanin0(p), pb = m.fanin1(p);
  const Lit qa = m.fanin0(q), qb = m.fanin1(q);
  return (qa == neg(pa) && qb == neg(pb)) || (qa == neg(pb) && qb == neg(pa));
}

// The structural match proposes; this disposes. Evaluates the two roots over
// all eight operand assignments, only ever stepping on the seven nodes a full
// adder owns, so any aliasing or polarity surprise the match missed fails
// here instead of miscoding.
bool verifyFullAdder(const Manager& m, Lit la, Lit lb, Lit lc, Node sum,
                     Node carry, const Node allowed[10])
{
  struct Eval
  {
    const Manager& m;
    const Node* allowed;
    Node leaf[3];
    bool val[3];
    int depth = 0;
    bool ok = true;

    bool node(Node x)
    {
      for (int i = 0; i < 3; i++)
        if (x == leaf[i])
          return val[i];
      if (++depth > 16)
      {
        ok = false;
        return false;
      }
      bool inCone = false;
      for (int i = 0; i < 10 && !inCone; i++)
        inCone = allowed[i] == x;
      if (!inCone || !m.isAnd(x))
      {
        ok = false;
        return false;
      }
      const bool r = lit(m.fanin0(x)) && lit(m.fanin1(x));
      --depth;
      return r;
    }
    bool lit(Lit l) { return node(nodeOf(l)) ^ (isNeg(l) ? true : false); }
  };

  for (unsigned bits = 0; bits < 8; bits++)
  {
    Eval e{m, allowed, {nodeOf(la), nodeOf(lb), nodeOf(lc)},
           {(bits & 1) != 0, (bits & 2) != 0, (bits & 4) != 0}};
    const bool A = e.val[0] ^ (isNeg(la) ? true : false);
    const bool B = e.val[1] ^ (isNeg(lb) ? true : false);
    const bool C = e.val[2] ^ (isNeg(lc) ? true : false);
    const bool s = e.node(sum);
    const bool o = e.node(carry);
    if (!e.ok || s != (A ^ B ^ C))
      return false;
    // The carry-out literal is the complement of the carry node.
    const bool maj = (A && B) || (A && C) || (B && C);
    if (o != !maj)
      return false;
  }
  return true;
}

} // namespace

bool matchMajority(const Manager& m, Node n, Lit& x, Lit& y, Lit& z)
{
  Lit c, t, e;
  if (!matchIte(m, n, c, t, e))
    return false;
  Node p, q;
  if (!xorShape(m, nodeOf(c), p, q))
    return false;

  // The exclusive-or computes u xor v over its grandchild literals, so read
  // through the edge `c` the condition is u == w.
  const Lit u = m.fanin0(p);
  const Lit v = m.fanin1(p);
  const Lit w = isNeg(c) ? v : neg(v);

  // n = (u == w) ? t : e. When an arm is a literal of u's or w's node the
  // selection collapses: agreeing arms are the majority's two aligned
  // inputs, the remaining arm is its third.
  if (e == w || e == neg(u))
  {
    x = neg(u);
    y = w;
    z = t;
  }
  else if (e == u || e == neg(w))
  {
    x = u;
    y = neg(w);
    z = t;
  }
  else if (t == u || t == w)
  {
    x = u;
    y = w;
    z = e;
  }
  else if (t == neg(u) || t == neg(w))
  {
    x = neg(u);
    y = neg(w);
    z = e;
  }
  else
    return false;
  return true;
}

bool matchXorAnd(const Manager& m, Node n, Lit& g, Lit& h)
{
  if (!m.isAnd(n))
    return false;
  for (int side = 0; side < 2; side++)
  {
    const Lit fx = side ? m.fanin1(n) : m.fanin0(n);
    const Lit fg = side ? m.fanin0(n) : m.fanin1(n);
    Node p, q;
    if (!xorShape(m, nodeOf(fx), p, q))
      continue;
    const Lit u = m.fanin0(p);
    const Lit v = m.fanin1(p);
    const Node gn = nodeOf(fg);
    // n = (u xor v, read through fx) & fg. With fg on u's node the
    // exclusive-or contributes only v's polarity, and symmetrically.
    if (gn == nodeOf(u))
    {
      g = fg;
      h = (!isNeg(fx) == (fg == u)) ? neg(v) : v;
      return true;
    }
    if (gn == nodeOf(v))
    {
      g = fg;
      h = (!isNeg(fx) == (fg == v)) ? neg(u) : u;
      return true;
    }
  }
  return false;
}

namespace
{

// Evaluates a cell's cone from leaf nodes, refusing to step outside
// `allowed` -- the discipline verifyFullAdder applies. A leaf that aliases
// another leaf reads the first one's value, which makes the verification
// fail closed on degenerate shapes.
struct CellEval
{
  const Manager& m;
  const Node* allowed;
  unsigned nAllowed;
  const Node* leaf;
  const bool* val;
  unsigned nLeaf;
  int depth = 0;
  bool ok = true;

  bool node(Node x)
  {
    for (unsigned i = 0; i < nLeaf; i++)
      if (x == leaf[i])
        return val[i];
    if (++depth > 16)
    {
      ok = false;
      return false;
    }
    bool inCone = false;
    for (unsigned i = 0; i < nAllowed && !inCone; i++)
      inCone = allowed[i] == x;
    if (!inCone || !m.isAnd(x))
    {
      ok = false;
      return false;
    }
    const bool r = lit(m.fanin0(x)) && lit(m.fanin1(x));
    --depth;
    return r;
  }
  bool lit(Lit l) { return node(nodeOf(l)) != isNeg(l); }
};

} // namespace

bool matchJointCell(const Manager& m, Node n, Lit& a, Lit& b, Lit& e,
                    Lit& other, bool& tSide)
{
  Lit c, t, el;
  if (!matchIte(m, n, c, t, el))
    return false;
  Node p, q;
  if (!xorShape(m, nodeOf(c), p, q))
    return false;
  const Lit u = m.fanin0(p);
  const Lit v = m.fanin1(p);

  // The edge of the condition node that is true when u and v agree, and the
  // arms as that edge selects them.
  e = litOf(nodeOf(c), true);
  Lit onEq = t, onNeq = el;
  if (!isNeg(c))
    std::swap(onEq, onNeq);

  if (onNeq == v || onNeq == neg(v) || onNeq == u || onNeq == neg(u))
  {
    // out = e ? other : b -- the borrow-chain cell.
    tSide = false;
    b = onNeq;
    a = (onNeq == v) ? u : (onNeq == neg(v)) ? neg(u)
        : (onNeq == u) ? v : neg(v);
    other = onEq;
  }
  else if (onEq == u || onEq == neg(u) || onEq == v || onEq == neg(v))
  {
    // out = e ? a : other -- the agreeing arm is an operand.
    tSide = true;
    a = onEq;
    b = (onEq == u) ? v : (onEq == neg(u)) ? neg(v)
        : (onEq == v) ? u : neg(u);
    other = onNeq;
  }
  else
    return false;

  // The structural match proposes; the evaluation disposes, over every
  // assignment of the three operand nodes.
  const Node allowed[6] = {n, nodeOf(m.fanin0(n)), nodeOf(m.fanin1(n)),
                           nodeOf(c), p, q};
  const Node leaves[3] = {nodeOf(a), nodeOf(b), nodeOf(other)};
  for (unsigned bits = 0; bits < 8; bits++)
  {
    const bool vals[3] = {(bits & 1) != 0, (bits & 2) != 0, (bits & 4) != 0};
    CellEval ev{m, allowed, 6, leaves, vals, 3};
    const bool A = vals[0] != isNeg(a);
    const bool B = vals[1] != isNeg(b);
    const bool O = vals[2] != isNeg(other);
    const bool E = (A == B);
    const bool want = tSide ? (E ? A : O) : (E ? O : B);
    if (ev.node(n) != want || ev.lit(e) != E || !ev.ok)
      return false;
  }
  return true;
}

bool matchXorAndJoint(const Manager& m, Node n, Lit& a, Lit& b, Lit& e)
{
  if (!m.isAnd(n))
    return false;
  for (int side = 0; side < 2; side++)
  {
    const Lit fx = side ? m.fanin1(n) : m.fanin0(n);
    const Lit fg = side ? m.fanin0(n) : m.fanin1(n);
    Node p, q;
    if (!xorShape(m, nodeOf(fx), p, q))
      continue;
    const Lit u = m.fanin0(p);
    const Lit v = m.fanin1(p);
    const Node gn = nodeOf(fg);
    if (gn != nodeOf(u) && gn != nodeOf(v))
      continue;
    // Template: out = !e & b with e == (a == b). A positive read of the
    // exclusive-or is the disagreeing case, so e is its complement edge.
    e = litOf(nodeOf(fx), !isNeg(fx));
    b = fg;
    const bool agree = !isNeg(fx); // e true <=> u == v
    if (gn == nodeOf(u))
      a = ((fg == u) == agree) ? v : neg(v);
    else
      a = ((fg == v) == agree) ? u : neg(u);

    const Node allowed[4] = {n, nodeOf(fx), p, q};
    const Node leaves[2] = {nodeOf(a), nodeOf(b)};
    bool verified = true;
    for (unsigned bits = 0; bits < 4 && verified; bits++)
    {
      const bool vals[2] = {(bits & 1) != 0, (bits & 2) != 0};
      CellEval ev{m, allowed, 4, leaves, vals, 2};
      const bool A = vals[0] != isNeg(a);
      const bool B = vals[1] != isNeg(b);
      const bool E = (A == B);
      verified = ev.node(n) == (!E && B) && ev.lit(e) == E && ev.ok;
    }
    if (verified)
      return true;
  }
  return false;
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

void Cone::clearFa(Node carry)
{
  const FullAdder fa = fas_.at(carry);
  faCarry_[carry >> 6] &= ~(1ull << (carry & 63));
  faSum_[fa.sum >> 6] &= ~(1ull << (fa.sum & 63));
  fas_.erase(carry);
  carryOfSum_.erase(fa.sum);
}

// One descending scan proposing full adders. The carry node is created after
// the sum (fullAdder builds the sum tower first), so descending order meets
// the carry first: a node of carry shape -- !(operand-conjunction | tower-
// conjunction) -- files itself under (tower-conjunction, operand-conjunction),
// and the sum tower that later mentions both claims it. The interior
// reference counts must be exactly what a private cone gives (1,2,2,1,2):
// anything shared with outside logic keeps the plain encoding, since the
// block does not define the interiors.
void Cone::findFullAdders(const Manager& m, const std::vector<uint8_t>& refs)
{
  std::unordered_map<uint64_t, Node> pending; // (mB << 32) | nA -> carry
  const auto key = [](Node mB, Node nA) {
    return (static_cast<uint64_t>(mB) << 32) | nA;
  };

  for (Node n = static_cast<Node>(m.nodeCount()); n-- > 1;)
  {
    if (refs[n] == 0 || !m.isAnd(n))
      continue;
    const Lit f0 = m.fanin0(n), f1 = m.fanin1(n);
    if (!isNeg(f0) || !isNeg(f1))
      continue;
    const Node p = nodeOf(f0), q = nodeOf(f1);
    if (!m.isAnd(p) || !m.isAnd(q))
      continue;

    // Carry candidacy: one fanin conjoins the operands, the other conjoins
    // the operands' exclusive-or with the carry-in.
    for (int pick = 0; pick < 2; pick++)
    {
      const Node mB = pick ? q : p;
      const Node nA = pick ? p : q;
      for (int side = 0; side < 2; side++)
      {
        const Node x = nodeOf(side ? m.fanin1(mB) : m.fanin0(mB));
        Node u, v;
        if (xorShape(m, x, u, v) && (u == nA || v == nA))
          pending[key(mB, nA)] = n;
      }
    }

    // Sum candidacy: the two-level exclusive-or tower whose inner conjunction
    // a filed carry also uses.
    Node m1, m2;
    if (!xorShape(m, n, m1, m2))
      continue;
    for (int pick = 0; pick < 2 && !faSum(n); pick++)
    {
      const Node mB = pick ? m2 : m1;
      const Node mOther = pick ? m1 : m2;
      for (int side = 0; side < 2 && !faSum(n); side++)
      {
        const Lit xl = side ? m.fanin1(mB) : m.fanin0(mB);
        const Lit lc = side ? m.fanin0(mB) : m.fanin1(mB);
        const Node x1 = nodeOf(xl);
        Node u, v;
        if (!xorShape(m, x1, u, v))
          continue;
        for (int cand = 0; cand < 2; cand++)
        {
          const Node nA = cand ? v : u;
          const Node n1 = cand ? u : v;
          const auto it = pending.find(key(mB, nA));
          if (it == pending.end())
            continue;
          const Node carry = it->second;

          // The interiors must be private to the cone, and nothing may be
          // claimed twice. refs saturates at 3, so == distinguishes an
          // exact count from "more".
          const Node interior[5] = {n1, nA, x1, mOther, mB};
          const uint8_t want[5] = {1, 2, 2, 1, 2};
          bool ok = !faSum(carry) && !faCarry(carry) && !faSum(n) &&
                    !faCarry(n) && carry != n;
          for (int i = 0; i < 5 && ok; i++)
          {
            const Node node = interior[i];
            ok = refs[node] == want[i] && node != n && node != carry &&
                 !faSum(node) && !faCarry(node);
            for (int j = 0; j < i && ok; j++)
              ok = interior[j] != node;
          }
          if (!ok)
            continue;

          const Lit la = m.fanin0(nA), lb = m.fanin1(nA);
          const Node allowed[10] = {n1, nA, x1, mOther, mB,
                                    n,  carry, 0, 0, 0};
          if (!verifyFullAdder(m, la, lb, lc, n, carry, allowed))
            continue;

          setFaSum(n);
          setFaCarry(carry);
          fas_[carry] = FullAdder{la, lb, lc, n};
          carryOfSum_[n] = carry;
          pending.erase(it);
          break;
        }
      }
    }
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
  majority_.assign(words, 0);
  majorityLink_.assign(words, 0);
  xorAnd_.assign(words, 0);
  xorAndLink_.assign(words, 0);
  absorbed_.assign(words, 0);
  faSum_.assign(words, 0);
  faCarry_.assign(words, 0);

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
  // One byte each, saturating at three -- the full-adder match needs to tell
  // an exact count of two from "more" -- and gone when this constructor
  // returns.
  const bool matchPatterns = recover != Recover::Nothing;
  const bool collapseAnds = recover == Recover::PatternsAndAnds;

  std::vector<uint8_t> refs;
  if (matchPatterns)
  {
    refs.assign(nNodes, 0);
    const auto bump = [&refs](Node x) {
      if (x != 0 && refs[x] < 3)
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

    findFullAdders(m, refs);
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
  const auto faMember = [&](Node x) { return faSum(x) || faCarry(x); };
  const auto wouldPattern = [&](Node x) {
    Lit c, t, e;
    return matchPatterns && m.isAnd(x) && !faMember(x) &&
           refs[nodeOf(m.fanin0(x))] == 1 && refs[nodeOf(m.fanin1(x))] == 1 &&
           !faMember(nodeOf(m.fanin0(x))) && !faMember(nodeOf(m.fanin1(x))) &&
           matchIte(m, x, c, t, e);
  };

  // An AND reading an exclusive-or against one of the exclusive-or's own
  // operands is a two-literal conjunction over the operands. The
  // comparators' borrow chains bottom out in exactly this gate. A private
  // exclusive-or dies with it; a shared one stays, and the gate emits the
  // linking clauses instead.
  const auto xorAndMatch = [&](Node x, Lit& g, Lit& h, Node& xn) {
    if (!matchPatterns || !m.isAnd(x) || faMember(x) ||
        !matchXorAnd(m, x, g, h))
      return false;
    const Lit f0 = m.fanin0(x);
    xn = nodeOf(g == f0 ? m.fanin1(x) : f0);
    return !faMember(xn);
  };
  const auto wouldXorAnd = [&](Node x) {
    Lit g, h;
    Node xn;
    return xorAndMatch(x, g, h, xn);
  };

  for (Node n = static_cast<Node>(nNodes); n-- > 1;)
  {
    if (!live(n) || !m.isAnd(n))
      continue;

    // A recovered full adder defines its sum and carry in one block over the
    // operands; the interiors stay dead. The carry has the higher id, so it
    // is reached first, and by then every consumer of both roots has been
    // processed -- if the sum never came live (its consumers folded it some
    // other way), the recovery is dropped and both nodes take the ordinary
    // path.
    if (faCarry(n))
    {
      const FullAdder& fa = fas_.at(n);
      if (live(fa.sum))
      {
        setLive(nodeOf(fa.a));
        setLive(nodeOf(fa.b));
        setLive(nodeOf(fa.c));
        continue;
      }
      clearFa(n);
    }
    else if (faSum(n))
    {
      const Node carry = carryOfSum_.at(n);
      if (live(carry))
        continue; // operands were marked when the carry was reached
      clearFa(carry);
    }

    Lit c, t, e;
    if (wouldPattern(n))
    {
      const bool matched = matchIte(m, n, c, t, e);
      assert(matched);
      (void)matched;

      const Node cn = nodeOf(c);
      if (m.isAnd(cn) && !faMember(cn))
      {
        // A private exclusive-or condition (its two references are the
        // cell's own) dies with the cell: the majority block replaces both
        // gates. A shared one keeps its variable and its own definition,
        // and the cell instead adds the linking clauses that keep the
        // window propagation-complete with the equality inside it.
        Lit x, y, z;
        if (refs[cn] == 2 && matchMajority(m, n, x, y, z))
        {
          setMajority(n);
          setLive(nodeOf(x));
          setLive(nodeOf(y));
          setLive(nodeOf(z));
          continue;
        }
        Lit a, b, e2, other;
        bool tSide;
        if (refs[cn] > 2 && matchJointCell(m, n, a, b, e2, other, tSide))
        {
          setMajorityLink(n);
          setLive(nodeOf(a));
          setLive(nodeOf(b));
          setLive(cn);
          setLive(nodeOf(other));
          continue;
        }
      }

      setPatterned(n);
      setLive(nodeOf(c));
      setLive(nodeOf(t));
      setLive(nodeOf(e));
      continue;
    }

    {
      Lit g, h;
      Node xn;
      if (xorAndMatch(n, g, h, xn))
      {
        if (refs[xn] == 1)
        {
          setXorAnd(n);
          setLive(nodeOf(g));
          setLive(nodeOf(h));
          continue;
        }
        Lit a, b, e;
        if (matchXorAndJoint(m, n, a, b, e))
        {
          setXorAndLink(n);
          setLive(nodeOf(a));
          setLive(nodeOf(b));
          setLive(xn);
          continue;
        }
      }
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
          !faMember(x) && !wouldPattern(x) && !wouldXorAnd(x))
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
    if (faSum(n))
      continue; // priced with its carry's block
    if (faCarry(n))
    {
      nClauses_ += 14;
      nLiterals_ += 44;
      continue;
    }
    if (majorityCell(n))
    {
      nClauses_ += 6;
      nLiterals_ += 18;
      continue;
    }
    if (majorityLink(n))
    {
      nClauses_ += 10;
      nLiterals_ += 30;
      continue;
    }
    if (xorAnd(n))
    {
      nClauses_ += 3;
      nLiterals_ += 7;
      continue;
    }
    if (xorAndLink(n))
    {
      nClauses_ += 5;
      nLiterals_ += 12;
      continue;
    }
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
