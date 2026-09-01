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

#ifndef STP_AIG_TSEITIN_H
#define STP_AIG_TSEITIN_H

#include "stp/AIG/CNF.h"
#include "stp/AIG/Manager.h"

#include <cassert>
#include <cstdint>
#include <unordered_map>
#include <vector>

namespace stp
{
namespace aig
{

// Is node `n` an if-then-else, and over what?
//
// An AIG spells `ITE(c,t,e)` as `!(!(c & t) & !(!c & e))`, so the node one
// level above that -- the one with both fanins inverted -- computes the
// negation of an ITE, which is itself an ITE with both arms inverted. Written
// out: if the two fanin nodes are (A,B) and (C,D) and any one of the four
// cross pairs is complementary, say A == !C, then
//
//     n = !(A & B) & !(C & D) = ITE(A, !B, !D)
//
// Exclusive-or needs no separate case. It is this same shape with a second
// complementary pair, and the clauses below degenerate into the four an XOR
// wants when `t == !e` -- so one test and one emitter cover both.
//
// Fanins are never constants (And() folds those away) and never LIT_NULL once
// isAnd() has agreed, so c, t and e always name real nodes.
bool matchIte(const Manager& m, Node n, Lit& c, Lit& t, Lit& e);

// Is node `n` an if-then-else whose condition is an exclusive-or that shares
// a node with one of the arms? Selecting between an arm and a literal the
// condition already relates collapses the pair of gates to one three-literal
// majority: n = maj(x, y, z). The borrow chain the comparators blast into is
// made of exactly this cell. Structural only -- whether the condition's
// nodes are private to `n` is the caller's to establish.
bool matchMajority(const Manager& m, Node n, Lit& x, Lit& y, Lit& z);

// Is node `n` an AND reading an exclusive-or against one of the
// exclusive-or's own operands? Fixing the shared operand fixes what the
// exclusive-or contributes, so the node is a plain two-literal conjunction
// over the operands: n = g & h. Structural only, as matchMajority is.
bool matchXorAnd(const Manager& m, Node n, Lit& g, Lit& h);

// The same two cells for a condition that stays live because something else
// reads it. matchJointCell normalizes an ITE cell to the study templates
// over (a, b, e, other, out) with e == (a == b): tSide false means
// out = e ? other : b (the borrow-chain cell), true means out = e ? a :
// other. matchXorAndJoint normalizes the bottom cell to out = !e & b.
// Both verify the claim by evaluating the cone over every operand
// assignment, so a polarity surprise declines instead of miscoding.
bool matchJointCell(const Manager& m, Node n, Lit& a, Lit& b, Lit& e,
                    Lit& other, bool& tSide);
bool matchXorAndJoint(const Manager& m, Node n, Lit& a, Lit& b, Lit& e);

// The leaves of the maximal AND rooted at `n`, appended to `into`.
//
// An AIG has no OR node: `a | b` is `!(!a & !b)`, one AND with the
// complements on the edges. So an n-ary OR *is* an n-ary AND over negated
// leaves, with the output polarity carried by the edge above it -- and one
// collector recovers both. Nothing here looks at the sign above `n`.
//
// Descends through an uncomplemented fanin whose node `absorbed` marks, and
// stops everywhere else. Stopping at a complemented edge is what keeps a
// conjunction from swallowing a disjunction: an alternation of the two shows
// up as a complemented edge and cuts the collection there.
//
// Iterative: a query's top-level conjunction reaches a thousand leaves, and
// this runs once per root over the whole cone.
void collectAndLeaves(const Manager& m, Node n, const std::vector<uint64_t>& absorbed,
                      std::vector<Lit>& into, std::vector<Lit>& stack);

// What the writer recovers from the AIG before emitting. Each rung adds to
// the one above it, and each is a strict size reduction -- see the report in
// bench-hard for what each is worth.
enum class Recover
{
  Nothing,        // plain Tseitin: three clauses for every AND node
  Patterns,       // + XOR, if-then-else and full adders
  PatternsAndAnds // + maximal n-ary ANDs, and so n-ary ORs, collapsed
};

// Which nodes the CNF will talk about, and how many clauses that will take.
//
// Pass A of the writer, split out because it is the same work whatever the
// clauses get written into, and because the counts have to be known before
// the first clause is emitted if the arena is to be sized exactly once.
//
// Its sweeps run *down* the node array. Fanins always have smaller ids than
// their node, so descending order visits every reference to a node before the
// node itself -- no recursion, no explicit stack, and no visited set beyond
// the bitmap. That retires the Cnf_ManScanMapping_rec stack-overflow class
// outright rather than raising a limit.
class Cone
{
public:
  // namedOutputs: how many of the *trailing* combinational outputs get a
  // variable of their own instead of being asserted. That is the split
  // Cnf_DeriveSimple takes, and the two callers want its ends: a formula
  // asserts its single output, a fragment names all of them.
  Cone(const Manager& m, unsigned namedOutputs = 0,
       Recover recover = Recover::PatternsAndAnds);

  // In the cone, so it gets a variable and its defining clauses.
  bool live(Node n) const { return (live_[n >> 6] >> (n & 63)) & 1u; }

  // Encoded as one four-clause ITE over its grandchildren rather than as
  // three ANDs. Its two fanin nodes are then not live at all.
  bool patterned(Node n) const
  {
    return (pattern_[n >> 6] >> (n & 63)) & 1u;
  }

  // A comparator/borrow cell: an ITE over a private exclusive-or that one
  // arm shares a node with, encoded as the six prime implicates of the
  // three-literal majority it computes. The exclusive-or and all four
  // intermediates get no variables.
  bool majorityCell(Node n) const
  {
    return (majority_[n >> 6] >> (n & 63)) & 1u;
  }

  // An AND over a private exclusive-or and one of its operands, collapsed
  // to the two-literal conjunction it computes. The exclusive-or and its
  // intermediates get no variables.
  bool xorAnd(Node n) const { return (xorAnd_[n >> 6] >> (n & 63)) & 1u; }

  // The same two cells when the exclusive-or is shared: it keeps its
  // variable and its own definition, and the cell emits the minimum linking
  // clauses that keep the window propagation-complete with the equality
  // inside it -- ten for the full cell, five for the bottom.
  bool majorityLink(Node n) const
  {
    return (majorityLink_[n >> 6] >> (n & 63)) & 1u;
  }
  bool xorAndLink(Node n) const
  {
    return (xorAndLink_[n >> 6] >> (n & 63)) & 1u;
  }

  // A recovered full adder: sum and carry defined together by one fourteen-
  // clause block over the operands -- the minimum propagation-complete
  // clause set for the relation, which the per-gate encodings are not. The
  // five interior nodes get no variables. Stored at the carry node, whose
  // complement is the carry-out.
  struct FullAdder
  {
    Lit a, b, c; // the operand literals
    Node sum;
  };
  bool faSum(Node n) const { return (faSum_[n >> 6] >> (n & 63)) & 1u; }
  bool faCarry(Node n) const { return (faCarry_[n >> 6] >> (n & 63)) & 1u; }
  const FullAdder& faAt(Node carry) const { return fas_.at(carry); }

  uint32_t varCount() const { return nVars_; }
  uint64_t clauseCount() const { return nClauses_; }
  uint64_t literalCount() const { return nLiterals_; }
  // Live AND nodes, which is how many variables the cone itself needs.
  // Absorbed into the n-ary AND of its parent: no variable, no clauses of
  // its own, and its leaves appear in the parent's big clause instead.
  bool absorbed(Node n) const
  {
    return (absorbed_[n >> 6] >> (n & 63)) & 1u;
  }

  uint64_t liveAndCount() const { return nAnds_; }

  // For the emit pass, which has to collect the same leaves this counted.
  const std::vector<uint64_t>& absorbedBits() const { return absorbed_; }

  // Variable layout, closed form and no lookup table:
  //   1 .. nCi                      the CIs, in ordinal order
  //   nCi+1 .. nCi+nNamed           the named outputs, in output order
  //   the rest                      the cone's AND nodes, ascending by id
  static constexpr uint32_t ciVarBase() { return 1; }
  uint32_t coVarBase() const { return 1 + nCi_; }
  uint32_t andVarBase() const { return 1 + nCi_ + nNamed_; }

  // Outputs at or above this index are named; the ones below are asserted.
  uint32_t firstNamedOutput() const { return firstNamed_; }

private:
  void setLive(Node n) { live_[n >> 6] |= 1ull << (n & 63); }
  void setPatterned(Node n) { pattern_[n >> 6] |= 1ull << (n & 63); }
  void setMajority(Node n) { majority_[n >> 6] |= 1ull << (n & 63); }
  void setMajorityLink(Node n) { majorityLink_[n >> 6] |= 1ull << (n & 63); }
  void setXorAnd(Node n) { xorAnd_[n >> 6] |= 1ull << (n & 63); }
  void setXorAndLink(Node n) { xorAndLink_[n >> 6] |= 1ull << (n & 63); }
  void setAbsorbed(Node n) { absorbed_[n >> 6] |= 1ull << (n & 63); }
  void setFaSum(Node n) { faSum_[n >> 6] |= 1ull << (n & 63); }
  void setFaCarry(Node n) { faCarry_[n >> 6] |= 1ull << (n & 63); }
  void clearFa(Node carry);
  void findFullAdders(const Manager& m, const std::vector<uint8_t>& refs);

  std::vector<uint64_t> live_;
  std::vector<uint64_t> pattern_;
  std::vector<uint64_t> majority_;
  std::vector<uint64_t> majorityLink_;
  std::vector<uint64_t> xorAnd_;
  std::vector<uint64_t> xorAndLink_;
  std::vector<uint64_t> absorbed_;
  std::vector<uint64_t> faSum_;
  std::vector<uint64_t> faCarry_;
  std::unordered_map<Node, FullAdder> fas_;
  std::unordered_map<Node, Node> carryOfSum_;
  uint64_t nClauses_ = 0;
  uint64_t nLiterals_ = 0;
  uint64_t nAnds_ = 0;
  uint32_t nVars_ = 1;
  uint32_t nCi_ = 0;
  uint32_t nNamed_ = 0;
  uint32_t firstNamed_ = 0;
};

// Pass B: emit. Ascending is automatically topological, so a fanin's variable
// is always a smaller index that was written a moment ago.
//
// Templated over the sink although only CNF implements it today, so that a
// DIMACS writer or one that feeds a live solver costs no indirection when it
// arrives.
template <class Sink>
void writeTseitin(const Manager& m, const Cone& cone, Sink& sink)
{
  const uint32_t nCi = m.ciCount();
  const uint32_t nCo = m.outputCount();
  const uint32_t firstNamed = cone.firstNamedOutput();

  sink.begin(cone.varCount(), cone.clauseCount(), cone.literalCount(), nCi,
             nCo);

  // Scratch for the n-ary AND collection, hoisted so the whole emit pass
  // reuses one allocation rather than one per root.
  std::vector<Lit> leaves;
  std::vector<Lit> stack;
  std::vector<int> clause;

  // Four bytes a node, and it dies with this function. The CNF that outlives
  // it carries no node map at all -- which is the whole difference from
  // Cnf_Dat_t::pVarNums, held for the length of the solve.
  std::vector<uint32_t> var(m.nodeCount(), 0);

  for (uint32_t i = 0; i < nCi; i++)
  {
    var[m.ciNode(i)] = Cone::ciVarBase() + i;
    sink.mapCi(i, Cone::ciVarBase() + i);
  }
  for (uint32_t i = 0; i < nCo; i++)
    sink.mapCo(i, i < firstNamed ? 0 : cone.coVarBase() + (i - firstNamed));

  const auto cnfLit = [&var](Lit l) -> int {
    assert(!isConst(l));
    assert(var[nodeOf(l)] != 0);
    return static_cast<int>(2 * var[nodeOf(l)] + (l & 1u));
  };

  uint32_t next = cone.andVarBase();
  for (Node n = 1; n < m.nodeCount(); ++n)
  {
    if (!m.isAnd(n) || !cone.live(n) || cone.absorbed(n))
      continue;
    const uint32_t x = next++;
    var[n] = x;
    const int px = static_cast<int>(2 * x), nx = px | 1;

    if (cone.faSum(n))
      continue; // defined by its full adder's block, emitted at the carry

    if (cone.faCarry(n))
    {
      // The fourteen-clause propagation-complete block for
      //   s = a xor b xor c,  carry-out = majority(a, b, c)
      // where the carry-out is the complement of this node. All twenty prime
      // implicates minus the six parity clauses whose conflicts re-derive
      // through the carry.
      const Cone::FullAdder& fa = cone.faAt(n);
      const int A = cnfLit(fa.a), B = cnfLit(fa.b), C = cnfLit(fa.c);
      const int S = static_cast<int>(2 * var[fa.sum]);
      const int T = nx, Tn = px; // t is the carry-out literal, so !node
      sink.clause(C ^ 1, S, T);
      sink.clause(B ^ 1, C ^ 1, T);
      sink.clause(B ^ 1, S, T);
      sink.clause(A ^ 1, C ^ 1, T);
      sink.clause(A ^ 1, B ^ 1, T);
      sink.clause(A ^ 1, S, T);
      sink.clause(A, S ^ 1, Tn);
      sink.clause(A, B, Tn);
      sink.clause(A, C, Tn);
      sink.clause(B, S ^ 1, Tn);
      sink.clause(B, C, Tn);
      sink.clause(C, S ^ 1, Tn);
      const int q1[4] = {A ^ 1, B ^ 1, C ^ 1, S};
      const int q2[4] = {A, B, C, S ^ 1};
      sink.clause(q1, 4);
      sink.clause(q2, 4);
      continue;
    }

    if (cone.majorityCell(n))
    {
      Lit x, y, z;
      const bool matched = matchMajority(m, n, x, y, z);
      assert(matched);
      (void)matched;
      const int lx = cnfLit(x), ly = cnfLit(y), lz = cnfLit(z);
      sink.clause(px, lx ^ 1, ly ^ 1);
      sink.clause(px, lx ^ 1, lz ^ 1);
      sink.clause(px, ly ^ 1, lz ^ 1);
      sink.clause(nx, lx, ly);
      sink.clause(nx, lx, lz);
      sink.clause(nx, ly, lz);
    }
    else if (cone.majorityLink(n))
    {
      Lit a, b, e, other;
      bool tSide;
      const bool matched = matchJointCell(m, n, a, b, e, other, tSide);
      assert(matched);
      (void)matched;
      // The minimum linking sets from the comparator study: with the
      // exclusive-or's own four clauses alongside (its patterned emission),
      // the window over (a, b, e, other, out) is propagation-complete.
      static const int8_t ESIDE[10][3] = {
          {-3, -4, 5}, {-3, 4, -5}, {-2, -4, 5}, {-1, 3, -5}, {-1, 4, -5},
          {1, -4, 5},  {1, -2, 5},  {1, 3, 5},   {2, 3, -5},  {2, 4, -5}};
      static const int8_t TSIDE[10][3] = {
          {-2, -4, 5}, {-1, -4, 5}, {-1, -3, 5}, {-1, -2, 5}, {1, 2, -5},
          {1, 4, -5},  {2, -3, -5}, {2, 4, -5},  {3, -4, 5},  {3, 4, -5}};
      const int base[6] = {0, cnfLit(a), cnfLit(b), cnfLit(e), cnfLit(other),
                           px};
      const int8_t(*tpl)[3] = tSide ? TSIDE : ESIDE;
      for (int i = 0; i < 10; i++)
      {
        int lits[3];
        for (int j = 0; j < 3; j++)
        {
          const int t = tpl[i][j];
          lits[j] = base[t < 0 ? -t : t] ^ (t < 0 ? 1 : 0);
        }
        sink.clause(lits[0], lits[1], lits[2]);
      }
    }
    else if (cone.xorAnd(n))
    {
      Lit g, h;
      const bool matched = matchXorAnd(m, n, g, h);
      assert(matched);
      (void)matched;
      const int lg = cnfLit(g), lh = cnfLit(h);
      sink.clause(nx, lg);
      sink.clause(nx, lh);
      sink.clause(px, lg ^ 1, lh ^ 1);
    }
    else if (cone.xorAndLink(n))
    {
      Lit a, b, e;
      const bool matched = matchXorAndJoint(m, n, a, b, e);
      assert(matched);
      (void)matched;
      const int la = cnfLit(a), lb = cnfLit(b), le = cnfLit(e);
      sink.clause(le ^ 1, nx);
      sink.clause(la ^ 1, nx);
      sink.clause(lb, nx);
      sink.clause(la, lb ^ 1, px);
      sink.clause(la, le, px);
    }
    else if (cone.patterned(n))
    {
      Lit c, t, e;
      const bool matched = matchIte(m, n, c, t, e);
      assert(matched);
      (void)matched;
      const int lc = cnfLit(c), lt = cnfLit(t), le = cnfLit(e);
      sink.clause(nx, lc ^ 1, lt);
      sink.clause(px, lc ^ 1, lt ^ 1);
      sink.clause(nx, lc, le);
      sink.clause(px, lc, le ^ 1);
    }
    else
    {
      // The n-ary AND. Collected exactly as Cone counted it -- same
      // function, same bitmap -- because the arena was reserved from that
      // count and CNF::end() checks the two agree.
      leaves.clear();
      collectAndLeaves(m, n, cone.absorbedBits(), leaves, stack);

      // x -> every leaf, and every leaf together -> x.
      clause.clear();
      clause.push_back(px);
      for (const Lit l : leaves)
        clause.push_back(cnfLit(l) ^ 1);
      sink.clause(clause.data(), clause.size());
      for (const Lit l : leaves)
        sink.clause(nx, cnfLit(l));
    }
  }
  assert(next == cone.varCount());

  for (uint32_t i = 0; i < nCo; i++)
  {
    const Lit o = m.output(i);
    if (i < firstNamed)
    {
      // Asserted. A constant here is the one place a constant literal can
      // reach: And() folds every other. True asserts nothing at all, and
      // false is the empty clause -- neither needs a variable, which is why
      // there is no constant variable and no constant unit clause anywhere in
      // this encoding.
      if (o == LIT_TRUE)
        continue;
      if (o == LIT_FALSE)
        sink.emptyClause();
      else
        sink.clause(cnfLit(o));
    }
    else
    {
      const int pv = static_cast<int>(2 * (cone.coVarBase() + (i - firstNamed)));
      if (isConst(o))
        sink.clause(o == LIT_TRUE ? pv : (pv | 1));
      else
      {
        const int d = cnfLit(o);
        sink.clause(pv, d ^ 1);
        sink.clause(pv | 1, d);
      }
    }
  }
  sink.end();
}

// Both passes, into a materialised CNF.
CNF deriveTseitin(const Manager& m, unsigned namedOutputs = 0,
                  Recover recover = Recover::PatternsAndAnds);

} // namespace aig
} // namespace stp

#endif
