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

#ifndef STP_AIG_MANAGER_H
#define STP_AIG_MANAGER_H

#include "stp/AIG/Literal.h"

#include <cassert>
#include <cstdint>
#include <stdexcept>
#include <vector>

namespace stp
{
namespace aig
{

// An and-inverter graph: a flat array of two-input AND nodes, hash-consed on
// creation, never mutated and never deleted.
//
// Eight bytes a node, against the 48 of the ABC object this replaces, because
// everything else that object carries pays for a capability we do not use.
// No reference count and no free list, since nothing is ever deleted; no
// level or phase, since nothing rewrites in place; no traversal id or mark,
// since a side bitmap is cheaper than a word per node and can be thrown away;
// no id field, since the id *is* the array index; and no hash-chain link,
// since the table is beside the nodes rather than woven through them -- which
// is also what lets the table be released before the CNF is derived.
//
// Two invariants hold the rest of the design up:
//
//   * A node's fanins always have strictly smaller ids than the node, because
//     And() only ever receives literals of nodes that already exist and
//     appends. So creation order is topological order, and reachability is a
//     descending sweep rather than a depth-first search -- no recursion, no
//     stack, and sequential memory access.
//
//   * A CI or the constant holds LIT_NULL in both fanin slots. See Literal.h
//     for why that value in particular.
class Manager
{
public:
  // Thrown when the AND-node count passes nodeBudget, or when the id space is
  // exhausted. Whoever set the budget owns the abandonment policy, so this
  // escapes And() and every frame above it.
  struct BudgetExhausted : public std::runtime_error
  {
    uint64_t nodeCount;
    explicit BudgetExhausted(uint64_t n)
        : std::runtime_error("AIG node budget exhausted"), nodeCount(n) {}
  };

  Manager() { reset(); }

  // Hard cap on AND nodes; -1 is no limit, 0 permits none.
  int64_t nodeBudget = -1;

  // Size the node array and the hash table for an expected AND count.
  //
  // Worth doing when the count can be estimated even loosely. The table
  // doubles, and a doubling holds the old and the new table at once, so the
  // last one costs 1.5x the final table in transient peak -- which on a large
  // blast is the single biggest allocation in the manager, larger than the
  // nodes themselves. Sizing once removes the spike and the copying with it.
  void reserveNodes(uint64_t expectedAnds);

  Lit constTrue() const { return LIT_TRUE; }
  Lit constFalse() const { return LIT_FALSE; }

  uint64_t andCount() const { return nAnds_; }
  uint64_t nodeCount() const { return nodes_.size(); }
  uint32_t ciCount() const { return static_cast<uint32_t>(cis_.size()); }
  Node ciNode(uint32_t ordinal) const { return cis_[ordinal]; }
  uint32_t outputCount() const { return static_cast<uint32_t>(outputs_.size()); }
  Lit output(uint32_t i) const { return outputs_[i]; }

  bool isAnd(Node n) const { return nodes_[n].f0 != LIT_NULL; }
  bool isCi(Node n) const { return n != 0 && nodes_[n].f0 == LIT_NULL; }
  bool isConstNode(Node n) const { return n == 0; }
  Lit fanin0(Node n) const { return nodes_[n].f0; }
  Lit fanin1(Node n) const { return nodes_[n].f1; }

  Lit createCi();

  // A combinational output. These take no node id, which is what keeps the
  // "fanins have smaller ids" invariant a statement about AND nodes alone.
  uint32_t createOutput(Lit driver)
  {
    outputs_.push_back(driver);
    return static_cast<uint32_t>(outputs_.size() - 1);
  }

  Lit And(Lit a, Lit b);
  Lit Or(Lit a, Lit b) { return neg(And(neg(a), neg(b))); }

  // Each of these builds its intermediate nodes in *separate statements*.
  // Building two of them inside one argument list leaves the order they are
  // created in unspecified, and the order decides their ids, and the ids reach
  // the CNF -- which is why the ABC path needs hand-written replacements for
  // its own Exor and Mux. Written this way the question does not arise.
  Lit Xor(Lit a, Lit b);
  Lit Iff(Lit a, Lit b) { return neg(Xor(a, b)); }
  Lit Mux(Lit c, Lit t, Lit e);

  // Release the structural-hash table. The nodes are unaffected; only the
  // ability to find an existing one by its fanins goes, so this is for a
  // manager that has finished being built. Calling And() afterwards asserts.
  void freeStrash();

  void reset();

  // Invariants, for assertions builds and the tests: canonical fanin order,
  // fanins below their node, CI slots both sentinel, and every AND node
  // findable in the table.
  bool check() const;

private:
  struct AndNode
  {
    Lit f0, f1;
  };
  // The headline of the whole design, so it is pinned rather than assumed:
  // ABC's Aig_Obj_t is 48 bytes on LP64.
  static_assert(sizeof(AndNode) == 8, "an AIG node must stay two literals");

  std::vector<AndNode> nodes_;
  std::vector<Node> cis_;
  std::vector<Lit> outputs_;

  // Open-addressed, Robin Hood. A slot is
  //     [ distance : 8 ][ fingerprint : 24 ][ node index : 32 ]
  // with the distance in the *high* bits so that one unsigned comparison both
  // decides "is this entry closer to home than I am" and, when the distances
  // tie, compares fingerprints. Distance starts at 1, so an occupied slot is
  // never zero and zero means empty.
  //
  // The key -- the fanin pair -- is not stored. It is nodes_[n], which we are
  // keeping anyway, so storing it again would be the largest single cost in
  // the manager. The fingerprint is what makes that affordable: a probe that
  // fails on it costs nothing beyond the word already in the register, so the
  // node array is touched only when the fingerprint agrees.
  std::vector<uint64_t> table_;
  uint64_t mask_ = 0;
  uint64_t occupied_ = 0;
  uint64_t capacityLimit_ = 0;
  uint64_t nAnds_ = 0;
  bool strashLive_ = true;

  static constexpr uint64_t DIST_ONE = 1ull << 56;

  static uint64_t mixKey(Lit l0, Lit l1)
  {
    uint64_t k = (static_cast<uint64_t>(l0) << 32) | l1;
    k ^= k >> 30;
    k *= 0xBF58476D1CE4E5B9ull;
    k ^= k >> 27;
    k *= 0x94D049BB133111EBull;
    return k ^ (k >> 31);
  }
  // Distance 1 in the top byte, 24 bits of fingerprint below it.
  static uint64_t probeHead(uint64_t h)
  {
    return DIST_ONE | ((h >> 32) & 0x00FFFFFFull) << 32;
  }

  Lit lookupOrCreate(Lit l0, Lit l1);
  Node newAnd(Lit l0, Lit l1);
  void growTable();
  void setTableSize(uint64_t slots);

  // The two-level rules. Returns true when it has rewritten (p0,p1) and the
  // caller should start again; otherwise `out` is the answer, or LIT_NULL to
  // mean no rule applied.
  bool twoLevel(Lit& p0, Lit& p1, Lit& out) const;
};

} // namespace aig
} // namespace stp

#endif
