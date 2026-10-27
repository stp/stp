/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: October, 2026
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

// Randomised checking of MutableGraph against an oracle that never touches
// the graph.
//
// A random DAG with heavy sharing is imported, then a random sequence of
// operations is applied: materialise an immutable node, patch a slot of a
// mutable node, replace a mutable node outright, or build a node through
// the graph's simplifying factory and splice it in. After every operation:
//
//   1. checkInvariant(): parent counts recounted from scratch agree with
//      the incremental ones; table and back-pointers consistent.
//   2. always hashed: no two nodes of the current formula have the same
//      kind and children.
//   3. export agrees with the oracle: the hash-consed formula from before
//      the operation, with the operation applied as a plain substitution
//      and every changed node rebuilt through the simplifying factory (the
//      graph runs the rules on a patched node and on every ancestor it
//      converts), is pointer-identical to exportRoot().
//   4. export is idempotent: a second export is the same node, and a fresh
//      graph importing it exports it unchanged.
//
// MUTABLEGRAPH_FUZZ_SEEDS overrides the number of seeds (default 300),
// MUTABLEGRAPH_FUZZ_STEPS the operations per seed (default 40),
// MUTABLEGRAPH_FUZZ_ONLY selects one seed, MUTABLEGRAPH_FUZZ_TRACE prints
// every operation and MUTABLEGRAPH_TRACE the graph's own steps.

#include "stp/AST/AST.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/MutableGraph.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include <cstdlib>
#include <gtest/gtest.h>
#include <iostream>
#include <random>
#include <algorithm>
#include <map>
#include <set>

using namespace stp;

namespace
{
const unsigned W = 8;
int currentSeed = 0;
bool tracing();

struct Fuzz
{
  STPMgr mgr;
  SimplifyingNodeFactory snf;
  NodeFactory& hashing;
  std::mt19937_64 rng;

  std::vector<ASTNode> terms; // width W
  std::vector<ASTNode> bools;

  explicit Fuzz(uint64_t seed)
      : snf(*mgr.hashingNodeFactory, mgr), hashing(*mgr.hashingNodeFactory),
        rng(seed)
  {
    mgr.defaultNodeFactory = &snf;
  }

  size_t pick(size_t n) { return std::uniform_int_distribution<size_t>(0, n - 1)(rng); }
  bool coin(double p) { return std::uniform_real_distribution<double>(0, 1)(rng) < p; }

  // Recent nodes more often, so the DAG has depth as well as sharing.
  const ASTNode& from(const std::vector<ASTNode>& pool)
  {
    if (pool.size() > 4 && coin(0.5))
      return pool[pool.size() - 1 - pick(4)];
    return pool[pick(pool.size())];
  }

  // Through the simplifying factory over sorted children, as the graph
  // presents a node to the rules: every generated node is then a fixpoint
  // of the rules, so only the edits change anything.
  ASTNode term(Kind kind, ASTVec kids)
  {
    sortLikeGraph(kind, kids);
    return snf.CreateTerm(kind, W, kids);
  }
  ASTNode form(Kind kind, ASTVec kids)
  {
    sortLikeGraph(kind, kids);
    return snf.CreateNode(kind, kids);
  }

  ASTNode randomTerm()
  {
    switch (pick(9))
    {
      case 0: return term(BVPLUS, {from(terms), from(terms)});
      case 1: return term(BVMULT, {from(terms), from(terms)});
      case 2: return term(BVAND, {from(terms), from(terms)});
      case 3: return term(BVOR, {from(terms), from(terms)});
      case 4: return term(BVXOR, {from(terms), from(terms)});
      case 5: return term(BVNOT, {from(terms)});
      case 6: return term(BVUMINUS, {from(terms)});
      case 7: return term(ITE, {from(bools), from(terms), from(terms)});
      default: return term(BVSUB, {from(terms), from(terms)});
    }
  }

  ASTNode randomBool()
  {
    switch (pick(8))
    {
      case 0: return form(AND, {from(bools), from(bools)});
      case 1: return form(OR, {from(bools), from(bools)});
      case 2: {
        const ASTNode b = from(bools);
        return b.GetKind() == NOT ? b[0] : form(NOT, {b});
      }
      case 3: return form(EQ, {from(terms), from(terms)});
      case 4: return form(BVGT, {from(terms), from(terms)});
      case 5: return form(BVSLT, {from(terms), from(terms)});
      case 6: return form(ITE, {from(bools), from(bools), from(bools)});
      default: return form(XOR, {from(bools), from(bools)});
    }
  }

  ASTNode randomFormula()
  {
    terms.clear();
    bools.clear();
    for (int i = 0; i < 4; i++)
      terms.push_back(hashing.CreateSymbol(("t" + std::to_string(i)).c_str(), 0, W));
    terms.push_back(mgr.CreateBVConst(W, 0));
    terms.push_back(mgr.CreateBVConst(W, 1));
    terms.push_back(mgr.CreateBVConst(W, 255));
    for (int i = 0; i < 3; i++)
      bools.push_back(hashing.CreateSymbol(("p" + std::to_string(i)).c_str(), 0, 0));
    const size_t size = 6 + pick(40);
    for (size_t i = 0; i < size; i++)
    {
      if (coin(0.6))
        terms.push_back(randomTerm());
      else
        bools.push_back(randomBool());
    }
    ASTVec conj;
    // MUTABLEGRAPH_FUZZ_WIDE: one formula in five gets a root conjunction
    // wider than the table admits (over 64 children), so the wide paths
    // (no re-sort, no merge, slot-indexed repointing) are exercised.
    const bool wide = std::getenv("MUTABLEGRAPH_FUZZ_WIDE") != NULL && coin(0.2);
    const size_t k = wide ? 70 + pick(30) : 1 + pick(4);
    for (size_t i = 0; i < k; i++)
      conj.push_back(wide ? randomBool() : from(bools));
    return conj.size() == 1 ? conj[0] : form(AND, conj);
  }

  // -------------------------------------------------------------- oracle

  // A node whose children changed is rebuilt through the simplifying
  // factory: that is what the graph does to a patched node and to every
  // ancestor it converts above a replacement.
  // The graph re-keys with the hashing factory's order before the rules
  // see the node, and some rules only look at one orientation.
  static void sortLikeGraph(Kind kind, ASTVec& kids)
  {
    if (kids.size() > 1 && isCommutative(kind))
    {
      if (is_Form_kind(kind))
        SortByExprNum(kids);
      else
        SortByArith(kids);
    }
  }

  ASTNode hashCons(const ASTNode& like, const ASTVec& given)
  {
    ASTVec kids(given);
    sortLikeGraph(like.GetKind(), kids);
    if (like.GetIndexWidth() > 0)
      return snf.CreateArrayTerm(like.GetKind(), like.GetIndexWidth(),
                                 like.GetValueWidth(), kids);
    if (like.GetValueWidth() > 0)
      return snf.CreateTerm(like.GetKind(), like.GetValueWidth(), kids);
    return snf.CreateNode(like.GetKind(), kids);
  }

  // `tree` with every occurrence of `from` replaced by `to`, hash-consed.
  ASTNode substitute(const ASTNode& tree, const ASTNode& from, const ASTNode& to,
                     ASTNodeMap& memo)
  {
    if (tree == from)
      return to;
    if (tree.Degree() == 0)
      return tree;
    const auto it = memo.find(tree);
    if (it != memo.end())
      return it->second;
    ASTVec kids;
    bool changed = false;
    for (const ASTNode& c : tree)
    {
      kids.push_back(substitute(c, from, to, memo));
      changed |= (kids.back() != c);
    }
    const ASTNode r = changed ? hashCons(tree, kids) : tree;
    memo.insert({tree, r});
    return r;
  }

  // ------------------------------------------------- views of the graph

  // Every node of the current formula, each once, as the graph holds it.
  void currentNodes(MutableGraph& g, std::vector<ASTNode>& out)
  {
    ASTNodeSet seen;
    std::vector<ASTNode> stack;
    stack.push_back(g.current(g.root()));
    while (!stack.empty())
    {
      const ASTNode n = stack.back();
      stack.pop_back();
      if (!seen.insert(n).second)
        continue;
      out.push_back(n);
      for (const ASTNode& c : n)
        stack.push_back(g.current(c));
    }
  }

  bool conesContain(MutableGraph& g, const ASTNode& root, const ASTNode& target)
  {
    ASTNodeSet seen;
    std::vector<ASTNode> stack;
    stack.push_back(g.current(root));
    while (!stack.empty())
    {
      const ASTNode n = stack.back();
      stack.pop_back();
      if (n == target)
        return true;
      if (!seen.insert(n).second)
        continue;
      for (const ASTNode& c : n)
        stack.push_back(g.current(c));
    }
    return false;
  }

  static bool sameSort(const ASTNode& a, const ASTNode& b)
  {
    return a.GetType() == b.GetType() && a.GetValueWidth() == b.GetValueWidth() &&
           a.GetIndexWidth() == b.GetIndexWidth();
  }

  // A node of the current formula with the sort of `like` whose cone does not
  // contain `avoid`, or a fresh symbol of that sort.
  ASTNode replacementFor(MutableGraph& g, const std::vector<ASTNode>& cur,
                         const ASTNode& like, const ASTNode& avoid)
  {
    for (int tries = 0; tries < 12; tries++)
    {
      const ASTNode& c = cur[pick(cur.size())];
      if (sameSort(c, like) && c != avoid && !conesContain(g, c, avoid))
        return c;
    }
    if (like.GetValueWidth() > 0 && coin(0.5))
      return mgr.CreateBVConst(W, pick(256));
    return hashing.CreateSymbol(("fresh" + std::to_string(pick(1000000))).c_str(),
                                like.GetIndexWidth(), like.GetValueWidth());
  }

  // ------------------------------------------------------------- checks

  // Kind, width and the current identity of each child; order-free for a
  // commutative kind, since a stale node keeps its old order.
  std::vector<uint64_t> structureKey(MutableGraph& g, const ASTNode& n)
  {
    std::vector<uint64_t> kids;
    for (const ASTNode& c : n)
      kids.push_back(g.current(c).GetNodeNum());
    if (isCommutative(n.GetKind()))
      std::sort(kids.begin(), kids.end());
    std::vector<uint64_t> key;
    key.push_back(n.GetKind());
    key.push_back(n.GetValueWidth());
    key.insert(key.end(), kids.begin(), kids.end());
    return key;
  }

  // A stale immutable ancestor whose current structure equals n. Lazy B
  // merges it with n only at export, so an edit of n reaches n's holders
  // and not the twin's: the hash-consed oracle cannot express that, so
  // the harness does not edit such a node.
  // Likewise a stale NOT whose child has become a NOT: export collapses it
  // to the grandchild, so the oracle's before-formula no longer holds the
  // occurrence an edit below it changes.
  size_t skippedForTwin = 0;
  // Export and oracle differ in structure but agree on every sampled
  // assignment: the simplifying factory is not confluent, and the two sides
  // run its rules in different orders (the graph by node number, children
  // first; the oracle in the order of its rebuild).
  size_t scheduleDiffs = 0;
  size_t graphLarger = 0; // of those, the export has more nodes

  static size_t nodeCount(const ASTNode& n)
  {
    ASTNodeSet seen;
    std::vector<ASTNode> stack(1, n);
    while (!stack.empty())
    {
      const ASTNode x = stack.back();
      stack.pop_back();
      if (!seen.insert(x).second)
        continue;
      for (const ASTNode& c : x)
        stack.push_back(c);
    }
    return seen.size();
  }

  void symbolsOf(const ASTNode& n, std::vector<ASTNode>& out)
  {
    ASTNodeSet seen;
    std::vector<ASTNode> stack(1, n);
    while (!stack.empty())
    {
      const ASTNode x = stack.back();
      stack.pop_back();
      if (!seen.insert(x).second)
        continue;
      if (x.GetKind() == SYMBOL)
        out.push_back(x);
      for (const ASTNode& c : x)
        stack.push_back(c);
    }
  }

  // Both sides agree at 64 random assignments to the symbols of either.
  bool equivalentBySampling(const ASTNode& a, const ASTNode& b, std::string& why)
  {
    std::vector<ASTNode> syms;
    symbolsOf(a, syms);
    symbolsOf(b, syms);
    std::sort(syms.begin(), syms.end(), ExprLess{});
    syms.erase(std::unique(syms.begin(), syms.end()), syms.end());
    for (int round = 0; round < 64; round++)
    {
      ASTNodeMap assignment;
      for (const ASTNode& sym : syms)
      {
        if (sym.GetValueWidth() == 0)
          assignment[sym] = coin(0.5) ? mgr.ASTTrue : mgr.ASTFalse;
        else
          assignment[sym] = mgr.CreateBVConst(sym.GetValueWidth(), pick(256));
      }
      ASTNodeMap cacheA, cacheB;
      ASTNode va = SubstitutionMap::replace(a, assignment, cacheA, &snf);
      ASTNode vb = SubstitutionMap::replace(b, assignment, cacheB, &snf);
      if (!va.isConstant())
        va = NonMemberBVConstEvaluator(&mgr, va);
      if (!vb.isConstant())
        vb = NonMemberBVConstEvaluator(&mgr, vb);
      if (va != vb)
      {
        why = "export and oracle disagree at an assignment";
        return false;
      }
    }
    return true;
  }
  bool hasStaleTwin(MutableGraph& g, const std::vector<ASTNode>& cur, const ASTNode& n)
  {
    // By exported structure: a twin's children may themselves be stale
    // nodes equivalent to n's children, which identities do not show.
    const ASTNode nExport = g.exportNode(n);
    for (const ASTNode& o : cur)
    {
      if (o.Degree() == 0 || o.isMutableInterior() || !g.isStale(o))
        continue;
      if (o != n && g.exportNode(o) == nExport)
        return true;
      if (o.GetKind() == NOT && g.exportNode(o[0]).GetKind() == NOT)
        return true;
    }
    return false;
  }

  bool alwaysHashed(MutableGraph& g, const std::vector<ASTNode>& cur,
                    std::string& why)
  {
    // Key: kind plus the current identity of each child. Stale immutable
    // ancestors are left out: they stand above a replacement and are only
    // merged when export rebuilds them, by design.
    std::map<std::vector<uint64_t>, ASTNode> keys;
    for (const ASTNode& n : cur)
    {
      if (n.Degree() == 0 || (!n.isMutableInterior() && g.isStale(n)))
        continue;
      std::vector<uint64_t> key;
      key.push_back(n.GetKind());
      key.push_back(n.GetValueWidth());
      for (const ASTNode& c : n)
        key.push_back(g.current(c).GetNodeNum());
      const auto ins = keys.insert({key, n});
      if (!ins.second)
      {
        const ASTNode& o = ins.first->second;
        auto describe = [&g](const ASTNode& x) {
          return std::to_string(x.GetNodeNum()) + (x.isMutableInterior() ? " mutable" : " immutable") +
                 (!x.isMutableInterior() && g.isStale(x) ? " stale" : "") +
                 " count " + std::to_string(g.parentCount(x));
        };
        why = "duplicate structure: " + describe(o) + " and " + describe(n) + " kind " +
              std::to_string(n.GetKind());
        std::cerr << why << "\n  first: " << o << "\n  second: " << n << "\n";
        return false;
      }
    }
    return true;
  }

  // `expected` is re-synced to the export after a schedule difference, so
  // one divergence is counted once and later steps start from the graph.
  void checkAll(MutableGraph& g, ASTNode& expected, const char* what,
                uint64_t seed, int step)
  {
    std::string why;
    if (!g.checkInvariant(&why) && tracing())
      dump(g);
    ASSERT_TRUE(g.checkInvariant(&why)) << why << ": " << what << " seed " << seed << " step " << step;
    std::vector<ASTNode> cur;
    currentNodes(g, cur);
    ASSERT_TRUE(alwaysHashed(g, cur, why)) << why << ": " << what << " seed " << seed << " step " << step;
    const ASTNode out = g.exportRoot();
    if (out != expected)
    {
      if (tracing())
        std::cerr << "===OUT\n" << out << "\n===EXP\n" << expected << "\n===END\n";
      // A different schedule of the same rules, or a bug: only the first
      // is equivalent.
      ASSERT_TRUE(equivalentBySampling(out, expected, why))
          << why << ": " << what << " seed " << seed << " step " << step
          << "\nexport " << out << "\noracle " << expected;
      scheduleDiffs++;
      if (nodeCount(out) > nodeCount(expected))
        graphLarger++;
      if (std::getenv("MUTABLEGRAPH_FUZZ_SCHEDULE") != NULL)
        std::cerr << "schedule difference: " << what << " seed " << seed << " step " << step
                  << "\nexport " << out << "\noracle " << expected << "\n";
      expected = out;
    }
    ASSERT_EQ(g.exportRoot(), out) << "export not idempotent, seed " << seed;
  }

  void dump(MutableGraph& g)
  {
    std::vector<ASTNode> cur;
    currentNodes(g, cur);
    std::cerr << "  current formula, root " << g.current(g.root()).GetNodeNum() << ":\n";
    for (const ASTNode& n : cur)
    {
      std::cerr << "    " << n.GetNodeNum() << " " << n.GetKind()
                << (n.isMutableInterior() ? " M" : "") << (g.isStale(n) ? " stale" : "")
                << " count " << g.parentCount(n) << " kids";
      for (const ASTNode& c : n)
        std::cerr << " " << c.GetNodeNum() << (g.current(c) != c ? ("->" + std::to_string(g.current(c).GetNodeNum())) : "");
      std::cerr << "\n";
    }
  }

  // ---------------------------------------------------------------- run

  void run(uint64_t seed, int steps)
  {
    currentSeed = seed;
    if (tracing())
      setenv("MUTABLEGRAPH_TRACE", "1", 1);
    else
      unsetenv("MUTABLEGRAPH_TRACE");
    const ASTNode f = randomFormula();
    MutableGraph g(mgr);
    g.import(f);
    ASTNode expected = f;
    checkAll(g, expected, "import", seed, -1);

    for (int step = 0; step < steps; step++)
    {
      std::vector<ASTNode> cur;
      currentNodes(g, cur);
      std::vector<ASTNode> immutableInteriors, mutables;
      for (const ASTNode& n : cur)
      {
        if (n.isMutableInterior())
          mutables.push_back(n);
        else if (n.Degree() > 0)
          immutableInteriors.push_back(n);
      }

      if (tracing())
        dump(g);
      const int op = pick(10);
      if (op < 4 || mutables.empty())
      {
        if (immutableInteriors.empty())
          continue;
        const ASTNode target = immutableInteriors[pick(immutableInteriors.size())];
        if (tracing())
          std::cerr << "step " << step << " materialise " << target << "\n";
        g.materialise(target); // may be NULL: collapsed to a leaf
        checkAll(g, expected, "materialise", seed, step);
        continue;
      }

      MutableInterior* m = MutableGraph::asMutable(mutables[pick(mutables.size())]);
      const ASTNode mh = m->handle();
      if (tracing())
        std::cerr << "step " << step << " op " << op << " on " << mh.GetNodeNum() << "\n";
      if (hasStaleTwin(g, cur, mh))
      {
        skippedForTwin++;
        continue;
      }
      const ASTNode before = g.exportNode(mh);

      if (op < 8)
      {
        const size_t slot = pick(mh.Degree());
        const ASTNode old = g.current(mh[slot]);
        ASTNode c;
        if (op == 7)
        {
          // Through the simplifying rules: a node built over current nodes.
          const ASTNode a = replacementFor(g, cur, old, mh);
          const ASTNode b = replacementFor(g, cur, old, mh);
          if (tracing())
            std::cerr << "  factory over " << a.GetNodeNum() << " " << b.GetNodeNum() << "\n";
          if (old.GetValueWidth() > 0)
            c = g.factory().CreateTerm(coin(0.5) ? BVPLUS : BVAND, W, {a, b});
          else
            c = g.factory().CreateNode(coin(0.5) ? AND : OR, {a, b});
          if (!sameSort(c, old) || conesContain(g, c, mh))
            continue;
        }
        else
          c = replacementFor(g, cur, old, mh);
        if (tracing())
          std::cerr << "  candidate " << c.GetNodeNum() << "\n";

        // As the graph will see it. A stale twin resolves to the node
        // itself, which would be a cycle.
        c = g.normalise(c);
        if (m->isDead() || c == mh || conesContain(g, c, mh))
        {
          skippedForTwin++; // normalising c can merge m away
          continue;
        }
        // A no-op patch runs no rules in the graph; the oracle's rebuild
        // would canonicalise a hashing-built node the graph never touched.
        if (c == old)
          continue;

        ASTVec kids;
        for (const ASTNode& k : mh)
          kids.push_back(g.exportNode(k));
        kids[slot] = g.exportNode(c);
        const ASTNode after = hashCons(mh, kids);
        if (tracing())
          std::cerr << "step " << step << " replaceChild slot " << slot
                    << "\n  m: " << mh << "\n  old: " << old << "\n  c: " << c
                    << "\n  before: " << before << "\n  after: " << after << "\n";
        g.replaceChild(m, slot, c);
        ASTNodeMap memo;
        expected = substitute(expected, before, after, memo);
        checkAll(g, expected, "replaceChild", seed, step);
      }
      else
      {
        const ASTNode by = g.normalise(replacementFor(g, cur, mh, mh));
        if (m->isDead() || by == mh)
        {
          skippedForTwin++; // normalising by can merge m away
          continue;
        }
        const ASTNode after = g.exportNode(by);
        if (tracing())
          std::cerr << "step " << step << " replaceNode\n  m: " << mh << "\n  by: " << by
                    << "\n  before: " << before << "\n  after: " << after << "\n";
        g.replaceNode(m, by);
        ASTNodeMap memo;
        expected = substitute(expected, before, after, memo);
        checkAll(g, expected, "replaceNode", seed, step);
      }
    }

    // A fresh graph over the result exports it unchanged.
    const ASTNode out = g.exportRoot();
    MutableGraph again(mgr);
    again.import(out);
    ASSERT_EQ(again.exportRoot(), out) << "re-import not identity, seed " << seed;
    ASSERT_TRUE(again.checkInvariant());
  }
};

// MUTABLEGRAPH_FUZZ_TRACE turns tracing on; MUTABLEGRAPH_FUZZ_TRACE_SEED
// restricts it to one seed, and the graph's own trace follows it.
bool tracing()
{
  if (std::getenv("MUTABLEGRAPH_FUZZ_TRACE") == NULL)
    return false;
  const char* only = std::getenv("MUTABLEGRAPH_FUZZ_TRACE_SEED");
  return only == NULL || std::atoi(only) == currentSeed;
}

int seedsFromEnv(int dflt)
{
  const char* e = std::getenv("MUTABLEGRAPH_FUZZ_SEEDS");
  return e == NULL ? dflt : std::atoi(e);
}

TEST(MutableGraphFuzz, RandomEditSequencesAgreeWithTheOracle)
{
  const int seeds = seedsFromEnv(300);
  const char* only = std::getenv("MUTABLEGRAPH_FUZZ_ONLY");
  size_t skipped = 0;
  size_t diffs = 0, larger = 0;
  for (int s = 1; s <= seeds; s++)
  {
    if (only != NULL && s != std::atoi(only))
      continue;
    if (std::getenv("MUTABLEGRAPH_FUZZ_PROGRESS") != NULL)
      std::cerr << "seed " << s << "\n";
    Fuzz fz(s);
    const char* stepsEnv = std::getenv("MUTABLEGRAPH_FUZZ_STEPS");
    fz.run(s, stepsEnv == NULL ? 40 : std::atoi(stepsEnv));
    skipped += fz.skippedForTwin;
    diffs += fz.scheduleDiffs;
    larger += fz.graphLarger;
    if (::testing::Test::HasFatalFailure())
      return;
  }
  std::cerr << "edits skipped for a stale twin: " << skipped
            << "; schedule differences: " << diffs << " (export larger in " << larger
            << ")\n";
}

TEST(MutableGraphFuzz, MaterialisingAloneChangesNothing)
{
  const int seeds = seedsFromEnv(300);
  const char* only = std::getenv("MUTABLEGRAPH_FUZZ_ONLY");
  for (int s = 1; s <= seeds; s++)
  {
    if (only != NULL && s != std::atoi(only))
      continue;
    Fuzz fz(1000003ULL * s);
    const ASTNode f = fz.randomFormula();
    if (tracing())
      std::cerr << "formula " << f << "\n";
    MutableGraph g(fz.mgr);
    g.import(f);
    std::vector<ASTNode> cur;
    fz.currentNodes(g, cur);
    for (const ASTNode& n : cur)
      if (n.Degree() > 0 && fz.coin(0.7))
      {
        if (tracing())
          std::cerr << "materialise " << n.GetNodeNum() << "\n";
        g.materialise(n);
        std::string why;
        ASSERT_TRUE(g.checkInvariant(&why)) << why << " seed " << s << " after " << n.GetNodeNum();
      }
    ASSERT_TRUE(g.checkInvariant()) << "seed " << s;
    ASSERT_EQ(g.exportRoot(), f) << "seed " << s;
    // Everything materialised, including the root.
    cur.clear();
    fz.currentNodes(g, cur);
    for (const ASTNode& n : cur)
      if (n.Degree() > 0)
        g.materialise(n);
    ASSERT_TRUE(g.checkInvariant()) << "seed " << s;
    ASSERT_EQ(g.exportRoot(), f) << "seed " << s;
  }
}
} // namespace
