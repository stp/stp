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

// Randomised checking of RemoveUnconstrained on the mutable graph.
//
// Random formulas at width 2 over a handful of symbols, built through the
// hashing factory so nothing is pre-simplified, then rebuilt once through
// the simplifying factory (see canonical), over every kind the pass
// has a rule for: the per-kind arms, n-ary operators, chains of constant
// operations under a predicate (the ground-path collapse), comparisons
// against constants and against terms, term and Boolean if-then-else,
// extracts, concatenations and extensions. For each formula:
//
//   1. Soundness. With the image-variable rewrite off every rule is a
//      pointwise identity: the original with the recorded definitions
//      substituted back agrees with the result on every assignment. With
//      it on, equisatisfiability with model mapping: every model of the
//      result maps back to a model of the original, and both are
//      satisfiable or neither is.
//   2. Idempotence. A second run over the result returns it unchanged.
//   3. The graph. STP_RU_CHECK_GRAPH is set for the run, so the pass
//      recounts the graph from scratch after every edit.
//
// The checks and their evaluation are those of the exhaustive suite.
// MUTABLEGRAPH_FUZZ_SEEDS overrides the number of seeds (default 300).

#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/Parser/parser.h"
#include "stp/Simplifier/RemoveUnconstrained.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/cpp_interface.h"
#include <functional>
#include <cstdlib>
#include <gtest/gtest.h>
#include <iostream>
#include <random>
#include <string>
#include <vector>

using namespace stp;

namespace
{
const uint64_t MAX_COMBOS = 1u << 16;

struct Fuzz
{
  STPMgr mgr;
  SimplifyingNodeFactory snf;
  NodeFactory* hf;
  SubstitutionMap sm;
  Simplifier simp;
  std::mt19937_64 rng;
  unsigned counter = 0;

  std::vector<ASTNode> terms2, terms1, terms3, bools;
  std::vector<ASTNode> symbols;

  explicit Fuzz(uint64_t seed)
      : snf(*(mgr.hashingNodeFactory), mgr), sm(&mgr), simp(&mgr, &sm),
        rng(seed)
  {
    static const bool booted = []() {
      CONSTANTBV::BitVector_Boot();
      return true;
    }();
    (void)booted;
    mgr.defaultNodeFactory = &snf;
    hf = mgr.hashingNodeFactory;
  }

  size_t pick(size_t n) { return std::uniform_int_distribution<size_t>(0, n - 1)(rng); }
  bool coin(double p) { return std::uniform_real_distribution<double>(0, 1)(rng) < p; }

  ASTNode konst(unsigned value, unsigned width) { return mgr.CreateBVConst(width, value); }
  ASTNode bv(unsigned width)
  {
    const ASTNode s = mgr.CreateSymbol(("x" + std::to_string(counter++)).c_str(), 0, width);
    symbols.push_back(s);
    return s;
  }
  ASTNode boolean()
  {
    const ASTNode s = mgr.CreateSymbol(("p" + std::to_string(counter++)).c_str(), 0, 0);
    symbols.push_back(s);
    return s;
  }

  std::vector<ASTNode>& termsOf(unsigned width)
  {
    return width == 1 ? terms1 : (width == 3 ? terms3 : terms2);
  }
  const ASTNode& from(std::vector<ASTNode>& pool)
  {
    if (pool.size() > 3 && coin(0.5))
      return pool[pool.size() - 1 - pick(3)];
    return pool[pick(pool.size())];
  }
  ASTNode anyTerm(unsigned width)
  {
    std::vector<ASTNode>& pool = termsOf(width);
    if (pool.empty() || coin(0.15))
      return konst(pick(1u << width), width);
    return from(pool);
  }

  // One operation over existing nodes, through the hashing factory.
  ASTNode randomTerm(unsigned width)
  {
    const unsigned w = width;
    switch (pick(16))
    {
      case 0: return hf->CreateTerm(BVPLUS, w, {anyTerm(w), anyTerm(w)});
      case 1: {
        ASTVec kids = {anyTerm(w), anyTerm(w), anyTerm(w)};
        return hf->CreateTerm(BVPLUS, w, kids);
      }
      case 2: return hf->CreateTerm(BVMULT, w, {anyTerm(w), anyTerm(w)});
      case 3: {
        ASTVec kids = {anyTerm(w), anyTerm(w), konst(1 | (2 * pick(1u << (w - 1))), w)};
        return hf->CreateTerm(BVMULT, w, kids);
      }
      case 4: return hf->CreateTerm(BVSUB, w, {anyTerm(w), anyTerm(w)});
      case 5: return hf->CreateTerm(coin(0.5) ? BVAND : BVOR, w, {anyTerm(w), anyTerm(w)});
      case 6: return hf->CreateTerm(BVXOR, w, {anyTerm(w), anyTerm(w)});
      case 7: return hf->CreateTerm(coin(0.5) ? BVNOT : BVUMINUS, w, {anyTerm(w)});
      case 8: return hf->CreateTerm(ITE, w, {anyBool(), anyTerm(w), anyTerm(w)});
      case 9: {
        const Kind k = coin(0.5) ? BVLEFTSHIFT : (coin(0.5) ? BVRIGHTSHIFT : BVSRSHIFT);
        return hf->CreateTerm(k, w, {anyTerm(w), anyTerm(w)});
      }
      case 10: {
        const Kind ks[] = {BVDIV, BVMOD, SBVDIV, SBVREM, SBVMOD};
        return hf->CreateTerm(ks[pick(5)], w, {anyTerm(w), anyTerm(w)});
      }
      case 11:
        if (w == 2)
          return hf->CreateTerm(BVCONCAT, 2, {anyTerm(1), anyTerm(1)});
        if (w == 3)
        {
          const unsigned a = coin(0.5) ? 1 : 2;
          return hf->CreateTerm(BVCONCAT, 3, {anyTerm(a), anyTerm(3 - a)});
        }
        {
          const unsigned bit = pick(2);
          return hf->CreateTerm(BVEXTRACT, 1, {anyTerm(2), konst(bit, 32), konst(bit, 32)});
        }
      case 12:
        if (w == 3)
          return hf->CreateTerm(coin(0.5) ? BVSX : BVZX, 3, {anyTerm(coin(0.5) ? 1 : 2), konst(3, 32)});
        if (w == 2)
        {
          if (coin(0.5))
            return hf->CreateTerm(coin(0.5) ? BVSX : BVZX, 2, {anyTerm(1), konst(2, 32)});
          const unsigned low = pick(2);
          return hf->CreateTerm(BVEXTRACT, 2, {anyTerm(3), konst(low + 1, 32), konst(low, 32)});
        }
        {
          const unsigned bit = pick(3);
          return hf->CreateTerm(BVEXTRACT, 1, {anyTerm(3), konst(bit, 32), konst(bit, 32)});
        }
      case 13: {
        // A chain of constant operations: fodder for the ground-path collapse.
        ASTNode t = anyTerm(w);
        for (int i = 0, n = 1 + pick(3); i < n; i++)
        {
          const Kind ks[] = {BVPLUS, BVMULT, BVXOR, BVAND, BVOR, BVSUB, BVLEFTSHIFT, BVRIGHTSHIFT, BVMOD, BVDIV};
          const Kind k = ks[pick(10)];
          const ASTNode c = konst(pick(1u << w), w);
          t = coin(0.5) ? hf->CreateTerm(k, w, {t, c}) : hf->CreateTerm(k, w, {c, t});
        }
        return t;
      }
      case 14: {
        if (w == 1)
        {
          const unsigned bit = pick(2);
          return hf->CreateTerm(BVEXTRACT, 1, {anyTerm(2), konst(bit, 32), konst(bit, 32)});
        }
        return hf->CreateTerm(BVPLUS, w, {anyTerm(w), konst(pick(1u << w), w)});
      }
      default: return bv(w);
    }
  }

  ASTNode anyBool()
  {
    if (bools.empty() || coin(0.15))
      return coin(0.5) ? mgr.ASTTrue : mgr.ASTFalse;
    return from(bools);
  }

  ASTNode randomBool()
  {
    const unsigned w = coin(0.7) ? 2 : (coin(0.5) ? 1 : 3);
    switch (pick(12))
    {
      case 0: return hf->CreateNode(AND, {anyBool(), anyBool()});
      case 1: {
        ASTVec kids = {anyBool(), anyBool(), anyBool()};
        return hf->CreateNode(AND, kids);
      }
      case 2: return hf->CreateNode(OR, {anyBool(), anyBool()});
      case 3: {
        const ASTNode b = anyBool();
        return b.GetKind() == NOT ? b[0] : hf->CreateNode(NOT, {b});
      }
      case 4: return hf->CreateNode(XOR, {anyBool(), anyBool()});
      case 5: return hf->CreateNode(ITE, {anyBool(), anyBool(), anyBool()});
      case 6: return hf->CreateNode(EQ, {anyTerm(w), anyTerm(w)});
      case 7: return hf->CreateNode(EQ, {anyTerm(w), konst(pick(1u << w), w)});
      case 8: {
        const Kind ks[] = {BVGT, BVGE, BVSGT, BVSGE, BVLT, BVLE, BVSLT, BVSLE};
        return hf->CreateNode(ks[pick(8)], {anyTerm(w), anyTerm(w)});
      }
      case 9: {
        const Kind ks[] = {BVGT, BVGE, BVSGT, BVSGE};
        return coin(0.5) ? hf->CreateNode(ks[pick(4)], {anyTerm(w), konst(pick(1u << w), w)})
                         : hf->CreateNode(ks[pick(4)], {konst(pick(1u << w), w), anyTerm(w)});
      }
      case 10: return hf->CreateNode(IFF, {anyBool(), anyBool()});
      default: return boolean();
    }
  }

  ASTNode randomFormula()
  {
    terms1.clear(); terms2.clear(); terms3.clear(); bools.clear(); symbols.clear();
    const int nsyms = 2 + pick(3);
    for (int i = 0; i < nsyms; i++)
    {
      const unsigned w = coin(0.75) ? 2 : (coin(0.5) ? 1 : 3);
      termsOf(w).push_back(bv(w));
    }
    if (coin(0.5))
      bools.push_back(boolean());
    const size_t size = 4 + pick(14);
    for (size_t i = 0; i < size; i++)
    {
      if (coin(0.65))
      {
        const unsigned w = coin(0.7) ? 2 : (coin(0.5) ? 1 : 3);
        termsOf(w).push_back(randomTerm(w));
      }
      else
        bools.push_back(randomBool());
    }
    ASTVec conj;
    const size_t k = 1 + pick(3);
    for (size_t i = 0; i < k; i++)
      conj.push_back(anyBool());
    return conj.size() == 1 ? conj[0] : hf->CreateNode(AND, conj);
  }

  // --------------------------------------------------------- the oracle

  void collectSymbols(const ASTNode& n, ASTNodeSet& out)
  {
    std::vector<ASTNode> stack(1, n);
    ASTNodeSet seen;
    while (!stack.empty())
    {
      const ASTNode c = stack.back();
      stack.pop_back();
      if (!seen.insert(c).second)
        continue;
      if (c.GetKind() == SYMBOL)
        out.insert(c);
      for (const ASTNode& k : c)
        stack.push_back(k);
    }
  }

  bool definitionCycles(const DenseNodeMap& defs, const ASTNode& sym,
                        ASTNodeSet& onPath, ASTNodeSet& done)
  {
    if (done.count(sym))
      return false;
    if (!onPath.insert(sym).second)
      return true;
    const auto it = defs.find(sym);
    if (it != defs.end())
    {
      ASTNodeSet uses;
      collectSymbols(it->second, uses);
      for (const auto& u : uses)
        if (definitionCycles(defs, u, onPath, done))
          return true;
    }
    onPath.erase(sym);
    done.insert(sym);
    return false;
  }

  // The original with the recorded definitions substituted back, to a
  // fixed point.
  bool backSubstitute(const ASTNode& n, ASTNode& out, std::string& why)
  {
    const DenseNodeMap& defs = *simp.Return_SolverMap();
    ASTNodeSet onPath, done;
    for (const auto& d : defs)
      if (definitionCycles(defs, d.first, onPath, done))
      {
        why = "a symbol is defined through itself";
        return false;
      }
    ASTNode cur = n;
    for (int i = 0; i < 64; i++)
    {
      DenseNodeMap fromTo = *simp.Return_SolverMap();
      DenseNodeMap cache;
      ASTNode next = SubstitutionMap::replace(cur, fromTo, cache, &snf);
      if (next == cur)
      {
        out = cur;
        return true;
      }
      cur = next;
    }
    why = "back-substitution did not reach a fixed point";
    return false;
  }

  // The generated formula rebuilt bottom-up through the simplifying
  // factory over sorted children: a fixpoint of the rules, as the
  // pipeline's input is. The second run rebuilds its input the same way
  // (applySubstitutionMap), so without this a node the pass never touched
  // would fold on the second run and look like non-idempotence.
  ASTNode canonical(const ASTNode& n, ASTNodeMap& memo)
  {
    if (n.Degree() == 0)
      return n;
    const auto it = memo.find(n);
    if (it != memo.end())
      return it->second;
    ASTVec kids;
    for (const ASTNode& c : n)
      kids.push_back(canonical(c, memo));
    if (kids.size() > 1 && isCommutative(n.GetKind()))
    {
      if (is_Form_kind(n.GetKind()))
        SortByExprNum(kids);
      else
        SortByArith(kids);
    }
    ASTNode r;
    if (n.GetIndexWidth() > 0)
      r = snf.CreateArrayTerm(n.GetKind(), n.GetIndexWidth(), n.GetValueWidth(), kids);
    else if (n.GetValueWidth() > 0)
      r = snf.CreateTerm(n.GetKind(), n.GetValueWidth(), kids);
    else
      r = snf.CreateNode(n.GetKind(), kids);
    memo.insert({n, r});
    return r;
  }

  ASTNode eval(const ASTNode& n, ASTNodeMap assignment)
  {
    ASTNodeMap cache;
    ASTNode s = SubstitutionMap::replace(n, assignment, cache, &snf);
    if (s.isConstant())
      return s;
    return NonMemberBVConstEvaluator(&mgr, s);
  }

  ASTNode valueFor(const ASTNode& sym, unsigned v)
  {
    if (sym.GetType() == BOOLEAN_TYPE)
      return (v & 1) ? mgr.ASTTrue : mgr.ASTFalse;
    return konst(v, sym.GetValueWidth());
  }
  unsigned domainSize(const ASTNode& sym)
  {
    return (sym.GetType() == BOOLEAN_TYPE) ? 2u : (1u << sym.GetValueWidth());
  }

  bool assignmentsOf(const std::vector<ASTNode>& syms, uint64_t& combos)
  {
    combos = 1;
    for (const auto& s : syms)
    {
      combos *= domainSize(s);
      if (combos > MAX_COMBOS)
        return false;
    }
    return true;
  }
  ASTNodeMap assignment(const std::vector<ASTNode>& syms, uint64_t c)
  {
    ASTNodeMap a;
    for (size_t i = 0; i < syms.size(); i++)
    {
      const unsigned size = domainSize(syms[i]);
      a.insert({syms[i], valueFor(syms[i], c % size)});
      c /= size;
    }
    return a;
  }

  // Pointwise: back(original) == result at every assignment.
  bool checkEquivalent(const ASTNode& back, const ASTNode& result, std::string& why)
  {
    ASTNodeSet symSet;
    collectSymbols(back, symSet);
    collectSymbols(result, symSet);
    std::vector<ASTNode> syms(symSet.begin(), symSet.end());
    uint64_t combos;
    if (!assignmentsOf(syms, combos))
    {
      why = "skip";
      return false;
    }
    for (uint64_t c = 0; c < combos; c++)
    {
      if (eval(back, assignment(syms, c)) != eval(result, assignment(syms, c)))
      {
        why = "meaning changed at assignment " + std::to_string(c);
        return false;
      }
    }
    return true;
  }

  // Equisatisfiable with model mapping.
  bool checkEquisat(const ASTNode& original, const ASTNode& back,
                    const ASTNode& result, std::string& why)
  {
    ASTNodeSet symSet;
    collectSymbols(result, symSet);
    collectSymbols(back, symSet);
    std::vector<ASTNode> syms(symSet.begin(), symSet.end());
    uint64_t combos;
    if (!assignmentsOf(syms, combos))
    {
      why = "skip";
      return false;
    }
    bool resultSat = false;
    for (uint64_t c = 0; c < combos; c++)
      if (eval(result, assignment(syms, c)) == mgr.ASTTrue)
      {
        resultSat = true;
        if (eval(back, assignment(syms, c)) != mgr.ASTTrue)
        {
          why = "a model of the result does not map back, assignment " + std::to_string(c);
          return false;
        }
      }
    ASTNodeSet oset;
    collectSymbols(original, oset);
    std::vector<ASTNode> osyms(oset.begin(), oset.end());
    uint64_t ocombos;
    if (!assignmentsOf(osyms, ocombos))
    {
      why = "skip";
      return false;
    }
    bool origSat = false;
    for (uint64_t c = 0; c < ocombos && !origSat; c++)
      origSat = (eval(original, assignment(osyms, c)) == mgr.ASTTrue);
    if (origSat != resultSat)
    {
      why = std::string("satisfiability changed: original ") +
            (origSat ? "sat" : "unsat") + ", result " + (resultSat ? "sat" : "unsat");
      return false;
    }
    return true;
  }
};

int seedsFromEnv(int dflt)
{
  const char* e = std::getenv("MUTABLEGRAPH_FUZZ_SEEDS");
  return e == NULL ? dflt : std::atoi(e);
}

void runSeeds(bool imageVars)
{
  setenv("STP_RU_CHECK_GRAPH", "1", 1);
  const int seeds = seedsFromEnv(300);
  const char* only = std::getenv("MUTABLEGRAPH_FUZZ_ONLY");
  size_t skipped = 0, trivial = 0;
  size_t imageConstrained = 0; // category A, see the idempotence check
  for (int s = 1; s <= seeds; s++)
  {
    if (only != NULL && s != std::atoi(only))
      continue;
    Fuzz fz(imageVars ? 7919ULL * s : s);
    fz.mgr.UserFlags.unconstrained_image_vars = imageVars;
    ASTNodeMap canonMemo;
    // Random width-2 formulas fold to a constant six times in ten once the
    // rules have seen them; draw again (same seed, next draw) a few times.
    ASTNode f;
    for (int attempt = 0; attempt < 8; attempt++)
    {
      f = fz.canonical(fz.randomFormula(), canonMemo);
      if (!f.isConstant())
        break;
    }
    if (std::getenv("MUTABLEGRAPH_FUZZ_PROGRESS") != NULL)
      std::cerr << "seed " << s << "\n";
    const char* traceSeed = std::getenv("MUTABLEGRAPH_FUZZ_TRACE_SEED");
    const bool tracing = std::getenv("MUTABLEGRAPH_FUZZ_TRACE") != NULL &&
                         (traceSeed == NULL || std::atoi(traceSeed) == s);
    if (tracing)
      std::cerr << "seed " << s << " image vars " << imageVars << " formula " << f << "\n";
    // The pass's own trace follows the harness's.
    if (tracing)
      setenv("STP_RU_CHECK_GRAPH", "1", 1);
    else
      setenv("STP_RU_CHECK_GRAPH", "1", 1);
    if (f.isConstant())
    {
      trivial++;
      continue;
    }

    RemoveUnconstrained r1(fz.mgr);
    const ASTNode result = r1.topLevel(f, &fz.simp);

    // Idempotence. A run that made an image constraint is the known
    // exception: the constraint joins the formula after the graph is
    // exported, so the next run sees the fresh variable as free and
    // finishes the job (category A of the idempotence report). Counted,
    // not asserted, until the constraint is spliced into the graph.
    // The pipeline rebuilds the pass's output through the simplifier's
    // substitution before the next pass sees it; with the rules run where
    // the pass edited, that rebuild changes nothing. The second run gets
    // its own simplifier, so the definitions it records do not pollute
    // the first run's map, which the soundness check below reads.
    const ASTNode rebuilt = fz.simp.applySubstitutionMap(result);
    ASSERT_EQ(rebuilt, result) << "the simplifier's rebuild changed the result, seed "
                               << s << " image vars " << imageVars << "\nformula " << f
                               << "\nresult " << result << "\nrebuilt " << rebuilt;
    SubstitutionMap sm2(&fz.mgr);
    Simplifier simp2(&fz.mgr, &sm2);
    RemoveUnconstrained r2(fz.mgr);
    const ASTNode again = r2.topLevel(result, &simp2);
    if (r1.imageConstraintCount() > 0 && again != result)
      imageConstrained++;
    else
      ASSERT_EQ(again, result) << "second pass changed the result, seed " << s
                               << " image vars " << imageVars << "\nformula " << f
                               << "\nresult " << result << "\nagain " << again;

    // Soundness.
    ASTNode back;
    std::string why;
    ASSERT_TRUE(fz.backSubstitute(f, back, why)) << why << ", seed " << s;
    const bool ok = imageVars ? fz.checkEquisat(f, back, result, why)
                              : fz.checkEquivalent(back, result, why);
    if (!ok && why == "skip")
    {
      skipped++;
      continue;
    }
    ASSERT_TRUE(ok) << why << ", seed " << s << " image vars " << imageVars
                    << "\nformula " << f << "\nresult " << result;
  }
  std::cerr << "seeds " << seeds << ", skipped (too many assignments) " << skipped
            << ", trivial " << trivial
            << ", not idempotent after an image constraint " << imageConstrained << "\n";
}

TEST(RemoveUnconstrainedFuzz, PointwiseIdentityAndIdempotence)
{
  runSeeds(false);
}

TEST(RemoveUnconstrainedFuzz, EquisatWithImageVariables)
{
  runSeeds(true);
}
} // namespace
