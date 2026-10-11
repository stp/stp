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

/*
 * Random formulas and the evaluation oracle shared by the fuzzers of the
 * size-reducing passes (RemoveUnconstrained_Fuzz_Test,
 * GraphRulePass_Fuzz_Test).
 *
 * Formulas at width 2 (some 1 and 3) over a handful of symbols, built
 * through the hashing factory so nothing is pre-simplified, over every
 * kind the passes have rules for. The oracle evaluates two formulas on
 * every assignment of their free variables.
 */

#ifndef RANDOMFORMULA_H_
#define RANDOMFORMULA_H_

#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/cpp_interface.h"
#include <random>
#include <string>
#include <vector>

namespace stp
{
namespace fuzz
{
const uint64_t MAX_COMBOS = 1u << 16;

struct RandomFormula
{
  STPMgr mgr;
  SimplifyingNodeFactory snf;
  NodeFactory* hf;
  std::mt19937_64 rng;
  unsigned counter = 0;

  std::vector<ASTNode> terms2, terms1, terms3, bools;
  std::vector<ASTNode> symbols;
  // Mix in the shapes the sharing-aware rewriting rules match (a constant
  // beside an if-then-else of constants, a comparison with a constant
  // against a sum with one, nested multiplexers that repeat a value, an
  // extract over a bitwise operation), built over the pools so that some
  // of them are shared and the guards have something to refuse.
  bool rewritingShapes = false;

  explicit RandomFormula(uint64_t seed)
      : snf(*(mgr.hashingNodeFactory), mgr), rng(seed)
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

  ASTNode constIte(unsigned w)
  {
    return hf->CreateTerm(ITE, w, {anyBool(), konst(pick(1u << w), w), konst(pick(1u << w), w)});
  }
  ASTNode shapedTerm(unsigned w)
  {
    const ASTNode c = konst(pick(1u << w), w);
    switch (pick(13))
    {
      case 0: return hf->CreateTerm(BVPLUS, w, {c, constIte(w)});
      case 1: return hf->CreateTerm(BVAND, w, {c, constIte(w)});
      case 2: return hf->CreateTerm(coin(0.5) ? BVUMINUS : BVNOT, w, {constIte(w)});
      case 3:
        if (w == 2)
          return hf->CreateTerm(BVCONCAT, 2, {konst(pick(2), 1), constIte(1)});
        return hf->CreateTerm(BVPLUS, w, {c, anyTerm(w)});
      case 4: {
        const ASTNode a = anyTerm(w);
        return hf->CreateTerm(BVPLUS, w, {hf->CreateTerm(BVPLUS, w, {c, a}),
                                          hf->CreateTerm(BVPLUS, w, {konst(pick(1u << w), w), anyTerm(w)})});
      }
      case 5: {
        const ASTNode a = anyTerm(w);
        const ASTNode shared = anyTerm(w);
        return hf->CreateTerm(BVPLUS, w, {hf->CreateTerm(BVMULT, w, {shared, a}),
                                          hf->CreateTerm(BVMULT, w, {shared, anyTerm(w)})});
      }
      case 6: {
        const ASTNode x = anyTerm(w);
        return hf->CreateTerm(BVPLUS, w, {x, hf->CreateTerm(BVUMINUS, w, {hf->CreateTerm(BVPLUS, w, {x, anyTerm(w)})})});
      }
      case 7: {
        const ASTNode t = anyTerm(w);
        return hf->CreateTerm(ITE, w, {anyBool(), t, hf->CreateTerm(ITE, w, {anyBool(), coin(0.5) ? t : anyTerm(w), coin(0.5) ? anyTerm(w) : t})});
      }
      case 8: {
        const ASTNode e = anyTerm(w);
        return hf->CreateTerm(ITE, w, {anyBool(), hf->CreateTerm(ITE, w, {anyBool(), coin(0.5) ? e : anyTerm(w), coin(0.5) ? anyTerm(w) : e}), e});
      }
      case 9: {
        const Kind k = coin(0.5) ? BVAND : (coin(0.5) ? BVXOR : BVOR);
        const ASTNode op = hf->CreateTerm(k, w == 1 ? 2 : w, {anyTerm(w == 1 ? 2 : w), konst(pick(w == 1 ? 4 : (1u << w)), w == 1 ? 2 : w)});
        if (w == 1)
        {
          const unsigned bit = pick(2);
          return hf->CreateTerm(BVEXTRACT, 1, {op, konst(bit, 32), konst(bit, 32)});
        }
        return op;
      }
      case 10: {
        if (w == 1)
        {
          const unsigned bit = pick(2);
          return hf->CreateTerm(BVEXTRACT, 1, {constIte(2), konst(bit, 32), konst(bit, 32)});
        }
        return hf->CreateTerm(BVMULT, w, {konst(1 | (2 * pick(1u << (w - 1))), w), anyTerm(w)});
      }
      case 12: {
        // A symbol read only through extracts over disjoint ranges, for the
        // split-extracts pass; the other half goes to the pool, where it may
        // or may not be picked up.
        const ASTNode sym = bv(3); // in `symbols` only: read through these two
        const ASTNode top = hf->CreateTerm(BVEXTRACT, 1, {sym, konst(2, 32), konst(2, 32)});
        const ASTNode bottom = hf->CreateTerm(BVEXTRACT, 2, {sym, konst(1, 32), konst(0, 32)});
        if (w == 1)
          return hf->CreateTerm(BVXOR, 1, {top, hf->CreateTerm(BVEXTRACT, 1, {bottom, konst(0, 32), konst(0, 32)})});
        if (w == 2)
          return hf->CreateTerm(BVXOR, 2, {bottom, hf->CreateTerm(BVCONCAT, 2, {top, top})});
        return hf->CreateTerm(BVCONCAT, 3, {top, hf->CreateTerm(BVNOT, 2, {bottom})});
      }
      case 11: {
        // Nested same-kind operators, some of them shared through the pools.
        const Kind ks[] = {BVPLUS, BVMULT, BVAND, BVXOR};
        const Kind k = ks[pick(4)];
        const ASTNode inner = hf->CreateTerm(k, w, {anyTerm(w), anyTerm(w)});
        if (coin(0.4))
          termsOf(w).push_back(inner);
        return hf->CreateTerm(k, w, {anyTerm(w), inner});
      }
      default: return constIte(w);
    }
  }
  ASTNode shapedBool()
  {
    const unsigned w = coin(0.7) ? 2 : (coin(0.5) ? 1 : 3);
    const ASTNode c = konst(pick(1u << w), w);
    const ASTNode k = konst(pick(1u << w), w);
    switch (pick(11))
    {
      case 10: {
        // A sum of products with an operand in common, for the factor
        // extraction; one of them negated now and then, one of them
        // shared through the pool now and then.
        const ASTNode x = anyTerm(w);
        ASTVec addends;
        const size_t n = 2 + pick(2);
        for (size_t i = 0; i < n; i++)
        {
          ASTNode product = hf->CreateTerm(BVMULT, w, {x, anyTerm(w)});
          if (coin(0.2))
            termsOf(w).push_back(product);
          if (coin(0.25))
            product = hf->CreateTerm(BVUMINUS, w, {product});
          addends.push_back(product);
        }
        if (coin(0.5))
          addends.push_back(anyTerm(w));
        const ASTNode sum = hf->CreateTerm(BVPLUS, w, addends);
        if (coin(0.3))
          termsOf(w).push_back(sum);
        return hf->CreateNode(coin(0.5) ? EQ : BVGT, {sum, coin(0.5) ? c : anyTerm(w)});
      }
      case 9: {
        const Kind kk = coin(0.5) ? AND : (coin(0.5) ? OR : XOR);
        const ASTNode inner = hf->CreateNode(kk, {anyBool(), anyBool()});
        if (coin(0.4))
          bools.push_back(inner);
        return hf->CreateNode(kk, {anyBool(), inner});
      }
      case 0: return hf->CreateNode(EQ, {c, hf->CreateTerm(BVPLUS, w, {k, anyTerm(w)})});
      case 1: return hf->CreateNode(coin(0.5) ? BVSGT : BVGT, {c, hf->CreateTerm(BVPLUS, w, {k, anyTerm(w)})});
      case 2: return hf->CreateNode(BVGT, {hf->CreateTerm(BVPLUS, w, {k, anyTerm(w)}), c});
      case 3: return hf->CreateNode(EQ, {konst(0, w), hf->CreateTerm(BVPLUS, w, {anyTerm(w), anyTerm(w)})});
      case 4: return hf->CreateNode(EQ, {c, hf->CreateTerm(BVPLUS, w, {anyTerm(w), hf->CreateTerm(BVUMINUS, w, {anyTerm(w)})})});
      case 5: return hf->CreateNode(EQ, {hf->CreateTerm(BVPLUS, w, {c, anyTerm(w)}), hf->CreateTerm(BVPLUS, w, {k, anyTerm(w)})});
      case 6: {
        const ASTNode a = anyTerm(w);
        return hf->CreateNode(EQ, {hf->CreateTerm(BVPLUS, w, {a, anyTerm(w), anyTerm(w)}), hf->CreateTerm(BVPLUS, w, {a, anyTerm(w)})});
      }
      case 7: return hf->CreateNode(coin(0.5) ? BVSGT : BVGT, {c, constIte(w)});
      default: {
        const ASTNode cond = anyBool();
        ASTVec kids = {coin(0.5) ? cond : hf->CreateNode(NOT, {cond}), anyBool(), anyBool()};
        return hf->CreateNode(ITE, {cond, hf->CreateNode(coin(0.5) ? OR : AND, kids), anyBool()});
      }
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

  // `topLevelDefinitions`: conjoin a few definitions of the symbols at
  // the top level, for an equality propagation to find.
  ASTNode randomFormula(bool topLevelDefinitions)
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
        termsOf(w).push_back(rewritingShapes && coin(0.5) ? shapedTerm(w) : randomTerm(w));
      }
      else
        bools.push_back(rewritingShapes && coin(0.5) ? shapedBool() : randomBool());
    }
    ASTVec conj;
    const size_t k = 1 + pick(3);
    for (size_t i = 0; i < k; i++)
      conj.push_back(anyBool());
    // Top-level definitions for the equality propagation to find.
    if (topLevelDefinitions && !symbols.empty())
    {
      const size_t e = pick(3);
      for (size_t i = 0; i < e; i++)
      {
        const ASTNode sym = symbols[pick(symbols.size())];
        if (sym.GetValueWidth() == 0)
          conj.push_back(coin(0.5) ? sym : hf->CreateNode(NOT, {sym}));
        else
          conj.push_back(hf->CreateNode(EQ, {sym, anyTerm(sym.GetValueWidth())}));
      }
    }
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
};

// A formula source with a substitution map, for passes that record
// definitions: the original with the definitions substituted back is what
// the result is compared with.
struct DefinitionFuzz : RandomFormula
{
  SubstitutionMap sm;
  Simplifier simp;

  explicit DefinitionFuzz(uint64_t seed) : RandomFormula(seed), sm(&mgr), simp(&mgr, &sm)
  {
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
  // fixed point. `from` is the map holding them: this fuzzer's own unless
  // a pass ran with another.
  bool backSubstitute(const ASTNode& n, ASTNode& out, std::string& why)
  {
    return backSubstitute(n, out, why, simp);
  }
  bool backSubstitute(const ASTNode& n, ASTNode& out, std::string& why,
                      Simplifier& from)
  {
    const DenseNodeMap& defs = *from.Return_SolverMap();
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
      DenseNodeMap fromTo = *from.Return_SolverMap();
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
}
}

#endif
