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

#include "stp/ToSat/BVExactEncoder.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/ToSat/BBNodeManagerAIG.h"
#include "stp/ToSat/BitBlaster.h"
#include "stp/ToSat/ToCNFAIG.h"

#include <cassert>

namespace stp
{

namespace
{

// x <-> y
void addEquiv(SATSolver& solver, unsigned x, unsigned y)
{
  SATSolver::vec_literals cl;
  cl.clear();
  cl.push(SATSolver::mkLit(x, true));
  cl.push(SATSolver::mkLit(y, false));
  solver.addClause(cl);
  cl.clear();
  cl.push(SATSolver::mkLit(x, false));
  cl.push(SATSolver::mkLit(y, true));
  solver.addClause(cl);
}

// The same rewriting ToCNFAIG runs before its own CNF conversion, and under
// the same flag: an encoding that is meant to be the one the query would
// have had is not that if it is optimised differently. Off by default,
// which is why the mapping below is where the size actually comes from.
void rewrite(BBNodeManagerAIG& mgr, int64_t iterations)
{
  if (iterations <= 0)
    return;

  Dar_LibStart();
  Dar_RwrPar_t Pars;
  Dar_ManDefaultRwrParams(&Pars);

  for (int64_t i = 0; i < iterations; i++)
  {
    const int before = mgr.aigMgr->nObjs[AIG_OBJ_AND];

    Aig_Man_t* pTemp;
    mgr.aigMgr = Aig_ManDupDfs(pTemp = mgr.aigMgr);
    Aig_ManStop(pTemp);
    Dar_ManRewrite(mgr.aigMgr, &Pars);

    // Rewriting can leave an unreferenced AND node behind, which
    // Aig_ManDupDfs asserts about rather than copies; see the same call in
    // ToCNFAIG for the whole story.
    Aig_ManCleanup(mgr.aigMgr);
    mgr.aigMgr = Aig_ManDupDfs(pTemp = mgr.aigMgr);
    Aig_ManStop(pTemp);

    if (before == mgr.aigMgr->nObjs[AIG_OBJ_AND])
      break;
  }
}

} // namespace

// ---------------------------------------------------------------------------
// The facts, as values.
//
// Written over unsigned arithmetic on the bit vectors rather than over the
// circuits below, so that the test which checks the two against each other
// is checking two things and not one.
// ---------------------------------------------------------------------------

namespace
{

bool allZero(const std::vector<bool>& v)
{
  for (bool b : v)
    if (b)
      return false;
  return true;
}

bool allOnes(const std::vector<bool>& v)
{
  for (bool b : v)
    if (!b)
      return false;
  return true;
}

bool ule(const std::vector<bool>& a, const std::vector<bool>& b)
{
  for (int i = (int)a.size() - 1; i >= 0; --i)
    if (a[i] != b[i])
      return b[i];
  return true;
}

std::vector<bool> notOf(const std::vector<bool>& v)
{
  std::vector<bool> r(v.size());
  for (unsigned i = 0; i < v.size(); ++i)
    r[i] = !v[i];
  return r;
}

// Two's complement negation: the bitwise complement plus one.
std::vector<bool> negOf(const std::vector<bool>& v)
{
  std::vector<bool> r = notOf(v);
  bool carry = true;
  for (unsigned i = 0; i < r.size() && carry; ++i)
  {
    const bool sum = r[i] ^ carry;
    carry = r[i] && carry;
    r[i] = sum;
  }
  return r;
}

std::vector<bool> decOf(const std::vector<bool>& v)
{
  // v - 1, which is v + ~0.
  std::vector<bool> r(v.size());
  bool borrow = true;
  for (unsigned i = 0; i < v.size(); ++i)
  {
    r[i] = v[i] ^ borrow;
    borrow = !v[i] && borrow;
  }
  return r;
}

std::vector<bool> andOf(const std::vector<bool>& a, const std::vector<bool>& b)
{
  std::vector<bool> r(a.size());
  for (unsigned i = 0; i < a.size(); ++i)
    r[i] = a[i] && b[i];
  return r;
}

// A logical right shift by the value `amt` holds. A shift at or past the
// width clears the vector, which is what SMT-LIB's bvlshr does and what the
// circuit below is built to match.
std::vector<bool> shrOf(const std::vector<bool>& v, const std::vector<bool>& amt)
{
  const unsigned W = (unsigned)v.size();
  unsigned long long by = 0;
  for (unsigned i = 0; i < W; ++i)
    if (amt[i])
    {
      if (i >= 64 || by > W)
      {
        by = W; // saturate rather than overflow; anything >= W clears it
        break;
      }
      by += (1ull << i);
      if (by > W)
      {
        by = W;
        break;
      }
    }

  std::vector<bool> r(W, false);
  for (unsigned i = 0; i + by < W; ++i)
    r[i] = v[i + (unsigned)by];
  return r;
}

} // namespace

bool divLemmaHolds(DivLemma lemma, const std::vector<bool>& x,
                   const std::vector<bool>& s, const std::vector<bool>& t)
{
  const unsigned W = (unsigned)x.size();
  const std::vector<bool> zero(W, false);
  std::vector<bool> one(W, false);
  one[0] = true;

  switch (lemma)
  {
    case DivLemma::DividendZero:
      return !(allZero(x) && !allZero(s)) || allZero(t);

    case DivLemma::DivisorEqualsDividend:
      return !(s == x && !allZero(s)) || t == one;

    case DivLemma::DivisorAllOnes:
      return !(allOnes(s) && !allOnes(x)) || allZero(t);

    case DivLemma::QuotientBelowNegatedDivisor:
    {
      std::vector<bool> sOr1 = s;
      sOr1[0] = true;
      return ule(t, negOf(sOr1));
    }

    case DivLemma::DividendAboveNegatedAnd:
      return ule(negOf(andOf(negOf(s), negOf(t))), x);

    case DivLemma::DivisorAboveShiftedDividend:
      return ule(shrOf(x, t), s);

    case DivLemma::DivisorLessOneAboveShiftedDividend:
      return ule(shrOf(x, t), decOf(s));
  }
  return true;
}

const char* divLemmaName(DivLemma lemma)
{
  switch (lemma)
  {
    case DivLemma::DividendZero: return "dividend-zero";
    case DivLemma::DivisorEqualsDividend: return "divisor-equals-dividend";
    case DivLemma::DivisorAllOnes: return "divisor-all-ones";
    case DivLemma::QuotientBelowNegatedDivisor:
      return "quotient-below-negated-divisor";
    case DivLemma::DividendAboveNegatedAnd:
      return "dividend-above-negated-and";
    case DivLemma::DivisorAboveShiftedDividend:
      return "divisor-above-shifted-dividend";
    case DivLemma::DivisorLessOneAboveShiftedDividend:
      return "divisor-less-one-above-shifted-dividend";
  }
  return "unknown";
}

void BVExactEncoder::encodeDivLemma(SATSolver& solver, DivLemma lemma,
                                    unsigned width,
                                    const std::vector<unsigned>& dividendVars,
                                    const std::vector<unsigned>& divisorVars,
                                    const std::vector<unsigned>& resultVars)
{
  assert(dividendVars.size() >= width);
  assert(divisorVars.size() >= width);
  assert(resultVars.size() >= width);

  BBNodeManagerAIG mgr;
  mgr.nodeBudget = bm->UserFlags.aig_node_budget;
  SubstitutionMap sm(bm);
  Simplifier simp(bm, &sm);
  // Told not to abstract, for the reason encode() gives: the circuit here is
  // spliced onto an abstraction's own variables, so a record minted inside it
  // would be against an AIG this call throws away.
  BitBlaster bb(&mgr, &simp, bm->defaultNodeFactory, &bm->UserFlags, NULL,
                /*allowAbstraction=*/false);

  // Three input vectors this time, in the order the splice reads them back:
  // the dividend, the divisor, then the abstraction's own result bits. The
  // result is an input here and not an output -- the lemma constrains it
  // without defining it, which is the whole difference from `encode`.
  BBNodeVec x(width), s(width), t(width);
  BBNodeVec* const ins[3] = {&x, &s, &t};
  for (unsigned v = 0; v < 3; v++)
    for (unsigned i = 0; i < width; i++)
    {
      (*ins[v])[i] = BBNodeAIG(Aig_ObjCreateCi(mgr.aigMgr));
      (*ins[v])[i].symbol_index = mgr.aigMgr->vCis->nSize - 1;
    }

  BBNodeSet support;
  const BBNodeAIG claim = bb.BBDivLemma(lemma, x, s, t, support);

  Aig_ObjCreateCo(mgr.aigMgr, claim.n);
  for (const BBNodeAIG& c : support)
    Aig_ObjCreateCo(mgr.aigMgr, c.n);

  const unsigned outputs = 1 + (unsigned)support.size();

  rewrite(mgr, bm->UserFlags.AIG_rewrites_iterations);
  assert(Aig_ManCheck(mgr.aigMgr));
  assert((unsigned)Aig_ManCoNum(mgr.aigMgr) == outputs);

  Cnf_Dat_t* cnf = ToCNFAIG(bm->UserFlags).derive_cnf(mgr, outputs);
  assert(cnf != NULL);

  std::vector<unsigned> cnfToSolver(cnf->nVars, ~((unsigned)0));
  for (unsigned i = 0; i < 3 * width; i++)
  {
    const int var = cnf->pVarNums[Aig_ManCi(mgr.aigMgr, (int)i)->Id];
    if (var < 0)
      continue;
    cnfToSolver[var] = (i < width)         ? dividendVars[i]
                       : (i < 2 * width)   ? divisorVars[i - width]
                                           : resultVars[i - 2 * width];
  }

  for (int var = 0; var < cnf->nVars; var++)
    if (cnfToSolver[var] == ~((unsigned)0))
    {
      const unsigned fresh = solver.newVar();
      solver.setFrozen(fresh);
      cnfToSolver[var] = fresh;
    }

  SATSolver::vec_literals cl;
  for (int i = 0; i < cnf->nClauses; i++)
  {
    cl.clear();
    for (int *pLit = cnf->pClauses[i], *pStop = cnf->pClauses[i + 1];
         pLit < pStop; pLit++)
      cl.push(SATSolver::mkLit(cnfToSolver[(*pLit) >> 1], ((*pLit) & 1) != 0));
    solver.addClause(cl);
  }

  // Every output is asserted: the claim itself, and whatever the circuit
  // wanted conjoined to it.
  for (unsigned i = 0; i < outputs; i++)
  {
    const unsigned var =
        cnfToSolver[cnf->pVarNums[Aig_ManCo(mgr.aigMgr, (int)i)->Id]];
    cl.clear();
    cl.push(SATSolver::mkLit(var, false));
    solver.addClause(cl);
  }

  Cnf_DataFree(cnf);
}

void BVExactEncoder::encode(SATSolver& solver, const ASTNode& term,
                            unsigned width,
                            const std::vector<unsigned>& aVars,
                            const std::vector<unsigned>& bVars,
                            const std::vector<unsigned>& resultVars,
                            const std::vector<signed char>& knownA,
                            const std::vector<signed char>& knownB)
{
  assert(aVars.size() >= width);
  assert(bVars.size() >= width);
  assert(resultVars.size() >= width);

  BBNodeManagerAIG mgr;
  mgr.nodeBudget = bm->UserFlags.aig_node_budget;
  SubstitutionMap sm(bm);
  Simplifier simp(bm, &sm);
  // No constant-bit propagation: its results belong to the blast that ran
  // over the whole query, and this one is a fragment of it. The multiplier
  // asks for them only through statsFound(), which answers no without it.
  //
  // And no abstraction: this circuit is what the refinement gave up in
  // favour of, so re-abstracting it would put the record straight back --
  // against an AIG thrown away at the end of this call, which nothing could
  // ever refine. Said to this blast rather than by clearing the manager's
  // flags around it, which let one blast see another's policy.
  BitBlaster bb(&mgr, &simp, bm->defaultNodeFactory, &bm->UserFlags, NULL,
                /*allowAbstraction=*/false);

  // The operand bits: a constant where the query's own blast had one, and a
  // combinational input everywhere else.
  //
  // The constants are what make this the encoding the query would have had.
  // Every constant shortcut in the operations reachable from here reads the
  // bit vector rather than the AST -- mult_normal skips a false multiplier
  // bit, Booth recoding classifies through convert(), and Aig_And folds a
  // constant argument structurally -- so an operand rebuilt entirely out of
  // free inputs gets none of them. A 64-bit multiply against a literal of
  // popcount 8 built 64 partial-product rows rather than 8: 33,968 clauses
  // where the unabstracted blast of the whole query was 12,380.
  //
  // Dropping the operand variable that a constant bit displaces is sound.
  // The abstraction reads its operands through proxy inputs that
  // ensureProxyCIs minted precisely because the vector was not all inputs,
  // and each of those proxies is tied to its bit by a side constraint -- so
  // the variable this circuit no longer mentions is already pinned to the
  // same constant that replaced it.
  //
  // `ciVars` therefore carries the solver variable of each input actually
  // created, in creation order, because that is the order the splice below
  // reads them back in -- their positions are their indices for the whole of
  // this function, which is what makes them findable after ABC has
  // renumbered every object in the manager.
  std::vector<unsigned> ciVars;
  ciVars.reserve(2 * width);

  const std::vector<signed char>* known[2] = {&knownA, &knownB};
  const std::vector<unsigned>* opVars[2] = {&aVars, &bVars};
  BBNodeVec operands[2] = {BBNodeVec(width), BBNodeVec(width)};

  for (unsigned op = 0; op < 2; op++)
    for (unsigned i = 0; i < width; i++)
    {
      const signed char bit = i < known[op]->size() ? (*known[op])[i] : -1;
      if (bit >= 0)
      {
        operands[op][i] = bit != 0 ? mgr.getTrue() : mgr.getFalse();
        continue;
      }
      operands[op][i] = BBNodeAIG(Aig_ObjCreateCi(mgr.aigMgr));
      operands[op][i].symbol_index = mgr.aigMgr->vCis->nSize - 1;
      ciVars.push_back((*opVars[op])[i]);
    }

  const BBNodeVec& x = operands[0];
  const BBNodeVec& y = operands[1];

  BBNodeSet support;
  const BBNodeVec result = bb.BBExactBinaryOp(term, x, y, support);
  assert(result.size() == width);

  // Outputs, then whatever the circuit wants conjoined to the top. Both are
  // combinational outputs and all of them are given CNF variables -- ABC's
  // generator asserts every output it is not asked to name, and it can only
  // be asked for all of them or none -- so the support is asserted below by
  // a unit clause over the variable it comes back with.
  for (unsigned i = 0; i < width; i++)
    Aig_ObjCreateCo(mgr.aigMgr, result[i].n);
  for (const BBNodeAIG& s : support)
    Aig_ObjCreateCo(mgr.aigMgr, s.n);

  const unsigned outputs = width + (unsigned)support.size();

  rewrite(mgr, bm->UserFlags.AIG_rewrites_iterations);
  assert(Aig_ManCheck(mgr.aigMgr));
  assert((unsigned)Aig_ManCoNum(mgr.aigMgr) == outputs);
  assert((unsigned)Aig_ManCiNum(mgr.aigMgr) == ciVars.size());

  // Use the query's selected CNF strategy. All outputs are named rather than
  // asserted because the splice below connects each result bit explicitly
  // and asserts only the side constraints.
  Cnf_Dat_t* cnf = ToCNFAIG(bm->UserFlags, /*allowAuto=*/false).derive_cnf(mgr, outputs);
  assert(cnf != NULL);

  // The splice. Every variable of the derived CNF becomes a variable of the
  // live solver: the inputs become the ones the operands are already
  // carried by, and everything else becomes a fresh one. Reusing the
  // operands' own variables rather than minting a copy and equating it is
  // the whole point -- the clauses have to talk about the bits the rest of
  // the query talks about.
  std::vector<unsigned> cnfToSolver(cnf->nVars, ~((unsigned)0));

  for (unsigned i = 0; i < ciVars.size(); i++)
  {
    const int var = cnf->pVarNums[Aig_ManCi(mgr.aigMgr, (int)i)->Id];
    // An input the circuit never reads is given no variable, and needs
    // none: nothing the CNF says mentions it.
    if (var < 0)
      continue;
    cnfToSolver[var] = ciVars[i];
  }

  for (int var = 0; var < cnf->nVars; var++)
    if (cnfToSolver[var] == ~((unsigned)0))
    {
      const unsigned fresh = solver.newVar();
      solver.setFrozen(fresh);
      cnfToSolver[var] = fresh;
    }

  SATSolver::vec_literals cl;
  for (int i = 0; i < cnf->nClauses; i++)
  {
    cl.clear();
    for (int *pLit = cnf->pClauses[i], *pStop = cnf->pClauses[i + 1];
         pLit < pStop; pLit++)
      cl.push(SATSolver::mkLit(cnfToSolver[(*pLit) >> 1], ((*pLit) & 1) != 0));
    solver.addClause(cl);
  }

  for (unsigned i = 0; i < outputs; i++)
  {
    const unsigned var =
        cnfToSolver[cnf->pVarNums[Aig_ManCo(mgr.aigMgr, (int)i)->Id]];
    if (i < width)
    {
      addEquiv(solver, resultVars[i], var);
      continue;
    }
    cl.clear();
    cl.push(SATSolver::mkLit(var, false));
    solver.addClause(cl);
  }

  Cnf_DataFree(cnf);
}

} // namespace stp
