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

// The abstraction, off for the length of one encoding.
//
// The blast below runs the ordinary BitBlaster, and the ordinary BitBlaster
// abstracts every wide multiplication it is handed. Left on, the circuit
// this is here to build would come back as another set of free bits and
// another record -- and the record would be minted against an AIG that is
// thrown away at the end of this function, so nothing could ever refine it.
// The refinement that reaches this point has already decided the
// abstraction is not paying; this is the encoding it decided in favour of.
struct AbstractionOff
{
  UserDefinedFlags& uf;
  const bool term;
  const bool eq;

  explicit AbstractionOff(UserDefinedFlags& uf_)
      : uf(uf_), term(uf_.bv_term_abstraction), eq(uf_.bv_eq_abstraction)
  {
    uf.bv_term_abstraction = false;
    uf.bv_eq_abstraction = false;
  }

  ~AbstractionOff()
  {
    uf.bv_term_abstraction = term;
    uf.bv_eq_abstraction = eq;
  }
};

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

void BVExactEncoder::encode(SATSolver& solver, const ASTNode& term,
                            unsigned width,
                            const std::vector<unsigned>& aVars,
                            const std::vector<unsigned>& bVars,
                            const std::vector<unsigned>& resultVars)
{
  assert(aVars.size() >= width);
  assert(bVars.size() >= width);
  assert(resultVars.size() >= width);

  AbstractionOff scope(bm->UserFlags);

  BBNodeManagerAIG mgr;
  mgr.nodeBudget = bm->UserFlags.aig_node_budget;
  SubstitutionMap sm(bm);
  Simplifier simp(bm, &sm);
  // No constant-bit propagation: its results belong to the blast that ran
  // over the whole query, and this one is a fragment of it. The multiplier
  // asks for them only through statsFound(), which answers no without it.
  BitBlaster bb(&mgr, &simp, bm->defaultNodeFactory, &bm->UserFlags);

  // The operand bits, as combinational inputs, in the order the splice
  // below reads them back: the first operand's `width` bits, then the
  // second's. Nothing else creates an input, so their positions are their
  // indices for the whole of this function -- which is what makes them
  // findable after ABC has renumbered every object in the manager.
  BBNodeVec x(width), y(width);
  for (unsigned i = 0; i < width; i++)
  {
    x[i] = BBNodeAIG(Aig_ObjCreateCi(mgr.aigMgr));
    x[i].symbol_index = mgr.aigMgr->vCis->nSize - 1;
  }
  for (unsigned i = 0; i < width; i++)
  {
    y[i] = BBNodeAIG(Aig_ObjCreateCi(mgr.aigMgr));
    y[i].symbol_index = mgr.aigMgr->vCis->nSize - 1;
  }

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
  assert((unsigned)Aig_ManCiNum(mgr.aigMgr) == 2 * width);

  // Use the query's selected CNF strategy. All outputs are named rather than
  // asserted because the splice below connects each result bit explicitly
  // and asserts only the side constraints.
  Cnf_Dat_t* cnf = ToCNFAIG(bm->UserFlags).derive_cnf(mgr, outputs);
  assert(cnf != NULL);

  // The splice. Every variable of the derived CNF becomes a variable of the
  // live solver: the inputs become the ones the operands are already
  // carried by, and everything else becomes a fresh one. Reusing the
  // operands' own variables rather than minting a copy and equating it is
  // the whole point -- the clauses have to talk about the bits the rest of
  // the query talks about.
  std::vector<unsigned> cnfToSolver(cnf->nVars, ~((unsigned)0));

  for (unsigned i = 0; i < 2 * width; i++)
  {
    const int var = cnf->pVarNums[Aig_ManCi(mgr.aigMgr, (int)i)->Id];
    // An input the circuit never reads is given no variable, and needs
    // none: nothing the CNF says mentions it.
    if (var < 0)
      continue;
    cnfToSolver[var] = (i < width) ? aVars[i] : bVars[i - width];
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
