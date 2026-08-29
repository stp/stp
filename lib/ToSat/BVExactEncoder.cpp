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
#include <limits>

namespace stp
{

BVExactEncoder::BVExactEncoder(STPMgr* bm_)
    : bm(bm_), substitutions_(new SubstitutionMap(bm_)),
      scratch_(new Simplifier(bm_, substitutions_.get()))
{
}

BVExactEncoder::~BVExactEncoder() = default;

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

  ensureDarLibrary();
  Dar_RwrPar_t Pars;
  Dar_ManDefaultRwrParams(&Pars);

  for (int64_t i = 0; i < iterations; i++)
  {
    const int before = mgr.totalNumberOfNodes();

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

    if (before == mgr.totalNumberOfNodes())
      break;
  }
}

} // namespace


namespace
{

// Blast one theorem, splice the resulting CNF onto its live SAT vectors, and
// assert it. Most facts have two operands and one abstract result; paired
// DIV/REM recomposition has four vectors. The delicate CI/CNF variable
// mapping belongs in one arity-independent place.
template <typename BuildClaim>
void encodeNaryLemma(
    STPMgr* bm, Simplifier* scratch, SATSolver& solver, unsigned width,
    const std::vector<const std::vector<unsigned>*>& liveVars,
    BuildClaim buildClaim)
{
  assert(!liveVars.empty());
  for ([[maybe_unused]] const std::vector<unsigned>* vars : liveVars)
  {
    assert(vars != NULL);
    assert(vars->size() >= width);
  }

  BBNodeManagerAIG mgr;
  mgr.nodeBudget = bm->UserFlags.aig_node_budget;
  // Nothing this blast produces may itself be abstracted: the record would
  // be minted against an AIG thrown away when this returns, so nothing could
  // ever refine it.
  BitBlaster bb(&mgr, scratch, bm->defaultNodeFactory, &bm->UserFlags, NULL,
                /*allowAbstraction=*/false);

  // Every live vector is an input here. Abstract results are not circuit
  // outputs: the theorem constrains them without defining the operations.
  std::vector<BBNodeVec> inputs(liveVars.size(), BBNodeVec(width));
  for (unsigned v = 0; v < inputs.size(); ++v)
    for (unsigned i = 0; i < width; i++)
    {
      inputs[v][i] = mgr.CreateFreshInput();
    }

  BBNodeSet support;
  const BBNodeAIG claim = buildClaim(bb, inputs, support);

  Aig_ObjCreateCo(mgr.aigMgr, claim.n);
  for (const BBNodeAIG& c : support)
    Aig_ObjCreateCo(mgr.aigMgr, c.n);

  const unsigned outputs = 1 + (unsigned)support.size();

  rewrite(mgr, bm->UserFlags.AIG_rewrites_iterations);
  assert(Aig_ManCheck(mgr.aigMgr));
  assert((unsigned)Aig_ManCoNum(mgr.aigMgr) == outputs);
  // The splice below finds the live vectors' inputs by position, so the claim
  // must not have created an input of its own. None of the lemma builders
  // can -- only BBTerm and BBForm mint symbols, and nothing here calls them
  // -- and if one ever did, the extra input would take a fresh unconstrained
  // solver variable and quietly weaken the lemma to something the candidate
  // satisfies. `encode` has always checked this; the lemma path had not.
  assert((unsigned)Aig_ManCiNum(mgr.aigMgr) == liveVars.size() * width);

  // No AUTO, for the reason ToCNFAIG.h gives about the exact splice below:
  // AUTO was calibrated on whole-query conversion, where the CNF is built once
  // and thrown away, so trading clauses for generation time costs nothing.
  // These clauses go into a live solver and stay there for the rest of the
  // search. The paired DIV/REM identity is a full-width multiplier, which is
  // exactly the circuit that argument is about. An explicitly chosen level
  // still reaches here.
  Cnf_Dat_t* cnf =
      ToCNFAIG(bm->UserFlags, /*allowAuto=*/false).derive_cnf(mgr, outputs);
  assert(cnf != NULL);

  std::vector<unsigned> cnfToSolver(cnf->nVars, ~((unsigned)0));
  for (unsigned i = 0; i < liveVars.size() * width; ++i)
  {
    const int var = cnf->pVarNums[mgr.ciObjectId((int)i)];
    if (var < 0)
      continue;
    cnfToSolver[var] = (*liveVars[i / width])[i % width];
  }

  // From 1: every ABC CNF generator numbers variables from 1 and reports
  // nVars as one past the last, so index 0 names nothing. Allocating a solver
  // variable for it, and freezing it, left one unreachable variable in the
  // live solver per splice. The assertion in the clause loop below is what
  // holds this: a literal over variable 0 would mean a generator numbered
  // from 0 after all.
  for (int var = 1; var < cnf->nVars; var++)
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
    {
      assert(((*pLit) >> 1) != 0 && "a CNF generator numbered variables from 0");
      cl.push(SATSolver::mkLit(cnfToSolver[(*pLit) >> 1], ((*pLit) & 1) != 0));
    }
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

template <typename BuildClaim>
void encodeTernaryLemma(STPMgr* bm, Simplifier* scratch, SATSolver& solver,
                        unsigned width, const std::vector<unsigned>& xVars,
                        const std::vector<unsigned>& sVars,
                        const std::vector<unsigned>& tVars,
                        BuildClaim buildClaim)
{
  std::vector<const std::vector<unsigned>*> liveVars;
  liveVars.push_back(&xVars);
  liveVars.push_back(&sVars);
  liveVars.push_back(&tVars);
  encodeNaryLemma(
      bm, scratch, solver, width, liveVars,
      [&buildClaim](BitBlaster& bb, const std::vector<BBNodeVec>& inputs,
                    BBNodeSet& support) {
        return buildClaim(bb, inputs[0], inputs[1], inputs[2], support);
      });
}

} // namespace

void BVExactEncoder::encodeDivLemma(SATSolver& solver, DivLemma lemma,
                                    unsigned width,
                                    const std::vector<unsigned>& dividendVars,
                                    const std::vector<unsigned>& divisorVars,
                                    const std::vector<unsigned>& resultVars)
{
  encodeTernaryLemma(
      bm, scratch_.get(), solver, width, dividendVars, divisorVars, resultVars,
      [lemma](BitBlaster& bb, const BBNodeVec& x, const BBNodeVec& s,
              const BBNodeVec& t, BBNodeSet& support) {
        return bb.BBDivLemma(lemma, x, s, t, support);
      });
}

void BVExactEncoder::encodeRemLemma(SATSolver& solver, RemLemma lemma,
                                    unsigned width,
                                    const std::vector<unsigned>& dividendVars,
                                    const std::vector<unsigned>& divisorVars,
                                    const std::vector<unsigned>& resultVars)
{
  encodeTernaryLemma(
      bm, scratch_.get(), solver, width, dividendVars, divisorVars, resultVars,
      [lemma](BitBlaster& bb, const BBNodeVec& x, const BBNodeVec& s,
              const BBNodeVec& t, BBNodeSet& support) {
        return bb.BBRemLemma(lemma, x, s, t, support);
      });
}

void BVExactEncoder::encodeMulLemma(SATSolver& solver, MulLemma lemma,
                                    unsigned width,
                                    const std::vector<unsigned>& xVars,
                                    const std::vector<unsigned>& sVars,
                                    const std::vector<unsigned>& resultVars)
{
  encodeTernaryLemma(
      bm, scratch_.get(), solver, width, xVars, sVars, resultVars,
      [lemma](BitBlaster& bb, const BBNodeVec& x, const BBNodeVec& s,
              const BBNodeVec& t, BBNodeSet& support) {
        return bb.BBMulLemma(lemma, x, s, t, support);
      });
}

void BVExactEncoder::encodeAddLemma(SATSolver& solver, AddLemma lemma,
                                    unsigned width,
                                    const std::vector<unsigned>& xVars,
                                    const std::vector<unsigned>& sVars,
                                    const std::vector<unsigned>& resultVars)
{
  encodeTernaryLemma(
      bm, scratch_.get(), solver, width, xVars, sVars, resultVars,
      [lemma](BitBlaster& bb, const BBNodeVec& x, const BBNodeVec& s,
              const BBNodeVec& t, BBNodeSet& support) {
        return bb.BBAddLemma(lemma, x, s, t, support);
      });
}

void BVExactEncoder::encodeDivRemIdentity(
    SATSolver& solver, const ASTNode& product, unsigned width,
    const std::vector<unsigned>& dividendVars,
    const std::vector<unsigned>& divisorVars,
    const std::vector<unsigned>& quotientVars,
    const std::vector<unsigned>& remainderVars)
{
  std::vector<const std::vector<unsigned>*> liveVars;
  liveVars.push_back(&dividendVars);
  liveVars.push_back(&divisorVars);
  liveVars.push_back(&quotientVars);
  liveVars.push_back(&remainderVars);
  encodeNaryLemma(
      bm, scratch_.get(), solver, width, liveVars,
      [&product](BitBlaster& bb, const std::vector<BBNodeVec>& inputs,
                 BBNodeSet& support) {
        return bb.BBDivRemIdentity(product, inputs[0], inputs[1], inputs[2],
                                   inputs[3], support);
      });
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
  // No constant-bit propagation: its results belong to the blast that ran
  // over the whole query, and this one is a fragment of it. The multiplier
  // asks for them only through statsFound(), which answers no without it.
  // And no abstraction: this circuit is what the refinement gave up in
  // favour of, so re-abstracting it would put the record straight back.
  BitBlaster bb(&mgr, scratch_.get(), bm->defaultNodeFactory, &bm->UserFlags, NULL,
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
  // popcount 8 built 64 partial-product rows rather than 8.
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
      operands[op][i] = mgr.CreateFreshInput();
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
    const int var = cnf->pVarNums[mgr.ciObjectId((int)i)];
    // An input the circuit never reads is given no variable, and needs
    // none: nothing the CNF says mentions it.
    if (var < 0)
      continue;
    cnfToSolver[var] = ciVars[i];
  }

  // From 1: every ABC CNF generator numbers variables from 1 and reports
  // nVars as one past the last, so index 0 names nothing. Allocating a solver
  // variable for it, and freezing it, left one unreachable variable in the
  // live solver per splice. The assertion in the clause loop below is what
  // holds this: a literal over variable 0 would mean a generator numbered
  // from 0 after all.
  for (int var = 1; var < cnf->nVars; var++)
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
    {
      assert(((*pLit) >> 1) != 0 && "a CNF generator numbered variables from 0");
      cl.push(SATSolver::mkLit(cnfToSolver[(*pLit) >> 1], ((*pLit) & 1) != 0));
    }
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
