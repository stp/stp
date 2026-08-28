/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: June, 2010
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

#ifndef TOSATAIG_H
#define TOSATAIG_H
#include <cmath>

#include "stp/AST/AST.h"
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/STPManager/STPManager.h"
#include "stp/ToSat/BBNodeManagerAIG.h"
#include "stp/ToSat/ToCNFAIG.h"
#include "stp/ToSat/BitBlaster.h"
#include "stp/ToSat/BVAbstractionRefiner.h"
#include "stp/Util/RunTimes.h"

namespace stp
{

class DLL_PUBLIC ToSATAIG : public ToSATBase
{
private:
  ASTNodeToSATVar nodeToSATVar;
  simplifier::constantBitP::ConstantBitPropagation* cb;

  ArrayTransformer* arrayTransformer;

  // don't assign or copy construct.
  ToSATAIG& operator=(const ToSATAIG& other);
  ToSATAIG(const ToSATAIG& other);

  // Minisat doesn't, but simplifying minisat and cryptominsat eliminate
  // variables during their
  // simplification phases. The problem is that we may later add clauses in that
  // refer to those
  // simplified-away variables. Here we mark them as frozen which prevents them
  // from being removed.
  void mark_variables_as_frozen(SATSolver& satSolver);
  // Advisory first-candidate bias for the congruence checker's scalars;
  // a no-op unless --uf-phase-hints is set.
  void suggest_uf_scalar_phases(SATSolver& satSolver);

  bool runSolver(SATSolver& satSolver);
  void handle_cnf_options(Cnf_Dat_t* cnfData, bool needAbsRef);

  // Resolve the injectivity guard to a SAT variable and decide how it is
  // held: assumed (and so retractable) on a backend that can assume, and
  // asserted as a unit otherwise. Called once, with the rest of the
  // freezing, so that every refinement round after it holds the same thing.
  void bind_injectivity_guard(SATSolver& satSolver);

  // The guard's variable and whether this query is still holding it. Lives
  // on the lowering rather than on the manager because retraction is a
  // property of one encoding, and the batch pipeline builds a fresh one per
  // query.
  STPMgr::InjectivityAssumption injectivity_;

  bool first;

  ToCNFAIG toCNF;

  // The abstractions this lowering minted, and the CEGAR loop that
  // refines them. Both live here for the batch pipeline's lifetime of one
  // query; the incremental driver keeps its own across a session.
  BVAbstractionRefiner abstraction_;
  // Whether this lowering may abstract at all; see the constructors.
  bool allowAbstraction_ = true;

  void init() { first = true; }

  static THREAD_LOCAL_IE int cnf_calls;

public:
  void add_cnf_to_solver(SATSolver& satSolver, Cnf_Dat_t* cnfData);

  // Blast `input` and convert it to CNF. Returns NULL, having freed the AIG
  // and the constant-bit propagator, when UserFlags::aig_node_budget is set
  // and the blast exceeds it -- there is no CNF in that case, and the caller
  // must abandon the query rather than treat the absence as unsatisfiable.
  Cnf_Dat_t* bitblast(const ASTNode& input, bool needAbsRef);
  void release_cnf_memory(Cnf_Dat_t* cnfData);

  bool cbIsDestructed() { return cb == NULL; }

  // `allowAbstraction` is false for a lowering whose query must be encoded
  // exactly whatever the session's flags say -- the same argument BitBlaster
  // takes, reaching it from here so that a caller does not have to clear the
  // manager's flags and put them back.
  //
  // maxPrecision is the one such caller: it drives this class over auxiliary
  // queries a few bits wide, which gain nothing from abstracting, and its
  // result handling reads the SOLVER_UNDECIDED a refinement round returns as
  // an error from the backend. It used to save the two feature flags, clear
  // them and restore them around its loop, which is a manager-wide write for
  // a decision belonging to one encoding, invisible to anything else sharing
  // the manager, and undone only on the paths that reach the bottom of the
  // function.
  ToSATAIG(STPMgr* bm, ArrayTransformer* at, bool allowAbstraction = true)
      : ToSATBase(bm), toCNF(bm->UserFlags), abstraction_(bm),
        allowAbstraction_(allowAbstraction)
  {
    cb = NULL;
    init();
    arrayTransformer = at;
  }

  ToSATAIG(STPMgr* bm, simplifier::constantBitP::ConstantBitPropagation* cb_,
           ArrayTransformer* at, bool allowAbstraction = true)
      : ToSATBase(bm), cb(cb_), toCNF(bm->UserFlags), abstraction_(bm),
        allowAbstraction_(allowAbstraction)
  {
    init();
    arrayTransformer = at;
  }

  ~ToSATAIG();

  void ClearAllTables() override { nodeToSATVar.clear(); }

  // Used to read out the satisfiable answer.
  ASTNodeToSATVar& SATVar_to_SymbolIndexMap() override { return nodeToSATVar; }

  bool CallSAT(SATSolver& satSolver, const ASTNode& input,
               bool needAbsRef) override;

  bool hasBVEQAbstractions() const { return abstraction_.hasEqualities(); }
  bool hasBVTermAbstractions() const { return abstraction_.hasTerms(); }

  // Test-only inspection: the term records this lowering filed. The invariant
  // under test is that each carries its own result variables rather than
  // relying on the AST-keyed registry, which holds one vector per node and so
  // can name only the newest result registered for it. Nothing observable
  // changes while canonical reuse holds, which is why it needs pinning here
  // rather than by a query that would answer the same either way.
  const std::vector<BVTermAbstraction>& termRecordsForTesting() const
  {
    return abstraction_.terms();
  }

  AbstractionRefinementResult
  refineAbstractions(SATSolver& solver) override;
  uint64_t abstractionRefinements() const override
  {
    return abstraction_.refinements();
  }
};
}

#endif
