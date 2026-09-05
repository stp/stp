/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
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

#ifndef STP_H
#define STP_H

#include "stp/AST/AST.h"
#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/FloatBlaster/FpEncodingContext.h"
#include "stp/Parser/LetMgr.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/BVSolver.h"
#include "stp/Simplifier/PropagateEqualities.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Util/Attributes.h"
#include "stp/ToSat/ToSATAIG.h"
#include "stp/Simplifier/NodeDomainAnalysis.h"
#include <memory>

namespace stp
{
class IncrementalSolver;
class LoweredApplicationView;
class UFBatchAdapter;

// FIXME: This needs a better name
class STP
{

  // Whether the skeleton has already been asked about this query.
  //
  // sizeReducing runs to a fixpoint, and asking again is both wasted and
  // pointless: the facts from the first pass are top-level conjuncts by
  // then, so the second pass rediscovers exactly them at the cost of
  // another SAT call over the whole propositional structure.
  bool skeletonAsked = false;

  ASTNode sizeReducing(ASTNode input, BVSolver* bvSolver,
                       PropagateEqualities* pe, NodeDomainAnalysis* domain);

  // A copy of all the state we need to restore to a prior expression.
  struct Revert_to
  {
    ASTNodeMap initialSolverMap; // Map from variables to expressions they were
                                 // replaced with.
    ASTNode toRevertTo;          // The original expression.
    ArrayTransformer::ArrType
        backup_arrayToIndexToRead; // array-indices already removed.
  };

  // Accepts query and returns the answer. if query is valid,
  // returns VALID, else returns INVALID. Automatically constructs
  // counterexample for invalid queries, and prints them upon
  // request.
  SOLVER_RETURN_TYPE TopLevelSTPAux(SATSolver& NewSolver,
                                    const ASTNode& modified_input,
                                    const ASTNodeMap& arrayEqualityRewrites);

  SOLVER_RETURN_TYPE solve_by_sat_solver(SATSolver* newS,
                                         ASTNode original_input,
                                         const ASTNodeMap&
                                             arrayEqualityRewrites);

  SATSolver* get_new_sat_solver();

  // The source-to-carrier mapping for the most recent solve. It remains
  // alive after TopLevelSTP returns so model queries use that exact encoding.
  std::unique_ptr<FpEncodingContext> fpEncodingContext;

  // Public and semantic UF roots for the most recent fresh-query solve. The
  // value remains alive with the model, while batchUFAdapter owns the
  // query-local SAT/checker mutation.
  std::unique_ptr<LoweredApplicationView> batchUFView;
  std::unique_ptr<UFBatchAdapter> batchUFAdapter;
  uint64_t batchUFScopeGeneration = 0;

public:
  STPMgr* bm;
  Simplifier* simp;
  ToSATBase* tosat;
  AbsRefine_CounterExample* Ctr_Example;
  ArrayTransformer* arrayTransformer;
  SubstitutionMap* substitutionMap;

  // The incremental driver (docs/incremental-solving.rst), created on first
  // use and destroyed by reset/reset-assertions. NULL while no incremental
  // session is active; the batch pipeline never touches it.
  IncrementalSolver* incrementalSolver = nullptr;

  // The C API's engagement bookkeeping, mirroring the SMT-LIB2 frontend's:
  // the driver engages from the second solve of a session (the first,
  // largest all-new formula gets the batch pipeline's whole-formula
  // simplification), unless vc_setFlags 'i' asked for it from the start.
  // The SMT-LIB2 frontend keeps its own copies in Cpp_interface.
  bool incrementalFromStart = false;
  // Session state, turned on by the first vc_push unless the caller asked for
  // IncrementalMode::OFF. Separate from UserFlags.incremental_mode, which
  // stays the caller's request.
  bool sessionIncremental = false;
  size_t incrementalSolvesRun = 0;

  // Whether a query has been decided and its counterexample tables have not
  // been discarded since -- that is, whether there is a model to read at all.
  //
  // The C API's contract in as much state as it needs: a counterexample
  // describes the last query, survives vc_pop, and is discarded by the next
  // vc_push or vc_query. ClearAllTables is where that discarding happens, so
  // that is where this is cleared; vc_query_with_timeout sets it again when
  // the query comes back decided, and leaves it clear when the answer was a
  // unknown or an error, because neither leaves a model behind.
  //
  // The SMT-LIB2 frontend has always kept the equivalent (model_valid) and
  // answers "unsupported" without it. Nothing on the C API side did, so a
  // model query with no solve behind it read an empty counterexample map
  // instead of being refused.
  bool queryAnswered = false;

  DLL_PUBLIC IncrementalSolver* getIncrementalSolver();
  DLL_PUBLIC void resetIncrementalSolver();
  bool hasIncrementalSolver() const { return incrementalSolver != nullptr; }

public:
  // Out of line so the UF implementation types above remain incomplete here.
  DLL_PUBLIC STP(STPMgr* b);

  STP(const STP&) = delete;
  STP& operator=(const STP&) = delete;

  DLL_PUBLIC ~STP();

  // NB doesn't delete the STPMgr.
  void deleteObjects()
  {
    resetIncrementalSolver();

    if (Ctr_Example != NULL)
    {
      Ctr_Example->setFpEncodingContext(NULL);
      Ctr_Example->setUFTheoryAdapter(NULL);
    }
    fpEncodingContext.reset();

    delete Ctr_Example;
    Ctr_Example = NULL;

    delete arrayTransformer;
    arrayTransformer = NULL;

    delete tosat;
    tosat = NULL;

    delete simp;
    simp = NULL;

    delete substitutionMap;
    substitutionMap = NULL;
  }

  // The absolute TopLevel function that invokes STP on the input
  // formula
  // One run of the pipeline: lower, preprocess, bit-blast, solve, refine.
  // TopLevelSTP calls it a second time when the first run reached an unsat
  // nobody could attribute -- see the comment there.
  SOLVER_RETURN_TYPE topLevelSTPOnce(const ASTNode& inputasserts,
                                     const ASTNode& query);

  DLL_PUBLIC SOLVER_RETURN_TYPE TopLevelSTP(const ASTNode& inputasserts,
                                            const ASTNode& query);

  // calls sizeReducing and the bitblasting simplification.
  ASTNode callSizeReducing(ASTNode simplified_solved_InputToSAT,
                           BVSolver* bvSolver, PropagateEqualities* pe, NodeDomainAnalysis* domain);

  DLL_PUBLIC void ClearAllTables(void);
};
} // end of namespace
#endif
