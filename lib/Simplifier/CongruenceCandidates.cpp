/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: September, 2026
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

#include "stp/Simplifier/CongruenceCandidates.h"
#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/Sat/SATSolverFactory.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/ToSat/ToSATAIG.h"
#include "stp/Util/DagWalk.h"

#include <algorithm>
#include <memory>
#include <unordered_set>

namespace stp
{

// Merging the operands of these shares a circuit rather than wiring, so a
// sub-solve spent on one of them buys the most. An extract or a concat of
// the same operand costs nothing to duplicate, and a pairing under one is
// not worth the budget it would take.
bool CongruenceCandidates::worthMerging(Kind k)
{
  switch (k)
  {
    case BVDIV:
    case BVMOD:
    case SBVDIV:
    case SBVREM:
    case SBVMOD:
    case BVMULT:
    case BVPLUS:
    case BVSUB:
    case BVLEFTSHIFT:
    case BVRIGHTSHIFT:
    case BVSRSHIFT:
      return true;
    default:
      return false;
  }
}

void CongruenceCandidates::collect(const ASTNode& n)
{
  walkPreOrder(n, [&](const ASTNode& current) {
    if (current.Degree() < 2)
      return current.Degree() > 0;

    if (!worthMerging(current.GetKind()))
      return true;

    for (unsigned i = 0; i < current.Degree(); i++)
    {
      const ASTNode& operand = current[i];

      // A constant is already whatever it is: two of them in one slot are
      // either the same node or provably different, and neither is worth a
      // sub-solve.
      if (operand.GetKind() == BVCONST || operand.GetType() != BITVECTOR_TYPE)
        continue;

      std::vector<uint64_t> others;
      others.reserve(current.Degree() - 1);
      for (unsigned j = 0; j < current.Degree(); j++)
        if (j != i)
          others.push_back(current[j].GetNodeNum());

      // The factory sorts a commutative operator's children, so which
      // position a term ends up in is decided by its node number rather
      // than by the query. Keying on the position as well would put
      // bvadd(X, c) and bvadd(c, Y) in different slots and miss the
      // pairing they are: what identifies the slot is the operator and
      // what else is in it.
      const unsigned position = isCommutative(current.GetKind()) ? 0 : i;

      std::vector<ASTNode>& here =
          slots[{{current.GetKind(), position}, others}];

      bool seen = false;
      for (const ASTNode& already : here)
        if (already == operand)
        {
          seen = true;
          break;
        }

      if (!seen)
        here.push_back(operand);
    }

    return true;
  });
}

// The equality as its own query. Everything here is local to the call: the
// substitution map, the simplifier, the array transformer and the SAT
// solver all go out of scope with it, so nothing the main solve is holding
// is disturbed. Abstraction is declined for the same reason maxPrecision
// declines it -- a refinement round answers SOLVER_UNDECIDED, which here
// would be read as "not proved" and throw away a theorem.
bool CongruenceCandidates::proves(const ASTNode& equality)
{
  SubstitutionMap substitutions(bm);
  Simplifier simplifier(bm, &substitutions);

  // Simplified before it is blasted, on its own substitution map, so that
  // nothing here reaches the main query's. What arrives is two terms the
  // factory has already normalised as far as it normalises anything, and
  // what the rewriter adds on top of that is what decides whether the
  // proof is a few hundred conflicts or a few hundred thousand: unsimplified
  // it is two full circuits and a comparison.
  const ASTNode query =
      simplifier.SimplifyFormula_TopLevel(nf->CreateNode(NOT, equality), false);

  if (query == bm->ASTFalse)
    return true; // the rewriter settled it: no solver needed
  if (query == bm->ASTTrue)
    return false;

  ArrayTransformer transformer(bm, &simplifier);
  AbsRefine_CounterExample counterExample(bm, &simplifier, &transformer);

  std::unique_ptr<SATSolver> solver(createSATSolver(bm->UserFlags));
  if (solver == NULL)
    return false;

  if (conflictBudget >= 0)
    solver->setMaxConflicts(conflictBudget);

  ToSATAIG tosat(bm, &transformer, /*allowAbstraction=*/false);

  // Everything the manager records about a solve that gave up belongs to the
  // solve that gave up. A candidate is allowed to run out of conflicts --
  // that is what the budget is for -- and the flag and reason it raises on
  // its way out would otherwise be read by the main query as its own, which
  // turns a query STP can answer into an unknown. The current query is
  // manager-wide for the same reason: the C interface reads it back.
  const ASTNode savedQuery = bm->GetQuery();
  const bool savedExpired = bm->soft_timeout_expired;
  const UnknownReason savedReason = bm->getUnknownReason();
  const std::string savedDetail = bm->getUnknownReasonDetail();

  bm->SetQuery(bm->ASTUndefined);

  const SOLVER_RETURN_TYPE result = counterExample.CallSAT_ResultCheck(
      *solver, query, query, query, &tosat, false);

  bm->SetQuery(savedQuery);
  bm->soft_timeout_expired = savedExpired;
  bm->clearUnknown();
  if (savedReason != UnknownReason::None)
    bm->noteUnknown(savedReason, savedDetail);

  return result == SOLVER_VALID;
}

ASTVec CongruenceCandidates::derive(const ASTNode& input)
{
  bm->GetRunTimes()->start(RunTimes::CongruenceCandidates);

  proposed = 0;
  tested = 0;
  proved = 0;

  ASTVec found;

  collect(input);

  // Every pairing the slots offer, with the cheapest slots first: a slot
  // holding two terms is one sub-solve, where one holding ten is
  // forty-five, and spending the budget on the narrow slots settles more
  // of them.
  std::vector<std::pair<ASTNode, ASTNode>> candidates;
  std::vector<const std::vector<ASTNode>*> ordered;
  ordered.reserve(slots.size());
  for (const auto& slot : slots)
    if (slot.second.size() > 1)
      ordered.push_back(&slot.second);

  std::stable_sort(ordered.begin(), ordered.end(),
                   [](const std::vector<ASTNode>* a,
                      const std::vector<ASTNode>* b) {
                     return a->size() < b->size();
                   });

  for (const std::vector<ASTNode>* slot : ordered)
    for (size_t i = 0; i < slot->size(); i++)
      for (size_t j = i + 1; j < slot->size(); j++)
      {
        const ASTNode& a = (*slot)[i];
        const ASTNode& b = (*slot)[j];

        // The same slot can hold operands of different widths: a concat
        // says nothing about how its pieces divide up.
        if (a.GetValueWidth() != b.GetValueWidth())
          continue;

        // Merging two symbols removes no circuit -- there was none to
        // remove. What pays is a composite collapsing, whether onto
        // another composite or onto a symbol.
        if (a.Degree() == 0 && b.Degree() == 0)
          continue;

        candidates.push_back({a, b});
      }

  proposed = candidates.size();

  // A pair is the same question whichever application produced it.
  std::unordered_set<uint64_t> asked;

  for (const auto& candidate : candidates)
  {
    if (tested >= candidateLimit)
      break;

    if (bm->soft_timeout_expired)
      break;

    const ASTNode equality =
        nf->CreateNode(EQ, candidate.first, candidate.second);

    // Settled by the factory on its way in: a pair it already made equal
    // needs no proof, and a pair it already refuted admits none.
    if (equality == bm->ASTTrue || equality == bm->ASTFalse)
      continue;
    if (!asked.insert(equality.GetNodeNum()).second)
      continue;

    tested++;
    if (proves(equality))
    {
      proved++;
      found.push_back(equality);
    }
  }

  if (bm->UserFlags.stats_flag)
    std::cerr << "{CongruenceCandidates} proposed:" << proposed
              << " tested:" << tested << " proved:" << proved << std::endl;

  slots.clear();

  bm->GetRunTimes()->stop(RunTimes::CongruenceCandidates);
  return found;
}
}
