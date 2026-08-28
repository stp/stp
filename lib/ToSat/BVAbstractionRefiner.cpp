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

#include "stp/ToSat/BVAbstractionRefiner.h"
#include "stp/ToSat/BBNodeManagerAIG.h"
#include "stp/ToSat/BVEQCongruenceClosure.h"
#include "stp/ToSat/BVExactEncoder.h"
#include "stp/Simplifier/Simplifier.h"

#include <algorithm>
#include <chrono>
#include <iostream>
#include <limits>
#include <set>
#include <unordered_map>
#include <unordered_set>

namespace stp
{

// The solver's totals before one schema install, so that the site which
// counts the lemma also charges what it cost.
//
// One lemma is not one price. The hand-written bounds are a comparison chain,
// the exact prefixes are three columns of a multiplier, and a registry fact
// like UDIV15 is three barrel shifters spliced through BVExactEncoder --
// 229,374 clauses at 256 bits for that one fact. A profile is a choice of
// which schema families to enable, so the lemma count alone cannot answer the
// question the profiles exist to ask.
struct SchemaInstallCost
{
  uint64_t clauses;
  uint32_t variables;
  std::chrono::steady_clock::time_point started;

  explicit SchemaInstallCost(SATSolver& solver)
      : clauses(solver.submittedClauses()), variables(solver.nVars()),
        started(std::chrono::steady_clock::now())
  {
  }
};

// Count a schema lemma without charging it, for the one whose cost belongs in
// another bucket: the paired DIV/REM identity builds a full-width multiplier
// and is measured as the full-width install it is.
static void countFullWidthSchemaLemma(UserDefinedFlags& flags,
                                      BVSchemaGroup group)
{
  const unsigned index = static_cast<unsigned>(group);
  assert(index < BV_SCHEMA_GROUP_COUNT);
  flags.coverage.bv_schema_lemmas++;
  flags.coverage.bv_schema_group_lemmas[index]++;
}

// Count a schema lemma and charge what installing it cost, on the terms the
// full-width installs are measured on: the backend's own totals across the
// install, and the wall clock spent building it. Taking the count and the
// price in one call is what keeps a family from being counted without its
// cost, which is how the registry splices came to report nothing at all.
static void countSchemaLemma(UserDefinedFlags& flags, BVSchemaGroup group,
                             SATSolver& solver,
                             const SchemaInstallCost& before)
{
  countFullWidthSchemaLemma(flags, group);
  flags.coverage.bv_schema_clauses +=
      solver.submittedClauses() - before.clauses;
  flags.coverage.bv_schema_variables += solver.nVars() - before.variables;
  flags.coverage.bv_schema_microseconds += static_cast<uint64_t>(
      std::chrono::duration_cast<std::chrono::microseconds>(
          std::chrono::steady_clock::now() - before.started)
          .count());
}

// Both families in one call, equalities first: theirs is the cheaper scan,
// and the congruence phase inside it can refute a candidate at word level
// without reading a single bit. A round that refined an equality stops
// there rather than going on to the terms -- the term scan reads the same
// model, and what it would find in it has already been ruled out.
// Run an optional schema splice that builds a circuit, and say whether the
// AIG node budget let it through.
//
// An algebraic fact or the paired DIV/REM identity is only a strengthening,
// so refusal disables that schema and falls through to the ordinary record
// path. The mandatory exact backstop deliberately does not use this helper:
// once its bounded value allowance is spent, refusal is Unknown rather than
// an unbounded value-pair enumeration.
//
// Nothing partial reaches the solver: the budget is checked as AIG nodes are
// created, which is before any CNF is derived and before a single clause is
// submitted.
template <typename Splice>
static bool spliceWithinBudget(STPMgr* bm, const char* what, Splice splice)
{
  try
  {
    splice();
    return true;
  }
  catch (const AIGBudgetExhausted& e)
  {
    if (bm->UserFlags.stats_flag)
      std::cerr << "BV abstraction: the AIG node budget refused " << what
                << " at " << e.nodeCount << " nodes; refining without it"
                << std::endl;
    return false;
  }
}

static size_t selectedSize(size_t all,
                           const std::vector<size_t>* selected)
{
  return selected == NULL ? all : selected->size();
}

static size_t selectedIndex(size_t position,
                            const std::vector<size_t>* selected)
{
  return selected == NULL ? position : (*selected)[position];
}

void BVAbstractionRefiner::rebuildRecordIndex()
{
  recordOfId_.clear();
  for (size_t i = 0; i < eqs_.size(); ++i)
  {
    if (!eqs_[i].id.valid())
      continue;
    [[maybe_unused]] const bool inserted =
        recordOfId_.insert({eqs_[i].id, {true, i}}).second;
    assert(inserted && "two BV abstraction records share one producer ID");
  }
  for (size_t i = 0; i < terms_.size(); ++i)
  {
    if (!terms_[i].id.valid())
      continue;
    [[maybe_unused]] const bool inserted =
        recordOfId_.insert({terms_[i].id, {false, i}}).second;
    assert(inserted && "two BV abstraction records share one producer ID");
  }
  indexedRecords_ = eqs_.size() + terms_.size();
}

void BVAbstractionRefiner::appendEquality(BVEQAbstraction record)
{
  assert(record.id.valid());
  if (indexedRecords_ != eqs_.size() + terms_.size())
    rebuildRecordIndex();
  const size_t index = eqs_.size();
  [[maybe_unused]] const bool inserted =
      recordOfId_.insert({record.id, {true, index}}).second;
  assert(inserted && "two BV abstraction records share one producer ID");
  eqs_.push_back(std::move(record));
  ++indexedRecords_;
}

void BVAbstractionRefiner::appendTerm(BVTermAbstraction record)
{
  assert(record.id.valid());
  if (indexedRecords_ != eqs_.size() + terms_.size())
    rebuildRecordIndex();
  const size_t index = terms_.size();
  [[maybe_unused]] const bool inserted =
      recordOfId_.insert({record.id, {false, index}}).second;
  assert(inserted && "two BV abstraction records share one producer ID");
  terms_.push_back(std::move(record));
  ++indexedRecords_;
}

BVAbstractionScope BVAbstractionRefiner::dependencyClosure(
    const std::vector<BVAbstractionId>& seeds)
{
  if (indexedRecords_ != eqs_.size() + terms_.size())
    rebuildRecordIndex();

  BVAbstractionScope scope = BVAbstractionScope::selected();
  std::vector<BVAbstractionId> pending = seeds;
  std::set<BVAbstractionId> reached;
  while (!pending.empty())
  {
    const BVAbstractionId id = pending.back();
    pending.pop_back();
    if (!id.valid())
    {
      scope.complete = false;
      return scope;
    }
    if (!reached.insert(id).second)
      continue;

    const auto found = recordOfId_.find(id);
    if (found == recordOfId_.end())
    {
      scope.complete = false;
      return scope;
    }

    const RecordLocation& location = found->second;
    const std::vector<BVAbstractionId>* dependencies = NULL;
    if (location.equality)
    {
      assert(location.index < eqs_.size());
      scope.equalityIndices.push_back(location.index);
      dependencies = &eqs_[location.index].dependencies;
    }
    else
    {
      assert(location.index < terms_.size());
      scope.termIndices.push_back(location.index);
      dependencies = &terms_[location.index].dependencies;
    }
    pending.insert(pending.end(), dependencies->begin(), dependencies->end());
  }

  std::sort(scope.equalityIndices.begin(), scope.equalityIndices.end());
  std::sort(scope.termIndices.begin(), scope.termIndices.end());
  return scope;
}

void BVAbstractionRefiner::prepareTermForQuery(BVTermAbstraction& term)
{
  if (term.queryGeneration == queryGeneration_)
    return;
  term.blockedThisQuery = 0;
  term.schemasThisQuery = 0;
  term.queryGeneration = queryGeneration_;
}

AbstractionRefinementResult BVAbstractionRefiner::refine(
    SATSolver& solver, const ToSATBase::ASTNodeToSATVar& nodeToSATVar)
{
  return refine(solver, nodeToSATVar, BVAbstractionScope::all());
}

AbstractionRefinementResult BVAbstractionRefiner::refine(
    SATSolver& solver, const ToSATBase::ASTNodeToSATVar& nodeToSATVar,
    const BVAbstractionScope& scope)
{
  if (!scope.complete)
  {
    bm->noteUnknown(
        UnknownReason::Incomplete,
        "a live BV abstraction dependency had no harvested producer record");
    return AbstractionRefinementResult::unknown();
  }

  const std::vector<size_t>* selectedEqualities =
      scope.allRecords ? NULL : &scope.equalityIndices;
  const std::vector<size_t>* selectedTerms =
      scope.allRecords ? NULL : &scope.termIndices;
  unsigned refined = 0;
  AbstractionRefinementResult result =
      AbstractionRefinementResult::faithful();
  if (hasEqualities())
    refined = refineEqualities(solver, nodeToSATVar, selectedEqualities);
  if (refined == 0 && hasTerms())
    result = refineTerms(solver, nodeToSATVar, selectedTerms);
  else if (refined > 0)
    result = AbstractionRefinementResult::progress(refined);

  refined = result.refined;
  if (refined > 0)
  {
    refinements_ += refined;
    bm->UserFlags.coverage.bv_refinement_rounds++;
    if (bm->UserFlags.stats_flag)
      std::cerr << "BV abstraction: refined " << refined << " operations"
                << std::endl;
  }
  return result;
}

// Which variables carry a term record's result: its own, where the lowering
// filed them, and otherwise whatever the AST-keyed map holds for its term.
// NULL when neither has an answer.
//
// Both readers of a result go through here, and that is the point. They are
// entitled to different things -- freezing runs before the first solve and
// tolerates a record whose bits are not encoded yet, refinement runs after it
// and does not -- but neither is entitled to its own opinion about WHICH
// variables the result is. A record frozen at one set and checked at another
// is the shape of the bug the record-owned result exists to close, rebuilt
// inside this file.
static const std::vector<unsigned>*
resultVarsOf(const BVTermAbstraction& abstraction,
             const ToSATBase::ASTNodeToSATVar& nodeToSATVar)
{
  if (!abstraction.resultSATVars.empty())
    return &abstraction.resultSATVars;

  const auto it = nodeToSATVar.find(abstraction.termNode);
  return it == nodeToSATVar.end() ? NULL : &it->second;
}

void BVAbstractionRefiner::freezeVariables(
    SATSolver& satSolver,
    const ToSATBase::ASTNodeToSATVar& nodeToSATVar) const
{
  // Every variable a future refinement lemma can be written over: the
  // records' own inputs, and the operand bits the pinning clauses name.
  // A simplifying backend is free to eliminate anything not frozen, and a
  // clause added later over an eliminated variable is exactly the write
  // the simplifying MiniSat family cannot take back -- backends that
  // restore an eliminated variable on contact make every one of these
  // calls a deliberate no-op instead (see Cadical::setFrozen).
  //
  // Best effort, and the one place a record's variables may be absent
  // without anything being wrong: this runs before the first solve, so it
  // is not the party entitled to a complete encoding. Refinement is, and
  // says so itself. Freezing what is not there would be a write against a
  // variable the backend does not have.
  for (const auto& a : eqs_)
  {
    if (a.abstractionSATVar != BV_ABSTRACTION_NO_VAR)
      satSolver.setFrozen(a.abstractionSATVar);
    // The equality's lemmas are Tseitin clauses over the operands' bits,
    // so those bits need freezing exactly as a term record's operands do.
    const ASTNode* sides[2] = {&a.leftSymbol, &a.rightSymbol};
    for (const ASTNode* side : sides)
    {
      auto sideIt = nodeToSATVar.find(*side);
      if (sideIt != nodeToSATVar.end())
        for (unsigned v : sideIt->second)
          if (v != BV_ABSTRACTION_NO_VAR)
            satSolver.setFrozen(v);
    }
  }

  for (const auto& a : terms_)
  {
    const std::vector<unsigned>* result = resultVarsOf(a, nodeToSATVar);
    if (result != NULL)
      for (unsigned v : *result)
        if (v != BV_ABSTRACTION_NO_VAR)
          satSolver.setFrozen(v);
    for (unsigned i = 0; i < a.numOperands; i++)
    {
      auto opIt = nodeToSATVar.find(a.operands[i]);
      if (opIt != nodeToSATVar.end())
        for (unsigned v : opIt->second)
          if (v != BV_ABSTRACTION_NO_VAR)
            satSolver.setFrozen(v);
    }
    if (a.condSATVar != BV_ABSTRACTION_NO_VAR)
      satSolver.setFrozen(a.condSATVar);
  }
}

// The SAT variables one operand of a record was encoded into, ready to be
// read out of a candidate or written into a clause. A record's own result
// does not come through here: it is the record's to name, and resultVarsOf
// answers for it.
//
// Three things have to hold for the record to be checkable at all, and all
// three hold by construction.
//
// The node is in the map. The blaster registers every node it abstracts and
// every operand it abstracts one over, through ensureProxyCIs or the
// assignment beside the record, and both lowerings carry the whole of that
// registry across: fill_node_to_var for the batch pipeline, and
// addAbstractionOperand for the incremental driver, which harvests records
// and operands from the one blaster and drops both together on a rebuild.
//
// The vector is at least as wide as the record. Both widths are the same
// node's GetValueWidth(), and an operation and its operands have the width
// STP's type checker gave them.
//
// And every bit in that range is a variable the CNF has. ~0u marks one that
// is not, which is how a symbol only partly bit-blasted is reported; the
// nodes here are either whole symbols or vectors of proxy inputs minted a
// bit at a time, so none of them is partial.
//
// So none of this fires -- across the in-tree corpus under both drivers and
// all five CNF generators, some 450,000 record checks, not once. It is here
// because all three fail quietly and none of them is checked anywhere else.
// Reading past the vector is an out-of-bounds read: a record one bit wider
// than its operand segfaulted on an eight-bit equality and, on the term
// path, quietly answered from whatever followed the allocation. Reading ~0u
// asks the SAT backend for the value of a variable it never had. And
// skipping the record -- which is what returning "no bits" used to lead to
// at every one of these call sites -- is worse than either, because an
// abstraction is an over-approximation until refinement pins it to its
// operands: a record left unchecked is a record no candidate can contradict,
// so the search is free to satisfy the query by giving it whatever value it
// likes. With the operands of `a = 1 and b = 2 and a = b` taken out of the
// map, that unsatisfiable query came back sat, with exit status 0 and no
// diagnostic at all.
//
// There is no conservative way to carry on from any of the three, so say
// which one happened instead.
static const std::vector<unsigned>&
encodedBitsOf(const ASTNode& node, unsigned width,
              const ToSATBase::ASTNodeToSATVar& nodeToSATVar)
{
  const auto it = nodeToSATVar.find(node);
  if (it == nodeToSATVar.end())
    FatalError("BV abstraction: an abstracted operation names a node that "
               "the bit-blast did not encode, so no candidate can be "
               "checked against it: ",
               node);

  const std::vector<unsigned>& vars = it->second;
  if (vars.size() < width)
    FatalError("BV abstraction: an abstracted operation is recorded wider "
               "than the bits the bit-blast encoded for it; the record's "
               "width is: ",
               node, (int)width);

  for (unsigned i = 0; i < width; ++i)
    if (vars[i] == BV_ABSTRACTION_NO_VAR)
      FatalError("BV abstraction: an abstracted operation names a bit that "
                 "never reached the CNF; the bit is: ",
                 node, (int)i);

  return vars;
}

// The same result, for refinement: every bit a variable the CNF has, or the
// call does not come back. The three things checked here are the three
// encodedBitsOf checks for an operand, and hold for the same reasons.
static const std::vector<unsigned>&
encodedResultBitsOf(const BVTermAbstraction& abstraction,
                    const ToSATBase::ASTNodeToSATVar& nodeToSATVar)
{
  const std::vector<unsigned>* vars = resultVarsOf(abstraction, nodeToSATVar);
  if (vars == NULL)
    FatalError("BV abstraction: an abstracted operation has no result the "
               "bit-blast encoded, so no candidate can be checked against "
               "it: ",
               abstraction.termNode);

  if (vars->size() < abstraction.width)
    FatalError("BV abstraction: an abstracted operation is recorded wider "
               "than the result the bit-blast gave it; the record's width "
               "is: ",
               abstraction.termNode, (int)abstraction.width);

  for (unsigned i = 0; i < abstraction.width; ++i)
    if ((*vars)[i] == BV_ABSTRACTION_NO_VAR)
      FatalError("BV abstraction: an abstracted operation's result names a "
                 "bit that never reached the CNF; the bit is: ",
                 abstraction.termNode, (int)i);

  return *vars;
}

// A record's own variable: the Boolean an equality became, or the condition
// input of a comparison or an if-then-else. ~0u is both "the family has none"
// and "the one it has never reached the solver", and neither is a state any
// caller can go on from -- see encodedBitsOf above for why skipping is not an
// option.
//
// Called where a round first reads the variable, which is always the scan; the
// clause phases below run only over the records that scan accepted, so what
// they write over has been through here already.
static unsigned recordedVar(unsigned var, const ASTNode& node,
                            const char* what)
{
  if (var == BV_ABSTRACTION_NO_VAR)
    FatalError(what, node);
  return var;
}

unsigned BVAbstractionRefiner::refineEqualities(
    SATSolver& solver, const ToSATBase::ASTNodeToSATVar& nodeToSATVar,
    const std::vector<size_t>* selected)
{
  // Phase 1: Congruence closure — detect transitivity conflicts at word level.
  //
  // Defined records take part too. A defined equality's Boolean is exact --
  // its clauses force it to the operands' bits -- so its model value is a
  // fact about the candidate, chains are free to run through it, and an
  // explanation clause naming it stays a theorem. Leaving defined records
  // out breaks exactly the chains that mature first: a conflict whose path
  // crosses one would fall through to the bit-level scan and be rediscovered
  // a definition at a time. A conflict can still never be built from defined
  // records alone -- their Booleans mirror real bit-vectors, and equality of
  // bit-vectors is transitive -- so every clause this phase emits constrains
  // at least one undefined record, and blocks the candidate it was read from.
  {
    std::unordered_map<ASTNode, unsigned, ASTNode::ASTNodeHasher,
                       ASTNode::ASTNodeEqual> symbolToIdx;
    unsigned nextIdx = 0;
    const size_t count = selectedSize(eqs_.size(), selected);
    for (size_t position = 0; position < count; ++position)
    {
      const size_t idx = selectedIndex(position, selected);
      assert(idx < eqs_.size());
      const auto& abs = eqs_[idx];
      if (symbolToIdx.find(abs.leftSymbol) == symbolToIdx.end())
        symbolToIdx[abs.leftSymbol] = nextIdx++;
      if (symbolToIdx.find(abs.rightSymbol) == symbolToIdx.end())
        symbolToIdx[abs.rightSymbol] = nextIdx++;
    }

    // Out-of-scope records are left out of the chains as well as out of the
    // scan. Their Booleans are free, so a chain through one would build a
    // conflict out of a value nothing in the query chose, and the
    // explanation clause would be spent constraining a record the query
    // cannot see.
    std::vector<BVEQCongruenceClosure::EqInfo> eqInfos;
    for (size_t position = 0; position < count; ++position)
    {
      const size_t idx = selectedIndex(position, selected);
      assert(idx < eqs_.size());
      const auto& abs = eqs_[idx];
      // Read once and checked once: the closure both reads this variable's
      // value and writes the explanation clause over it.
      const unsigned eqVar = recordedVar(
          abs.abstractionSATVar, abs.eqNode,
          "BV abstraction: an abstracted equality's own variable never "
          "reached the solver: ");
      bool modelTrue = (solver.modelValue(eqVar) == solver.true_literal());
      eqInfos.push_back({symbolToIdx[abs.leftSymbol],
                          symbolToIdx[abs.rightSymbol],
                          eqVar,
                          modelTrue});
    }

    BVEQCongruenceClosure cc;
    unsigned ccConflicts = cc.check(eqInfos, solver);
    if (ccConflicts > 0)
      return ccConflicts;
  }

  // Phase 2: Bit-level Tseitin encoding for remaining inconsistencies.
  // Scan phase: identify inconsistent EQs (model reads only).
  const unsigned refineWidth = bm->UserFlags.bv_eq_refine_width;

  struct InconsistentEQ {
    size_t absIdx;
    unsigned newEnd;
    const std::vector<unsigned>* leftVars;
    const std::vector<unsigned>* rightVars;
    // The candidate said unequal while the operands' bits agree. The
    // prefix clauses below say nothing to such a candidate -- they are all
    // conditioned on the Boolean being true -- so the clause phase owes it
    // a blocking lemma of its own, written over the one value both sides
    // share, which is cached here because phase 2 must not read the model.
    bool saidUnequal;
    std::vector<bool> sharedValue;
  };
  std::vector<InconsistentEQ> incEQs;

  const size_t count = selectedSize(eqs_.size(), selected);
  for (size_t position = 0; position < count; ++position)
  {
    const size_t idx = selectedIndex(position, selected);
    assert(idx < eqs_.size());
    auto& abs = eqs_[idx];
    if (abs.defined)
      continue;

    const unsigned eqVar = recordedVar(
        abs.abstractionSATVar, abs.eqNode,
        "BV abstraction: an abstracted equality's own variable never "
        "reached the solver: ");
    bool absTrue = (solver.modelValue(eqVar) == solver.true_literal());

    // Both sides, whatever their kind: the blaster registers a constant
    // operand as a vector of inputs pinned to it, so there is nothing to
    // fold in here and the clause phase below has real variables to write
    // its Tseitin encoding over.
    const std::vector<unsigned>& leftVars =
        encodedBitsOf(abs.leftSymbol, abs.width, nodeToSATVar);
    const std::vector<unsigned>& rightVars =
        encodedBitsOf(abs.rightSymbol, abs.width, nodeToSATVar);

    bool actualEqual = true;
    for (unsigned bit = 0; bit < abs.width; ++bit)
    {
      if (solver.modelValue(leftVars[bit]) != solver.modelValue(rightVars[bit]))
      {
        actualEqual = false;
        break;
      }
    }

    if (absTrue == actualEqual)
      continue;

    unsigned newEnd;
    if (refineWidth == 0 || refineWidth >= abs.width)
      newEnd = abs.width;
    else if (abs.refinedBits == 0)
      newEnd = std::min(refineWidth, abs.width);
    else
      newEnd = std::min(abs.refinedBits * 2, abs.width);

    InconsistentEQ inc{idx, newEnd, &leftVars, &rightVars, !absTrue, {}};
    if (inc.saidUnequal && newEnd < abs.width)
    {
      inc.sharedValue.resize(abs.width);
      for (unsigned bit = 0; bit < abs.width; ++bit)
        inc.sharedValue[bit] =
            (solver.modelValue(leftVars[bit]) == solver.true_literal());
    }
    incEQs.push_back(std::move(inc));
  }

  // Clause phase: add Tseitin encoding (no model reads).
  unsigned refined = 0;
  for (auto& inc : incEQs)
  {
    auto& abs = eqs_[inc.absIdx];

    // A candidate that said unequal over agreeing bits satisfies every
    // prefix clause vacuously -- each one is conditioned on the Boolean
    // being true -- so left to the prefix alone the search could hand the
    // identical candidate back until the definition completes, one full
    // solve per doubling. Rule the candidate out now instead: if both
    // sides hold the one value this candidate gave them, the equality is
    // true. That is the definition's own consequence at a single point,
    // so asserting it early is as sound as asserting the definition, and
    // it is one clause against a round of solving. A round that completes
    // the definition needs none of this: its closing clause already forces
    // the Boolean once every helper agrees.
    if (inc.saidUnequal && !inc.sharedValue.empty())
    {
      SATSolver::vec_literals cl;
      cl.push(SATSolver::mkLit(abs.abstractionSATVar, false));
      for (unsigned bit = 0; bit < abs.width; ++bit)
      {
        cl.push(SATSolver::mkLit((*inc.leftVars)[bit],
                                 inc.sharedValue[bit]));
        cl.push(SATSolver::mkLit((*inc.rightVars)[bit],
                                 inc.sharedValue[bit]));
      }
      solver.addClause(cl);
    }

    for (unsigned bit = abs.refinedBits; bit < inc.newEnd; ++bit)
    {
      unsigned lv = (*inc.leftVars)[bit];
      unsigned rv = (*inc.rightVars)[bit];
      unsigned h = solver.newVar();
      solver.setFrozen(h);
      abs.xnorHelpers.push_back(h);

      SATSolver::vec_literals cl;

      cl.clear();
      cl.push(SATSolver::mkLit(lv, true));
      cl.push(SATSolver::mkLit(rv, true));
      cl.push(SATSolver::mkLit(h, false));
      solver.addClause(cl);

      cl.clear();
      cl.push(SATSolver::mkLit(lv, false));
      cl.push(SATSolver::mkLit(rv, false));
      cl.push(SATSolver::mkLit(h, false));
      solver.addClause(cl);

      cl.clear();
      cl.push(SATSolver::mkLit(lv, false));
      cl.push(SATSolver::mkLit(rv, true));
      cl.push(SATSolver::mkLit(h, true));
      solver.addClause(cl);

      cl.clear();
      cl.push(SATSolver::mkLit(lv, true));
      cl.push(SATSolver::mkLit(rv, false));
      cl.push(SATSolver::mkLit(h, true));
      solver.addClause(cl);

      cl.clear();
      cl.push(SATSolver::mkLit(abs.abstractionSATVar, true));
      cl.push(SATSolver::mkLit(h, false));
      solver.addClause(cl);
    }

    abs.refinedBits = inc.newEnd;

    if (abs.refinedBits >= abs.width)
    {
      SATSolver::vec_literals cl;
      for (unsigned h : abs.xnorHelpers)
        cl.push(SATSolver::mkLit(h, true));
      cl.push(SATSolver::mkLit(abs.abstractionSATVar, false));
      solver.addClause(cl);

      abs.defined = true;
    }

    refined++;
  }
  return refined;
}

// A bit vector as the constant evaluator wants it, and back again.
static CBV toConstant(const std::vector<bool>& bits)
{
  CBV value = CONSTANTBV::BitVector_Create((unsigned)bits.size(), true);
  for (unsigned i = 0; i < bits.size(); ++i)
    if (bits[i])
      CONSTANTBV::BitVector_Bit_On(value, i);
  return value;
}

std::vector<bool> bvOperationValue(Kind opKind,
                                   const std::vector<bool>& aBits,
                                   const std::vector<bool>& bBits)
{
  assert(aBits.size() == bBits.size());
  assert(!aBits.empty());

  const unsigned width = (unsigned)aBits.size();
  CBV a = toConstant(aBits);
  CBV b = toConstant(bBits);
  std::vector<CBV> args;
  args.push_back(a);
  args.push_back(b);

  CBV computed = NonMemberBVConstEvaluator(opKind, args, width);
  std::vector<bool> result(width);
  for (unsigned i = 0; i < width; ++i)
    result[i] = CONSTANTBV::BitVector_bit_test(computed, i);

  CONSTANTBV::BitVector_Destroy(computed);
  CONSTANTBV::BitVector_Destroy(b);
  CONSTANTBV::BitVector_Destroy(a);
  return result;
}

static void readModelBits(const std::vector<unsigned>& satVars,
                          unsigned width, SATSolver& solver,
                          std::vector<bool>& bits)
{
  assert(satVars.size() >= width);
  bits.resize(width);
  for (unsigned i = 0; i < width; ++i)
    bits[i] = (solver.modelValue(satVars[i]) == solver.true_literal());
}

static void getOperandBits(
    const ASTNode& operand, unsigned width,
    const ToSATBase::ASTNodeToSATVar& nodeToSATVar, SATSolver& solver,
    std::vector<bool>& bits)
{
  bits.resize(width);
  if (operand.GetKind() == BVCONST)
  {
    CBV val = operand.GetBVConst();
    for (unsigned i = 0; i < width; ++i)
      bits[i] = CONSTANTBV::BitVector_bit_test(val, i);
    return;
  }
  const std::vector<unsigned>& satVars =
      encodedBitsOf(operand, width, nodeToSATVar);
  readModelBits(satVars, width, solver, bits);
}

static bool isBVCompare(Kind k)
{
  return k == BVLE || k == BVGE || k == BVGT || k == BVLT ||
         k == BVSLE || k == BVSGE || k == BVSGT || k == BVSLT;
}

static bool computeBVLE(const std::vector<bool>& left,
                        const std::vector<bool>& right,
                        bool isSigned)
{
  unsigned w = left.size();
  if (isSigned)
  {
    bool aSign = left[w - 1];
    bool bSign = right[w - 1];
    if (aSign && !bSign) return true;
    if (!aSign && bSign) return false;
  }
  for (int i = (int)w - 1; i >= 0; --i)
  {
    if (isSigned && i == (int)w - 1) continue;
    if (!left[i] && right[i]) return true;
    if (left[i] && !right[i]) return false;
  }
  return true;
}

// Every comparison is `<=` under some combination of swapping the operands,
// negating the answer, and reading the top bit as a sign. Named once, because
// the model check below and the clauses that pin the abstraction both need it
// and must not disagree: they did, over BVLT, and a lemma that pins an
// abstraction to a > b for a query that asked a < b is not a weaker claim than
// the right one but the opposite of it.
struct CompareForm
{
  bool swapOps;
  bool negateResult;
  bool isSigned;
};

static CompareForm comparisonForm(Kind k)
{
  switch (k)
  {
    case BVLE:  return {false, false, false};
    case BVGE:  return {true,  false, false};
    case BVGT:  return {false, true,  false};
    case BVLT:  return {true,  true,  false};
    case BVSLE: return {false, false, true};
    case BVSGE: return {true,  false, true};
    case BVSGT: return {false, true,  true};
    case BVSLT: return {true,  true,  true};
    default:    return {false, false, false};
  }
}

static bool computeBVCompare(Kind k, const std::vector<bool>& aBits,
                             const std::vector<bool>& bBits)
{
  const CompareForm form = comparisonForm(k);
  const bool le = form.swapOps ? computeBVLE(bBits, aBits, form.isSigned)
                               : computeBVLE(aBits, bBits, form.isSigned);
  return form.negateResult ? !le : le;
}

// The gates the refinement's own lemmas are built from, so that nothing here
// is a hand-written clause block; each is written out of the row of the truth
// table it rules out. mkLit(v, sign) is false exactly when v equals sign, so
// a literal at `bit` is false exactly when that input is `bit`, and a clause
// listing one row is falsified only on that row.

static unsigned freshVar(SATSolver& solver)
{
  const unsigned v = solver.newVar();
  solver.setFrozen(v);
  return v;
}

static unsigned pinnedVar(SATSolver& solver, bool value)
{
  const unsigned v = freshVar(solver);
  SATSolver::vec_literals cl;
  cl.push(SATSolver::mkLit(v, !value));
  solver.addClause(cl);
  return v;
}

// z <-> x | y
static unsigned mkOr(SATSolver& solver, unsigned x, unsigned y)
{
  const unsigned z = freshVar(solver);
  SATSolver::vec_literals cl;
  cl.clear(); cl.push(SATSolver::mkLit(x, true));  cl.push(SATSolver::mkLit(z, false)); solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(y, true));  cl.push(SATSolver::mkLit(z, false)); solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(x, false)); cl.push(SATSolver::mkLit(y, false)); cl.push(SATSolver::mkLit(z, true)); solver.addClause(cl);
  return z;
}

// z <-> x ^ y
static unsigned mkXor(SATSolver& solver, unsigned x, unsigned y)
{
  const unsigned z = freshVar(solver);
  SATSolver::vec_literals cl;
  cl.clear(); cl.push(SATSolver::mkLit(x, true));  cl.push(SATSolver::mkLit(y, true));  cl.push(SATSolver::mkLit(z, true));  solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(x, false)); cl.push(SATSolver::mkLit(y, false)); cl.push(SATSolver::mkLit(z, true));  solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(x, true));  cl.push(SATSolver::mkLit(y, false)); cl.push(SATSolver::mkLit(z, false)); solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(x, false)); cl.push(SATSolver::mkLit(y, true));  cl.push(SATSolver::mkLit(z, false)); solver.addClause(cl);
  return z;
}

// z <-> x & y
static unsigned mkAnd(SATSolver& solver, unsigned x, unsigned y)
{
  const unsigned z = freshVar(solver);
  SATSolver::vec_literals cl;
  cl.clear(); cl.push(SATSolver::mkLit(z, true));  cl.push(SATSolver::mkLit(x, false)); solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(z, true));  cl.push(SATSolver::mkLit(y, false)); solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(z, false)); cl.push(SATSolver::mkLit(x, true)); cl.push(SATSolver::mkLit(y, true)); solver.addClause(cl);
  return z;
}

static void addEquivalence(SATSolver& solver, unsigned x, unsigned y)
{
  SATSolver::vec_literals cl;
  cl.clear(); cl.push(SATSolver::mkLit(x, true));  cl.push(SATSolver::mkLit(y, false)); solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(x, false)); cl.push(SATSolver::mkLit(y, true));  solver.addClause(cl);
}

// The bits of -x. Two's complement negation is ~x + 1, and the whole of that
// carry is a prefix OR: bit j comes out flipped exactly when some bit below
// j is set. Below the lowest set bit nothing flips, at it the 1 survives,
// and above it every bit is complemented -- which is the same three cases
// read off the addition.
std::vector<unsigned> encodeNegate(SATSolver& solver,
                                   const std::vector<unsigned>& x,
                                   unsigned width)
{
  std::vector<unsigned> neg(width);
  unsigned lower = pinnedVar(solver, false);
  for (unsigned j = 0; j < width; ++j)
  {
    neg[j] = mkXor(solver, x[j], lower);
    if (j + 1 < width)
      lower = mkOr(solver, lower, x[j]);
  }
  return neg;
}

// The exponent of a power of two, or -1 for anything else. Exactly one bit
// set: zero has none and is not one.
static int powerOfTwoExponent(const std::vector<bool>& bits)
{
  int found = -1;
  for (unsigned i = 0; i < bits.size(); ++i)
    if (bits[i])
    {
      if (found >= 0)
        return -1;
      found = (int)i;
    }
  return found;
}

// The same negation encodeNegate() builds, over values rather than
// variables, so that the scan can decide whether the schema applies without
// putting a single clause in the solver.
static std::vector<bool> negatedValue(const std::vector<bool>& bits)
{
  std::vector<bool> out(bits.size());
  bool lower = false;
  for (unsigned j = 0; j < bits.size(); ++j)
  {
    out[j] = (bits[j] != lower);
    lower = lower || bits[j];
  }
  return out;
}

// Trailing zeros, which is the whole width when nothing is set.
static unsigned trailingZeros(const std::vector<bool>& bits)
{
  for (unsigned i = 0; i < bits.size(); ++i)
    if (bits[i])
      return i;
  return bits.size();
}

// Does the candidate's product agree with `other` shifted up by `shift`?
static bool productIsShift(const std::vector<bool>& other, unsigned shift,
                           const std::vector<bool>& tBits)
{
  for (unsigned j = 0; j < tBits.size(); ++j)
  {
    const bool shifted = (j >= shift) && other[j - shift];
    if (tBits[j] != shifted)
      return false;
  }
  return true;
}

bool exactLowPrefixHolds(Kind opKind, const std::vector<bool>& aBits,
                         const std::vector<bool>& bBits,
                         const std::vector<bool>& resultBits,
                         unsigned prefixBits)
{
  assert(opKind == BVPLUS || opKind == BVMULT);
  assert(aBits.size() == bBits.size());
  assert(aBits.size() == resultBits.size());
  assert(prefixBits > 0 && prefixBits <= resultBits.size());

  std::vector<bool> expected(prefixBits, false);
  if (opKind == BVPLUS)
  {
    bool carry = false;
    for (unsigned i = 0; i < prefixBits; ++i)
    {
      expected[i] = (aBits[i] != bBits[i]) != carry;
      carry = (aBits[i] && bBits[i]) || (aBits[i] && carry) ||
              (bBits[i] && carry);
    }
  }
  else
  {
    // Add each low shifted copy of b into the prefix. No operand bit at or
    // above prefixBits can affect a lower product bit.
    for (unsigned i = 0; i < prefixBits; ++i)
      if (aBits[i])
      {
        bool carry = false;
        for (unsigned j = 0; i + j < prefixBits; ++j)
        {
          const unsigned bit = i + j;
          const bool addend = bBits[j];
          const bool sum = (expected[bit] != addend) != carry;
          carry = (expected[bit] && addend) || (expected[bit] && carry) ||
                  (addend && carry);
          expected[bit] = sum;
        }
      }
  }

  for (unsigned i = 0; i < prefixBits; ++i)
    if (expected[i] != resultBits[i])
      return false;
  return true;
}

bool mulSchemaHolds(MulSchema schema, unsigned operand, unsigned shift,
                    const std::vector<bool>& aBits,
                    const std::vector<bool>& bBits,
                    const std::vector<bool>& tBits)
{
  assert(aBits.size() == bBits.size());
  assert(aBits.size() == tBits.size());
  assert(operand < 2);

  const std::vector<bool>* ops[2] = {&aBits, &bBits};
  const std::vector<bool>& chosen = *ops[operand];
  const std::vector<bool>& other = *ops[1 - operand];

  switch (schema)
  {
    case MulSchema::Odd:
      // t[0] = a[0] & b[0].
      return tBits[0] == (aBits[0] && bBits[0]);

    case MulSchema::TrailingZeros:
    {
      // The product carries at least as many trailing zeros as the operand.
      // The circuit says the same thing one bit at a time -- t[i] holds only
      // if some bit of the operand at or below i does -- and the two agree:
      // a product bit below the operand's lowest set bit has no such j.
      const unsigned zeros = trailingZeros(chosen);
      for (unsigned bit = 0; bit < zeros; ++bit)
        if (tBits[bit])
          return false;
      return true;
    }

    case MulSchema::Pow2:
      // a = 2^shift -> t = b << shift. Vacuous for any other operand value,
      // which is what makes it a theorem rather than a reading of this
      // candidate.
      return powerOfTwoExponent(chosen) != (int)shift ||
             productIsShift(other, shift, tBits);

    case MulSchema::NegPow2:
      // a = -2^shift -> t = (-b) << shift.
      return powerOfTwoExponent(negatedValue(chosen)) != (int)shift ||
             productIsShift(negatedValue(other), shift, tBits);

    case MulSchema::LowPrefix:
      return exactLowPrefixHolds(BVMULT, aBits, bBits, tBits, shift);

    case MulSchema::Lemma:
    case MulSchema::None:
      break;
  }

  FatalError("mulSchemaHolds: asked about a schema that is not one of the "
             "hand-written ones");
  return true;
}

bool divRemIdentityHolds(const std::vector<bool>& dividendBits,
                         const std::vector<bool>& divisorBits,
                         const std::vector<bool>& quotientBits,
                         const std::vector<bool>& remainderBits)
{
  assert(dividendBits.size() == divisorBits.size());
  assert(dividendBits.size() == quotientBits.size());
  assert(dividendBits.size() == remainderBits.size());
  assert(!dividendBits.empty());

  const unsigned width = static_cast<unsigned>(dividendBits.size());
  std::vector<bool> product(width, false);
  for (unsigned i = 0; i < width; ++i)
    if (quotientBits[i])
    {
      bool carry = false;
      for (unsigned j = 0; i + j < width; ++j)
      {
        const unsigned bit = i + j;
        const bool addend = divisorBits[j];
        const bool sum = (product[bit] != addend) != carry;
        carry = (product[bit] && addend) || (product[bit] && carry) ||
                (addend && carry);
        product[bit] = sum;
      }
    }

  bool carry = false;
  for (unsigned i = 0; i < width; ++i)
  {
    const bool sum = (product[i] != remainderBits[i]) != carry;
    carry = (product[i] && remainderBits[i]) || (product[i] && carry) ||
            (remainderBits[i] && carry);
    if (sum != dividendBits[i])
      return false;
  }
  return true;
}

AddSchemaChoice chooseAddSchema(const std::vector<bool>& aBits,
                                const std::vector<bool>& bBits,
                                const std::vector<bool>& tBits,
                                uint64_t installedSchemas,
                                uint32_t enabledGroups)
{
  const std::vector<bool>* ops[2] = {&aBits, &bBits};
  unsigned addCount = 0;
  const BVLemmaEntry<AddLemma>* addTable = addLemmaTable(addCount);
  for (unsigned lemmaIndex = 0; lemmaIndex < addCount; ++lemmaIndex)
  {
    const BVLemmaEntry<AddLemma>& entry = addTable[lemmaIndex];
    if (!bvSchemaGroupEnabled(enabledGroups, entry.group))
      continue;
    if (!entry.applicable((unsigned)tBits.size()))
      continue;
    // One reading for a fact that says the same thing either way round: the
    // second is one the first already installed, and offering it costs an
    // evaluation on every call for the life of the record. See
    // BVLemmaEntry::symmetric for what checks the claim.
    const unsigned readings = entry.symmetric ? 1u : 2u;
    for (unsigned operand = 0; operand < readings; ++operand)
    {
      if ((installedSchemas & addLemmaInstalledBit(lemmaIndex, operand)) != 0)
        continue;
      if (!addLemmaHolds(entry.lemma, *ops[operand], *ops[1 - operand], tBits))
        return {true, operand, lemmaIndex, 0, entry.group};
    }
  }

  const unsigned prefix = std::min(3u, (unsigned)tBits.size());
  if (bvSchemaGroupEnabled(enabledGroups, BVSchemaGroup::LOW_PREFIX) &&
      (installedSchemas & ADD_SCHEMA_INSTALLED_LOW_PREFIX) == 0 &&
      !exactLowPrefixHolds(BVPLUS, aBits, bBits, tBits, prefix))
    return {true, 0, 0, prefix, BVSchemaGroup::LOW_PREFIX};
  return AddSchemaChoice();
}

MulSchemaChoice chooseMulSchema(const std::vector<bool>& aBits,
                                const std::vector<bool>& bBits,
                                const std::vector<bool>& tBits,
                                uint64_t installedSchemas,
                                uint32_t enabledGroups)
{
  const std::vector<bool>* ops[2] = {&aBits, &bBits};
  const bool base = bvSchemaGroupEnabled(enabledGroups, BVSchemaGroup::BASE);

  // Bounded families first; the operand-value-guarded shifts last, for the
  // reason chooseDivSchema sets out at length: everything below except the
  // final block is offered a number of times that does not depend on the
  // width, while the two shift schemas have one instance per power of two an
  // operand can hold, and both draw on the one schemaRounds purse. A
  // width-scaled family placed first can spend the whole purse before a
  // once-only fact is ever evaluated, and the chooser is not called again
  // afterwards.

  // The product carries at least as many trailing zeros as either operand.
  // Check operand 1 before operand 0 so schema selection remains
  // deterministic for this commutative operator.
  static const unsigned tzInstalled[2] = {
      MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_0,
      MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_1};
  if (base)
    for (unsigned pass = 0; pass < 2; ++pass)
    {
      const unsigned i = 1 - pass;
      if ((installedSchemas & tzInstalled[i]) != 0)
        continue;
      if (!mulSchemaHolds(MulSchema::TrailingZeros, i, 0, aBits, bBits, tBits))
        return {MulSchema::TrailingZeros, i, 0};
    }

  // t[0] = a[0] & b[0].
  if (base && (installedSchemas & MUL_SCHEMA_INSTALLED_ODD) == 0 &&
      !mulSchemaHolds(MulSchema::Odd, 0, 0, aBits, bBits, tBits))
    return {MulSchema::Odd, 0, 0};

  // The registry facts are unconditional but asymmetric expressions over a
  // commutative operation. Offer each source fact in both readings, exactly
  // once apiece. MUL8 is entry zero, so the ranked 75-firing fact is offered
  // before the remainder of the imported catalogue.
  unsigned mulCount = 0;
  const BVLemmaEntry<MulLemma>* mulTable = mulLemmaTable(mulCount);
  for (unsigned lemmaIndex = 0; lemmaIndex < mulCount; ++lemmaIndex)
  {
    const BVLemmaEntry<MulLemma>& entry = mulTable[lemmaIndex];
    if (!bvSchemaGroupEnabled(enabledGroups, entry.group))
      continue;
    if (!entry.applicable((unsigned)tBits.size()))
      continue;
    // As in chooseAddSchema: a symmetric row has one reading, not two.
    const unsigned readings = entry.symmetric ? 1u : 2u;
    for (unsigned operand = 0; operand < readings; ++operand)
    {
      if ((installedSchemas &
           mulLemmaInstalledBit(lemmaIndex, operand)) != 0)
        continue;
      if (!mulLemmaHolds(entry.lemma, *ops[operand], *ops[1 - operand], tBits))
        return {MulSchema::Lemma, operand, 0, lemmaIndex, entry.group};
    }
  }

  const unsigned prefix = std::min(3u, (unsigned)tBits.size());
  if (bvSchemaGroupEnabled(enabledGroups, BVSchemaGroup::LOW_PREFIX) &&
      (installedSchemas & MUL_SCHEMA_INSTALLED_LOW_PREFIX) == 0 &&
      !mulSchemaHolds(MulSchema::LowPrefix, 0, prefix, aBits, bBits, tBits))
    return {MulSchema::LowPrefix, 0, prefix, 0, BVSchemaGroup::LOW_PREFIX};

  const bool shiftValueLeft = bvSchemaFamilyHasInstance(
      installedSchemas, BVSchemaFamily::MulShiftValue);

  // a = 2^k -> t = b << k, and the same read the other way round. Where it
  // applies it says the most of the four: the shift *is* the product for
  // that operand value, so one lemma settles every b at once where a
  // blocking lemma settles one pair. It therefore also always fires when it
  // applies -- this is only ever called over a candidate whose product is
  // already known wrong, and for a power-of-two operand "wrong" and
  // "disagrees with the shift" are the same statement.
  if (base && shiftValueLeft)
    for (unsigned i = 0; i < 2; ++i)
    {
      const int k = powerOfTwoExponent(*ops[i]);
      if (k >= 0 &&
          !mulSchemaHolds(MulSchema::Pow2, i, (unsigned)k, aBits, bBits, tBits))
        return {MulSchema::Pow2, i, (unsigned)k};
    }

  // a = -2^k -> t = (-b) << k. A power of two is skipped rather than
  // excluded by name: that covers the minimum signed value, which is its own
  // negation and which the schema above has already taken.
  if (base && shiftValueLeft)
    for (unsigned i = 0; i < 2; ++i)
    {
      if (powerOfTwoExponent(*ops[i]) >= 0)
        continue;
      const int k = powerOfTwoExponent(negatedValue(*ops[i]));
      if (k >= 0 && !mulSchemaHolds(MulSchema::NegPow2, i, (unsigned)k, aBits,
                                    bBits, tBits))
        return {MulSchema::NegPow2, i, (unsigned)k};
    }

  return MulSchemaChoice();
}

std::vector<int> divSchemaSources(Kind opKind, unsigned width,
                                  const DivSchemaChoice& choice)
{
  std::vector<int> source(width, DIV_SOURCE_ZERO);

  if (choice.schema == DivSchema::DivisorZero)
  {
    // What the unabstracted BBDivMod answers over a zero divisor, and what
    // SMT-LIB says: the quotient is all ones and the remainder is the
    // dividend. The two are not the same value, so each is written out.
    for (unsigned i = 0; i < width; ++i)
      source[i] = (opKind == BVDIV) ? DIV_SOURCE_ONE : (int)i;
    return source;
  }

  if (choice.schema != DivSchema::Pow2Divisor)
    return source;

  const unsigned shift = choice.shift;
  if (opKind == BVDIV)
  {
    // a >> shift. The bits above the shift come down and zeros arrive at
    // the top, which is what the vector was filled with.
    for (unsigned i = 0; i + shift < width; ++i)
      source[i] = (int)(i + shift);
  }
  else
  {
    // a & (2^shift - 1). The bits below the shift stay where they are and
    // everything at or above it goes.
    for (unsigned i = 0; i < shift && i < width; ++i)
      source[i] = (int)i;
  }
  return source;
}

// Does the candidate's result already say what these sources say it must?
// A schema the candidate satisfies is no use as a refinement: it would let
// the search offer the same model again, and the round would be spent for
// nothing.
static bool resultMatchesSources(const std::vector<int>& source,
                                 const std::vector<bool>& aBits,
                                 const std::vector<bool>& tBits)
{
  for (unsigned i = 0; i < source.size(); ++i)
  {
    const bool want = (source[i] == DIV_SOURCE_ZERO)  ? false
                      : (source[i] == DIV_SOURCE_ONE) ? true
                                                      : aBits[source[i]];
    if (tBits[i] != want)
      return false;
  }
  return true;
}

// Unsigned comparison over the bit vectors a candidate holds. A name for the
// reading the division bounds want -- `<=u` over a result the abstraction
// chose rather than over the operands of an abstracted comparison -- and not
// a second statement of it: two independently written comparisons in one file
// is how this file's own comment records a comparison chain coming out
// backwards.
static bool valueLessOrEqual(const std::vector<bool>& left,
                             const std::vector<bool>& right)
{
  return computeBVLE(left, right, false);
}

static bool valueIsZero(const std::vector<bool>& bits)
{
  for (unsigned i = 0; i < bits.size(); ++i)
    if (bits[i])
      return false;
  return true;
}

// The dividend shifted right by `shift`, which is what the two
// magnitude-guarded facts compare the quotient against.
static std::vector<bool> shiftedRight(const std::vector<bool>& bits,
                                      unsigned shift)
{
  const unsigned width = (unsigned)bits.size();
  std::vector<bool> out(width, false);
  for (unsigned i = 0; i + shift < width; ++i)
    out[i] = bits[i + shift];
  return out;
}

// 2^shift, as a vector of this width.
static std::vector<bool> powerOfTwoValue(unsigned width, unsigned shift)
{
  std::vector<bool> out(width, false);
  if (shift < width)
    out[shift] = true;
  return out;
}

bool divSchemaHolds(Kind opKind, DivSchema schema, unsigned shift,
                    const std::vector<bool>& aBits,
                    const std::vector<bool>& bBits,
                    const std::vector<bool>& tBits)
{
  assert(opKind == BVDIV || opKind == BVMOD);
  assert(aBits.size() == bBits.size());
  assert(aBits.size() == tBits.size());

  const unsigned width = (unsigned)tBits.size();
  const bool divisorZero = valueIsZero(bBits);
  // The three parameterised arms are theorems only for an exponent the width
  // has room for. Past it the two magnitude guards become vacuously true --
  // every divisor is at least a 2^shift that does not fit -- and what is left
  // is a claim that the quotient is zero, which is not a fact about anything.
  assert(schema != DivSchema::Pow2Divisor || shift < width);
  assert(schema != DivSchema::QuotientPow2Threshold || shift < width);
  assert(schema != DivSchema::DivisorMagnitudeBound || shift < width);

  switch (schema)
  {
    case DivSchema::DivisorZero:
    {
      // b = 0 -> t is what SMT-LIB totalises it to. Vacuous over any other
      // divisor.
      if (!divisorZero)
        return true;
      const DivSchemaChoice choice{DivSchema::DivisorZero, 0};
      return resultMatchesSources(divSchemaSources(opKind, width, choice),
                                  aBits, tBits);
    }

    case DivSchema::Pow2Divisor:
    {
      // b = 2^shift -> t = a >> shift, or a & (2^shift - 1) for the
      // remainder.
      if (powerOfTwoExponent(bBits) != (int)shift)
        return true;
      const DivSchemaChoice choice{DivSchema::Pow2Divisor, shift};
      return resultMatchesSources(divSchemaSources(opKind, width, choice),
                                  aBits, tBits);
    }

    case DivSchema::RemainderAtMostDividend:
      // r <=u a, over a zero divisor as well, where the remainder is the
      // dividend. No premise at all.
      assert(opKind == BVMOD);
      return valueLessOrEqual(tBits, aBits);

    case DivSchema::RemainderBelowDivisor:
      // b != 0 -> r <u b.
      assert(opKind == BVMOD);
      return divisorZero || !valueLessOrEqual(bBits, tBits);

    case DivSchema::QuotientAtMostDividend:
      // b != 0 -> q <=u a.
      assert(opKind == BVDIV);
      return divisorZero || valueLessOrEqual(tBits, aBits);

    case DivSchema::QuotientPow2Threshold:
    {
      // q >= 2^shift <-> b <=u (a >> shift). Both sides are true over a zero
      // divisor, so this one needs no premise either.
      assert(opKind == BVDIV);
      bool quotientAboveThreshold = false;
      for (unsigned i = shift; i < width; ++i)
        quotientAboveThreshold = quotientAboveThreshold || tBits[i];
      return quotientAboveThreshold ==
             valueLessOrEqual(bBits, shiftedRight(aBits, shift));
    }

    case DivSchema::DivisorMagnitudeBound:
      // b >=u 2^shift -> q <=u (a >> shift).
      assert(opKind == BVDIV);
      return !valueLessOrEqual(powerOfTwoValue(width, shift), bBits) ||
             valueLessOrEqual(tBits, shiftedRight(aBits, shift));

    case DivSchema::Lemma:
    case DivSchema::None:
      break;
  }

  FatalError("divSchemaHolds: asked about a schema that is not one of the "
             "hand-written ones");
  return true;
}

DivSchemaChoice chooseDivSchema(Kind opKind, const std::vector<bool>& aBits,
                                const std::vector<bool>& bBits,
                                const std::vector<bool>& tBits,
                                uint64_t installedSchemas,
                                uint32_t enabledGroups)
{
  const unsigned width = (unsigned)tBits.size();
  const bool divisorZero = valueIsZero(bBits);
  const bool base = bvSchemaGroupEnabled(enabledGroups, BVSchemaGroup::BASE);

  // Bounded families first; the divisor-guarded ones last.
  //
  // Every fact offered below except the final block is offered a number of
  // times that does not depend on the width: the bounds and the registry
  // entries carry an installedSchemas bit apiece, and the two magnitude
  // families are capped at two instances. The divisor-guarded facts are not
  // bounded that way -- there is one of them per divisor value a candidate
  // can hold, so a W-bit divisor has W+1 -- and all of them draw on one
  // purse, the bv_term_abstraction_rounds ceiling on schemaRounds.
  //
  // A width-scaled family offered first can therefore spend the whole purse
  // before a once-only fact that would have decided the query is ever
  // evaluated; and once the purse is gone the chooser is not called again,
  // so that fact is skipped permanently rather than merely deferred.
  // Measured on a query whose divisor is pinned to a power of two, where the
  // single clause `b != 0 -> q <=u a` refutes the query outright: with
  // Pow2Divisor going first it was never offered, and the record spent
  // thirty-two schema rounds and thirty-two blocking lemmas and then built a
  // 256-bit divider -- 1,617,712 clauses and 11.75s, against 0.01s for the
  // same query with a divisor shaped so the family cannot fire.
  //
  // Ordering it the other way costs at most one round per once-only fact,
  // after which the divisor-guarded family has the whole remaining purse and
  // behaves exactly as it did before. This is the rule DIVISOR_MAGNITUDE and
  // QUOTIENT_THRESHOLDS were already ordered by below; it simply had not been
  // applied to the family that sat above them.
  //
  // The bounds go first within that: they name no divisor, so they are the
  // ones a candidate over a wide random divisor actually runs into. Each is
  // offered only once -- they are unconditional, so once installed no
  // candidate can contradict them again and re-emitting one would spend a
  // round on a clause the solver already has.
  if (opKind == BVMOD)
  {
    // r <=u a, with no premise at all -- it holds over a zero divisor too,
    // where the remainder is the dividend.
    if (base &&
        (installedSchemas & DIV_SCHEMA_INSTALLED_REMAINDER_AT_MOST_DIVIDEND) ==
            0 &&
        !divSchemaHolds(opKind, DivSchema::RemainderAtMostDividend, 0, aBits,
                        bBits, tBits))
      return {DivSchema::RemainderAtMostDividend, 0};

    // b != 0 -> r <u b.
    if (base &&
        (installedSchemas & DIV_SCHEMA_INSTALLED_REMAINDER_BELOW_DIVISOR) ==
            0 &&
        !divSchemaHolds(opKind, DivSchema::RemainderBelowDivisor, 0, aBits,
                        bBits, tBits))
      return {DivSchema::RemainderBelowDivisor, 0};

    unsigned remCount = 0;
    const BVLemmaEntry<RemLemma>* remTable = remLemmaTable(remCount);
    for (unsigned i = 0; i < remCount; ++i)
    {
      const BVLemmaEntry<RemLemma>& entry = remTable[i];
      if (!bvSchemaGroupEnabled(enabledGroups, entry.group))
        continue;
      if (!entry.applicable(width))
        continue;
      if ((installedSchemas & divLemmaInstalledBit(i)) != 0)
        continue;
      if (!remLemmaHolds(entry.lemma, aBits, bBits, tBits))
        return {DivSchema::Lemma, 0, i, entry.group};
    }
  }
  else if (opKind == BVDIV)
  {
    // b != 0 -> t <=u a.
    if (base &&
        (installedSchemas & DIV_SCHEMA_INSTALLED_QUOTIENT_AT_MOST_DIVIDEND) ==
            0 &&
        !divSchemaHolds(opKind, DivSchema::QuotientAtMostDividend, 0, aBits,
                        bBits, tBits))
      return {DivSchema::QuotientAtMostDividend, 0, 0};

    // Try the ranked, fixed family before the synthesised thresholds below.
    // A W-bit quotient has W-1 distinct threshold facts, so putting that
    // open-ended family first can consume the complete schema-round budget
    // and starve a single stronger fact that would decide the query.
    // Quotients only: every one is about `t = a udiv b`.
    unsigned divCount = 0;
    const BVLemmaEntry<DivLemma>* divTable = divLemmaTable(divCount);
    for (unsigned i = 0; i < divCount; ++i)
    {
      const BVLemmaEntry<DivLemma>& entry = divTable[i];
      if (!bvSchemaGroupEnabled(enabledGroups, entry.group))
        continue;
      if ((installedSchemas & divLemmaInstalledBit(i)) != 0)
        continue;
      if (!entry.applicable(width))
        continue;
      if (!divLemmaHolds(entry.lemma, aBits, bBits, tBits))
        return {DivSchema::Lemma, 0, i, entry.group};
    }

    // Use the candidate divisor's highest set bit as a broad guard:
    // b >= 2^k -> q <= a >> k. This family is deliberately capped at two
    // magnitudes per abstraction, so give it precedence over the open-ended
    // quotient thresholds below. On a query that pins the divisor's binade,
    // the magnitude bound can decide the result in one round; letting the
    // thresholds go first can consume the complete schema allowance before
    // this stronger candidate-specific bound gets a turn.
    if (bvSchemaGroupEnabled(enabledGroups,
                             BVSchemaGroup::DIVISOR_MAGNITUDE) &&
        bvSchemaFamilyHasInstance(installedSchemas,
                                  BVSchemaFamily::DivisorMagnitude))
    {
      int divisorTop = -1;
      for (int i = (int)width - 1; i >= 0; --i)
        if (bBits[i])
        {
          divisorTop = i;
          break;
        }

      if (divisorTop >= 1 &&
          !divSchemaHolds(opKind, DivSchema::DivisorMagnitudeBound,
                          (unsigned)divisorTop, aBits, bBits, tBits))
        return {DivSchema::DivisorMagnitudeBound, (unsigned)divisorTop, 0,
                BVSchemaGroup::DIVISOR_MAGNITUDE};
    }

    // q >= 2^k iff b <= (a >> k). The right side is just a comparison over
    // wires from the dividend; the left side is the OR of q[k..W-1]. Start
    // at one because k=0 is the already-covered q != 0 boundary. No
    // installed bit is needed: once one threshold is in the permanent
    // solver clauses, no later candidate can contradict that same k.
    const auto thresholdMismatch = [&](unsigned k) {
      return !divSchemaHolds(opKind, DivSchema::QuotientPow2Threshold, k, aBits,
                             bBits, tBits);
    };

    // Every threshold below or at q's highest set bit has a true left side;
    // every one above it has a false left side. The real quotient has the
    // same shape, so if their magnitude bands differ, one of the two
    // boundaries around the candidate's band must witness it. Checking only
    // those two keeps schema selection linear in the width rather than
    // comparing W shifted dividends at O(W) apiece.
    int quotientTop = -1;
    for (int i = (int)width - 1; i >= 0; --i)
      if (tBits[i])
      {
        quotientTop = i;
        break;
      }
    if (bvSchemaGroupEnabled(enabledGroups,
                             BVSchemaGroup::QUOTIENT_THRESHOLDS) &&
        bvSchemaFamilyHasInstance(installedSchemas,
                                  BVSchemaFamily::QuotientThreshold))
    {
      if (quotientTop > 0 && thresholdMismatch((unsigned)quotientTop))
        return {DivSchema::QuotientPow2Threshold, (unsigned)quotientTop, 0,
                BVSchemaGroup::QUOTIENT_THRESHOLDS};
      const unsigned above = (quotientTop < 1) ? 1u : (unsigned)quotientTop + 1;
      if (above < width && thresholdMismatch(above))
        return {DivSchema::QuotientPow2Threshold, above, 0,
                BVSchemaGroup::QUOTIENT_THRESHOLDS};
    }
  }

  // ... and the divisor-guarded facts last, where they apply. Each says what
  // the operation *is* for one divisor value, which is more than any bound
  // can say -- but there is one of them per value, which is why they are
  // offered after everything that is offered a bounded number of times. Zero
  // is not a power of two, so the two never contend and the order between
  // them is a formality.
  const bool divisorValueLeft =
      bvSchemaFamilyHasInstance(installedSchemas, BVSchemaFamily::DivisorValue);
  if (base && divisorValueLeft && divisorZero)
  {
    const DivSchemaChoice choice{DivSchema::DivisorZero, 0};
    if (!divSchemaHolds(opKind, choice.schema, choice.shift, aBits, bBits,
                        tBits))
      return choice;
  }
  else if (base && divisorValueLeft)
  {
    const int k = powerOfTwoExponent(bBits);
    if (k >= 0)
    {
      const DivSchemaChoice choice{DivSchema::Pow2Divisor, (unsigned)k};
      if (!divSchemaHolds(opKind, choice.schema, choice.shift, aBits, bBits,
                          tBits))
        return choice;
    }
  }

  return DivSchemaChoice();
}

static const char* divSchemaName(DivSchema schema)
{
  switch (schema)
  {
    case DivSchema::DivisorZero: return "zero-divisor";
    case DivSchema::Pow2Divisor: return "power-of-two-divisor";
    case DivSchema::RemainderAtMostDividend: return "remainder-at-most-dividend";
    case DivSchema::RemainderBelowDivisor: return "remainder-below-divisor";
    case DivSchema::QuotientAtMostDividend: return "quotient-at-most-dividend";
    case DivSchema::QuotientPow2Threshold:
      return "power-of-two-quotient-threshold";
    case DivSchema::DivisorMagnitudeBound:
      return "divisor-magnitude-bound";
    case DivSchema::Lemma: return "lemma";
    case DivSchema::None: break;
  }
  return "none";
}

// How far past the lowest wrong bit a piece-at-a-time escalation reaches.
// A fixed 32-bit step; there is no measurement behind this value, which is
// part of why the flag that reaches it is off.
static const unsigned BV_INC_BITBLAST_STEP = 32;

// The operation again, narrowed to its low `upto` bits.
//
// The low bits of a truncated product depend only on the low bits of its
// operands, so `t[u:0] = (a[u:0] * b[u:0])[u:0]` is a theorem about the
// whole multiplication rather than an approximation of it -- which is what
// lets a piece of the encoding be installed and the rest left for later.
// The narrowed operands are real extracts and not merely a smaller width
// passed alongside the same node, because the multiplier reads its operands
// for constant detection and Booth recoding and would read the wrong values
// out of the wider ones.
//
// A null node comes back where the narrowing does not leave a
// multiplication standing -- the factory folds a product of two constants,
// which cannot reach here from a query the simplifier has been over, but
// costs one branch to be sure of. The caller encodes the whole width
// instead.
static ASTNode narrowedProduct(STPMgr* bm, const ASTNode& term, unsigned upto)
{
  NodeFactory* nf = bm->defaultNodeFactory;
  const ASTNode high = bm->CreateBVConst(32, upto - 1);
  const ASTNode low = bm->CreateZeroConst(32);

  ASTNode operands[2];
  for (unsigned i = 0; i < 2; ++i)
    operands[i] = (term[i].GetValueWidth() == upto)
                      ? term[i]
                      : nf->CreateTerm(BVEXTRACT, upto, term[i], high, low);

  const ASTNode narrowed =
      nf->CreateTerm(BVMULT, upto, operands[0], operands[1]);
  return narrowed.GetKind() == BVMULT ? narrowed : ASTNode();
}

unsigned valueLemmaAllowance(const UserDefinedFlags& uf, unsigned width)
{
  const unsigned ceiling = uf.bv_term_abstraction_rounds;
  if (ceiling == 0)
    return 0; // never escalate: enumerate without limit

  const unsigned divisor = uf.bv_term_abstraction_value_divisor;
  unsigned allowance = ceiling;
  if (divisor != 0)
  {
    // At least one. A rate that rounds to nothing would escalate before the
    // abstraction has been given a single chance to pay, which is not what
    // "scale it with the width" is meant to mean at narrow widths -- and
    // width zero does not occur, since the type checker gives every operation
    // a width and the abstraction has a floor besides.
    const unsigned scaled = width / divisor;
    allowance = std::min(allowance, scaled == 0 ? 1u : scaled);
  }

  return allowance;
}

unsigned valueLemmaAllowance(const UserDefinedFlags& uf, unsigned width,
                             Kind opKind)
{
  unsigned allowance = valueLemmaAllowance(uf, width);
  if (allowance == 0 || (opKind != BVDIV && opKind != BVMOD))
    return allowance;

  // Unlike the round ceiling, this does not alter how many algebraic schemas
  // a record may receive, and unlike the older width scaling it does not alter
  // BVMULT. It isolates the wide divider candidates which motivated the
  // experiment. Zero deliberately means absent rather than "escalate
  // immediately", leaving rounds=0 as the one spelling of never escalating.
  const unsigned valueLimit =
      uf.bv_term_abstraction_divmod_value_limit;
  return valueLimit == 0 ? allowance : std::min(allowance, valueLimit);
}

// A BVDIV and a BVMOD over the same operands at the same width carry a
// relation neither record can state alone. Finding them is the same question
// for the refinement that installs the relation and the diagnostic that
// reports it, so it is asked once, here.
//
// Node numbers are unique within the manager and the width is part of the
// key, so only genuinely identical operations meet. Records are keyed by
// insertion, and the map is walked in that order below, so the pairing a run
// produces does not depend on the hash.
namespace
{
struct DivRemPairKey
{
  uint64_t dividend;
  uint64_t divisor;
  unsigned width;

  bool operator==(const DivRemPairKey& other) const
  {
    return dividend == other.dividend && divisor == other.divisor &&
           width == other.width;
  }
};

struct DivRemPairKeyHash
{
  size_t operator()(const DivRemPairKey& key) const
  {
    size_t h = std::hash<uint64_t>{}(key.dividend);
    h ^= std::hash<uint64_t>{}(key.divisor) + 0x9e3779b9u + (h << 6) + (h >> 2);
    h ^= std::hash<unsigned>{}(key.width) + 0x9e3779b9u + (h << 6) + (h >> 2);
    return h;
  }
};
} // namespace

std::vector<BVAbstractionRefiner::DivRemPair>
BVAbstractionRefiner::divRemPairs(
    const std::vector<BVTermAbstraction>& terms,
    const std::vector<size_t>* selected)
{
  const size_t missing = std::numeric_limits<size_t>::max();
  std::unordered_map<DivRemPairKey, DivRemPair, DivRemPairKeyHash> found;
  std::vector<DivRemPairKey> order;

  const size_t count = selectedSize(terms.size(), selected);
  for (size_t position = 0; position < count; ++position)
  {
    const size_t idx = selectedIndex(position, selected);
    assert(idx < terms.size());
    const BVTermAbstraction& abs = terms[idx];
    if (abs.opKind != BVDIV && abs.opKind != BVMOD)
      continue;
    assert(abs.numOperands == 2);
    const DivRemPairKey key{abs.operands[0].GetNodeNum(),
                            abs.operands[1].GetNodeNum(), abs.width};
    auto it = found.find(key);
    if (it == found.end())
    {
      it = found.insert({key, DivRemPair{missing, missing}}).first;
      order.push_back(key);
    }
    if (abs.opKind == BVDIV)
      it->second.divIdx = idx;
    else
      it->second.remIdx = idx;
  }

  std::vector<DivRemPair> pairs;
  for (const DivRemPairKey& key : order)
  {
    const DivRemPair& pair = found[key];
    if (pair.divIdx != missing && pair.remIdx != missing)
      pairs.push_back(pair);
  }
  return pairs;
}

void BVAbstractionRefiner::reportRecords(std::ostream& out) const
{
  std::vector<bool> isPaired(terms_.size(), false);
  for (const DivRemPair& pair : divRemPairs(terms_))
  {
    isPaired[pair.divIdx] = true;
    isPaired[pair.remIdx] = true;
  }

  for (size_t i = 0; i < terms_.size(); ++i)
  {
    const BVTermAbstraction& abs = terms_[i];
    const bool paired = isPaired[i];
    const char* state = "open";
    if (abs.defined)
      state = abs.exactEscalations == 0 ? "defined" : "exact";
    else if (abs.blastedBits != 0)
      state = "partial";

    // Each value-pair block emits W clauses containing both W-bit operands
    // and one result bit. These derived counts expose the accumulated SAT
    // payload without adding bookkeeping to the hot path.
    const uint64_t blockingClauses =
        static_cast<uint64_t>(abs.blockedRounds) * abs.width;
    const uint64_t blockingLiterals =
        blockingClauses * (2 * static_cast<uint64_t>(abs.width) + 1);
    const bool hasValueAllowance =
        abs.opKind == BVMULT || abs.opKind == BVDIV || abs.opKind == BVMOD;
    const unsigned allowance =
        hasValueAllowance
            ? valueLemmaAllowance(bm->UserFlags, abs.width, abs.opKind)
            : 0;

    out << "BV abstraction record: record=" << i
        << " node=" << abs.termNode.GetNodeNum()
        << " kind=" << _kind_names[abs.opKind] << " width=" << abs.width
        << " state=" << state << " blocking=" << abs.blockedRounds
        << " schemas=" << abs.schemaRounds
        << " exact=" << abs.exactEscalations
        << " exact-bits=" << abs.blastedBits
        << " allowance=" << allowance
        << " paired=" << (paired ? 1 : 0)
        << " pair-full=" << (abs.divRemFullInstalled ? 1 : 0)
        << " blocking-clauses=" << blockingClauses
        << " blocking-literals=" << blockingLiterals
        << " exact-clauses=" << abs.exactClauses
        << " exact-vars=" << abs.exactVariables
        << " exact-us=" << abs.exactMicroseconds << '\n';
  }
}

static const char* mulSchemaName(MulSchema schema)
{
  switch (schema)
  {
    case MulSchema::Odd: return "odd";
    case MulSchema::TrailingZeros: return "trailing-zeros";
    case MulSchema::Pow2: return "power-of-two";
    case MulSchema::NegPow2: return "negated-power-of-two";
    case MulSchema::LowPrefix: return "exact-low-prefix";
    case MulSchema::Lemma: return "lemma";
    case MulSchema::None: break;
  }
  return "none";
}

// result[0] <-> a[0] & b[0].
void encodeMulOdd(SATSolver& solver, const std::vector<unsigned>& a,
                  const std::vector<unsigned>& b,
                  const std::vector<unsigned>& result)
{
  SATSolver::vec_literals cl;
  cl.clear(); cl.push(SATSolver::mkLit(result[0], true));  cl.push(SATSolver::mkLit(a[0], false)); solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(result[0], true));  cl.push(SATSolver::mkLit(b[0], false)); solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(result[0], false)); cl.push(SATSolver::mkLit(a[0], true)); cl.push(SATSolver::mkLit(b[0], true)); solver.addClause(cl);
}

void encodeAddLowPrefix(SATSolver& solver,
                        const std::vector<unsigned>& aVars,
                        const std::vector<unsigned>& bVars,
                        const std::vector<unsigned>& resultVars,
                        [[maybe_unused]] unsigned width, unsigned prefixBits,
                        bool aNegated, bool bNegated)
{
  assert(width > 0);
  assert(prefixBits > 0 && prefixBits <= width);
  assert(aVars.size() >= width);
  assert(bVars.size() >= width);
  assert(resultVars.size() >= width);
  assert(!(aNegated && bNegated));

  unsigned carryVar = pinnedVar(solver, aNegated != bNegated);
  for (unsigned bit = 0; bit < prefixBits; ++bit)
  {
    const unsigned a = aVars[bit];
    const unsigned b = bVars[bit];
    const unsigned result = resultVars[bit];
    const unsigned carry = carryVar;
    SATSolver::vec_literals cl;

    for (unsigned row = 0; row < 8; ++row)
    {
      const bool aBit = (row & 1) != 0;
      const bool bBit = (row & 2) != 0;
      const bool carryBit = (row & 4) != 0;
      const bool sum = (aBit != bBit) != carryBit;
      cl.clear();
      cl.push(SATSolver::mkLit(a, aBit != aNegated));
      cl.push(SATSolver::mkLit(b, bBit != bNegated));
      cl.push(SATSolver::mkLit(carry, carryBit));
      cl.push(SATSolver::mkLit(result, !sum));
      solver.addClause(cl);
    }

    if (bit + 1 < prefixBits)
    {
      const unsigned nextCarry = freshVar(solver);
      cl.clear(); cl.push(SATSolver::mkLit(a,aNegated));   cl.push(SATSolver::mkLit(b,bNegated));   cl.push(SATSolver::mkLit(nextCarry,true)); solver.addClause(cl);
      cl.clear(); cl.push(SATSolver::mkLit(a,aNegated));   cl.push(SATSolver::mkLit(carry,false));  cl.push(SATSolver::mkLit(nextCarry,true)); solver.addClause(cl);
      cl.clear(); cl.push(SATSolver::mkLit(b,bNegated));   cl.push(SATSolver::mkLit(carry,false));  cl.push(SATSolver::mkLit(nextCarry,true)); solver.addClause(cl);
      cl.clear(); cl.push(SATSolver::mkLit(a,!aNegated));  cl.push(SATSolver::mkLit(b,!bNegated));  cl.push(SATSolver::mkLit(nextCarry,false)); solver.addClause(cl);
      cl.clear(); cl.push(SATSolver::mkLit(a,!aNegated));  cl.push(SATSolver::mkLit(carry,true));   cl.push(SATSolver::mkLit(nextCarry,false)); solver.addClause(cl);
      cl.clear(); cl.push(SATSolver::mkLit(b,!bNegated));  cl.push(SATSolver::mkLit(carry,true));   cl.push(SATSolver::mkLit(nextCarry,false)); solver.addClause(cl);
      carryVar = nextCarry;
    }
  }
}

void encodeMulLowPrefix(SATSolver& solver,
                        const std::vector<unsigned>& aVars,
                        const std::vector<unsigned>& bVars,
                        const std::vector<unsigned>& resultVars,
                        [[maybe_unused]] unsigned width, unsigned prefixBits)
{
  assert(width > 0);
  assert(prefixBits > 0 && prefixBits <= width && prefixBits <= 3);
  assert(aVars.size() >= width);
  assert(bVars.size() >= width);
  assert(resultVars.size() >= width);

  const unsigned p00 = mkAnd(solver, aVars[0], bVars[0]);
  addEquivalence(solver, resultVars[0], p00);
  if (prefixBits == 1)
    return;

  const unsigned p10 = mkAnd(solver, aVars[1], bVars[0]);
  const unsigned p01 = mkAnd(solver, aVars[0], bVars[1]);
  addEquivalence(solver, resultVars[1], mkXor(solver, p10, p01));
  if (prefixBits == 2)
    return;

  // Column two consists of its three partial products plus the carry from
  // column one. Carries out of it are above the prefix and need not exist.
  const unsigned carry1 = mkAnd(solver, p10, p01);
  const unsigned p20 = mkAnd(solver, aVars[2], bVars[0]);
  const unsigned p11 = mkAnd(solver, aVars[1], bVars[1]);
  const unsigned p02 = mkAnd(solver, aVars[0], bVars[2]);
  const unsigned x0 = mkXor(solver, p20, p11);
  const unsigned x1 = mkXor(solver, p02, carry1);
  addEquivalence(solver, resultVars[2], mkXor(solver, x0, x1));
}

// result[i] -> some bit of `op` at or below i, one clause per bit. The
// product cannot have fewer trailing zeros than an operand, and truncating
// it to the width does not change its low bits, so this holds of the
// truncated product too.
void encodeMulTrailingZeros(SATSolver& solver, const std::vector<unsigned>& op,
                            const std::vector<unsigned>& result,
                            unsigned width)
{
  for (unsigned bit = 0; bit < width; ++bit)
  {
    SATSolver::vec_literals cl;
    cl.push(SATSolver::mkLit(result[bit], true));
    for (unsigned j = 0; j <= bit; ++j)
      cl.push(SATSolver::mkLit(op[j], false));
    solver.addClause(cl);
  }
}

// fixed = fixedBits -> result = source << shift.
//
// The premise is the very disjunction a blocking lemma opens with -- false
// exactly on the candidate's own operand value -- and that is the whole
// difference between the two: this leaves the other operand free, so it
// rules out 2^W pairs where the blocking lemma rules out one.
void encodeMulShiftUnderValue(SATSolver& solver,
                              const std::vector<unsigned>& fixedVars,
                              const std::vector<bool>& fixedBits,
                              const std::vector<unsigned>& source,
                              const std::vector<unsigned>& result,
                              unsigned width, unsigned shift)
{
  const auto guard = [&](SATSolver::vec_literals& cl) {
    cl.clear();
    for (unsigned i = 0; i < width; ++i)
      cl.push(SATSolver::mkLit(fixedVars[i], fixedBits[i]));
  };

  SATSolver::vec_literals cl;
  for (unsigned bit = 0; bit < width; ++bit)
  {
    if (bit < shift)
    {
      // Shifted in from below: zero, whatever the source holds.
      guard(cl);
      cl.push(SATSolver::mkLit(result[bit], true));
      solver.addClause(cl);
      continue;
    }

    const unsigned src = source[bit - shift];
    guard(cl);
    cl.push(SATSolver::mkLit(result[bit], true));
    cl.push(SATSolver::mkLit(src, false));
    solver.addClause(cl);

    guard(cl);
    cl.push(SATSolver::mkLit(result[bit], false));
    cl.push(SATSolver::mkLit(src, true));
    solver.addClause(cl);
  }
}

// divisor = divisorBits -> every result bit is a constant or a bit of the
// dividend, as `source` says.
//
// The premise is the blocking lemma's opening disjunction, exactly as the
// multiplication schemas use it: false only on the candidate's own divisor,
// and leaving the dividend entirely free. That is what makes one of these
// worth 2^W blocking lemmas over the same divisor.
// A variable that holds exactly when `lv <= rv`, over the operand bits
// already in the solver.
//
// From the least significant bit up, so that the most significant
// *differing* bit is the one that decides. Each step keeps the accumulator
// when the two bits agree and overrides it when they differ, so whichever
// bit is visited last among the differing ones settles the answer -- which
// is the top one only in this direction. Run downwards, as this once was,
// the bottom differing bit won instead, and the chain answered something
// that is not a comparison at all: it disagreed with `a <= b` on 31616 of
// the 65536 pairs of eight-bit values. The lemma then pinned the abstraction
// to that, and a query whose comparison the pinned value contradicted came
// back unsat.
//
// The sign bit is therefore also the last step, which is where flipping its
// sense belongs: for a signed comparison a leading 1 is the smaller side, so
// the roles of the two operands invert at that bit alone.
//
// The accumulator starts true, which is what makes this `<=` rather than
// `<`: two equal operands never reach a differing bit, so nothing overrides
// it.
unsigned encodeLessOrEqual(SATSolver& solver, const std::vector<unsigned>& lv,
                           const std::vector<unsigned>& rv, unsigned width,
                           bool isSigned)
{
  unsigned carryVar = solver.newVar();
  solver.setFrozen(carryVar);
  {
    SATSolver::vec_literals cl;
    cl.push(SATSolver::mkLit(carryVar, false));
    solver.addClause(cl);
  }

  for (int bit = 0; bit < (int)width; ++bit)
  {
    unsigned a = lv[bit];
    unsigned b = rv[bit];
    bool flipSign = (isSigned && bit == (int)width - 1);

    auto xP = SATSolver::mkLit(a, !flipSign);
    auto xN = SATSolver::mkLit(a, flipSign);
    auto yP = SATSolver::mkLit(b, flipSign);
    auto yN = SATSolver::mkLit(b, !flipSign);
    auto zP = SATSolver::mkLit(carryVar, false);
    auto zN = SATSolver::mkLit(carryVar, true);

    unsigned nc = solver.newVar();
    solver.setFrozen(nc);

    SATSolver::vec_literals cl;
    cl.clear(); cl.push(xN); cl.push(yN); cl.push(SATSolver::mkLit(nc, false)); solver.addClause(cl);
    cl.clear(); cl.push(xN); cl.push(zN); cl.push(SATSolver::mkLit(nc, false)); solver.addClause(cl);
    cl.clear(); cl.push(yN); cl.push(zN); cl.push(SATSolver::mkLit(nc, false)); solver.addClause(cl);
    cl.clear(); cl.push(xP); cl.push(yP); cl.push(SATSolver::mkLit(nc, true)); solver.addClause(cl);
    cl.clear(); cl.push(xP); cl.push(zP); cl.push(SATSolver::mkLit(nc, true)); solver.addClause(cl);
    cl.clear(); cl.push(yP); cl.push(zP); cl.push(SATSolver::mkLit(nc, true)); solver.addClause(cl);

    carryVar = nc;
  }

  return carryVar;
}

// The three bounds, each written straight onto the comparison chain.
//
// Where a bound carries the premise `b != 0`, it is spent as its
// contrapositive rather than through a fresh variable standing for the
// premise: `b != 0 -> P` is `not P -> b = 0`, and `b = 0` is a conjunction,
// so what goes in is one binary clause per divisor bit. No definition, no
// extra variable, and the solver sees the premise on every bit rather than
// behind one literal it has to reason through.
void encodeDivBound(SATSolver& solver, DivSchema schema,
                           const std::vector<unsigned>& dividendVars,
                           const std::vector<unsigned>& divisorVars,
                           const std::vector<unsigned>& resultVars,
                           unsigned width)
{
  SATSolver::vec_literals cl;

  // A switch, and not two tests and a fall-through. Every other dispatch over
  // these enumerators in this file is one, so a new bound breaks the build
  // rather than arriving somewhere; this one silently encoded the remainder
  // bound for whatever it was not asked about, which is a clause that is
  // still a theorem and still the wrong fact -- installed, counted as the
  // schema the chooser picked, and leaving that schema's own violation
  // unaddressed so the round bought nothing.
  switch (schema)
  {
    case DivSchema::RemainderAtMostDividend:
    {
      // r <= a, unconditionally: a unit clause on the chain's answer.
      const unsigned le =
          encodeLessOrEqual(solver, resultVars, dividendVars, width, false);
      cl.clear();
      cl.push(SATSolver::mkLit(le, false));
      solver.addClause(cl);
      return;
    }

    case DivSchema::QuotientAtMostDividend:
    {
      // b != 0 -> t <= a, i.e. t > a -> b = 0.
      const unsigned le =
          encodeLessOrEqual(solver, resultVars, dividendVars, width, false);
      for (unsigned i = 0; i < width; ++i)
      {
        cl.clear();
        cl.push(SATSolver::mkLit(le, false));
        cl.push(SATSolver::mkLit(divisorVars[i], true));
        solver.addClause(cl);
      }
      return;
    }

    case DivSchema::RemainderBelowDivisor:
    {
      // b != 0 -> r < b. `r < b` is `not (b <= r)`, so the chain is run the
      // other way round and its answer is the one that must be false.
      const unsigned bLeR =
          encodeLessOrEqual(solver, divisorVars, resultVars, width, false);
      for (unsigned i = 0; i < width; ++i)
      {
        cl.clear();
        cl.push(SATSolver::mkLit(bLeR, true));
        cl.push(SATSolver::mkLit(divisorVars[i], true));
        solver.addClause(cl);
      }
      return;
    }

    case DivSchema::None:
    case DivSchema::DivisorZero:
    case DivSchema::Pow2Divisor:
    case DivSchema::QuotientPow2Threshold:
    case DivSchema::DivisorMagnitudeBound:
    case DivSchema::Lemma:
      break;
  }

  FatalError("encodeDivBound: asked for a schema that is not one of the "
             "three bounds");
}

void encodeDivPow2Threshold(SATSolver& solver,
                            const std::vector<unsigned>& dividendVars,
                            const std::vector<unsigned>& divisorVars,
                            const std::vector<unsigned>& quotientVars,
                            unsigned width, unsigned shift)
{
  assert(width > 1);
  assert(shift > 0 && shift < width);
  assert(dividendVars.size() >= width);
  assert(divisorVars.size() >= width);
  assert(quotientVars.size() >= width);

  // Keep the comparison width unchanged: a divisor with any bit at or above
  // W-k cannot be <= the shifted dividend. The high zero is shared by all
  // of those positions.
  const unsigned zero = pinnedVar(solver, false);
  std::vector<unsigned> shiftedDividend(width, zero);
  for (unsigned i = 0; i + shift < width; ++i)
    shiftedDividend[i] = dividendVars[i + shift];

  const unsigned divisorBelowShiftedDividend = encodeLessOrEqual(
      solver, divisorVars, shiftedDividend, width, false);

  SATSolver::vec_literals cl;
  // comparison -> OR(quotient[shift..W-1])
  cl.push(SATSolver::mkLit(divisorBelowShiftedDividend, true));
  for (unsigned i = shift; i < width; ++i)
    cl.push(SATSolver::mkLit(quotientVars[i], false));
  solver.addClause(cl);

  // Each high quotient bit -> comparison. Together with the clause above,
  // these make the reduction-OR and the comparison equivalent without an
  // extra variable for the OR.
  for (unsigned i = shift; i < width; ++i)
  {
    cl.clear();
    cl.push(SATSolver::mkLit(quotientVars[i], true));
    cl.push(SATSolver::mkLit(divisorBelowShiftedDividend, false));
    solver.addClause(cl);
  }
}

void encodeDivisorMagnitudeBound(
    SATSolver& solver, const std::vector<unsigned>& dividendVars,
    const std::vector<unsigned>& divisorVars,
    const std::vector<unsigned>& quotientVars, unsigned width,
    unsigned shift)
{
  assert(width > 1);
  assert(shift > 0 && shift < width);
  assert(dividendVars.size() >= width);
  assert(divisorVars.size() >= width);
  assert(quotientVars.size() >= width);

  const unsigned zero = pinnedVar(solver, false);
  std::vector<unsigned> shiftedDividend(width, zero);
  for (unsigned i = 0; i + shift < width; ++i)
    shiftedDividend[i] = dividendVars[i + shift];

  const unsigned quotientBelowShiftedDividend = encodeLessOrEqual(
      solver, quotientVars, shiftedDividend, width, false);

  // b >= 2^shift is the disjunction of b[shift..W-1]. Its implication to
  // the comparison is one binary clause per possible witnessing bit, which
  // exposes the guard directly to the SAT solver without an auxiliary OR.
  for (unsigned i = shift; i < width; ++i)
  {
    SATSolver::vec_literals cl;
    cl.push(SATSolver::mkLit(quotientBelowShiftedDividend, false));
    cl.push(SATSolver::mkLit(divisorVars[i], true));
    solver.addClause(cl);
  }
}

void encodeDivUnderDivisorValue(
    SATSolver& solver, const std::vector<unsigned>& divisorVars,
    const std::vector<bool>& divisorBits,
    const std::vector<unsigned>& dividendVars,
    const std::vector<unsigned>& resultVars, unsigned width,
    const std::vector<int>& source)
{
  const auto guard = [&](SATSolver::vec_literals& cl) {
    cl.clear();
    for (unsigned i = 0; i < width; ++i)
      cl.push(SATSolver::mkLit(divisorVars[i], divisorBits[i]));
  };

  SATSolver::vec_literals cl;
  for (unsigned bit = 0; bit < width; ++bit)
  {
    if (source[bit] == DIV_SOURCE_ZERO || source[bit] == DIV_SOURCE_ONE)
    {
      guard(cl);
      cl.push(SATSolver::mkLit(resultVars[bit], source[bit] == DIV_SOURCE_ZERO));
      solver.addClause(cl);
      continue;
    }

    const unsigned src = dividendVars[source[bit]];
    guard(cl);
    cl.push(SATSolver::mkLit(resultVars[bit], true));
    cl.push(SATSolver::mkLit(src, false));
    solver.addClause(cl);

    guard(cl);
    cl.push(SATSolver::mkLit(resultVars[bit], false));
    cl.push(SATSolver::mkLit(src, true));
    solver.addClause(cl);
  }
}

AbstractionRefinementResult BVAbstractionRefiner::refineTerms(
    SATSolver& solver, const ToSATBase::ASTNodeToSATVar& nodeToSATVar,
    const std::vector<size_t>* selected)
{
  // Phase 1: Scan all abstractions, reading model values to find inconsistencies.
  // Cache the data needed for clause generation so we don't need modelValue later.
  struct InconsistentCmp {
    size_t absIdx;
    bool swapOps, negateResult, isSigned;
  };
  struct InconsistentPlus {
    size_t absIdx;
    AddSchemaChoice schema;
  };
  struct InconsistentITE {
    size_t absIdx;
  };
  struct InconsistentDivMul {
    size_t absIdx;
    std::vector<bool> aBits, bBits, expected;
    // The algebraic fact this candidate contradicts, if any. Decided here
    // rather than below because it is read off the model and the clause
    // phase must not touch the model. At most one of the two is ever set:
    // an abstraction is a multiplication or a division, never both.
    MulSchemaChoice schema;
    DivSchemaChoice divSchema;
    // The lowest bit the candidate's result got wrong, which is where a
    // piece-at-a-time escalation starts from. Always below the width: this
    // record exists because some bit is wrong.
    unsigned lowestWrongBit;
  };
  struct InconsistentDivRemPair {
    size_t divIdx;
    size_t remIdx;
    ASTNode product;
  };

  std::vector<InconsistentCmp> incCmps;
  std::vector<InconsistentPlus> incPlus;
  std::vector<InconsistentITE> incITE;
  std::vector<InconsistentDivMul> incDivMul;
  std::vector<InconsistentDivRemPair> incDivRemPairs;
  std::unordered_set<size_t> handledByDivRemPair;

  // A quotient and remainder over the same operands carry a relation neither
  // abstraction can state alone. Find those pairs by AST identity before the
  // per-record scan, and give a violated recomposition fact first refusal for
  // this round. Node numbers are unique within the manager and the width is
  // part of the key, so only genuinely identical operations meet here.
  if (bm->UserFlags.bv_term_abstraction_schemas &&
      bvSchemaGroupEnabled(bm->UserFlags.bv_term_abstraction_schema_groups,
                           BVSchemaGroup::DIVREM_FULL))
  {
    for (const DivRemPair& pair : divRemPairs(terms_, selected))
    {
      BVTermAbstraction& div = terms_[pair.divIdx];
      BVTermAbstraction& rem = terms_[pair.remIdx];
      // Two exact records cannot disagree with the relation between them, so
      // there is nothing here to read a model for.
      if (div.defined && rem.defined)
        continue;
      if (div.divRemFullInstalled || rem.divRemFullInstalled ||
          div.divRemFullRefused || rem.divRemFullRefused)
        continue;
      prepareTermForQuery(div);
      prepareTermForQuery(rem);
      const unsigned schemaLimit = bm->UserFlags.bv_term_abstraction_rounds;
      if (schemaLimit != 0 &&
          (div.schemasThisQuery >= schemaLimit ||
           rem.schemasThisQuery >= schemaLimit))
        continue;

      std::vector<bool> dividendBits, divisorBits, quotientBits, remainderBits;
      getOperandBits(div.operands[0], div.width, nodeToSATVar, solver,
                     dividendBits);
      getOperandBits(div.operands[1], div.width, nodeToSATVar, solver,
                     divisorBits);
      readModelBits(encodedResultBitsOf(div, nodeToSATVar), div.width, solver,
                    quotientBits);
      readModelBits(encodedResultBitsOf(rem, nodeToSATVar), rem.width, solver,
                    remainderBits);

      if (divRemIdentityHolds(dividendBits, divisorBits, quotientBits,
                              remainderBits))
        continue;

      const ASTNode product = bm->defaultNodeFactory->CreateTerm(
          BVMULT, div.width, div.termNode, div.operands[1]);
      // A folded product leaves no multiplication circuit worth splicing.
      // The individual schemas and fallback below remain available.
      if (product.GetKind() != BVMULT)
        continue;

      incDivRemPairs.push_back({pair.divIdx, pair.remIdx, product});
      handledByDivRemPair.insert(pair.divIdx);
      handledByDivRemPair.insert(pair.remIdx);
    }
  }

  const size_t selectedTermCount = selectedSize(terms_.size(), selected);
  for (size_t position = 0; position < selectedTermCount; ++position)
  {
    const size_t idx = selectedIndex(position, selected);
    assert(idx < terms_.size());
    auto& abs = terms_[idx];
    if (abs.defined)
      continue;
    prepareTermForQuery(abs);

    if (isBVCompare(abs.opKind))
    {
      const unsigned condVar = recordedVar(
          abs.condSATVar, abs.termNode,
          "BV abstraction: an abstracted comparison has no input carrying "
          "its answer: ");

      std::vector<bool> aBits, bBits;
      getOperandBits(abs.operands[0], abs.width, nodeToSATVar, solver, aBits);
      getOperandBits(abs.operands[1], abs.width, nodeToSATVar, solver, bBits);

      bool expected = computeBVCompare(abs.opKind, aBits, bBits);
      bool actual = (solver.modelValue(condVar) == solver.true_literal());
      if (expected == actual)
        continue;

      // The same three answers computeBVCompare just used, taken from the
      // same place rather than restated here.
      const CompareForm form = comparisonForm(abs.opKind);

      incCmps.push_back({idx, form.swapOps, form.negateResult, form.isSigned});
      continue;
    }

    const std::vector<unsigned>& resultVars =
        encodedResultBitsOf(abs, nodeToSATVar);

    if (abs.opKind == BVPLUS)
    {
      std::vector<bool> leftBits, rightBits;
      getOperandBits(abs.operands[0], abs.width, nodeToSATVar, solver, leftBits);
      getOperandBits(abs.operands[1], abs.width, nodeToSATVar, solver, rightBits);

      const bool lNeg = abs.operandNegated[0];
      const bool rNeg = abs.operandNegated[1];
      const bool carryInit = (lNeg != rNeg);

      bool carry = carryInit;
      bool consistent = true;
      std::vector<bool> actual(abs.width);
      for (unsigned bit = 0; bit < abs.width; ++bit)
      {
        bool l = leftBits[bit] ^ lNeg;
        bool r = rightBits[bit] ^ rNeg;
        bool s = (solver.modelValue(resultVars[bit]) == solver.true_literal());
        actual[bit] = s;
        bool expectedSum = l ^ r ^ carry;
        carry = (l && r) || (l && carry) || (r && carry);
        if (s != expectedSum)
          consistent = false;
      }
      if (consistent) continue;

      if (lNeg)
        leftBits = negatedValue(leftBits);
      if (rNeg)
        rightBits = negatedValue(rightBits);

      AddSchemaChoice schema;
      const unsigned schemaLimit = bm->UserFlags.bv_term_abstraction_rounds;
      if (bm->UserFlags.bv_term_abstraction_schemas &&
          (schemaLimit == 0 || abs.schemasThisQuery < schemaLimit))
        schema =
            chooseAddSchema(leftBits, rightBits, actual, abs.installedSchemas,
                            bm->UserFlags.bv_term_abstraction_schema_groups);

      incPlus.push_back({idx, schema});
    }
    else if (abs.opKind == ITE)
    {
      const unsigned condVar = recordedVar(
          abs.condSATVar, abs.termNode,
          "BV abstraction: an abstracted if-then-else has no input carrying "
          "its condition: ");

      bool condVal = (solver.modelValue(condVar) == solver.true_literal());
      unsigned branchIdx = condVal ? 1 : 2;
      std::vector<bool> branchBits;
      getOperandBits(abs.operands[branchIdx], abs.width, nodeToSATVar, solver,
                     branchBits);

      bool consistent = true;
      for (unsigned bit = 0; bit < abs.width; ++bit)
      {
        bool r = (solver.modelValue(resultVars[bit]) == solver.true_literal());
        if (r != branchBits[bit]) { consistent = false; break; }
      }
      if (consistent) continue;

      incITE.push_back({idx});
    }
    else if (abs.opKind == BVMULT || abs.opKind == BVDIV || abs.opKind == BVMOD)
    {
      std::vector<bool> aBits, bBits;
      getOperandBits(abs.operands[0], abs.width, nodeToSATVar, solver, aBits);
      getOperandBits(abs.operands[1], abs.width, nodeToSATVar, solver, bBits);

      unsigned W = abs.width;
      // What the operation really is at these operand values. This is the
      // oracle the whole loop rests on -- a candidate is faithful exactly
      // when its result matches it -- so it is STP's own constant evaluator
      // rather than a second implementation kept here. The one that used to
      // be here answered zero for a division by zero, which SMT-LIB totalises
      // to all ones, and called a bogus candidate consistent for it; the
      // evaluator gets that by construction, along with the remainder's
      // different totalisation, and is the same code every constant fold in
      // the solver goes through.
      const std::vector<bool> expected =
          bvOperationValue(abs.opKind, aBits, bBits);

      // Read out in full rather than stopping at the first disagreement:
      // the schemas below are chosen by what the candidate's own product
      // *is*, not merely by the fact that it is wrong.
      std::vector<bool> actual(W);
      for (unsigned bit = 0; bit < W; ++bit)
        actual[bit] =
            (solver.modelValue(resultVars[bit]) == solver.true_literal());

      unsigned lowestWrongBit = W;
      for (unsigned bit = 0; bit < W; ++bit)
        if (actual[bit] != expected[bit]) { lowestWrongBit = bit; break; }
      if (lowestWrongBit == W) continue;

      // Only while there is allowance left. Schemas are spent from a
      // separate purse: one is both cheaper and stronger than a blocking
      // lemma, so it should not bring the escalation forward -- but it must
      // not push it out of reach either, and a candidate that keeps landing
      // on fresh powers of two would buy a solve for each one. The bound is
      // the flat ceiling rather than the width-scaled allowance below,
      // because what makes that allowance narrow is exactly what a schema
      // does not suffer from: a blocking lemma is worth less as the
      // operands widen, and a fact about every pair is worth the same.
      //
      // Multiplication and division draw on the same purse and are asked
      // separately, because what they can say about a candidate has nothing
      // in common: the multiplication facts are about the low bits of a
      // product and the commutativity that gives each of them two readings,
      // and the division facts are about one divisor at a time.
      MulSchemaChoice schema;
      DivSchemaChoice divSchema;
      const unsigned schemaLimit = bm->UserFlags.bv_term_abstraction_rounds;
      const bool schemaAllowance =
          bm->UserFlags.bv_term_abstraction_schemas &&
          (schemaLimit == 0 || abs.schemasThisQuery < schemaLimit);
      if (schemaAllowance)
      {
        if (abs.opKind == BVMULT)
          schema =
              chooseMulSchema(aBits, bBits, actual, abs.installedSchemas,
                              bm->UserFlags.bv_term_abstraction_schema_groups);
        else
          divSchema = chooseDivSchema(
              abs.opKind, aBits, bBits, actual, abs.installedSchemas,
              bm->UserFlags.bv_term_abstraction_schema_groups);
      }

      incDivMul.push_back({idx, std::move(aBits), std::move(bBits),
                            std::move(expected), schema, divSchema,
                            lowestWrongBit});
    }
    else
    {
      // Falling off the end here would be the one failure this file argues
      // against everywhere else -- see encodedBitsOf. A record nothing checks
      // is a record no candidate can contradict, and an abstraction no
      // candidate can contradict is one the search may give any value it
      // likes, so an unsatisfiable query comes back sat with no diagnostic.
      // The blaster mints six kinds and the five branches above take all of
      // them, so this cannot fire today; a seventh added tomorrow would
      // otherwise arrive silently.
      FatalError("BV abstraction: an abstracted operation is of a kind the "
                 "refinement does not know how to check against its "
                 "operands: ",
                 abs.termNode);
    }
  }

  // Phase 2: Add refinement clauses (no model reads needed).
  unsigned refined = 0;

  for (const InconsistentDivRemPair& inc : incDivRemPairs)
  {
    BVTermAbstraction& div = terms_[inc.divIdx];
    BVTermAbstraction& rem = terms_[inc.remIdx];
    const std::vector<unsigned>& dividendVars =
        encodedBitsOf(div.operands[0], div.width, nodeToSATVar);
    const std::vector<unsigned>& divisorVars =
        encodedBitsOf(div.operands[1], div.width, nodeToSATVar);
    const std::vector<unsigned>& quotientVars =
        encodedResultBitsOf(div, nodeToSATVar);
    const std::vector<unsigned>& remainderVars =
        encodedResultBitsOf(rem, nodeToSATVar);

    // Measured like an escalation, because it is the same trade: a full-width
    // multiplier spliced through BVExactEncoder into a solver that is already
    // running. It is what makes the aggressive profile the slowest one, and
    // the totals exist to answer exactly that -- what a refinement handed the
    // solver, where the counts alone cannot say. It is not counted as an
    // escalation, because nothing was given up: the abstraction stays an
    // abstraction and the fact constrains it.
    //
    // Only the totals. The per-record fields say what one record's own
    // escalations cost, and this cost belongs to two records rather than
    // either -- the same reason divRemFullInstalled cannot live in
    // installedSchemas. Charging it to both would double it in any sum over
    // records, and to one would misattribute it.
    const uint64_t pairClausesBefore = solver.submittedClauses();
    const uint32_t pairVariablesBefore = solver.nVars();
    const std::chrono::steady_clock::time_point pairStarted =
        std::chrono::steady_clock::now();
    // This relation is an optional strengthening, not the completeness
    // backstop. If its full-width multiplier does not fit, remember the
    // refusal, unreserve both records, and let their ordinary cached
    // inconsistencies be refined below in this same round.
    const bool encoded = spliceWithinBudget(
        bm, "the paired division/remainder identity", [&] {
          exact_.encodeDivRemIdentity(solver, inc.product, div.width,
                                      dividendVars, divisorVars, quotientVars,
                                      remainderVars);
        });
    if (!encoded)
    {
      div.divRemFullRefused = true;
      rem.divRemFullRefused = true;
      handledByDivRemPair.erase(inc.divIdx);
      handledByDivRemPair.erase(inc.remIdx);
      continue;
    }
    div.divRemFullInstalled = true;
    rem.divRemFullInstalled = true;
    UserDefinedFlags::EncodingCoverage& pairCoverage = bm->UserFlags.coverage;
    pairCoverage.bv_exact_clauses +=
        solver.submittedClauses() - pairClausesBefore;
    pairCoverage.bv_exact_variables += solver.nVars() - pairVariablesBefore;
    pairCoverage.bv_exact_microseconds += static_cast<uint64_t>(
        std::chrono::duration_cast<std::chrono::microseconds>(
            std::chrono::steady_clock::now() - pairStarted)
            .count());

    div.schemaRounds++;
    rem.schemaRounds++;
    div.schemasThisQuery++;
    rem.schemasThisQuery++;
    countFullWidthSchemaLemma(bm->UserFlags, BVSchemaGroup::DIVREM_FULL);
    if (bm->UserFlags.stats_flag)
      std::cerr << "BV abstraction: paired BVDIV/BVMOD recomposition lemma "
                << "over " << div.width << " bits" << std::endl;
    refined++;
  }

  for (auto& inc : incCmps)
  {
    auto& abs = terms_[inc.absIdx];
    const std::vector<unsigned>& leftVars =
        encodedBitsOf(abs.operands[0], abs.width, nodeToSATVar);
    const std::vector<unsigned>& rightVars =
        encodedBitsOf(abs.operands[1], abs.width, nodeToSATVar);
    const std::vector<unsigned>& lv = inc.swapOps ? rightVars : leftVars;
    const std::vector<unsigned>& rv = inc.swapOps ? leftVars : rightVars;

    const unsigned carryVar =
        encodeLessOrEqual(solver, lv, rv, abs.width, inc.isSigned);

    {
      SATSolver::vec_literals cl;
      cl.clear(); cl.push(SATSolver::mkLit(abs.condSATVar, inc.negateResult));  cl.push(SATSolver::mkLit(carryVar, true));  solver.addClause(cl);
      cl.clear(); cl.push(SATSolver::mkLit(abs.condSATVar, !inc.negateResult)); cl.push(SATSolver::mkLit(carryVar, false)); solver.addClause(cl);
    }

    abs.defined = true;
    abs.blastedBits = abs.width;
    refined++;
  }

  for (auto& inc : incPlus)
  {
    auto& abs = terms_[inc.absIdx];
    const std::vector<unsigned>& leftVars =
        encodedBitsOf(abs.operands[0], abs.width, nodeToSATVar);
    const std::vector<unsigned>& rightVars =
        encodedBitsOf(abs.operands[1], abs.width, nodeToSATVar);
    const std::vector<unsigned>& resultVars =
        encodedResultBitsOf(abs, nodeToSATVar);
    const bool lNeg = abs.operandNegated[0];
    const bool rNeg = abs.operandNegated[1];

    if (inc.schema.found)
    {
      if (inc.schema.prefixBits != 0)
      {
        const SchemaInstallCost cost(solver);
        encodeAddLowPrefix(solver, leftVars, rightVars, resultVars, abs.width,
                           inc.schema.prefixBits, lNeg, rNeg);
        abs.installedSchemas |= ADD_SCHEMA_INSTALLED_LOW_PREFIX;
        abs.blastedBits = inc.schema.prefixBits;
        abs.defined = (inc.schema.prefixBits == abs.width);
        abs.schemaRounds++;
        abs.schemasThisQuery++;
        countSchemaLemma(bm->UserFlags, inc.schema.group, solver, cost);
        if (bm->UserFlags.stats_flag)
          std::cerr << "BV abstraction: BVPLUS exact-low-prefix lemma over "
                    << inc.schema.prefixBits << " bits" << std::endl;
        refined++;
        continue;
      }

      const SchemaInstallCost cost(solver);
      const std::vector<unsigned>* rawVars[2] = {&leftVars, &rightVars};
      const bool negated[2] = {lNeg, rNeg};
      const std::vector<unsigned>* effectiveVars[2] = {rawVars[0], rawVars[1]};
      for (unsigned i = 0; i < 2; ++i)
        if (negated[i])
        {
          if (abs.negatedOperand[i].empty())
            abs.negatedOperand[i] = encodeNegate(solver, *rawVars[i], abs.width);
          effectiveVars[i] = &abs.negatedOperand[i];
        }

      const unsigned chosen = inc.schema.operand;
      const bool spliced =
          spliceWithinBudget(bm, "an addition fact", [&] {
            exact_.encodeAddLemma(solver,
                                  addLemmaAt(inc.schema.lemmaIndex).lemma,
                                  abs.width, *effectiveVars[chosen],
                                  *effectiveVars[1 - chosen], resultVars);
          });
      // The bit goes on either way: it means "do not offer this again", and
      // a fact the AIG budget refused is one there is no point offering
      // again. Refused, the addition falls through to being defined outright
      // below, which is written a clause at a time and needs no circuit.
      abs.installedSchemas |=
          addLemmaInstalledBit(inc.schema.lemmaIndex, chosen);
      if (spliced)
      {
        abs.schemaRounds++;
        abs.schemasThisQuery++;
        countSchemaLemma(bm->UserFlags, inc.schema.group, solver, cost);
        if (bm->UserFlags.stats_flag)
          std::cerr << "BV abstraction: BVPLUS "
                    << addLemmaAt(inc.schema.lemmaIndex).name
                    << " lemma over operand " << chosen << std::endl;
        refined++;
        continue;
      }
    }

    // No schema remained: define the whole addition. The same encoder is
    // used for the prefix above, so a polarity fix cannot make the two paths
    // silently disagree.
    encodeAddLowPrefix(solver, leftVars, rightVars, resultVars, abs.width,
                       abs.width, lNeg, rNeg);

    abs.defined = true;
    abs.blastedBits = abs.width;
    refined++;
  }

  for (auto& inc : incITE)
  {
    auto& abs = terms_[inc.absIdx];
    // Both branches, where the scan above only read the one the candidate's
    // condition selected: a pinned if-then-else has to say what it is under
    // either.
    const std::vector<unsigned>& thenVars =
        encodedBitsOf(abs.operands[1], abs.width, nodeToSATVar);
    const std::vector<unsigned>& elseVars =
        encodedBitsOf(abs.operands[2], abs.width, nodeToSATVar);
    const std::vector<unsigned>& resultVars =
        encodedResultBitsOf(abs, nodeToSATVar);
    unsigned c = abs.condSATVar;

    for (unsigned bit = 0; bit < abs.width; ++bit)
    {
      unsigned r = resultVars[bit];
      unsigned t = thenVars[bit];
      unsigned e = elseVars[bit];
      SATSolver::vec_literals cl;

      cl.clear(); cl.push(SATSolver::mkLit(c,true));  cl.push(SATSolver::mkLit(r,true));  cl.push(SATSolver::mkLit(t,false)); solver.addClause(cl);
      cl.clear(); cl.push(SATSolver::mkLit(c,true));  cl.push(SATSolver::mkLit(r,false)); cl.push(SATSolver::mkLit(t,true));  solver.addClause(cl);

      cl.clear(); cl.push(SATSolver::mkLit(c,false)); cl.push(SATSolver::mkLit(r,true));  cl.push(SATSolver::mkLit(e,false)); solver.addClause(cl);
      cl.clear(); cl.push(SATSolver::mkLit(c,false)); cl.push(SATSolver::mkLit(r,false)); cl.push(SATSolver::mkLit(e,true));  solver.addClause(cl);
    }

    abs.defined = true;
    abs.blastedBits = abs.width;
    refined++;
  }

  for (auto& inc : incDivMul)
  {
    // A successfully installed paired identity owns this round for both
    // records. A refused identity cleared these bits above, so the same
    // cached model data falls through to the ordinary refinement instead.
    if (handledByDivRemPair.find(inc.absIdx) != handledByDivRemPair.end())
      continue;

    auto& abs = terms_[inc.absIdx];
    const std::vector<unsigned>& aVars =
        encodedBitsOf(abs.operands[0], abs.width, nodeToSATVar);
    const std::vector<unsigned>& bVars =
        encodedBitsOf(abs.operands[1], abs.width, nodeToSATVar);
    const std::vector<unsigned>& resultVars =
        encodedResultBitsOf(abs, nodeToSATVar);
    unsigned W = abs.width;

    // An algebraic fact the candidate contradicts, where there is one.
    // Every branch here writes a theorem about the operation over the
    // variables already in the solver -- the operand proxies and the
    // abstraction's own result bits -- so none of it is retractable and
    // none of it needs to be. What the candidate chose is only *which*
    // theorem to spend a round on.
    bool schemaSpliced = true;
    if (inc.divSchema.schema != DivSchema::None)
    {
      const SchemaInstallCost cost(solver);
      switch (inc.divSchema.schema)
      {
        case DivSchema::DivisorZero:
        case DivSchema::Pow2Divisor:
          encodeDivUnderDivisorValue(
              solver, bVars, inc.bBits, aVars, resultVars, W,
              divSchemaSources(abs.opKind, W, inc.divSchema));
          abs.installedSchemas = bvSchemaFamilyRecordInstance(
              abs.installedSchemas, BVSchemaFamily::DivisorValue);
          break;

        case DivSchema::RemainderAtMostDividend:
          encodeDivBound(solver, inc.divSchema.schema, aVars, bVars, resultVars,
                         W);
          abs.installedSchemas |=
              DIV_SCHEMA_INSTALLED_REMAINDER_AT_MOST_DIVIDEND;
          break;

        case DivSchema::RemainderBelowDivisor:
          encodeDivBound(solver, inc.divSchema.schema, aVars, bVars, resultVars,
                         W);
          abs.installedSchemas |= DIV_SCHEMA_INSTALLED_REMAINDER_BELOW_DIVISOR;
          break;

        case DivSchema::QuotientAtMostDividend:
          encodeDivBound(solver, inc.divSchema.schema, aVars, bVars, resultVars,
                         W);
          abs.installedSchemas |=
              DIV_SCHEMA_INSTALLED_QUOTIENT_AT_MOST_DIVIDEND;
          break;

        case DivSchema::QuotientPow2Threshold:
          assert(abs.opKind == BVDIV);
          encodeDivPow2Threshold(solver, aVars, bVars, resultVars, W,
                                 inc.divSchema.shift);
          abs.installedSchemas = bvSchemaFamilyRecordInstance(
              abs.installedSchemas, BVSchemaFamily::QuotientThreshold);
          break;

        case DivSchema::DivisorMagnitudeBound:
          assert(abs.opKind == BVDIV);
          encodeDivisorMagnitudeBound(solver, aVars, bVars, resultVars, W,
                                      inc.divSchema.shift);
          abs.installedSchemas = bvSchemaFamilyRecordInstance(
              abs.installedSchemas, BVSchemaFamily::DivisorMagnitude);
          break;

        case DivSchema::Lemma:
          // The bit goes on whether or not the circuit fitted: it means
          // "do not offer this again", and a fact the AIG budget refused is
          // one there is no point offering again. Refused, this record falls
          // through to the value-blocking lemma below.
          schemaSpliced = spliceWithinBudget(
              bm, "a division fact", [&] {
                if (abs.opKind == BVDIV)
                  exact_.encodeDivLemma(
                      solver, divLemmaAt(inc.divSchema.lemmaIndex).lemma, W,
                      aVars, bVars, resultVars);
                else
                {
                  assert(abs.opKind == BVMOD);
                  exact_.encodeRemLemma(
                      solver, remLemmaAt(inc.divSchema.lemmaIndex).lemma, W,
                      aVars, bVars, resultVars);
                }
              });
          abs.installedSchemas |=
              divLemmaInstalledBit(inc.divSchema.lemmaIndex);
          break;

        case DivSchema::None:
          break;
      }

      // A fact the budget refused bought nothing, so no round is spent on
      // it and the record falls through to the value-blocking lemma below.
      if (schemaSpliced)
      {
        abs.schemaRounds++;
        abs.schemasThisQuery++;
        countSchemaLemma(bm->UserFlags, inc.divSchema.group, solver, cost);
        if (bm->UserFlags.stats_flag)
          std::cerr << "BV abstraction: " << _kind_names[abs.opKind] << " "
                    << (inc.divSchema.schema == DivSchema::Lemma
                            ? (abs.opKind == BVDIV
                                   ? divLemmaAt(inc.divSchema.lemmaIndex).name
                                   : remLemmaAt(inc.divSchema.lemmaIndex).name)
                            : divSchemaName(inc.divSchema.schema))
                    << " lemma" << std::endl;
        refined++;
        continue;
      }
    }

    if (inc.schema.schema != MulSchema::None)
    {
      const SchemaInstallCost cost(solver);
      const unsigned chosen = inc.schema.operand;
      const std::vector<unsigned>* opVars[2] = {&aVars, &bVars};
      const std::vector<bool>* opBits[2] = {&inc.aBits, &inc.bBits};

      switch (inc.schema.schema)
      {
        case MulSchema::Odd:
          encodeMulOdd(solver, aVars, bVars, resultVars);
          abs.installedSchemas |= MUL_SCHEMA_INSTALLED_ODD;
          break;

        case MulSchema::TrailingZeros:
          encodeMulTrailingZeros(solver, *opVars[chosen], resultVars, W);
          abs.installedSchemas |=
              (chosen == 0 ? MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_0
                           : MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_1);
          break;

        case MulSchema::Pow2:
          encodeMulShiftUnderValue(solver, *opVars[chosen], *opBits[chosen],
                                   *opVars[1 - chosen], resultVars, W,
                                   inc.schema.shift);
          abs.installedSchemas = bvSchemaFamilyRecordInstance(
              abs.installedSchemas, BVSchemaFamily::MulShiftValue);
          break;

        case MulSchema::NegPow2:
        {
          // The negation circuit is minted once and kept: this schema can
          // fire once per power of two, and the operand proxies it is
          // written over are the same variables every round -- the blaster
          // registers them, so encodedBitsOf hands back the registry's
          // entry rather than fresh bits.
          const unsigned other = 1 - chosen;
          if (abs.negatedOperand[other].empty())
            abs.negatedOperand[other] =
                encodeNegate(solver, *opVars[other], W);
          encodeMulShiftUnderValue(solver, *opVars[chosen], *opBits[chosen],
                                   abs.negatedOperand[other], resultVars, W,
                                   inc.schema.shift);
          abs.installedSchemas = bvSchemaFamilyRecordInstance(
              abs.installedSchemas, BVSchemaFamily::MulShiftValue);
          break;
        }

        case MulSchema::LowPrefix:
          encodeMulLowPrefix(solver, aVars, bVars, resultVars, W,
                             inc.schema.shift);
          abs.installedSchemas |= MUL_SCHEMA_INSTALLED_LOW_PREFIX;
          abs.blastedBits = inc.schema.shift;
          abs.defined = (inc.schema.shift == W);
          break;

        case MulSchema::Lemma:
          schemaSpliced = spliceWithinBudget(
              bm, "a multiplication fact", [&] {
                exact_.encodeMulLemma(solver,
                                      mulLemmaAt(inc.schema.lemmaIndex).lemma,
                                      W, *opVars[chosen], *opVars[1 - chosen],
                                      resultVars);
              });
          abs.installedSchemas |=
              mulLemmaInstalledBit(inc.schema.lemmaIndex, chosen);
          break;

        case MulSchema::None:
          break;
      }

      // As above: a fact the budget refused bought nothing, so the record
      // falls through to the value-blocking lemma rather than spending a
      // round on it.
      if (schemaSpliced)
      {
        abs.schemaRounds++;
        abs.schemasThisQuery++;
        countSchemaLemma(bm->UserFlags, inc.schema.group, solver, cost);
        if (bm->UserFlags.stats_flag)
        {
          std::cerr << "BV abstraction: BVMULT "
                    << (inc.schema.schema == MulSchema::Lemma
                            ? mulLemmaAt(inc.schema.lemmaIndex).name
                            : mulSchemaName(inc.schema.schema))
                    << " lemma";
          if (inc.schema.schema == MulSchema::LowPrefix)
            std::cerr << " over " << inc.schema.shift << " bits";
          else
            std::cerr << " over operand " << chosen;
          std::cerr << std::endl;
        }
        refined++;
        continue;
      }
    }

    // Once this abstraction has been blocked its allowance of times, stop
    // ruling out operand pairs one at a time and say what the operation is.
    // Everything the encoding needs is already here and already frozen: the
    // operands, through the proxies tied to their real bits or pinned to a
    // constant, and the result, which is the abstraction's own bits. Every
    // one of those is a variable the CNF has -- encodedBitsOf above will not
    // hand back a vector holding anything else -- so there is no incomplete
    // mapping to fall back off, only the choice of when to stop enumerating.
    //
    // What it says is the encoding the query would have had if the term had
    // never been abstracted -- literally so: the same bit-blaster entry
    // point BBTerm uses, mapped to CNF by the same ABC pass. See
    // BVExactEncoder. Two independent encodings of a divider that agree
    // today are two that can stop agreeing, and these two already had: the
    // written-out one and BBDivMod disagreed about a zero divisor.
    const unsigned limit = valueLemmaAllowance(bm->UserFlags, W, abs.opKind);
    if (limit != 0 && abs.blockedThisQuery >= limit)
    {
      // A previous query may already have established that this mandatory
      // definition cannot fit. Value-pair enumeration beyond the bounded
      // allowance is not an acceptable substitute: its search space is
      // 2^(2W), so this candidate remains explicitly unknown.
      if (abs.exactRefused)
      {
        assert(abs.exactRefusedAtNodeCount >= 0);
        bm->noteAIGBudgetExhausted(abs.exactRefusedAtNodeCount);
        return AbstractionRefinementResult::unknown(refined);
      }

      // All of it, unless the piece-at-a-time escalation is on and this is
      // a multiplication. A piece reaches past the lowest bit the candidate
      // got wrong, which is at or above everything already encoded -- the
      // bits below are pinned exactly, so no candidate can disagree there
      // -- and so every round pushes the encoding strictly further up and
      // the last one finishes it.
      //
      // Each piece is a whole circuit for the bits below it, so a
      // multiplication that takes several of them pays for the low bits
      // more than once. This implementation does not reuse the lower-bit
      // circuit from an earlier piece, which is one reason the flag is off
      // until something measures it.
      unsigned upto = W;
      ASTNode encodeAs = abs.termNode;
      if (bm->UserFlags.bv_term_abstraction_inc_bitblast &&
          abs.opKind == BVMULT && inc.lowestWrongBit + 1 < W)
      {
        const unsigned reach = inc.lowestWrongBit + BV_INC_BITBLAST_STEP + 1;
        if (reach < W)
        {
          const ASTNode narrowed = narrowedProduct(bm, abs.termNode, reach);
          if (!narrowed.IsNull())
          {
            upto = reach;
            encodeAs = narrowed;
          }
        }
      }

      const uint64_t exactClausesBefore = solver.submittedClauses();
      const uint32_t exactVariablesBefore = solver.nVars();
      const std::chrono::steady_clock::time_point exactStarted =
          std::chrono::steady_clock::now();
      // With the operand bits the blast already knew, so the circuit this
      // falls back on is the one the query would have had rather than a
      // fully symbolic one. A narrowed piece reads the same vectors: it is
      // the low `upto` bits of the same operands, and the encoder only looks
      // that far.
      bool encoded = false;
      try
      {
        exact_.encode(solver, encodeAs, upto, aVars, bVars, resultVars,
                      abs.operandKnownBits[0], abs.operandKnownBits[1]);
        encoded = true;
      }
      catch (const AIGBudgetExhausted& e)
      {
        abs.exactRefused = true;
        abs.exactRefusedAtNodeCount = e.nodeCount;
        if (bm->UserFlags.stats_flag)
          std::cerr
              << "AIG node budget exhausted during exact BV refinement at "
              << e.nodeCount << " nodes" << std::endl;
        bm->noteAIGBudgetExhausted(e.nodeCount);
      }
      if (!encoded)
        return AbstractionRefinementResult::unknown(refined);

      const uint64_t exactMicros = static_cast<uint64_t>(
          std::chrono::duration_cast<std::chrono::microseconds>(
              std::chrono::steady_clock::now() - exactStarted)
              .count());
      abs.blastedBits = upto;
      abs.defined = (upto == W);
      const uint64_t exactClauses =
          solver.submittedClauses() - exactClausesBefore;
      const uint64_t exactVariables = solver.nVars() - exactVariablesBefore;
      abs.exactEscalations++;
      abs.exactClauses += exactClauses;
      abs.exactVariables += exactVariables;
      abs.exactMicroseconds += exactMicros;
      UserDefinedFlags::EncodingCoverage& coverage = bm->UserFlags.coverage;
      coverage.bv_exact_escalations++;
      if (abs.opKind == BVMULT)
        coverage.bv_exact_escalations_mult++;
      else
      {
        assert(abs.opKind == BVDIV || abs.opKind == BVMOD);
        coverage.bv_exact_escalations_divmod++;
      }
      coverage.bv_exact_clauses += exactClauses;
      coverage.bv_exact_variables += exactVariables;
      coverage.bv_exact_microseconds += exactMicros;

      if (bm->UserFlags.stats_flag)
      {
        std::cerr << "BV abstraction: encoding " << _kind_names[abs.opKind];
        if (!abs.defined)
          std::cerr << " up to bit " << (upto - 1);
        else
          std::cerr << " exactly";
        std::cerr << " after " << abs.blockedRounds << " blocking lemmas"
                  << std::endl;
      }
      refined++;
      continue;
    }
    abs.blockedRounds++;
    abs.blockedThisQuery++;
    bm->UserFlags.coverage.bv_blocking_lemmas++;

    for (unsigned bit = 0; bit < W; ++bit)
    {
      SATSolver::vec_literals cl;
      for (unsigned i = 0; i < W; ++i)
        cl.push(SATSolver::mkLit(aVars[i], inc.aBits[i]));
      for (unsigned i = 0; i < W; ++i)
        cl.push(SATSolver::mkLit(bVars[i], inc.bBits[i]));
      cl.push(SATSolver::mkLit(resultVars[bit], !inc.expected[bit]));
      solver.addClause(cl);
    }

    refined++;
  }

  return refined == 0 ? AbstractionRefinementResult::faithful()
                      : AbstractionRefinementResult::progress(refined);
}

} // namespace stp
