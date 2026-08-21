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

#ifndef BVABSTRACTIONREFINER_H
#define BVABSTRACTIONREFINER_H

// The CEGAR half of --bv-eq-abstraction and --bv-term-abstraction.
//
// The bit-blaster replaces an equality, a comparison or an arithmetic
// operation by free combinational inputs and records what it stood for.
// That is an over-approximation, so a candidate model is an assignment of
// the query only once every abstraction in it has been checked against
// the operands underneath and, where the two disagree, pinned by clauses.
// This is the party that does the checking and the pinning.
//
// It is kept apart from the lowering that mints the records because there
// are two of those -- the batch pipeline's whole-formula ToSATAIG and the
// incremental driver's persistent, per-conjunct encoder -- and only the
// resolution of a record's SAT variables differs between them. Everything
// here works from the records plus one map from node to SAT variables, and
// so is shared.
//
// Nothing it adds to the solver is retractable, and nothing needs to be:
// every clause is a definitional fact about the blasted circuit -- this
// abstraction variable means these operand bits -- which holds whatever
// else is asserted. Refining an abstraction only ever brings the encoding
// closer to the query it already stood for.

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/ToSat/ToSATBase.h"

#include <cstdint>
#include <vector>

namespace stp
{

// The variable a record does not have: the condition input of a family that
// carries none, or one whose input never reached the solver. It is ~0u
// rather than zero because zero is a SAT variable like any other -- the
// incremental driver has handed variable 1 to an abstraction input -- and a
// record whose variable read as absent would be skipped, which for an
// over-approximation means certified.
const unsigned BV_ABSTRACTION_NO_VAR = ~((unsigned)0);

// An equality replaced by one free Boolean. `refinedBits` counts the bit
// positions whose agreement has been encoded so far, and `defined` marks
// the point where all of them have been, after which the Boolean is the
// equality and the record is never revisited.
struct BVEQAbstraction
{
  ASTNode eqNode;
  unsigned abstractionSATVar = BV_ABSTRACTION_NO_VAR;
  ASTNode leftSymbol;
  ASTNode rightSymbol;
  unsigned width;
  bool defined = false;
  unsigned refinedBits = 0;
  std::vector<unsigned> xnorHelpers;
};

// An operation replaced by free result bits (and, for a comparison or an
// if-then-else, a free condition variable).
struct BVTermAbstraction
{
  ASTNode termNode;
  Kind opKind;
  ASTNode operands[3];
  unsigned numOperands;
  unsigned width;
  bool operandNegated[3] = {false, false, false};
  unsigned condSATVar = BV_ABSTRACTION_NO_VAR;
  bool defined = false;
  // Blocking lemmas spent on this one abstraction so far; see
  // bv_term_abstraction_rounds.
  unsigned blockedRounds = 0;
};

class DLL_PUBLIC BVAbstractionRefiner
{
  STPMgr* bm;

  std::vector<BVEQAbstraction> eqs_;
  std::vector<BVTermAbstraction> terms_;

  // Monotone across the session, including across a clear(): a driver
  // compares it either side of a round to learn whether that round found
  // anything, and a counter that went backwards would read as no progress.
  uint64_t refinements_ = 0;

  unsigned refineEqualities(SATSolver& solver,
                            const ToSATBase::ASTNodeToSATVar& nodeToSATVar);
  unsigned refineTerms(SATSolver& solver,
                       const ToSATBase::ASTNodeToSATVar& nodeToSATVar);

public:
  explicit BVAbstractionRefiner(STPMgr* bm_) : bm(bm_) {}

  bool empty() const { return eqs_.empty() && terms_.empty(); }
  bool hasEqualities() const { return !eqs_.empty(); }
  bool hasTerms() const { return !terms_.empty(); }

  // The records, for whoever mints them. Everything a refinement round
  // learns is written back into them, so an owner that discards its SAT
  // solver or its bit-blast has to discard these too.
  std::vector<BVEQAbstraction>& equalities() { return eqs_; }
  std::vector<BVTermAbstraction>& terms() { return terms_; }

  void clear()
  {
    eqs_.clear();
    terms_.clear();
  }

  uint64_t refinements() const { return refinements_; }

  // Keep a simplifying backend from eliminating anything a future lemma
  // will be written over.
  void freezeVariables(SATSolver& solver,
                       const ToSATBase::ASTNodeToSATVar& nodeToSATVar) const;

  // Check every record against the current SAT model and pin the ones the
  // model contradicts. Returns how many were pinned: zero means the
  // candidate is faithful and may be handed on.
  unsigned refine(SATSolver& solver,
                  const ToSATBase::ASTNodeToSATVar& nodeToSATVar);
};
}

#endif
