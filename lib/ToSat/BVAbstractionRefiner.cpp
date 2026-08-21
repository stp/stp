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
#include "stp/ToSat/BVEQCongruenceClosure.h"

#include <algorithm>
#include <iostream>
#include <unordered_map>

namespace stp
{

// Both families in one call, equalities first: theirs is the cheaper scan,
// and the congruence phase inside it can refute a candidate at word level
// without reading a single bit. A round that refined an equality stops
// there rather than going on to the terms -- the term scan reads the same
// model, and what it would find in it has already been ruled out.
unsigned BVAbstractionRefiner::refine(
    SATSolver& solver, const ToSATBase::ASTNodeToSATVar& nodeToSATVar)
{
  unsigned refined = 0;
  if (hasEqualities())
    refined = refineEqualities(solver, nodeToSATVar);
  if (refined == 0 && hasTerms())
    refined = refineTerms(solver, nodeToSATVar);
  if (refined > 0)
  {
    refinements_ += refined;
    if (bm->UserFlags.stats_flag)
      std::cerr << "BV abstraction: refined " << refined << " operations"
                << std::endl;
  }
  return refined;
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
    auto resultIt = nodeToSATVar.find(a.termNode);
    if (resultIt != nodeToSATVar.end())
      for (unsigned v : resultIt->second)
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

// The SAT variables one node of a record -- an operand, or the abstraction's
// own result -- was encoded into, ready to be read out of a candidate or
// written into a clause.
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
    SATSolver& solver, const ToSATBase::ASTNodeToSATVar& nodeToSATVar)
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
    for (const auto& abs : eqs_)
    {
      if (symbolToIdx.find(abs.leftSymbol) == symbolToIdx.end())
        symbolToIdx[abs.leftSymbol] = nextIdx++;
      if (symbolToIdx.find(abs.rightSymbol) == symbolToIdx.end())
        symbolToIdx[abs.rightSymbol] = nextIdx++;
    }

    std::vector<BVEQCongruenceClosure::EqInfo> eqInfos;
    for (const auto& abs : eqs_)
    {
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

  for (size_t idx = 0; idx < eqs_.size(); ++idx)
  {
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
  for (unsigned i = 0; i < width; ++i)
    bits[i] = (solver.modelValue(satVars[i]) == solver.true_literal());
}

static void getOperandVars(
    const ASTNode& operand, unsigned width,
    const ToSATBase::ASTNodeToSATVar& nodeToSATVar, SATSolver& solver,
    std::vector<unsigned>& vars)
{
  // The registry first, constants included. The blaster proxies every
  // operand it abstracts a multiplication, division or if-then-else over
  // -- a constant gets a vector of inputs pinned to it by biconditionals
  // -- and those variables are already in the solver and already frozen.
  // Minting a fresh pinned vector here instead, which is what the
  // constant short-circuit ahead of the lookup used to do, said the same
  // thing over new variables on every round the record was refined: a
  // multiplication enumerating blocking lemmas paid width variables and
  // width unit clauses per round for a value the CNF already carried.
  if (nodeToSATVar.find(operand) != nodeToSATVar.end())
  {
    vars = encodedBitsOf(operand, width, nodeToSATVar);
    return;
  }

  // A constant the blaster deliberately left out of the registry: BVPLUS
  // folds constant operands into the record rather than proxying them.
  // Its record defines itself in a single round, so this mints once.
  if (operand.GetKind() == BVCONST)
  {
    vars.resize(width);
    CBV val = operand.GetBVConst();
    for (unsigned i = 0; i < width; ++i)
    {
      vars[i] = solver.newVar();
      solver.setFrozen(vars[i]);
      SATSolver::vec_literals cl;
      cl.push(SATSolver::mkLit(vars[i],
              !CONSTANTBV::BitVector_bit_test(val, i)));
      solver.addClause(cl);
    }
    return;
  }

  // Neither registered nor a constant: refused, naming which of the three
  // registry guarantees broke.
  vars = encodedBitsOf(operand, width, nodeToSATVar);
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

// Exact CNF for the operations whose refinement would otherwise enumerate.
//
// A blocking lemma rules out one pair of operand values, so a query the solver
// has to search through can need more rounds than there are pairs of operands:
// a 64-bit factorisation spent 5816 of them and ninety seconds on a query the
// unabstracted solve answers in five hundredths of one. Past
// bv_term_abstraction_rounds the refinement stops enumerating and says what
// the operation is, over the same variables it has been talking about all
// along -- the operand proxies and the abstraction's own result bits, which
// are already in the solver and already frozen. The abstraction is then
// defined, so it is never revisited and the solve ends on the next round with
// the answer it would have given had the term never been abstracted.
//
// Everything below is built from three gates, so that nothing here is a fresh
// hand-written clause block; each is written out of the row of the truth table
// it rules out. mkLit(v, sign) is false exactly when v equals sign, so a
// literal at `bit` is false exactly when that input is `bit`, and a clause
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

// z <-> x & y
static unsigned mkAnd(SATSolver& solver, unsigned x, unsigned y)
{
  const unsigned z = freshVar(solver);
  SATSolver::vec_literals cl;
  cl.clear(); cl.push(SATSolver::mkLit(x, true));  cl.push(SATSolver::mkLit(y, true));  cl.push(SATSolver::mkLit(z, false)); solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(x, false)); cl.push(SATSolver::mkLit(z, true));  solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(y, false)); cl.push(SATSolver::mkLit(z, true));  solver.addClause(cl);
  return z;
}

// z <-> (sel ? t : e)
static unsigned mkMux(SATSolver& solver, unsigned sel, unsigned t, unsigned e)
{
  const unsigned z = freshVar(solver);
  SATSolver::vec_literals cl;
  cl.clear(); cl.push(SATSolver::mkLit(sel, true));  cl.push(SATSolver::mkLit(t, true));  cl.push(SATSolver::mkLit(z, false)); solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(sel, true));  cl.push(SATSolver::mkLit(t, false)); cl.push(SATSolver::mkLit(z, true));  solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(sel, false)); cl.push(SATSolver::mkLit(e, true));  cl.push(SATSolver::mkLit(z, false)); solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(sel, false)); cl.push(SATSolver::mkLit(e, false)); cl.push(SATSolver::mkLit(z, true));  solver.addClause(cl);
  return z;
}

// x <-> y
static void addEquiv(SATSolver& solver, unsigned x, unsigned y)
{
  SATSolver::vec_literals cl;
  cl.clear(); cl.push(SATSolver::mkLit(x, true));  cl.push(SATSolver::mkLit(y, false)); solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(x, false)); cl.push(SATSolver::mkLit(y, true));  solver.addClause(cl);
}

// sum <-> a ^ b ^ cin, carry <-> at least two of the three. `aNeg` reads a
// complemented, which is how the subtractor below gets its ~b.
static void addFullAdder(SATSolver& solver, unsigned a, bool aNeg, unsigned b,
                         unsigned cin, unsigned& sum, unsigned& carry)
{
  sum = freshVar(solver);
  carry = freshVar(solver);
  SATSolver::vec_literals cl;

  for (unsigned row = 0; row < 8; ++row)
  {
    const bool aBit = (row & 1) != 0;
    const bool bBit = (row & 2) != 0;
    const bool cBit = (row & 4) != 0;
    const bool s = aBit ^ bBit ^ cBit;
    const bool co = (aBit + bBit + cBit) >= 2;
    cl.clear();
    cl.push(SATSolver::mkLit(a, aBit != aNeg));
    cl.push(SATSolver::mkLit(b, bBit));
    cl.push(SATSolver::mkLit(cin, cBit));
    cl.push(SATSolver::mkLit(sum, !s));
    solver.addClause(cl);

    cl.clear();
    cl.push(SATSolver::mkLit(a, aBit != aNeg));
    cl.push(SATSolver::mkLit(b, bBit));
    cl.push(SATSolver::mkLit(cin, cBit));
    cl.push(SATSolver::mkLit(carry, !co));
    solver.addClause(cl);
  }
}

// z <-> (x <= y), unsigned, from the least significant bit up so that the most
// significant differing bit decides -- the same chain the comparison lemma
// uses, for the same reason.
static unsigned mkUnsignedLE(SATSolver& solver, const std::vector<unsigned>& x,
                             const std::vector<unsigned>& y, unsigned width)
{
  unsigned acc = pinnedVar(solver, true);
  SATSolver::vec_literals cl;
  for (unsigned bit = 0; bit < width; ++bit)
  {
    const unsigned nc = freshVar(solver);
    const unsigned a = x[bit];
    const unsigned b = y[bit];
    cl.clear(); cl.push(SATSolver::mkLit(a, false)); cl.push(SATSolver::mkLit(b, true));  cl.push(SATSolver::mkLit(nc, false)); solver.addClause(cl);
    cl.clear(); cl.push(SATSolver::mkLit(a, false)); cl.push(SATSolver::mkLit(acc, true)); cl.push(SATSolver::mkLit(nc, false)); solver.addClause(cl);
    cl.clear(); cl.push(SATSolver::mkLit(b, true));  cl.push(SATSolver::mkLit(acc, true)); cl.push(SATSolver::mkLit(nc, false)); solver.addClause(cl);
    cl.clear(); cl.push(SATSolver::mkLit(a, true));  cl.push(SATSolver::mkLit(b, false)); cl.push(SATSolver::mkLit(nc, true)); solver.addClause(cl);
    cl.clear(); cl.push(SATSolver::mkLit(a, true));  cl.push(SATSolver::mkLit(acc, false)); cl.push(SATSolver::mkLit(nc, true)); solver.addClause(cl);
    cl.clear(); cl.push(SATSolver::mkLit(b, false)); cl.push(SATSolver::mkLit(acc, false)); cl.push(SATSolver::mkLit(nc, true)); solver.addClause(cl);
    acc = nc;
  }
  return acc;
}

// result <-> a * b, truncated, by shift and add: one conditional row per bit
// of b, each added in at its own offset. Rows below the offset are zero, so
// the accumulator keeps those bits and the row's carry starts there.
static void encodeMultiply(SATSolver& solver, const std::vector<unsigned>& a,
                           const std::vector<unsigned>& b,
                           const std::vector<unsigned>& result, unsigned width)
{
  std::vector<unsigned> acc(width);
  for (unsigned j = 0; j < width; ++j)
    acc[j] = mkAnd(solver, a[j], b[0]);

  for (unsigned i = 1; i < width; ++i)
  {
    unsigned carry = pinnedVar(solver, false);
    for (unsigned j = i; j < width; ++j)
    {
      const unsigned pp = mkAnd(solver, a[j - i], b[i]);
      unsigned sum, cout;
      addFullAdder(solver, acc[j], false, pp, carry, sum, cout);
      acc[j] = sum;
      carry = cout;
    }
  }

  for (unsigned j = 0; j < width; ++j)
    addEquiv(solver, result[j], acc[j]);
}

// result <-> a / b or a % b, by restoring division. A zero divisor needs no
// special case: every shifted remainder is at or above it, so each step
// subtracts nothing and the quotient comes out all ones with the dividend left
// in the remainder -- which is what SMT-LIB asks for and what the unabstracted
// BBDivMod produces.
static void encodeDivMod(SATSolver& solver, const std::vector<unsigned>& a,
                         const std::vector<unsigned>& b,
                         const std::vector<unsigned>& result, unsigned width,
                         bool isDiv)
{
  const unsigned zero = pinnedVar(solver, false);
  std::vector<unsigned> quotient(width, zero);
  std::vector<unsigned> rem(width, zero);

  for (int i = (int)width - 1; i >= 0; --i)
  {
    // rem = (rem << 1) | a[i]
    for (unsigned j = width - 1; j > 0; --j)
      rem[j] = rem[j - 1];
    rem[0] = a[i];

    const unsigned geq = mkUnsignedLE(solver, b, rem, width);
    quotient[i] = geq;

    // rem - b, as rem + ~b + 1, kept only where the subtraction was taken.
    unsigned carry = pinnedVar(solver, true);
    std::vector<unsigned> sub(width);
    for (unsigned j = 0; j < width; ++j)
    {
      unsigned s, cout;
      addFullAdder(solver, b[j], true, rem[j], carry, s, cout);
      sub[j] = s;
      carry = cout;
    }
    for (unsigned j = 0; j < width; ++j)
      rem[j] = mkMux(solver, geq, sub[j], rem[j]);
  }

  const std::vector<unsigned>& answer = isDiv ? quotient : rem;
  for (unsigned j = 0; j < width; ++j)
    addEquiv(solver, result[j], answer[j]);
}

unsigned BVAbstractionRefiner::refineTerms(
    SATSolver& solver, const ToSATBase::ASTNodeToSATVar& nodeToSATVar)
{
  // Phase 1: Scan all abstractions, reading model values to find inconsistencies.
  // Cache the data needed for clause generation so we don't need modelValue later.
  struct InconsistentCmp {
    size_t absIdx;
    bool swapOps, negateResult, isSigned;
  };
  struct InconsistentPlus {
    size_t absIdx;
  };
  struct InconsistentITE {
    size_t absIdx;
  };
  struct InconsistentDivMul {
    size_t absIdx;
    std::vector<bool> aBits, bBits, expected;
  };

  std::vector<InconsistentCmp> incCmps;
  std::vector<InconsistentPlus> incPlus;
  std::vector<InconsistentITE> incITE;
  std::vector<InconsistentDivMul> incDivMul;

  for (size_t idx = 0; idx < terms_.size(); ++idx)
  {
    auto& abs = terms_[idx];
    if (abs.defined)
      continue;

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
        encodedBitsOf(abs.termNode, abs.width, nodeToSATVar);

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
      for (unsigned bit = 0; bit < abs.width; ++bit)
      {
        bool l = leftBits[bit] ^ lNeg;
        bool r = rightBits[bit] ^ rNeg;
        bool s = (solver.modelValue(resultVars[bit]) == solver.true_literal());
        bool expectedSum = l ^ r ^ carry;
        carry = (l && r) || (l && carry) || (r && carry);
        if (s != expectedSum) { consistent = false; break; }
      }
      if (consistent) continue;

      incPlus.push_back({idx});
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
      std::vector<bool> expected(W, false);
      if (abs.opKind == BVMULT)
      {
        for (unsigned i = 0; i < W; ++i)
          if (aBits[i])
            for (unsigned j = 0; j < W && i + j < W; ++j)
              if (bBits[j])
              {
                bool carry = false;
                for (unsigned p = i + j; p < W; ++p)
                {
                  if (p == i + j)
                  {
                    bool sum = expected[p] ^ true ^ carry;
                    carry = (expected[p] && true) || (expected[p] && carry) || (true && carry);
                    expected[p] = sum;
                  }
                  else
                  {
                    bool sum = expected[p] ^ false ^ carry;
                    carry = (expected[p] && carry);
                    expected[p] = sum;
                  }
                  if (!carry) break;
                }
              }
      }
      else
      {
        bool divisorZero = true;
        for (unsigned i = 0; i < W; ++i)
          if (bBits[i]) { divisorZero = false; break; }

        if (divisorZero)
        {
          // Both are totalised, and not to the same thing: division by zero
          // is all ones, while the remainder is the dividend. That is what
          // SMT-LIB says and what the unabstracted BBDivMod answers -- its
          // restoring loop finds every shifted remainder at or above a zero
          // divisor, subtracts nothing each time, and hands the dividend
          // back. Left at zero, this reference agreed with an abstraction
          // holding a value the query does not give it, so a bogus candidate
          // was called consistent: no lemma, and the refinement loop ran out
          // of things to say about a model it had already rejected.
          if (abs.opKind == BVDIV)
            for (unsigned i = 0; i < W; ++i) expected[i] = true;
          else
            expected = aBits;
        }
        else
        {
          std::vector<bool> quotient(W, false);
          std::vector<bool> remainder(W, false);
          for (int i = (int)W - 1; i >= 0; --i)
          {
            for (int j = (int)W - 1; j > 0; --j)
              remainder[j] = remainder[j - 1];
            remainder[0] = aBits[i];

            bool geq = true;
            for (int j = (int)W - 1; j >= 0; --j)
            {
              if (!remainder[j] && bBits[j]) { geq = false; break; }
              if (remainder[j] && !bBits[j]) break;
            }

            if (geq)
            {
              quotient[i] = true;
              bool borrow = false;
              for (unsigned j = 0; j < W; ++j)
              {
                bool sub = remainder[j] ^ bBits[j] ^ borrow;
                borrow = (!remainder[j] && bBits[j]) ||
                         (!remainder[j] && borrow) ||
                         (bBits[j] && borrow);
                remainder[j] = sub;
              }
            }
          }
          expected = (abs.opKind == BVDIV) ? quotient : remainder;
        }
      }

      bool consistent = true;
      for (unsigned bit = 0; bit < W; ++bit)
      {
        bool r = (solver.modelValue(resultVars[bit]) == solver.true_literal());
        if (r != expected[bit]) { consistent = false; break; }
      }
      if (consistent) continue;

      incDivMul.push_back({idx, std::move(aBits), std::move(bBits),
                            std::move(expected)});
    }
  }

  // Phase 2: Add refinement clauses (no model reads needed).
  unsigned refined = 0;

  for (auto& inc : incCmps)
  {
    auto& abs = terms_[inc.absIdx];
    std::vector<unsigned> leftVars, rightVars;
    getOperandVars(abs.operands[0], abs.width, nodeToSATVar, solver, leftVars);
    getOperandVars(abs.operands[1], abs.width, nodeToSATVar, solver, rightVars);
    const std::vector<unsigned>& lv = inc.swapOps ? rightVars : leftVars;
    const std::vector<unsigned>& rv = inc.swapOps ? leftVars : rightVars;

    unsigned carryVar = solver.newVar();
    solver.setFrozen(carryVar);
    {
      SATSolver::vec_literals cl;
      cl.push(SATSolver::mkLit(carryVar, false));
      solver.addClause(cl);
    }

    // From the least significant bit up, so that the most significant
    // *differing* bit is the one that decides. Each step keeps the accumulator
    // when the two bits agree and overrides it when they differ, so whichever
    // bit is visited last among the differing ones settles the answer -- which
    // is the top one only in this direction. Run downwards, as this was, the
    // bottom differing bit won instead, and the chain answered something that
    // is not a comparison at all: it disagreed with `a <= b` on 31616 of the
    // 65536 pairs of eight-bit values. The lemma then pinned the abstraction
    // to that, and a query whose comparison the pinned value contradicted came
    // back unsat.
    //
    // The sign bit is therefore also the last step, which is where flipping
    // its sense belongs: for a signed comparison a leading 1 is the smaller
    // side, so the roles of the two operands invert at that bit alone.
    for (int bit = 0; bit < (int)abs.width; ++bit)
    {
      unsigned a = lv[bit];
      unsigned b = rv[bit];
      bool flipSign = (inc.isSigned && bit == (int)abs.width - 1);

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

    {
      SATSolver::vec_literals cl;
      cl.clear(); cl.push(SATSolver::mkLit(abs.condSATVar, inc.negateResult));  cl.push(SATSolver::mkLit(carryVar, true));  solver.addClause(cl);
      cl.clear(); cl.push(SATSolver::mkLit(abs.condSATVar, !inc.negateResult)); cl.push(SATSolver::mkLit(carryVar, false)); solver.addClause(cl);
    }

    abs.defined = true;
    refined++;
  }

  for (auto& inc : incPlus)
  {
    auto& abs = terms_[inc.absIdx];
    std::vector<unsigned> leftVars, rightVars;
    getOperandVars(abs.operands[0], abs.width, nodeToSATVar, solver, leftVars);
    getOperandVars(abs.operands[1], abs.width, nodeToSATVar, solver, rightVars);
    const std::vector<unsigned>& resultVars =
        encodedBitsOf(abs.termNode, abs.width, nodeToSATVar);
    const bool lNeg = abs.operandNegated[0];
    const bool rNeg = abs.operandNegated[1];
    const bool carryInit = (lNeg != rNeg);

    unsigned carryVar = solver.newVar();
    solver.setFrozen(carryVar);
    {
      SATSolver::vec_literals cl;
      cl.push(SATSolver::mkLit(carryVar, !carryInit));
      solver.addClause(cl);
    }

    for (unsigned bit = 0; bit < abs.width; ++bit)
    {
      unsigned l = leftVars[bit];
      unsigned r = rightVars[bit];
      unsigned s = resultVars[bit];
      unsigned c = carryVar;
      SATSolver::vec_literals cl;

      // s <-> l ^ r ^ c, one clause per row of the three inputs, each falsified
      // only by that row paired with the wrong sum bit. Written out of the row
      // rather than transcribed, because the transcription carried every s
      // literal inverted: the lemma forced s = !(l ^ r ^ c), which is not a
      // weaker constraint on the abstraction but the negation of the one the
      // scan above had just checked. A refined addition was therefore still
      // inconsistent on the next round, and `defined` below meant it was never
      // looked at again.
      //
      // mkLit(v, sign) is false exactly when v equals sign, so a literal taken
      // at `bit != negated` is false exactly when that operand's effective bit
      // -- the variable read through the BVUMINUS that operandNegated records,
      // whose +1 the carry above seeds -- is `bit`.
      for (unsigned row = 0; row < 8; ++row)
      {
        const bool lBit = (row & 1) != 0;
        const bool rBit = (row & 2) != 0;
        const bool cBit = (row & 4) != 0;
        const bool sum = lBit ^ rBit ^ cBit;
        cl.clear();
        cl.push(SATSolver::mkLit(l, lBit != lNeg));
        cl.push(SATSolver::mkLit(r, rBit != rNeg));
        cl.push(SATSolver::mkLit(c, cBit));
        cl.push(SATSolver::mkLit(s, !sum));
        solver.addClause(cl);
      }

      if (bit < abs.width - 1)
      {
        unsigned nc = solver.newVar();
        solver.setFrozen(nc);

        cl.clear(); cl.push(SATSolver::mkLit(l,lNeg));   cl.push(SATSolver::mkLit(r,rNeg));   cl.push(SATSolver::mkLit(nc,true)); solver.addClause(cl);
        cl.clear(); cl.push(SATSolver::mkLit(l,lNeg));   cl.push(SATSolver::mkLit(c,false));   cl.push(SATSolver::mkLit(nc,true)); solver.addClause(cl);
        cl.clear(); cl.push(SATSolver::mkLit(r,rNeg));   cl.push(SATSolver::mkLit(c,false));   cl.push(SATSolver::mkLit(nc,true)); solver.addClause(cl);
        cl.clear(); cl.push(SATSolver::mkLit(l,!lNeg));  cl.push(SATSolver::mkLit(r,!rNeg));  cl.push(SATSolver::mkLit(nc,false)); solver.addClause(cl);
        cl.clear(); cl.push(SATSolver::mkLit(l,!lNeg));  cl.push(SATSolver::mkLit(c,true));   cl.push(SATSolver::mkLit(nc,false)); solver.addClause(cl);
        cl.clear(); cl.push(SATSolver::mkLit(r,!rNeg));  cl.push(SATSolver::mkLit(c,true));   cl.push(SATSolver::mkLit(nc,false)); solver.addClause(cl);

        carryVar = nc;
      }
    }

    abs.defined = true;
    refined++;
  }

  for (auto& inc : incITE)
  {
    auto& abs = terms_[inc.absIdx];
    // Both branches, where the scan above only read the one the candidate's
    // condition selected: a pinned if-then-else has to say what it is under
    // either.
    std::vector<unsigned> thenVars, elseVars;
    getOperandVars(abs.operands[1], abs.width, nodeToSATVar, solver, thenVars);
    getOperandVars(abs.operands[2], abs.width, nodeToSATVar, solver, elseVars);
    const std::vector<unsigned>& resultVars =
        encodedBitsOf(abs.termNode, abs.width, nodeToSATVar);
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
    refined++;
  }

  for (auto& inc : incDivMul)
  {
    auto& abs = terms_[inc.absIdx];
    std::vector<unsigned> aVars, bVars;
    getOperandVars(abs.operands[0], abs.width, nodeToSATVar, solver, aVars);
    getOperandVars(abs.operands[1], abs.width, nodeToSATVar, solver, bVars);
    const std::vector<unsigned>& resultVars =
        encodedBitsOf(abs.termNode, abs.width, nodeToSATVar);
    unsigned W = abs.width;

    // Once this abstraction has been blocked its allowance of times, stop
    // ruling out operand pairs one at a time and say what the operation is.
    // Everything the encoding needs is already here and already frozen: the
    // operands, through the proxies tied to their real bits or pinned to a
    // constant, and the result, which is the abstraction's own bits. Every
    // one of those is a variable the CNF has -- encodedBitsOf above will not
    // hand back a vector holding anything else -- so there is no incomplete
    // mapping to fall back off, only the choice of when to stop enumerating.
    const unsigned limit = bm->UserFlags.bv_term_abstraction_rounds;
    if (limit != 0 && abs.blockedRounds >= limit)
    {
      if (abs.opKind == BVMULT)
        encodeMultiply(solver, aVars, bVars, resultVars, W);
      else
        encodeDivMod(solver, aVars, bVars, resultVars, W,
                     abs.opKind == BVDIV);
      if (bm->UserFlags.stats_flag)
        std::cerr << "BV abstraction: encoding "
                  << _kind_names[abs.opKind] << " exactly after "
                  << abs.blockedRounds << " blocking lemmas" << std::endl;
      abs.defined = true;
      refined++;
      continue;
    }
    abs.blockedRounds++;

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

  return refined;
}

} // namespace stp
