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
  {
    try
    {
      refined = refineTerms(solver, nodeToSATVar);
    }
    catch (const AIGBudgetExhausted& e)
    {
      if (bm->UserFlags.stats_flag)
        std::cerr << "AIG node budget exhausted during exact BV refinement at "
                  << e.nodeCount << " nodes" << std::endl;
      bm->noteAIGBudgetExhausted(e.nodeCount);
      return 0;
    }
  }
  if (refined > 0)
  {
    refinements_ += refined;
    bm->UserFlags.coverage.bv_refinement_rounds++;
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

// The bits of -x. Two's complement negation is ~x + 1, and the whole of that
// carry is a prefix OR: bit j comes out flipped exactly when some bit below
// j is set. Below the lowest set bit nothing flips, at it the 1 survives,
// and above it every bit is complemented -- which is the same three cases
// read off the addition.
static std::vector<unsigned> encodeNegate(SATSolver& solver,
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

MulSchemaChoice chooseMulSchema(const std::vector<bool>& aBits,
                                const std::vector<bool>& bBits,
                                const std::vector<bool>& tBits,
                                unsigned installedSchemas)
{
  const std::vector<bool>* ops[2] = {&aBits, &bBits};

  // a = 2^k -> t = b << k, and the same read the other way round. Where it
  // applies it says the most of the four: the shift *is* the product for
  // that operand value, so one lemma settles every b at once where a
  // blocking lemma settles one pair. It therefore also always fires when it
  // applies -- this is only ever called over a candidate whose product is
  // already known wrong, and for a power-of-two operand "wrong" and
  // "disagrees with the shift" are the same statement.
  for (unsigned i = 0; i < 2; ++i)
  {
    const int k = powerOfTwoExponent(*ops[i]);
    if (k >= 0 && !productIsShift(*ops[1 - i], (unsigned)k, tBits))
      return {MulSchema::Pow2, i, (unsigned)k};
  }

  // a = -2^k -> t = (-b) << k. A power of two is skipped rather than
  // excluded by name: that covers the minimum signed value, which is its own
  // negation and which the schema above has already taken.
  for (unsigned i = 0; i < 2; ++i)
  {
    if (powerOfTwoExponent(*ops[i]) >= 0)
      continue;
    const int k = powerOfTwoExponent(negatedValue(*ops[i]));
    if (k >= 0 &&
        !productIsShift(negatedValue(*ops[1 - i]), (unsigned)k, tBits))
      return {MulSchema::NegPow2, i, (unsigned)k};
  }

  // The product carries at least as many trailing zeros as either operand.
  // Check operand 1 before operand 0 so schema selection remains
  // deterministic for this commutative operator.
  static const unsigned tzInstalled[2] = {
      MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_0,
      MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_1};
  for (unsigned pass = 0; pass < 2; ++pass)
  {
    const unsigned i = 1 - pass;
    if ((installedSchemas & tzInstalled[i]) != 0)
      continue;
    const unsigned zeros = trailingZeros(*ops[i]);
    for (unsigned bit = 0; bit < zeros; ++bit)
      if (tBits[bit])
        return {MulSchema::TrailingZeros, i, 0};
  }

  // t[0] = a[0] & b[0].
  if ((installedSchemas & MUL_SCHEMA_INSTALLED_ODD) == 0 &&
      tBits[0] != (aBits[0] && bBits[0]))
    return {MulSchema::Odd, 0, 0};

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

// Unsigned comparison over the bit vectors a candidate holds, least
// significant bit first. Written here rather than reusing computeBVLE
// because that one is about the operands of an abstracted comparison and
// this one is about a result the abstraction chose.
static bool valueLessOrEqual(const std::vector<bool>& left,
                             const std::vector<bool>& right)
{
  for (int i = (int)left.size() - 1; i >= 0; --i)
  {
    if (left[i] != right[i])
      return right[i];
  }
  return true;
}

static bool valueIsZero(const std::vector<bool>& bits)
{
  for (unsigned i = 0; i < bits.size(); ++i)
    if (bits[i])
      return false;
  return true;
}

// The DivLemma facts, in the order the chooser offers them: by how often
// they fired in the solver they come from, measured over the queries this
// is for. A candidate usually breaks more than one, so the order decides
// which round buys which fact, and buying the most productive first is the
// cheapest guess available.
static const DivLemma DIV_LEMMAS[] = {
    DivLemma::DivisorAboveShiftedDividend,          // 280 firings
    DivLemma::QuotientBelowNegatedDivisor,          // 200
    DivLemma::DividendAboveNegatedAnd,              // 187
    DivLemma::DividendZero,                         // 171
    DivLemma::DivisorEqualsDividend,                // 162
    DivLemma::DivisorLessOneAboveShiftedDividend,   // 161
    DivLemma::DivisorAllOnes};                      // 59

static const unsigned DIV_LEMMA_COUNT =
    sizeof(DIV_LEMMAS) / sizeof(DIV_LEMMAS[0]);

const DivLemma* divLemmaTable(unsigned& count)
{
  count = DIV_LEMMA_COUNT;
  return DIV_LEMMAS;
}

DivSchemaChoice chooseDivSchema(Kind opKind, const std::vector<bool>& aBits,
                                const std::vector<bool>& bBits,
                                const std::vector<bool>& tBits,
                                unsigned installedSchemas)
{
  const unsigned width = (unsigned)tBits.size();
  const bool divisorZero = valueIsZero(bBits);

  // The divisor-guarded facts first, where they apply: each says what the
  // operation *is* for that divisor, which is more than any bound can say.
  // Zero is not a power of two, so the two never contend and the order
  // between them is a formality.
  if (divisorZero)
  {
    const DivSchemaChoice choice{DivSchema::DivisorZero, 0};
    if (!resultMatchesSources(divSchemaSources(opKind, width, choice), aBits,
                              tBits))
      return choice;
  }
  else
  {
    const int k = powerOfTwoExponent(bBits);
    if (k >= 0)
    {
      const DivSchemaChoice choice{DivSchema::Pow2Divisor, (unsigned)k};
      if (!resultMatchesSources(divSchemaSources(opKind, width, choice), aBits,
                                tBits))
        return choice;
    }
  }

  // Then the bounds, which name no divisor and so are the ones a candidate
  // over a wide random divisor actually runs into. Each is offered only
  // once: they are unconditional, so once installed no candidate can
  // contradict them again and re-emitting one would spend a round on a
  // clause the solver already has.
  if (opKind == BVMOD)
  {
    // r <=u a, with no premise at all -- it holds over a zero divisor too,
    // where the remainder is the dividend.
    if ((installedSchemas &
         DIV_SCHEMA_INSTALLED_REMAINDER_AT_MOST_DIVIDEND) == 0 &&
        !valueLessOrEqual(tBits, aBits))
      return {DivSchema::RemainderAtMostDividend, 0};

    // b != 0 -> r <u b.
    if ((installedSchemas & DIV_SCHEMA_INSTALLED_REMAINDER_BELOW_DIVISOR) ==
            0 &&
        !divisorZero && valueLessOrEqual(bBits, tBits))
      return {DivSchema::RemainderBelowDivisor, 0};
  }
  else if (opKind == BVDIV)
  {
    // b != 0 -> t <=u a.
    if ((installedSchemas &
         DIV_SCHEMA_INSTALLED_QUOTIENT_AT_MOST_DIVIDEND) == 0 &&
        !divisorZero && !valueLessOrEqual(tBits, aBits))
      return {DivSchema::QuotientAtMostDividend, 0, 0};

    // Then the wider facts, first one the candidate breaks. Quotients only:
    // every one of them is about `t = a udiv b`.
    for (unsigned i = 0; i < DIV_LEMMA_COUNT; ++i)
    {
      if ((installedSchemas & divLemmaInstalledBit(i)) != 0)
        continue;
      if (!divLemmaHolds(DIV_LEMMAS[i], aBits, bBits, tBits))
        return {DivSchema::Lemma, 0, i};
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
  if (divisor == 0)
    return ceiling; // the flat allowance this replaced

  // At least one. A rate that rounds to nothing would escalate before the
  // abstraction has been given a single chance to pay, which is not what
  // "scale it with the width" is meant to mean at narrow widths -- and
  // width zero does not occur, since the type checker gives every operation
  // a width and the abstraction has a floor besides.
  const unsigned scaled = width / divisor;
  return std::min(ceiling, scaled == 0 ? 1u : scaled);
}

static const char* mulSchemaName(MulSchema schema)
{
  switch (schema)
  {
    case MulSchema::Odd: return "odd";
    case MulSchema::TrailingZeros: return "trailing-zeros";
    case MulSchema::Pow2: return "power-of-two";
    case MulSchema::NegPow2: return "negated-power-of-two";
    case MulSchema::None: break;
  }
  return "none";
}

// result[0] <-> a[0] & b[0].
static void encodeMulOdd(SATSolver& solver, const std::vector<unsigned>& a,
                         const std::vector<unsigned>& b,
                         const std::vector<unsigned>& result)
{
  SATSolver::vec_literals cl;
  cl.clear(); cl.push(SATSolver::mkLit(result[0], true));  cl.push(SATSolver::mkLit(a[0], false)); solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(result[0], true));  cl.push(SATSolver::mkLit(b[0], false)); solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(result[0], false)); cl.push(SATSolver::mkLit(a[0], true)); cl.push(SATSolver::mkLit(b[0], true)); solver.addClause(cl);
}

// result[i] -> some bit of `op` at or below i, one clause per bit. The
// product cannot have fewer trailing zeros than an operand, and truncating
// it to the width does not change its low bits, so this holds of the
// truncated product too.
static void encodeMulTrailingZeros(SATSolver& solver,
                                   const std::vector<unsigned>& op,
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
static void encodeMulShiftUnderValue(SATSolver& solver,
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

  if (schema == DivSchema::RemainderAtMostDividend)
  {
    // r <= a, unconditionally: a unit clause on the chain's answer.
    const unsigned le =
        encodeLessOrEqual(solver, resultVars, dividendVars, width, false);
    cl.clear();
    cl.push(SATSolver::mkLit(le, false));
    solver.addClause(cl);
    return;
  }

  if (schema == DivSchema::QuotientAtMostDividend)
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
          (schemaLimit == 0 || abs.schemaRounds < schemaLimit);
      if (schemaAllowance)
      {
        if (abs.opKind == BVMULT)
          schema = chooseMulSchema(aBits, bBits, actual, abs.installedSchemas);
        else
          divSchema = chooseDivSchema(abs.opKind, aBits, bBits, actual,
                                      abs.installedSchemas);
      }

      incDivMul.push_back({idx, std::move(aBits), std::move(bBits),
                            std::move(expected), schema, divSchema,
                            lowestWrongBit});
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

    const unsigned carryVar =
        encodeLessOrEqual(solver, lv, rv, abs.width, inc.isSigned);

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

    // An algebraic fact the candidate contradicts, where there is one.
    // Every branch here writes a theorem about the operation over the
    // variables already in the solver -- the operand proxies and the
    // abstraction's own result bits -- so none of it is retractable and
    // none of it needs to be. What the candidate chose is only *which*
    // theorem to spend a round on.
    if (inc.divSchema.schema != DivSchema::None)
    {
      switch (inc.divSchema.schema)
      {
        case DivSchema::DivisorZero:
        case DivSchema::Pow2Divisor:
          encodeDivUnderDivisorValue(
              solver, bVars, inc.bBits, aVars, resultVars, W,
              divSchemaSources(abs.opKind, W, inc.divSchema));
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

        case DivSchema::Lemma:
          BVExactEncoder(bm).encodeDivLemma(solver,
                                            DIV_LEMMAS[inc.divSchema.lemmaIndex],
                                            W, aVars, bVars, resultVars);
          abs.installedSchemas |=
              divLemmaInstalledBit(inc.divSchema.lemmaIndex);
          break;

        case DivSchema::None:
          break;
      }

      abs.schemaRounds++;
      bm->UserFlags.coverage.bv_schema_lemmas++;
      if (bm->UserFlags.stats_flag)
        std::cerr << "BV abstraction: " << _kind_names[abs.opKind] << " "
                  << (inc.divSchema.schema == DivSchema::Lemma
                          ? divLemmaName(DIV_LEMMAS[inc.divSchema.lemmaIndex])
                          : divSchemaName(inc.divSchema.schema))
                  << " lemma" << std::endl;
      refined++;
      continue;
    }

    if (inc.schema.schema != MulSchema::None)
    {
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
          break;

        case MulSchema::NegPow2:
        {
          // The negation circuit is minted once and kept: this schema can
          // fire once per power of two, and the operand proxies it is
          // written over are the same variables every round -- the blaster
          // registers them, so getOperandVars hands back the registry's
          // entry rather than fresh bits.
          const unsigned other = 1 - chosen;
          if (abs.negatedOperand[other].empty())
            abs.negatedOperand[other] =
                encodeNegate(solver, *opVars[other], W);
          encodeMulShiftUnderValue(solver, *opVars[chosen], *opBits[chosen],
                                   abs.negatedOperand[other], resultVars, W,
                                   inc.schema.shift);
          break;
        }

        case MulSchema::None:
          break;
      }

      abs.schemaRounds++;
      bm->UserFlags.coverage.bv_schema_lemmas++;
      if (bm->UserFlags.stats_flag)
        std::cerr << "BV abstraction: BVMULT "
                  << mulSchemaName(inc.schema.schema) << " lemma over operand "
                  << chosen << std::endl;
      refined++;
      continue;
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
    const unsigned limit = valueLemmaAllowance(bm->UserFlags, W);
    if (limit != 0 && abs.blockedRounds >= limit)
    {
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

      BVExactEncoder(bm).encode(solver, encodeAs, upto, aVars, bVars,
                                resultVars);
      abs.blastedBits = upto;
      abs.defined = (upto == W);

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

  return refined;
}

} // namespace stp
