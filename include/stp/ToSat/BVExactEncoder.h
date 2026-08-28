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

#ifndef BVEXACTENCODER_H
#define BVEXACTENCODER_H

// Puts `result = a op b` into a SAT solver that is already running, over
// variables it already has.
//
// This is how --bv-term-abstraction gives up, and how its algebraic schemas
// are inserted. A BVMULT, BVDIV or BVMOD it abstracted is refined by ruling
// out one pair of operand values at a time, and after a bounded number of
// those the refinement stops enumerating and says what the operation is.
// Addition, multiplication, division and remainder schemas use the same
// circuit-to-live-CNF splice to assert facts that rule out larger candidate
// regions. What any of those encodings says has to be worth having: an
// abstraction that is abandoned late should leave the solver no worse off
// than one that was never taken, and the only way that holds is if the
// encoding it falls back on is the one the query would have had anyway.
//
// So this does not write clauses. It builds the circuit with the same
// BitBlaster that a plain solve uses, hands the AIG to the same ABC cut
// enumeration and technology mapping that ToCNFAIG uses, and splices the
// CNF that comes back onto the variables the abstraction has been talking
// about all along -- the operand proxies and the abstraction's own result
// bits. Hand-written gates were about twice the clauses for the same
// function, which is a strange thing to pay for at the exact moment the
// abstraction has admitted it is not helping.
//
// Nothing here is retractable and nothing needs to be: what it adds is a
// definitional fact about the operation, true whatever else is asserted.

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Sat/SATSolver.h"
#include "stp/ToSat/BVLemmaCatalogue.h"

#include <memory>
#include <vector>

namespace stp
{

class Simplifier;
class SubstitutionMap;

class DLL_PUBLIC BVExactEncoder
{
  STPMgr* bm;

  // A blast needs a Simplifier, and a Simplifier needs a SubstitutionMap.
  // Neither carries anything from one call here to the next -- there is no
  // constant-bit propagation for a fragment of a query, and the multiplier
  // asks for it only through statsFound(), which answers no without one --
  // but both allocate, and a refinement round installs one lemma per
  // inconsistent record. Owned by the encoder rather than rebuilt per lemma.
  std::unique_ptr<SubstitutionMap> substitutions_;
  std::unique_ptr<Simplifier> scratch_;

public:
  explicit BVExactEncoder(STPMgr* bm_);
  ~BVExactEncoder();

  BVExactEncoder(const BVExactEncoder&) = delete;
  BVExactEncoder& operator=(const BVExactEncoder&) = delete;

  // `term` is the operation's own node -- its kind is one of BVMULT, BVDIV
  // and BVMOD, and it supplies the width and the operand order. `aVars`,
  // `bVars` and `resultVars` are the SAT variables the operands and the
  // result are already carried by, each `width` bits wide; every one of them
  // must be a variable the solver has.
  //
  // `knownA` and `knownB` are what the query's own blast knew about the
  // operand bits before the abstraction replaced them with proxy inputs: -1
  // for a live node, 0 or 1 for a constant, and empty for "nothing known".
  // A known bit is built into the circuit as a constant instead of a free
  // input, which is what makes this the encoding the query would have had
  // rather than a fully symbolic one -- every constant shortcut in the
  // multiplier and the divider tests the bit vector, not the AST, so without
  // them none of them fires. It is sound to drop the corresponding operand
  // variable from the splice: the proxy it names is pinned to that same
  // constant by the side constraint that minted it.
  //
  // The clauses added define the result bits from the operand bits, so a
  // caller may mark the abstraction defined once this returns.
  void encode(SATSolver& solver, const ASTNode& term, unsigned width,
              const std::vector<unsigned>& aVars,
              const std::vector<unsigned>& bVars,
              const std::vector<unsigned>& resultVars,
              const std::vector<signed char>& knownA = {},
              const std::vector<signed char>& knownB = {});

  // One algebraic fact about `t = x udiv s`, spliced onto the variables the
  // dividend, the divisor and the abstraction's result are already carried
  // by, and asserted.
  //
  // The same splice as `encode` above and for the same reason: a lemma has
  // to talk about the bits the rest of the query talks about. What differs
  // is that this asserts a single Boolean rather than defining the result
  // bits, so the abstraction stays an abstraction -- the fact constrains it
  // without saying what it is.
  //
  // Going through the bit-blaster rather than emitting clauses by hand is
  // what makes the facts below affordable at all: several are inequalities
  // over a shift by a variable amount, which is a barrel shifter, which is
  // not something to write a clause at a time.
  void encodeDivLemma(SATSolver& solver, DivLemma lemma, unsigned width,
                      const std::vector<unsigned>& dividendVars,
                      const std::vector<unsigned>& divisorVars,
                      const std::vector<unsigned>& resultVars);

  void encodeRemLemma(SATSolver& solver, RemLemma lemma, unsigned width,
                      const std::vector<unsigned>& dividendVars,
                      const std::vector<unsigned>& divisorVars,
                      const std::vector<unsigned>& resultVars);

  void encodeMulLemma(SATSolver& solver, MulLemma lemma, unsigned width,
                      const std::vector<unsigned>& xVars,
                      const std::vector<unsigned>& sVars,
                      const std::vector<unsigned>& resultVars);

  void encodeAddLemma(SATSolver& solver, AddLemma lemma, unsigned width,
                      const std::vector<unsigned>& xVars,
                      const std::vector<unsigned>& sVars,
                      const std::vector<unsigned>& resultVars);

  // Splice x = q*s+r over the four live vectors belonging to a paired BVDIV
  // and BVMOD abstraction. Arithmetic is truncated to `width`, so this is a
  // theorem of SMT-LIB's totalised division even when the divisor is zero.
  void encodeDivRemIdentity(SATSolver& solver, const ASTNode& product,
                            unsigned width,
                            const std::vector<unsigned>& dividendVars,
                            const std::vector<unsigned>& divisorVars,
                            const std::vector<unsigned>& quotientVars,
                            const std::vector<unsigned>& remainderVars);
};

} // namespace stp

#endif
