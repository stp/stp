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
// This is how --bv-term-abstraction gives up. A BVMULT, BVDIV or BVMOD it
// abstracted is refined by ruling out one pair of operand values at a time,
// and after a bounded number of those the refinement stops enumerating and
// says what the operation is. What it says has to be worth having: an
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

#include <vector>

namespace stp
{

class DLL_PUBLIC BVExactEncoder
{
  STPMgr* bm;

public:
  explicit BVExactEncoder(STPMgr* bm_) : bm(bm_) {}

  // `term` is the operation's own node -- its kind is one of BVMULT, BVDIV
  // and BVMOD, and the multiplier reads its operands for constant detection
  // and Booth recoding. `aVars`, `bVars` and `resultVars` are the SAT
  // variables the operands and the result are already carried by, each
  // `width` bits wide; every one of them must be a variable the solver has.
  //
  // The clauses added define the result bits from the operand bits, so a
  // caller may mark the abstraction defined once this returns.
  void encode(SATSolver& solver, const ASTNode& term, unsigned width,
              const std::vector<unsigned>& aVars,
              const std::vector<unsigned>& bVars,
              const std::vector<unsigned>& resultVars);
};

} // namespace stp

#endif
