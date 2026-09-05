/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: August, 2026
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

/********************************************************************
 * Certified public models for durable uninterpreted applications.
 ********************************************************************/
#ifndef STP_UFMODEL_H
#define STP_UFMODEL_H

#include "stp/UninterpretedFunctions/UFChecker.h"
#include <iosfwd>
#include <string>

namespace stp
{

class AbsRefine_CounterExample;
class STPMgr;
class UFTheoryAdapter;

// The only boundary from UFCHK's representation-independent values to host
// ASTs and public output. Lowered result/name symbols never cross it.
class DLL_PUBLIC UFModel final
{
public:
  // Build a constant of the value's own source sort in manager: a Boolean, a
  // bit-vector literal, or a rounding-mode constant. A carrier that denotes
  // no value of the sort is refused rather than published.
  static ASTNode concreteValue(STPMgr* manager,
                               const UFConcreteValue& value);

  // As above, for a value stored at a signature position's *lowering* sort
  // and published at its declared one. The two differ only for
  // FloatingPoint, which is solved as its canonical packed carrier and
  // becomes a float again here.
  static ASTNode concreteValue(STPMgr* manager, const UFConcreteValue& value,
                               const SourceSort& declared);

  // Evaluate one context-owned, active, registered durable application from
  // the most recently certified solve map. Failures are nonfatal and leave
  // value undefined.
  static bool evaluateApplication(STPMgr* manager,
                                  const UFTheoryAdapter* adapter,
                                  const ASTNode& durableHandle,
                                  ASTNode& value,
                                  std::string& diagnostic);

  // Evaluate a durable application when it appears *inside* a larger term
  // being read against the model, where refusing is not an option: the
  // enclosing operator needs a constant operand.
  //
  // An application the certified solve reached resolves exactly as
  // evaluateApplication does. One it did not reach is completed through the
  // certified function-model seed, keyed on `actualValues` -- the actuals
  // already evaluated to Bool/BV constants, in declaration order. That is the
  // same total interpretation printSMTLIB2 emits, so model output and model
  // evaluation cannot disagree, and equal argument tuples always give equal
  // results (completing with an arbitrary constant instead would break
  // congruence). A declaration with no certified observations at all is
  // completed with its codomain's zero.
  //
  // Failures are nonfatal and leave value undefined.
  static bool evaluateApplicationInTerm(
      STPMgr* manager, const UFTheoryAdapter* adapter,
      const ASTNode& durableHandle, const std::vector<ASTNode>& actualValues,
      ASTNode& value, std::string& diagnostic);

  // Complete every durable application in the preserved public root with its
  // certified value. This is used for the final pointwise model replay; the
  // returned root contains no UF_APPLY and no solve-local symbol.
  static bool completePublicRoot(STPMgr* manager,
                                 const UFTheoryAdapter& adapter,
                                 ASTNode& completed,
                                 std::string& diagnostic);

  static bool replayPublicRoot(AbsRefine_CounterExample& counterexample,
                               const UFTheoryAdapter& adapter,
                               std::string& diagnostic);

  // Vacuous certified interpretation for active declarations when the
  // completed root contains no UF application at all.
  static UFFunctionModelSeedSet
  defaultSeed(const std::vector<const UFDecl*>& declarations);

  // Emit one valid deterministic SMT-LIB2 define-fun per active declaration,
  // including declarations with no active observations.
  static void printSMTLIB2(std::ostream& os,
                           const UFFunctionModelSeedSet& seed);
};

} // namespace stp

#endif
