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
 * Side-effect-free congruence lemma canonicalization/validation.
 ********************************************************************/
#ifndef STP_UFLEMMA_H
#define STP_UFLEMMA_H

#include "stp/UninterpretedFunctions/UFChecker.h"

namespace stp
{

struct DLL_PUBLIC UFEqualityAtom
{
  ASTNode left;
  ASTNode right;
  SourceSort sort;
  size_t originalPosition = 0;
};

struct DLL_PUBLIC UFAbstractLemma
{
  std::vector<UFEqualityAtom> premise;
  UFEqualityAtom conclusion;
  uint64_t candidateVersion = 0;

  // The final implication clause has one negated literal per premise and one
  // positive conclusion literal. This evaluates it from already observed
  // equality truth values without constructing an AST or touching SAT.
  bool evaluate(bool conclusionEquality,
                const std::vector<bool>& premiseEqualities) const;
};

class DLL_PUBLIC UFLemmaOracle final
{
public:
  // Produces the canonical abstract layer and proves it rejects the
  // certificate's unchanged candidate before either host adapter may mutate
  // SAT. A false return is an internal error and carries a diagnostic.
  static bool buildAndValidate(const UFCongruenceConflict& conflict,
                               UFAbstractLemma& lemma,
                               std::string& diagnostic);
};

} // namespace stp

#endif
