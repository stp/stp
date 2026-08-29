/********************************************************************
 * AUTHORS: Trevor Hansen
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

#include "stp/AIG/CNF.h"

#include <ostream>

namespace stp
{

void CNF::begin(uint32_t nVars, uint64_t nClauses, uint64_t nLiterals,
                uint32_t nCi, uint32_t nCo)
{
  lits_.clear();
  offsets_.clear();
  emptyClause_ = false;

  nVars_ = nVars;
  expectedClauses_ = nClauses;
  expectedLiterals_ = nLiterals;

  // Exact, from the counting pass, so neither vector ever reallocates and
  // neither ends up holding spare capacity for the life of the solve.
  lits_.reserve(nLiterals);
  offsets_.reserve(nClauses + 1);
  offsets_.push_back(0);

  ciVar_.assign(nCi, 0);
  coVar_.assign(nCo, 0);
}

void CNF::end()
{
  assert(clauseCount() == expectedClauses_);
  assert(literalCount() == expectedLiterals_);
  (void)expectedClauses_;
  (void)expectedLiterals_;
}

// DIMACS numbers variables 1..N, which is ours minus the variable 0 that does
// not exist -- so N is one less than varCount(), not equal to it. ABC writes
// its nVars here and therefore declares one variable more than it uses; that
// is harmless but it is not the file the formula asks for.
void CNF::writeDimacs(std::ostream& out) const
{
  out << "p cnf " << (nVars_ == 0 ? 0 : nVars_ - 1) << ' ' << clauseCount()
      << '\n';
  for (uint64_t i = 0, n = clauseCount(); i < n; i++)
  {
    for (const int *p = clauseBegin(i), *stop = clauseEnd(i); p < stop; p++)
    {
      const int var = *p >> 1;
      out << ((*p & 1) ? -var : var) << ' ';
    }
    out << "0\n";
  }
}

} // namespace stp
