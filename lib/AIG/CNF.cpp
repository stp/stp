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
  discard();

  nVars_ = nVars;
  expectedClauses_ = nClauses;
  expectedLiterals_ = nLiterals;

  // Exact, from the counting pass, so neither vector ever reallocates and
  // neither ends up holding spare capacity for the life of the solve.
  // longLens_ is not reserved: the counting pass does not say how many
  // clauses are long, and on the formulas that have any there are a handful.
  lits_.reserve(nLiterals);
  lens_.reserve(nClauses);

  ciVar_.assign(nCi, 0);
  coVar_.assign(nCo, 0);
}

void CNF::end()
{
  assert(nClauses_ == expectedClauses_);
  assert(nLiterals_ == expectedLiterals_);
}

void CNF::adopt(void* owner, void (*release)(void*), const int* const* clauses,
                uint64_t nClauses, uint64_t nLiterals, uint32_t nVars,
                uint32_t nCi, uint32_t nCo)
{
  discard();

  adopted_ = clauses;
  owner_ = owner;
  release_ = release;
  nClauses_ = nClauses;
  nLiterals_ = nLiterals;
  nVars_ = nVars;
  ciVar_.assign(nCi, 0);
  coVar_.assign(nCo, 0);
}

void CNF::discard()
{
  if (release_ != nullptr)
    release_(owner_);
  adopted_ = nullptr;
  owner_ = nullptr;
  release_ = nullptr;

  // Actually give the memory back rather than clearing: a CNF is reset only
  // when it is about to hold a different formula, and the two must not be
  // resident at once.
  std::vector<int>().swap(lits_);
  std::vector<uint8_t>().swap(lens_);
  std::vector<uint64_t>().swap(longLens_);
  ciVar_.clear();
  coVar_.clear();

  nClauses_ = 0;
  nLiterals_ = 0;
  expectedClauses_ = 0;
  expectedLiterals_ = 0;
  nVars_ = 1;
  emptyClause_ = false;
}

void CNF::steal(CNF& o)
{
  lits_ = std::move(o.lits_);
  lens_ = std::move(o.lens_);
  longLens_ = std::move(o.longLens_);
  adopted_ = o.adopted_;
  owner_ = o.owner_;
  release_ = o.release_;
  ciVar_ = std::move(o.ciVar_);
  coVar_ = std::move(o.coVar_);
  nClauses_ = o.nClauses_;
  nLiterals_ = o.nLiterals_;
  expectedClauses_ = o.expectedClauses_;
  expectedLiterals_ = o.expectedLiterals_;
  nVars_ = o.nVars_;
  emptyClause_ = o.emptyClause_;

  // The source must not free what we now own.
  o.adopted_ = nullptr;
  o.owner_ = nullptr;
  o.release_ = nullptr;
  o.nClauses_ = 0;
  o.nLiterals_ = 0;
  o.nVars_ = 1;
  o.emptyClause_ = false;
}

// Byte for byte what Cnf_DataWriteIntoFile() produced, because --output-CNF
// is a user-facing file and an internal reshuffle is no reason for it to
// change -- and because CNF byte-identity across a refactor is only evidence
// if the bytes are of the formula rather than of the writer.
//
// Two things are ABC's rather than ours, and are kept deliberately. The
// banner names the package that used to write this. And the variable numbers
// are one *above* the formula's, so a file declaring N variables uses 2..N
// and leaves 1 unused: ABC numbered from 1 internally and then added another
// 1 on the way out. Both are worth revisiting when the ABC generators go, and
// neither before.
void CNF::writeDimacs(std::ostream& out) const
{
  out << "c Result of efficient AIG-to-CNF conversion using package CNF\n";
  out << "p cnf " << nVars_ << ' ' << clauseCount() << '\n';
  for (ClauseCursor c = clauses(); c.next();)
  {
    for (const int *p = c.begin(), *stop = c.end(); p < stop; p++)
    {
      const int var = (*p >> 1) + 1;
      out << ((*p & 1) ? -var : var) << ' ';
    }
    out << "0\n";
  }
  out << '\n';
}

} // namespace stp
