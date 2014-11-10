// -*- c++ -*-
/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: 2010
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

#ifndef SIMPLIFYINGMINISAT_H_
#define SIMPLIFYINGMINISAT_H_

#include "SATSolver.h"

namespace Minisat
{
class SimpSolver;
}

namespace BEEV
{
class SimplifyingMinisat : public SATSolver
{
  Minisat::SimpSolver* s;

public:
  SimplifyingMinisat(volatile bool& timeout);
  ~SimplifyingMinisat();

  bool addClause(const vec_literals& ps); // Add a clause to the solver.

  bool okay() const; // FALSE means solver is in a conflicting state

  bool solve(); // Search without assumptions.

  bool simplify(); // Removes already satisfied clauses.

  void setVerbosity(int v);

  virtual uint8_t modelValue(uint32_t x) const;

  virtual uint32_t newVar();

  unsigned long nVars();

  void printStats();

  virtual void setSeed(int i);

  virtual lbool true_literal() { return ((uint8_t)0); }
  virtual lbool false_literal() { return ((uint8_t)1); }
  virtual lbool undef_literal() { return ((uint8_t)2); }

  virtual void setFrozen(uint32_t x);
};
}

#endif /* CORE_H_ */
