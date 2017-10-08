/********************************************************************
 * AUTHORS: Vijay Ganesh, Dan Liew, Mate Soos
 *
 * BEGIN DATE: November, 2005
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

#define __STDC_FORMAT_MACROS
#define MINISAT_CONSTANTS_AS_MACROS
#include "stp/Sat/MinisatCore.h"
#include "minisat/core/Solver.h"
//#include "utils/System.h"
//#include "simp/SimpSolver.h"

namespace MiniSat
{
}
using namespace MiniSat;

namespace stp
{

uint8_t MinisatCore::value(uint32_t x) const
{
  return Minisat::toInt(s->value(x));
}

MinisatCore::MinisatCore()
{
  s = new Minisat::Solver;
}

MinisatCore::~MinisatCore()
{
  delete s;
}

void MinisatCore::setMaxConflicts(int64_t max_confl)
{
  s->setConfBudget(max_confl);
}

bool MinisatCore::addClause(
    const SATSolver::vec_literals& ps) // Add a clause to the solver.
{
  return s->addClause(ps);
}

bool MinisatCore::okay() const // FALSE means solver is in a conflicting state
{
  return s->okay();
}

// Doesn't solve, just does a single propagate.
// returns false if UNSAT.
bool MinisatCore::propagateWithAssumptions(
    const stp::SATSolver::vec_literals& assumps)
{
  if (!s->simplify())
    return false;

  Minisat::lbool ret = s->solveLimited(assumps);
  return ret != (Minisat::lbool)l_False;
}

bool MinisatCore::solve(bool& timeout_expired) // Search without assumptions.
{
  if (!s->simplify())
    return false;

  Minisat::vec<Minisat::Lit> assumps;
  Minisat::lbool ret = s->solveLimited(assumps);
  if (ret == (Minisat::lbool)l_Undef)
  {
    timeout_expired = true;
  }

  return ret == (Minisat::lbool)l_True;
}

uint8_t MinisatCore::modelValue(uint32_t x) const
{
  return Minisat::toInt(s->modelValue(x));
}

uint32_t MinisatCore::newVar()
{
  return s->newVar();
}

void MinisatCore::setVerbosity(int v)
{
  s->verbosity = v;
}

unsigned long MinisatCore::nVars() const
{
  return s->nVars();
}

void MinisatCore::printStats() const
{
  //s->printStats();
}

int MinisatCore::nClauses()
{
  return s->nClauses();
}

bool MinisatCore::simplify()
{
  return s->simplify();
}
}
