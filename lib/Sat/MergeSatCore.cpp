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
#include "stp/Sat/MergeSatCore.h"
#include "minisat/core/Solver.h"
//#include "utils/System.h"
//#include "simp/SimpSolver.h"

namespace MergeSat
{
}
using namespace MergeSat;

namespace stp
{

uint8_t MergeSatCore::value(uint32_t x) const
{
  return MergeSat::toInt(s->value(x));
}

MergeSatCore::MergeSatCore()
{
  s = new MergeSat::Solver;
}

MergeSatCore::~MergeSatCore()
{
  delete s;
}

void MergeSatCore::setMaxConflicts(int64_t max_confl)
{
  s->setConfBudget(max_confl);
}

bool MergeSatCore::addClause(
    const SATSolver::vec_literals& ps) // Add a clause to the solver.
{
  return s->addClause(ps);
}

bool MergeSatCore::okay() const // FALSE means solver is in a conflicting state
{
  return s->okay();
}

// *Doesn't solve*, just does a single unit propagate.
// returns false if UNSAT.
bool MergeSatCore::propagateWithAssumptions(
    const stp::SATSolver::vec_literals& assumps)
{
  if (!s->simplify())
    return false;

  setMaxConflicts(0);
  MergeSat::lbool ret = s->solveLimited(assumps);
  assert(s->conflicts ==0);
  return ret != (MergeSat::lbool)l_False;
}

bool MergeSatCore::solve(bool& timeout_expired) // Search without assumptions.
{
  if (!s->simplify())
    return false;

  MergeSat::vec<MergeSat::Lit> assumps;
  MergeSat::lbool ret = s->solveLimited(assumps);
  if (ret == (MergeSat::lbool)l_Undef)
  {
    timeout_expired = true;
  }

  return ret == (MergeSat::lbool)l_True;
}

uint8_t MergeSatCore::modelValue(uint32_t x) const
{
  return MergeSat::toInt(s->modelValue(x));
}

uint32_t MergeSatCore::newVar()
{
  return s->newVar();
}

void MergeSatCore::setVerbosity(int v)
{
  s->verbosity = v;
}

unsigned long MergeSatCore::nVars() const
{
  return s->nVars();
}

void MergeSatCore::printStats() const
{
  //s->printStats();
}

int MergeSatCore::nClauses()
{
  return s->nClauses();
}

bool MergeSatCore::simplify()
{
  return s->simplify();
}
}
