/********************************************************************
 * AUTHORS: Vijay Ganesh, Dan Liew, Mate Soos, Norbert Manthey
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
#include "stp/Sat/Riss.h"
#include "riss/core/Solver.h"
//#include "utils/System.h"
//#include "simp/SimpSolver.h"

namespace Riss
{
}
using namespace Riss;

namespace stp
{

uint8_t RissCore::value(uint32_t x) const
{
  return Riss::toInt(s->value(x));
}

RissCore::RissCore()
{
  s = new Riss::Solver;
  riss_clause = new Riss::vec<Lit>();
}

RissCore::~RissCore()
{
  delete s;
  if(riss_clause) {
    Riss::vec<Riss::Lit> *v = (Riss::vec<Riss::Lit> *)riss_clause;
    delete v;
    riss_clause = 0;
  }
}

void RissCore::setMaxConflicts(int64_t max_confl)
{
  s->setConfBudget(max_confl);
}

bool RissCore::addClause(
    const SATSolver::vec_literals& ps) // Add a clause to the solver.
{
  // convert the vector
  Riss::vec<Lit> &v = *(Riss::vec<Riss::Lit> *)riss_clause;
  v.capacity(ps.size());
  v.clear();
  for(int i = 0 ; i < ps.size(); ++ i) v.push_(Riss::toLit(Minisat::toInt(ps[i])));

  return s->addClause(v);
}

bool RissCore::okay() const // FALSE means solver is in a conflicting state
{
  return s->okay();
}

// *Doesn't solve*, just does a single unit propagate.
// returns false if UNSAT.
bool RissCore::propagateWithAssumptions(
    const stp::SATSolver::vec_literals& assumps)
{
  if (!s->simplify())
    return false;

  setMaxConflicts(0);

  // convert the vector
  Riss::vec<Lit> &v = *(Riss::vec<Riss::Lit> *)riss_clause;
  v.capacity(assumps.size());
  v.clear();
  for(int i = 0 ; i < assumps.size(); ++ i) v.push_(Riss::toLit(Minisat::toInt(assumps[i])));

  Riss::lbool ret = s->solveLimited(v);
  assert(s->conflicts ==0);
  return ret != (Riss::lbool)l_False;
}

bool RissCore::solve(bool& timeout_expired) // Search without assumptions.
{
  if (!s->simplify())
    return false;

  Riss::vec<Riss::Lit> assumps;
  Riss::lbool ret = s->solveLimited(assumps);
  if (ret == (Riss::lbool)l_Undef)
  {
    timeout_expired = true;
  }

  return ret == (Riss::lbool)l_True;
}

uint8_t RissCore::modelValue(uint32_t x) const
{
  return Riss::toInt(s->modelValue(x));
}

uint32_t RissCore::newVar()
{
  return s->newVar();
}

void RissCore::setVerbosity(int v)
{
  s->verbosity = v;
}

unsigned long RissCore::nVars() const
{
  return s->nVars();
}

void RissCore::printStats() const
{
  //s->printStats();
}

int RissCore::nClauses()
{
  return s->nClauses();
}

bool RissCore::simplify()
{
  return s->simplify();
}
}
