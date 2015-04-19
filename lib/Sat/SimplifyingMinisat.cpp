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

#define __STDC_FORMAT_MACROS
#define MINISAT_CONSTANTS_AS_MACROS
#include "minisat/simp/SimpSolver.h"
#include "stp/Sat/SimplifyingMinisat.h"

namespace MiniSat {
}
using namespace MiniSat;

namespace stp
{
using std::cout;

SimplifyingMinisat::SimplifyingMinisat()
{
  s = new Minisat::SimpSolver();
}

SimplifyingMinisat::~SimplifyingMinisat()
{
  delete s;
}

void SimplifyingMinisat::setMaxConflicts(int64_t max_confl)
{
  if (max_confl> 0)
    s->setConfBudget(max_confl);
}

bool SimplifyingMinisat::addClause(
    const vec_literals& ps) // Add a clause to the solver.
{
  return s->addClause(ps);
}

bool
SimplifyingMinisat::okay() const // FALSE means solver is in a conflicting state
{
  return s->okay();
}

bool SimplifyingMinisat::solve(bool& timeout_expired) // Search without assumptions.
{
  if (!s->simplify())
    return false;

  Minisat::vec<Minisat::Lit> assumps;
  Minisat::lbool ret = s->solveLimited(assumps);
  if (ret == (Minisat::lbool)l_Undef) {
    timeout_expired = true;
  }

  return s->okay();
}

bool SimplifyingMinisat::simplify() // Removes already satisfied clauses.
{
  return s->simplify();
}

uint8_t SimplifyingMinisat::modelValue(uint32_t x) const
{
  return Minisat::toInt(s->modelValue(x));
}

void SimplifyingMinisat::setVerbosity(int v)
{
  s->verbosity = v;
}

void SimplifyingMinisat::setSeed(int i)
{
  s->random_seed = i;
}

uint32_t SimplifyingMinisat::newVar()
{
  return s->newVar();
}

unsigned long SimplifyingMinisat::nVars() const
{
  return s->nVars();
}

void SimplifyingMinisat::printStats() const
{
  //s->printStats();
}

void SimplifyingMinisat::setFrozen(uint32_t x)
{
  s->setFrozen(x, true);
}
}
