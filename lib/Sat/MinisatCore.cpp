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
#include "stp/Sat/MinisatCore.h"
#include "minisat/core/Solver.h"
#include <iostream>
//#include "utils/System.h"
//#include "simp/SimpSolver.h"

namespace MiniSat
{
}
using namespace MiniSat;

namespace stp
{

// STP's literal encoding (variable*2 + sign) is the one MiniSat itself
// uses, so translation is a straight reinterpretation of each literal.
static void convert(const SATSolver::vec_literals& ps,
                    Minisat::vec<Minisat::Lit>& out)
{
  for (int i = 0; i < ps.size(); i++)
    out.push(Minisat::toLit(SATSolver::toInt(ps[i])));
}

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
  assert(max_confl >= 0);
  s->setConfBudget(max_confl);
}

bool MinisatCore::addClauseInternal(
    const SATSolver::vec_literals& ps) // Add a clause to the solver.
{
  Minisat::vec<Minisat::Lit> clause;
  convert(ps, clause);
  return s->addClause_(clause);
}

void MinisatCore::unsatAssumptions(const vec_literals& assumps,
                                   std::vector<int>& out)
{
  // After an unsat assumption solve, MiniSat's `conflict` holds the final
  // conflict clause expressed in the assumptions: the negations of the
  // failed ones. An assumption is in the core iff its negation appears.
  out.clear();
  for (int i = 0; i < assumps.size(); i++)
  {
    const Minisat::Lit assumed =
        Minisat::toLit(SATSolver::toInt(assumps[i]));
    if (s->conflict.has(~assumed))
      out.push_back(assumps[i].x);
  }
}

bool MinisatCore::okay() const // FALSE means solver is in a conflicting state
{
  return s->okay();
}

bool MinisatCore::solveInternal(bool& timeout_expired)
{
  if (!s->simplify())
    return false;

  Minisat::vec<Minisat::Lit> assumps;
  Minisat::lbool ret = s->solveLimited(assumps);
  if (ret == (Minisat::lbool)Minisat::l_Undef)
  {
    timeout_expired = true;
  }

  return ret == (Minisat::lbool)Minisat::l_True;
}

bool MinisatCore::solveWithAssumptionsInternal(
    const stp::SATSolver::vec_literals& assumps, bool& timeout_expired)
{
  // simplify() only removes clauses satisfied at level 0; the core solver
  // never eliminates variables, so assumption literals are safe across it.
  if (!s->simplify())
    return false;

  Minisat::vec<Minisat::Lit> ms_assumps;
  convert(assumps, ms_assumps);
  Minisat::lbool ret = s->solveLimited(ms_assumps);
  if (ret == (Minisat::lbool)Minisat::l_Undef)
  {
    timeout_expired = true;
  }

  return ret == (Minisat::lbool)Minisat::l_True;
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

uint32_t MinisatCore::nVars() const
{
  return s->nVars();
}

void MinisatCore::printStats() const
{
  // MiniSat's periodic table is useful while a long search is running, but
  // fixed-conflict profiles also need exact final totals. In particular,
  // propagations/conflict distinguishes SAT-search work from front-end time.
  std::cerr << "MiniSat starts: " << s->starts << '\n';
  std::cerr << "MiniSat conflicts: " << s->conflicts << '\n';
  std::cerr << "MiniSat decisions: " << s->decisions << '\n';
  std::cerr << "MiniSat propagations: " << s->propagations << '\n';
  std::cerr << "MiniSat variables: " << s->nVars() << '\n';
  if (s->conflicts != 0)
  {
    std::cerr << "MiniSat decisions per conflict: "
              << static_cast<double>(s->decisions) / s->conflicts << '\n';
    std::cerr << "MiniSat propagations per conflict: "
              << static_cast<double>(s->propagations) / s->conflicts << '\n';
  }
  std::cerr << "MiniSat active original clauses: " << s->nClauses() << '\n';
  std::cerr << "MiniSat active original literals: " << s->clauses_literals
            << '\n';
  std::cerr << "MiniSat active learnt clauses: " << s->nLearnts() << '\n';
  std::cerr << "MiniSat active learnt literals: " << s->learnts_literals
            << '\n';
  if (s->nLearnts() != 0)
    std::cerr << "MiniSat active learnt literals per clause: "
              << static_cast<double>(s->learnts_literals) / s->nLearnts()
              << '\n';
  std::cerr << "MiniSat learnt literals before minimization: "
            << s->max_literals << '\n';
  std::cerr << "MiniSat learnt literals after minimization: "
            << s->tot_literals << '\n';
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
