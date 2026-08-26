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

// Everything from Riss is spelled out with its namespace. A `using namespace
// Riss;` here does not do what it looks like it does: inside a member function
// of RissCore, class scope is searched first, so an unqualified `Lit` binds to
// the inherited SATSolver::Lit and never reaches Riss at all. That silently
// produced a Riss::vec<stp::SATSolver::Lit> where a Riss::vec<Riss::Lit> was
// meant. Riss's l_True/l_False/l_Undef are macros, so they need no using
// directive (and cannot be namespace-qualified).
namespace stp
{

RissCore::RissCore()
{
  s = new Riss::Solver;
  riss_clause = new Riss::vec<Riss::Lit>();
}

RissCore::~RissCore()
{
  // Riss::Solver is polymorphic but declares no virtual destructor. The delete
  // is safe because the object is always created as exactly Riss::Solver and
  // never as a subclass, but the compiler cannot see that. (MiniSat's Solver
  // does declare a virtual destructor, which is why MinisatCore needs no
  // equivalent suppression.)
#if defined(__GNUC__) || defined(__clang__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wdelete-non-virtual-dtor"
#endif
  delete s;
#if defined(__GNUC__) || defined(__clang__)
#pragma GCC diagnostic pop
#endif
  if(riss_clause) {
    Riss::vec<Riss::Lit> *v = (Riss::vec<Riss::Lit> *)riss_clause;
    delete v;
    riss_clause = 0;
  }
}

void RissCore::setMaxConflicts(int64_t max_confl)
{
  assert(max_confl >= 0);
  s->setConfBudget(max_confl);
}

bool RissCore::addClauseInternal(
    const SATSolver::vec_literals& ps) // Add a clause to the solver.
{
  // STP's literal encoding (variable*2 + sign) is the one Riss itself uses, so
  // translation is a straight reinterpretation of each literal.
  Riss::vec<Riss::Lit>& v = *(Riss::vec<Riss::Lit>*)riss_clause;
  v.capacity(ps.size());
  v.clear();
  for(int i = 0 ; i < ps.size(); ++ i)
    v.push_(Riss::toLit(SATSolver::toInt(ps[i])));

  return s->addClause(v);
}

bool RissCore::okay() const // FALSE means solver is in a conflicting state
{
  return s->okay();
}

void RissCore::unsatAssumptions(const vec_literals& assumps,
                                std::vector<int>& out)
{
  // After an unsat assumption solve, Riss's `conflict` holds the final
  // conflict clause expressed in the assumptions: the negations of the failed
  // ones. An assumption is in the core iff its negation appears. Without this
  // Riss would inherit SATSolver's fallback, which reports every assumption --
  // sound, but no use to anyone asking which one is to blame.
  out.clear();
  for (int i = 0; i < assumps.size(); i++)
  {
    const Riss::Lit assumed = Riss::toLit(SATSolver::toInt(assumps[i]));
    // Riss's vec has no has(), unlike MiniSat's, so this scans.
    for (int j = 0; j < s->conflict.size(); j++)
    {
      if (s->conflict[j] == ~assumed)
      {
        out.push_back(assumps[i].x);
        break;
      }
    }
  }
}

bool RissCore::solveInternal(bool& timeout_expired)
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

bool RissCore::solveWithAssumptionsInternal(
    const stp::SATSolver::vec_literals& assumps, bool& timeout_expired)
{
  if (!s->simplify())
    return false;

  // convert the vector, as in addClause
  Riss::vec<Riss::Lit> riss_assumps;
  riss_assumps.capacity(assumps.size());
  for (int i = 0; i < assumps.size(); ++i)
    riss_assumps.push_(Riss::toLit(SATSolver::toInt(assumps[i])));

  Riss::lbool ret = s->solveLimited(riss_assumps);
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

uint32_t RissCore::nVars() const
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
