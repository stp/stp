/********************************************************************
  *
 * BEGIN DATE: May, 2022
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

#include "stp/Sat/Cadical.h"
#include <unordered_set>
#include <algorithm>
#include <limits>
using std::vector;

namespace stp
{
unsigned long Cadical::nVars() const
{
  // Unlike other solvers Cadical doesn't need to be told about the variable in advance.
  return next_variable;
}

bool Cadical::simplify()
{
  s->simplify();
  return false;
}

void Cadical::setMaxConflicts(int64_t _max_confl)
{
  assert(_max_confl >= 0);
  max_confl = _max_confl;
}

 //    0 = UNSOLVED     (limit reached or interrupted through 'terminate')
 //   10 = SATISFIABLE
 //   20 = UNSATISFIABLE
bool Cadical::solveInternal(bool& timeout_expired)
{
  // Cadical's conflict limit only applies to the next solve() call and is
  // reset once it returns, so it has to be re-armed here. Cadical exposes no
  // count of the conflicts it has used, so unlike the time budget this one
  // cannot be made to span the whole query: each call gets the full figure.
  if (max_confl >= 0)
  {
    const int budget =
        (int)std::min(max_confl, (int64_t)std::numeric_limits<int>::max());
    s->limit("conflicts", budget);
  }

  // The Terminator reads the query's deadline from the base class, so this
  // only needs connecting -- there is nothing to re-arm.
  if (hasTimeLimit())
  {
    s->connect_terminator(&time_limit);
  }

  auto ret = s->solve();
  if (ret == 0)
  {
    timeout_expired = true;
  }
  return ret == 10;
}

Cadical::Cadical() : time_limit(*this)
{
  s = new CaDiCaL::Solver ();
  s->set("quiet",1);
}

Cadical::~Cadical()
{
  delete s;
  s = nullptr;
}

void Cadical::printStats() const
{
    std::cerr << "print stats not yet implemented.";
}

uint32_t Cadical::newVar()
{
  return ++next_variable;
}

void Cadical::setFrozen(uint32_t var)
{
  // Deliberately not s->freeze(var). Refinement encodes clauses over
  // these variables in later solve calls, which is safe here without
  // freezing: Cadical restores an eliminated variable the moment a new
  // clause mentions it, and extends every model over the eliminated
  // variables, so both the added clauses and the values the refinement
  // loop reads stay correct. Freezing instead would keep every
  // refinement-visible variable out of inprocessing whether or not any
  // lemma ever mentions it, which measures ~25% slower on the
  // wchains array-equality benchmarks (three-run A/B on wchains016ue:
  // 19.9-20.5s frozen against 15.9-16.0s restored). Solvers without
  // restoration (the simplifying Minisat family) genuinely need their
  // setFrozen; this one is a documented decision, not an omission.
  (void)var;
}

bool Cadical::setSearchBias(SearchBias bias)
{
  // Cadical has named configurations of its own, so this is a straight
  // translation. "unsat" turns off stabilising search and the local-search
  // walker, keeping Cadical in focused, restart-heavy search; "sat" leaves it
  // stabilising and spends more effort on elimination and subsumption.
  //
  // Cadical only accepts a configuration "right after initialization", which
  // is why this is applied here rather than at solve time. Setting "quiet" in
  // the constructor doesn't spoil that: quiet and verbose are exempt from
  // Cadical's state check, and only adding a clause leaves the configuring
  // state.
  const char* config = nullptr;
  switch (bias)
  {
    case SearchBias::SAT:
      config = "sat";
      break;
    case SearchBias::UNSAT:
      config = "unsat";
      break;
    case SearchBias::NONE:
      return true; // nothing to do, which counts as honouring the request.
  }

  return s->configure(config);
}

void Cadical::setVerbosity(int v)
{
  if (v ==0)
    {
      s->set("quiet",1);
      s->set("verbose",0);
    }
  else
    {
      s->set("quiet",0);
      s->set("verbose",1);
    }

}

bool Cadical::okay()
    const // FALSE means solver is in a conflicting state
{
  return s->state() != CaDiCaL::State::UNSATISFIED; 
}

bool Cadical::addClause(const vec_literals& ps) // Add a clause to the solver.
{
  for (int i=0; i < ps.size(); i++)
    {
      uint32_t var = ps[i].x >> 1;
      uint32_t polarity = ps[i].x & 1;
      s->add(polarity? -(int)var : (int)var);
    }
  s->add(0);
  return false;
}

uint8_t Cadical::modelValue(uint32_t x) const
{
  if (s->val(x) > 0)
    return true_literal();
  else
    return false_literal();
}


} //end namespace stp
