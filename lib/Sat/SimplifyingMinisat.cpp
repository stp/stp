#include "stp/Sat/SimplifyingMinisat.h"
#include "minisat/simp/SimpSolver.h"
//#include "utils/System.h"

namespace BEEV
{
  using std::cout;

  SimplifyingMinisat::SimplifyingMinisat(volatile bool& timeout)
  {
	 s = new Minisat::SimpSolver(timeout);
  }

  SimplifyingMinisat::~SimplifyingMinisat()
  {
    delete s;
  }

  bool
  SimplifyingMinisat::addClause(const vec_literals& ps) // Add a clause to the solver.
  {
    return s->addClause(ps);
  }

  bool
  SimplifyingMinisat::okay() const // FALSE means solver is in a conflicting state
  {
    return s->okay();
  }

  bool
  SimplifyingMinisat::solve() // Search without assumptions.
  {
    if (!s->simplify())
      return false;

    return s->solve();
  }

  bool
  SimplifyingMinisat::simplify() // Removes already satisfied clauses.
  {
    return s->simplify();
  }

  uint8_t
  SimplifyingMinisat::modelValue(uint32_t x) const
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

  uint32_t
  SimplifyingMinisat::newVar()
  {
    return s->newVar();
  }

  unsigned long SimplifyingMinisat::nVars()
  {return s->nVars();}

  void SimplifyingMinisat::printStats()
  {
      s->printStats();
  }

  void SimplifyingMinisat::setFrozen(uint32_t x)
  {
      s->setFrozen(x,true);
  }
}
