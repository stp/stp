#include "minisat/core/Solver.h"
#include "MinisatCore.h"
//#include "utils/System.h"
//#include "simp/SimpSolver.h"

namespace BEEV
{

  template <class T>
  MinisatCore<T>::MinisatCore(volatile bool& interrupt)
  {
     s = new T(interrupt);
  };

  template <class T>
  MinisatCore<T>::~MinisatCore()
  {
    delete s;
  }

  template <class T>
  bool
  MinisatCore<T>::addClause(const SATSolver::vec_literals& ps) // Add a clause to the solver.
  {
    return s->addClause(ps);
  }

  template <class T>
  bool
  MinisatCore<T>::okay() const // FALSE means solver is in a conflicting state
  {
    return s->okay();
  }

  template <class T>
  bool
  MinisatCore<T>::solve() // Search without assumptions.
  {
    if (!s->simplify())
      return false;

    return s->solve();

  }

  template <class T>
  uint8_t
  MinisatCore<T>::modelValue(Var x) const
  {
    return Minisat::toInt(s->modelValue(x));
  }

  template <class T>
  Minisat::Var
  MinisatCore<T>::newVar()
  {
    return s->newVar();
  }

  template <class T>
  void MinisatCore<T>::setVerbosity(int v)
  {
    s->verbosity = v;
  }

    template <class T>
    void MinisatCore<T>::setSeed(int i)
    {
      s->random_seed = i;
    }


  template <class T>
  int MinisatCore<T>::nVars()
  {return s->nVars();}

  template <class T>
  void MinisatCore<T>::printStats()
    {
      s->printStats();
    }

  template <class T>
    int MinisatCore<T>::nClauses()
  {
    return s->nClauses();
  }

  template <class T>
    bool MinisatCore<T>::simplify()
  {
    return s->simplify();
  }



  // I was going to make SimpSolver and Solver instances of this template.
  // But I'm not so sure now because I don't understand what eliminate() does in the simp solver.
  template class MinisatCore<Minisat::Solver>;
  //template class MinisatCore<Minisat::SimpSolver>;
};
