#include "CryptoMinisat.h"
#include "utils/System.h"

#undef var_Undef
#undef l_True
#undef l_False
#undef l_Undef


#include "cryptominisat2/Solver.h"
#include "cryptominisat2/SolverTypes.h"

namespace BEEV
{

  CryptoMinisat::CryptoMinisat()
  {
     s = new MINISAT::Solver();
  }

  CryptoMinisat::~CryptoMinisat()
  {
    delete s;
  }

  bool
  CryptoMinisat::addClause(const vec_literals& ps) // Add a clause to the solver.
  {
    // Cryptominisat uses a slightly different vec class.
    // Cryptominisat uses a slightly different Lit class too.

    // VERY SLOW>
    MINISAT::vec<MINISAT::Lit>  v;
    for (int i =0; i<ps.size();i++)
      v.push(MINISAT::Lit(var(ps[i]), sign(ps[i])));

    s->addClause(v);
  }

  bool
  CryptoMinisat::okay() const // FALSE means solver is in a conflicting state
  {
    return s->okay();
  }

  bool
  CryptoMinisat::solve() // Search without assumptions.
  {
    return s->solve().getchar();
  }

  uint8_t
  CryptoMinisat::modelValue(Var x) const
  {
    return s->model[x].getchar();
  }

  Minisat::Var
  CryptoMinisat::newVar()
  {
    return s->newVar();
  }

  int CryptoMinisat::setVerbosity(int v)
  {
    s->verbosity = v;
  }

  int CryptoMinisat::nVars()
  {return s->nVars();}

  void CryptoMinisat::printStats()
    {
        s->printStats();
    }
};
