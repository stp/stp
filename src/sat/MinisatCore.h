/*
 * Wraps around CORE minisat.
 */
#ifndef MINISATCORE_H_
#define MINISATCORE_H_

#include "SATSolver.h"

namespace Minisat
{
   class Solver;
}

namespace BEEV
{
  template <class T>
  class MinisatCore: public SATSolver
  {
    T * s;

  public:
    MinisatCore(volatile bool& interrupt);

    ~MinisatCore();

    bool
    addClause(const vec_literals& ps); // Add a clause to the solver.

    bool
    okay() const; // FALSE means solver is in a conflicting state


    bool
    solve(); // Search without assumptions.

    virtual
    bool
    simplify(); // Removes already satisfied clauses.

    virtual uint8_t modelValue(uint32_t x) const;

    uint8_t
    value(uint32_t x) const
    {
      return Minisat::toInt(s->value(x));
    }

    virtual uint32_t newVar();

    void setVerbosity(int v);

    unsigned long nVars();

    void printStats();

    virtual void setSeed(int i);

    virtual lbool true_literal() {return ((uint8_t)0);}
    virtual lbool false_literal()  {return ((uint8_t)1);}
    virtual lbool undef_literal()  {return ((uint8_t)2);}

    virtual int nClauses();

    bool unitPropagate(const vec_literals& ps)
    {
      return s->unitPropagate(ps);
    }
  };
}
;

#endif
