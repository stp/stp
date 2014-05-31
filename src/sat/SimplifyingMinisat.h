/*
 * Wraps around Simplifying minisat.
 */
#ifndef SIMPLIFYINGMINISAT_H_
#define SIMPLIFYINGMINISAT_H_

#include "SATSolver.h"

namespace Minisat
{
   class SimpSolver;
}

namespace BEEV
{
  class SimplifyingMinisat : public SATSolver
  {
    Minisat::SimpSolver* s;

  public:

    SimplifyingMinisat(volatile bool& timeout);
    ~SimplifyingMinisat();

    bool
    addClause(const vec_literals& ps); // Add a clause to the solver.

    bool
    okay() const; // FALSE means solver is in a conflicting state

    bool
    solve(); // Search without assumptions.

    bool
    simplify(); // Removes already satisfied clauses.

    void setVerbosity(int v);

    virtual uint8_t modelValue(uint32_t x) const;

    virtual uint32_t newVar();

    int nVars();

    void printStats();

    virtual void setSeed(int i);

    virtual lbool true_literal() {return ((uint8_t)0);}
    virtual lbool false_literal()  {return ((uint8_t)1);}
    virtual lbool undef_literal()  {return ((uint8_t)2);}

    virtual void setFrozen(uint32_t x);
 };
}
;

#endif /* CORE_H_ */
