/*
 * Wraps around Cryptominisat minisat.
 */
#ifndef CRYPTOMINISAT4_H_
#define CRYPTOMINISAT4_H_

#include "SATSolver.h"

namespace CMSat
{
   class SATSolver;
}

namespace BEEV
{
  class CryptoMinisat4 : public SATSolver
  {
    CMSat::SATSolver* s;

  public:
    CryptoMinisat4();

    ~CryptoMinisat4();

    bool
    addClause(const vec_literals& ps); // Add a clause to the solver.

    bool
    okay() const; // FALSE means solver is in a conflicting state


    bool
    solve(); // Search without assumptions.

    virtual uint8_t modelValue(uint32_t x) const;

    virtual uint32_t newVar();

    void setVerbosity(int v);

    int nVars();

    void printStats();

    //nb CMS2 has different literal values to the other minisats.
    virtual lbool true_literal() {return ((uint8_t)1);}
    virtual lbool false_literal()  {return ((uint8_t)-1);}
    virtual lbool undef_literal()  {return ((uint8_t)0);}
  private:
    void* temp_cl;
  };
}

#endif
