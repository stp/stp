#ifndef SAT_H_
#define SAT_H_

#ifdef CRYPTOMINISAT
  #include "cryptominisat/Solver/Solver.h"
  #include "cryptominisat/Solver/SolverTypes.h"
#else
  #include "core/Solver.h"
  #include "core/SolverTypes.h"
  //#include "simp/SimpSolver.h"
  //#include "unsound/UnsoundSimpSolver.h"
#endif

#endif
