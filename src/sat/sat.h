#ifndef SAT_H_
#define SAT_H_

#ifdef CRYPTOMINISAT
  #include "cryptominisat/Solver.h"
  #include "cryptominisat/SolverTypes.h"
#endif

#ifdef CORE
  #include "core/Solver.h"
  #include "core/SolverTypes.h"
#endif

#ifdef SIMP
  #include "simp/SimpSolver.h"
  #include "core/SolverTypes.h"
#endif

#ifdef UNSOUND
  #include "unsound/UnsoundSimpSolver.h"
  #include "core/SolverTypes.h"
#endif

#endif
