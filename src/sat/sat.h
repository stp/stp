#ifndef SAT_H_
#define SAT_H_

#ifdef CRYPTOMINISAT
#include "cryptominisat/Solver.h"
#include "cryptominisat/SolverTypes.h"
#else
#include "core/Solver.h"
#include "core/SolverTypes.h"
//#include "simp/SimpSolver.h"
//#include "unsound/UnsoundSimpSolver.h"
#endif

#endif
