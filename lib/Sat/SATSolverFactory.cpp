/********************************************************************
 * AUTHORS: Vijay Ganesh, Andrew Teylu
 *
 * BEGIN DATE: August, 2026
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

#include "stp/Sat/SATSolverFactory.h"

#include "stp/STPManager/UserDefinedFlags.h"

#ifdef USE_CRYPTOMINISAT
#include "stp/Sat/CryptoMinisat5.h"
#endif

#ifdef USE_RISS
#include "stp/Sat/Riss.h"
#endif

#ifdef USE_CADICAL
#include "stp/Sat/Cadical.h"
#endif

#include "stp/Sat/MinisatCore.h"
#include "stp/Sat/SimplifyingMinisat.h"

#include <cstdlib>
#include <iostream>

namespace stp
{

SATSolver* createSATSolver(const UserDefinedFlags& flags)
{
  SATSolver* newS = NULL;
  switch (flags.solver_to_use)
  {
    case UserDefinedFlags::SIMPLIFYING_MINISAT_SOLVER:
      newS = new SimplifyingMinisat;
      break;

    case UserDefinedFlags::CRYPTOMINISAT5_SOLVER:
#ifdef USE_CRYPTOMINISAT
      newS = new CryptoMiniSat5(flags.num_solver_threads);
#else
      std::cerr << "CryptoMiniSat5 support was not enabled at configure time."
                << std::endl;
      exit(-1);
#endif
      break;
    case UserDefinedFlags::RISS_SOLVER:
#ifdef USE_RISS
      newS = new RissCore();
#else
      std::cerr << "Riss support was not enabled at configure time."
                << std::endl;
      exit(-1);
#endif
      break;
    case UserDefinedFlags::MINISAT_SOLVER:
      newS = new MinisatCore;
      break;

    case UserDefinedFlags::CADICAL_SOLVER:
#ifdef USE_CADICAL
      newS = new Cadical();
      break;
#else
      std::cerr << "Cadical support was not enabled at configure time."
                << std::endl;
      exit(-1);
#endif
    default:
      std::cerr << "ERROR: Undefined solver to use." << std::endl;
      exit(-1);
      break;
  };

  return newS;
}
}
