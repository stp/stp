/********************************************************************
 * AUTHORS: Andrew Teylu
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
#include "stp/Sat/SATSolver.h"
#include "stp/Sat/SearchBias.h"

#ifdef USE_CRYPTOMINISAT
#include "stp/Sat/CryptoMinisat5.h"
#endif

#ifdef USE_RISS
#include "stp/Sat/Riss.h"
#endif

#ifdef USE_CADICAL
#include "stp/Sat/Cadical.h"
#endif

#ifdef USE_MINISAT
#include "stp/Sat/MinisatCore.h"
#include "stp/Sat/SimplifyingMinisat.h"
#endif

#include <cstdlib>
#include <iostream>

namespace stp
{

std::vector<std::string> compiledSolverVersions()
{
  std::vector<std::string> solvers;

#ifdef USE_CADICAL
  {
    // Present in every CaDiCaL STP builds against, 1.8.0 included, and it
    // returns the string compiled into the library rather than a macro the
    // includer expanded.
    const std::string linked = CaDiCaL::Solver::version();
    std::string entry = "cadical " + linked;

    // The semantic-version macros only arrived in the 3.x headers, so their
    // absence is not a mismatch -- it just means there is nothing to check
    // the library against.
    //
    // Major.minor only: CADICAL_PATCH is not maintained upstream (3.0.1
    // ships a header saying 0), so comparing it flags every correct build
    // and the note stops being worth reading. The mismatch actually worth
    // catching is a whole different checkout -- headers from one, library
    // from another -- which moves the major or the minor.
#ifdef CADICAL_MAJOR
    const std::string headers =
        std::to_string(CADICAL_MAJOR) + "." + std::to_string(CADICAL_MINOR);
    if (linked.compare(0, headers.size(), headers) != 0 ||
        (linked.size() > headers.size() && linked[headers.size()] != '.'))
      entry += " (built against headers " + headers + ".x)";
#endif
    solvers.push_back(entry);
  }
#endif

#ifdef USE_CRYPTOMINISAT
  solvers.push_back("cryptominisat " + CryptoMiniSat5::version());
#endif

#ifdef USE_MINISAT
  // MiniSat has no version API, and STP links a checkout that carries no
  // version of its own either.
  solvers.push_back("minisat (no version reported)");
#endif

#ifdef USE_RISS
  solvers.push_back("riss (no version reported)");
#endif

  return solvers;
}

SATSolver* createSATSolver(const UserDefinedFlags& flags)
{
  SATSolver* newS = NULL;
  switch (flags.solver_to_use)
  {
    case UserDefinedFlags::SIMPLIFYING_MINISAT_SOLVER:
#ifdef USE_MINISAT
      newS = new SimplifyingMinisat;
#else
      std::cerr << "MiniSat support was not enabled at configure time."
                << std::endl;
      exit(-1);
#endif
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
#ifdef USE_MINISAT
      newS = new MinisatCore;
#else
      std::cerr << "MiniSat support was not enabled at configure time."
                << std::endl;
      exit(-1);
#endif
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

void applySearchBias(SATSolver& s, const UserDefinedFlags& flags, bool warn)
{
  if (flags.search_bias == SearchBias::NONE ||
      s.setSearchBias(flags.search_bias))
    return;
  if (warn)
  {
    std::cerr << "Warning: the SAT solver in use has no '"
              << searchBiasName(flags.search_bias)
              << "' search bias to select; using its own settings instead."
              << std::endl;
  }
}

bool enableBVAIfWanted(SATSolver& s, const UserDefinedFlags& flags,
                       bool wants, bool warn)
{
  // A declined request is only worth reporting when the user asked for it by
  // name: ON is the default, so warning on the mode alone would put a warning
  // on every solve of a build whose CaDiCaL has no factor.
  if (!wants || s.enableBVA() || !flags.cadical_factor_explicit ||
      flags.cadical_factor != UserDefinedFlags::BVAMode::ON || !warn)
    return false;
  std::cerr << "Warning: --cadical-factor was requested but the SAT "
               "solver in use has no bounded variable addition to "
               "enable; using its own settings instead."
            << std::endl;
  return true;
}

void applySolveBudgets(SATSolver& s, const UserDefinedFlags& flags)
{
  if (flags.timeout_max_conflicts >= 0)
    s.setMaxConflicts(flags.timeout_max_conflicts);
  if (flags.timeout_max_time >= 0)
    s.setMaxTime(flags.timeout_max_time);
}
}
