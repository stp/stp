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

#ifndef SATSOLVERFACTORY_H_
#define SATSOLVERFACTORY_H_

#include "stp/Util/Attributes.h"
#include <string>
#include <vector>

namespace stp
{
class SATSolver;
struct UserDefinedFlags;

// Every SAT backend compiled into this binary, as "name version".
//
// The version is what the linked library reports at run time, not what its
// headers say. Those two can disagree -- a build picking up one checkout's
// headers and another's library is a real and quiet failure mode -- and it
// is the library that decides how the solver behaves, so that is the number
// worth printing. Where the headers also carry a version and it differs,
// the entry says so rather than choosing a side. Backends that expose no
// version at all report their name alone.
//
// DLL_PUBLIC because the stp binary prints this from --version, alongside
// the equally-annotated accessors in GitSHA1.h, and the default build hides
// everything else in the shared library.
DLL_PUBLIC std::vector<std::string> compiledSolverVersions();

// Construct the SAT backend that flags.solver_to_use selects, or exit with
// a diagnostic if that backend was not compiled in. The caller owns the
// returned solver.
SATSolver* createSATSolver(const UserDefinedFlags& flags);

// The configuration-window plumbing shared by the batch pipeline and the
// incremental driver; each used to carry its own copy, warning strings
// included.

// Apply the configured search bias -- before any clause reaches the
// backend, which is the only point some backends accept it -- warning
// (when `warn`) if the backend declines an explicit choice.
void applySearchBias(SATSolver& s, const UserDefinedFlags& flags, bool warn);

// Ask for bounded variable addition when `wants` says the caller's policy
// selected it. A declined explicit ON is worth a warning (no CaDiCaL 3.x
// behind the build, or a different backend); a declined AUTO is just the
// default heuristic not applying. Returns whether the warning fired, so a
// session-latched caller can warn once.
bool enableBVAIfWanted(SATSolver& s, const UserDefinedFlags& flags,
                       bool wants, bool warn);

// STP spells "no limit" as a negative value, and every other value --
// zero included -- is a budget to be honoured. Translate once, here, so
// backends are only ever handed a value >= 0 and cannot each decide what,
// say, zero means.
void applySolveBudgets(SATSolver& s, const UserDefinedFlags& flags);
}

#endif
