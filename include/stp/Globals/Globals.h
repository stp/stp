/********************************************************************
 * AUTHORS: Michael Katelman, Trevor Hansen, Stephen McCamant, Vijay Ganesh
 *
 * BEGIN DATE: Februrary, 2010
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

/* This is ABSOLUTELY DISGUSTING!
 * These globals used by the library should
 * be encapsulated in a "Context" class
 * to allow concurrent usage of the STP library
 */

#ifndef GLOBALS_H
#define GLOBALS_H
#include "stp/Util/Attributes.h"
#include <vector>

/* FIXME: Clients who import this header file have to have
 * ASTNode already declarted (eurgh)
 *
 */

namespace stp
{
// FIXME: We don't need all these forward declarations here!
class STPMgr;
class ASTNode;
class ASTInternal;
class ASTInterior;
class ASTSymbol;
class ASTBVConst;
class BVSolver;
class STP;
class Cpp_interface;

enum inputStatus
{
  NOT_DECLARED = 0, // Not included in the input file / stream
  TO_BE_SATISFIABLE,
  TO_BE_UNSATISFIABLE,
  TO_BE_UNKNOWN // Specified in the input file as unknown.
};

// return types for the GetType() function in ASTNode class.
// FLOATINGPOINT_TYPE is appended after UNKNOWN_TYPE, not slotted in sort
// order. The legacy prefix of the C API's type_t mirrors these values
// numerically, preserving values compiled into pre-floating-point clients.
// Source-only sorts such as RoundingMode are intentionally absent here:
// GetType() describes the carrier used by the bit-vector pipeline.
enum types
{
  BOOLEAN_TYPE = 0,
  BITVECTOR_TYPE,
  ARRAY_TYPE,
  UNKNOWN_TYPE,
  FLOATINGPOINT_TYPE
};

enum SOLVER_RETURN_TYPE
{
  SOLVER_INVALID = 0,
  SOLVER_VALID = 1,
  SOLVER_UNDECIDED = 2,
  // Every way of giving up shares this value, whichever budget ran out: a
  // caller that only wants to know whether there is an answer keeps the one
  // test it already had, and the budgets are told apart by
  // (get-info :reason-unknown) rather than by the verdict.
  SOLVER_TIMEOUT = 3,
  SOLVER_ERROR = -100,
  SOLVER_UNSATISFIABLE = 1,
  SOLVER_SATISFIABLE = 0
};

// Why the last solve had no answer, for (get-info :reason-unknown). SMT-LIB 2
// predefines two spellings for that flag, `memout` and `incomplete`, and
// admits any other s-expression besides; `incomplete` is what a spent budget
// is, and `timeout` is the free-form spelling for the one budget a caller may
// beat by re-running.
enum class UnknownReason
{
  None,
  Timeout,
  // The conflict budget (--max-num-confl) ran out. Told apart from the clock
  // because a caller acts differently on the two: a wall-clock timeout may
  // succeed with more time on the same machine, while a conflict budget is
  // deterministic and will not.
  ConflictBudget,
  // Something other than a budget on the search: the encoding itself was
  // abandoned. Carries its own sentence in STPMgr::unknown_detail, because
  // the name alone does not say what was abandoned or what to do about it.
  Incomplete
};

// Empty vector. Useful commonly used ASTNodes
DLL_PUBLIC extern std::vector<ASTNode> _empty_ASTVec;

extern THREAD_LOCAL_IE enum inputStatus
    input_status; // Needed by the SMTLIB printer

// Useful global variables. Use for parsing only
DLL_PUBLIC extern THREAD_LOCAL_IE STP* GlobalSTP;
DLL_PUBLIC extern THREAD_LOCAL_IE STPMgr* GlobalParserBM;
DLL_PUBLIC extern THREAD_LOCAL_IE Cpp_interface* GlobalParserInterface;

// Function that computes various kinds of statistics for the phases
// of STP
void CountersAndStats(const char* functionname, STPMgr *bm);
}
#endif
