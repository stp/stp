// vim: tabstop=2:shiftwidth=2:softtabstop=2:expandtab

/* This is ABSOLUTELY DISGUSTING!
 * These globals used by the library should
 * be encapsulated in a "Context" class
 * to allow concurrent usage of the STP library
 */

#ifndef GLOBALS_H
#define GLOBALS_H
#include <vector>

/* FIXME: Clients who import this header file have to have
 * ASTNode already declarted (eurgh)
 *
 */

namespace BEEV
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
    NOT_DECLARED =0, // Not included in the input file / stream
    TO_BE_SATISFIABLE,
    TO_BE_UNSATISFIABLE,
    TO_BE_UNKNOWN // Specified in the input file as unknown.
  };

  //return types for the GetType() function in ASTNode class
  enum types
  {
      BOOLEAN_TYPE = 0,
      BITVECTOR_TYPE,
      ARRAY_TYPE,
      UNKNOWN_TYPE
  };

  enum SOLVER_RETURN_TYPE
    {
      SOLVER_INVALID=0,
      SOLVER_VALID=1,
      SOLVER_UNDECIDED=2,
      SOLVER_TIMEOUT=3,
      SOLVER_ERROR=-100,
      SOLVER_UNSATISFIABLE = 1,
      SOLVER_SATISFIABLE = 0
    };

  //Empty vector. Useful commonly used ASTNodes
  extern std::vector<ASTNode> _empty_ASTVec;

  // FIXME: Why aren't these defined in Globals.cpp?
  extern ASTNode ASTFalse, ASTTrue, ASTUndefined;

  //Useful global variables. Use for parsing only
  extern  STP * GlobalSTP;
  extern  STPMgr * ParserBM;
  extern Cpp_interface * parserInterface;

  // Needed by the SMTLIB printer
  extern enum inputStatus input_status;

  // Function that computes various kinds of statistics for the phases
  // of STP
  void CountersAndStats(const char * functionname, STPMgr * bm);

}
#endif
