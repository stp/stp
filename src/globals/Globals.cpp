#include "../AST/AST.h"
#include "../STPManager/STPManager.h"
#include "../STPManager/STP.h"

// FIXME: We can't include this first!
// Circular dependecies (AST ends up including
// Globals.h because it needs types enum but
// it can't be included but ASTNode is not yet defined!
#include "Globals.h"

namespace BEEV
{
  enum inputStatus input_status = NOT_DECLARED;

  //Originally just used by the parser, now used elesewhere.
  STP     * GlobalSTP;
  STPMgr  * ParserBM;

  // Used exclusively for parsing.
  Cpp_interface * parserInterface;

  // FIXME: This isn't in Globals.h so how can anyone use this?
  void (*vc_error_hdlr)(const char* err_msg) = 0;

  // This is reusable empty vector, for representing empty children
  // arrays
  ASTVec _empty_ASTVec;
}
