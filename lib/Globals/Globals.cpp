// -*- c++ -*-
/********************************************************************
 * AUTHORS: Unknown
 *
 * BEGIN DATE: November, 2005
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
 * OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 ********************************************************************/

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/STPManager/STP.h"

// FIXME: We can't include this first!
// Circular dependecies (AST ends up including
// Globals.h because it needs types enum but
// it can't be included but ASTNode is not yet defined!
#include "stp/Globals/Globals.h"

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
