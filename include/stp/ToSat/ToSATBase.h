/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: Jul, 2010
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

#ifndef TOSATBASE_H
#define TOSATBASE_H

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"

namespace stp
{
class ToSATBase // not copyable
{
protected:
  ASTNode ASTTrue, ASTFalse, ASTUndefined;

  // Ptr to STPManager
  STPMgr* bm;

public:
  typedef std::unordered_map<ASTNode, vector<unsigned>, ASTNode::ASTNodeHasher,
                             ASTNode::ASTNodeEqual>
      ASTNodeToSATVar;

  ToSATBase(STPMgr* bm) : bm(bm)
  {
    ASTTrue = bm->CreateNode(TRUE);
    ASTFalse = bm->CreateNode(FALSE);
    ASTUndefined = bm->CreateNode(UNDEFINED);
  }

  virtual ~ToSATBase() {}

  // print the STP solver output
  DLL_PUBLIC void PrintOutput(SOLVER_RETURN_TYPE ret);

  // Bitblasts, CNF conversion and calls toSATandSolve()
  virtual bool CallSAT(SATSolver& SatSolver, const ASTNode& input,
                       bool doesAbsRef) = 0;

  virtual ASTNodeToSATVar& SATVar_to_SymbolIndexMap() = 0;

  virtual void ClearAllTables(void) = 0;
};
}

#endif
