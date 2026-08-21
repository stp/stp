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
class DLL_PUBLIC ToSATBase // not copyable
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

  // Print the STP solver output. Static because it needs no instance state:
  // everything it touches is either the result passed in, the manager, or
  // the thread-local input_status.
  static void PrintOutput(STPMgr* bm, SOLVER_RETURN_TYPE ret);

  // Bitblasts, CNF conversion and calls toSATandSolve()
  virtual bool CallSAT(SATSolver& SatSolver, const ASTNode& input,
                       bool doesAbsRef) = 0;

  virtual ASTNodeToSATVar& SATVar_to_SymbolIndexMap() = 0;

  // The lowering may have replaced a bit-vector operation by a free
  // Boolean or a free vector of bits -- an over-approximation which is
  // only a faithful encoding once refinement has pinned it to the
  // operands it stands for. A candidate that contradicts one of those
  // abstractions is not an assignment of the query at all, so it must be
  // ruled out before anything downstream reads it: the theory checkers
  // and the model evaluator are entitled to assume the bit-vector layer
  // means what it says, and report a candidate that does not as an
  // internal error.
  //
  // Returns the number of abstractions whose definition grew, which is
  // also the caller's progress measure: non-zero means clauses were added
  // and the search must run again.
  virtual unsigned refineAbstractions(SATSolver& /*SatSolver*/) { return 0; }

  // Total across the session, so a driver can tell whether the round it
  // just ran refined anything without owning the abstraction tables.
  virtual uint64_t abstractionRefinements() const { return 0; }

  virtual void ClearAllTables(void) = 0;
};
}

#endif
