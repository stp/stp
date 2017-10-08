/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: June, 2010
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

#ifndef TOSATAIG_H
#define TOSATAIG_H
#include <cmath>

#include "stp/AST/AST.h"
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/STPManager/STPManager.h"
#include "stp/ToSat/AIG/BBNodeManagerAIG.h"
#include "stp/ToSat/AIG/ToCNFAIG.h"
#include "stp/ToSat/BitBlaster.h"
#include "stp/Util/RunTimes.h"

namespace stp
{

class ToSATAIG : public ToSATBase
{
private:
  ASTNodeToSATVar nodeToSATVar;
  simplifier::constantBitP::ConstantBitPropagation* cb;

  ArrayTransformer* arrayTransformer;

  // don't assign or copy construct.
  ToSATAIG& operator=(const ToSATAIG& other);
  ToSATAIG(const ToSATAIG& other);

  // Minisat doesn't, but simplifying minisat and cryptominsat eliminate
  // variables during their
  // simplification phases. The problem is that we may later add clauses in that
  // refer to those
  // simplified-away variables. Here we mark them as frozen which prevents them
  // from being removed.
  void mark_variables_as_frozen(SATSolver& satSolver);

  bool runSolver(SATSolver& satSolver);
  void add_cnf_to_solver(SATSolver& satSolver, Cnf_Dat_t* cnfData);
  Cnf_Dat_t* bitblast(const ASTNode& input, bool needAbsRef);
  void handle_cnf_options(Cnf_Dat_t* cnfData, bool needAbsRef);
  void release_cnf_memory(Cnf_Dat_t* cnfData);

  int count;
  bool first;

  ToCNFAIG toCNF;

  void init()
  {
    count = 0;
    first = true;
  }

  static THREAD_LOCAL int cnf_calls;

public:
  bool cbIsDestructed() { return cb == NULL; }

  ToSATAIG(STPMgr* bm, ArrayTransformer* at)
      : ToSATBase(bm), toCNF(bm->UserFlags)
  {
    cb = NULL;
    init();
    arrayTransformer = at;
  }

  ToSATAIG(STPMgr* bm, simplifier::constantBitP::ConstantBitPropagation* cb_,
           ArrayTransformer* at)
      : ToSATBase(bm), cb(cb_), toCNF(bm->UserFlags)
  {
    cb = cb_;
    init();
    arrayTransformer = at;
  }

  ~ToSATAIG();

  void ClearAllTables() { nodeToSATVar.clear(); }

  // Used to read out the satisfiable answer.
  ASTNodeToSATVar& SATVar_to_SymbolIndexMap() { return nodeToSATVar; }

  bool CallSAT(SATSolver& satSolver, const ASTNode& input, bool needAbsRef);
};
}

#endif
