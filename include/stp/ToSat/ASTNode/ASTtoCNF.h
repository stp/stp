/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
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

#ifndef TOCNF_H
#define TOCNF_H

#include <cmath>
#include <cassert>
#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/ToSat/ASTNode/ClauseList.h"

namespace stp
{

class ASTtoCNF // not copyable
{
private:
  //########################################
  // data types

  // for the meaning of control bits, see "utilities for contol
  // bits".
  struct CNFInfo
  {
    int control;
    ClauseList* clausespos;
    union
    {
      ClauseList* clausesneg;
      ASTNode* termforcnf;
    };

    CNFInfo()
    {
      control = 0;
      clausespos = NULL;
      clausesneg = NULL;
    }
  };

  typedef std::unordered_map<ASTNode, CNFInfo*, ASTNode::ASTNodeHasher,
                   ASTNode::ASTNodeEqual> ASTNodeToCNFInfoMap;

  typedef std::unordered_map<ASTNode, ASTNode*, ASTNode::ASTNodeHasher,
                   ASTNode::ASTNodeEqual> ASTNodeToASTNodePtrMap;

  //########################################
  //########################################
  // this is the data

  STPMgr* bm;
  ASTNodeToCNFInfoMap info;
  ASTNodeToASTNodePtrMap store;

  //########################################
  //########################################
  // utility predicates

  bool onChildDoPos(const ASTNode& varphi, unsigned int idx);

  bool onChildDoNeg(const ASTNode& varphi, unsigned int idx);

  //########################################
  //########################################
  // utilities for control bits.

  void initializeCNFInfo(CNFInfo& x);

  void incrementSharesPos(CNFInfo& x);

  int sharesPos(CNFInfo& x);

  void incrementSharesNeg(CNFInfo& x);

  int sharesNeg(CNFInfo& x);

  void setControlBit(CNFInfo& x, unsigned int idx);

  bool getControlBit(CNFInfo& x, unsigned int idx);

  void setIsTerm(CNFInfo& x);

  bool isTerm(CNFInfo& x);

  void setDoRenamePos(CNFInfo& x);

  bool doRenamePos(CNFInfo& x);

  void setWasRenamedPos(CNFInfo& x);

  bool wasRenamedPos(CNFInfo& x);

  void setDoRenameNeg(CNFInfo& x);

  bool doRenameNeg(CNFInfo& x);

  void setWasRenamedNeg(CNFInfo& x);

  bool wasRenamedNeg(CNFInfo& x);

  void setDoSibRenamingPos(CNFInfo& x);

  bool doSibRenamingPos(CNFInfo& x);

  void setDoSibRenamingNeg(CNFInfo& x);

  bool doSibRenamingNeg(CNFInfo& x);

  void setWasVisited(CNFInfo& x);

  bool wasVisited(CNFInfo& x);

  //########################################
  //########################################
  // utilities for clause sets

  ClauseList* SINGLETON(const ASTNode& varphi);

  //########################################
  //########################################
  // prep. for cnf conversion

  void scanFormula(const ASTNode& varphi, bool isPos);

  void scanTerm(const ASTNode& varphi);

  //########################################
  //########################################
  // main cnf conversion function

  void convertFormulaToCNF(const ASTNode& varphi, ClauseList* defs);

  void convertTermForCNF(const ASTNode& varphi, ClauseList* defs);

  //########################################
  //########################################
  // functions for renaming nodes during cnf conversion

  ASTNode* doRenameITE(const ASTNode& varphi, ClauseList* defs);

  void doRenamingPos(const ASTNode& varphi, ClauseList* defs);

  void doRenamingPosXor(const ASTNode& varphi);

  void doRenamingNegXor(const ASTNode& varphi);

  void doRenamingNeg(const ASTNode& varphi, ClauseList* defs);

  //########################################
  //########################################
  // main switch for individual cnf conversion cases

  void convertFormulaToCNFPosCases(const ASTNode& varphi, ClauseList* defs);
  void convertFormulaToCNFNegCases(const ASTNode& varphi, ClauseList* defs);

  //########################################
  //########################################
  // individual cnf conversion cases

  void convertFormulaToCNFPosPred(const ASTNode& varphi, ClauseList* defs);
  void convertFormulaToCNFPosFALSE(const ASTNode& varphi, ClauseList* defs);
  void convertFormulaToCNFPosTRUE(const ASTNode& varphi, ClauseList* defs);
  void convertFormulaToCNFPosBOOLEXTRACT(const ASTNode& varphi,
                                         ClauseList* defs);
  void convertFormulaToCNFPosSYMBOL(const ASTNode& varphi, ClauseList* defs);
  void convertFormulaToCNFPosNOT(const ASTNode& varphi, ClauseList* defs);
  void convertFormulaToCNFPosAND(const ASTNode& varphi, ClauseList* defs);
  void convertFormulaToCNFPosNAND(const ASTNode& varphi, ClauseList* defs);
  void convertFormulaToCNFPosOR(const ASTNode& varphi, ClauseList* defs);
  void convertFormulaToCNFPosNOR(const ASTNode& varphi, ClauseList* defs);
  void convertFormulaToCNFPosIMPLIES(const ASTNode& varphi, ClauseList* defs);
  void convertFormulaToCNFPosITE(const ASTNode& varphi, ClauseList* defs);
  void convertFormulaToCNFPosXOR(const ASTNode& varphi, ClauseList* defs);
  ClauseList* convertFormulaToCNFPosXORAux(const ASTNode& varphi,
                                           unsigned int idx, ClauseList* defs);
  void convertFormulaToCNFNegPred(const ASTNode& varphi, ClauseList* defs);
  void convertFormulaToCNFNegFALSE(const ASTNode& varphi, ClauseList* defs);
  void convertFormulaToCNFNegTRUE(const ASTNode& varphi, ClauseList* defs);
  void convertFormulaToCNFNegBOOLEXTRACT(const ASTNode& varphi,
                                         ClauseList* defs);
  void convertFormulaToCNFNegSYMBOL(const ASTNode& varphi, ClauseList* defs);
  void convertFormulaToCNFNegNOT(const ASTNode& varphi, ClauseList* defs);
  void convertFormulaToCNFNegAND(const ASTNode& varphi, ClauseList* defs);
  void convertFormulaToCNFNegNAND(const ASTNode& varphi, ClauseList* defs);
  void convertFormulaToCNFNegOR(const ASTNode& varphi, ClauseList* defs);
  void convertFormulaToCNFNegNOR(const ASTNode& varphi, ClauseList* defs);
  void convertFormulaToCNFNegIMPLIES(const ASTNode& varphi, ClauseList* defs);
  void convertFormulaToCNFNegITE(const ASTNode& varphi, ClauseList* defs);
  void convertFormulaToCNFNegXOR(const ASTNode& varphi, ClauseList* defs);
  ClauseList* convertFormulaToCNFNegXORAux(const ASTNode& varphi,
                                           unsigned int idx, ClauseList* defs);

  //########################################
  //########################################
  // utilities for reclaiming memory.

  void reduceMemoryFootprintPos(const ASTNode& varphi);
  void reduceMemoryFootprintNeg(const ASTNode& varphi);

  //########################################
  //########################################

  ASTNode* ASTNodeToASTNodePtr(const ASTNode& varphi);

  //########################################
  //########################################

  void cleanup(const ASTNode& varphi);

  ASTNode dummy_true_var;

public:
  ASTtoCNF(STPMgr* bmgr);
  ~ASTtoCNF();

  // top-level conversion function
  ClauseList* convertToCNF(const ASTNode& varphi);

  // Destructors that need to be explicitly called...(yuck).
  // One deletes the thing passed into it.
  static void DELETE(ClauseList*& varphi);
};
} // end of namespace
#endif
