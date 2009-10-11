// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef TOCNF_H
#define TOCNF_H

#include <cmath>
#include <cassert>
#include "../AST/AST.h"
#include "../STPManager/STPManager.h"

namespace BEEV
{
  class CNFMgr
  {  
  private:
    //########################################
    //########################################
    // data types

    // for the meaning of control bits, see "utilities for contol bits".
    typedef struct
    {
      int control;
      ClauseList* clausespos;
      union
      {
        ClauseList* clausesneg;
        ASTNode* termforcnf;
      };
    } CNFInfo;

    typedef hash_map<
      ASTNode, 
      CNFInfo*, 
      ASTNode::ASTNodeHasher, 
      ASTNode::ASTNodeEqual> ASTNodeToCNFInfoMap;

    typedef hash_map<
      ASTNode, 
      ASTNode*, 
      ASTNode::ASTNodeHasher, 
      ASTNode::ASTNodeEqual> ASTNodeToASTNodePtrMap;

    //########################################
    //########################################
    // this is the data

    STPMgr *bm;
    ASTNodeToCNFInfoMap info;
    ASTNodeToASTNodePtrMap store;

    //########################################
    //########################################
    // utility predicates

    bool isAtom(const ASTNode& varphi);

    bool isPred(const ASTNode& varphi);

    bool isITE(const ASTNode& varphi);
    
    bool onChildDoPos(const ASTNode& varphi, unsigned int idx);
    
    bool onChildDoNeg(const ASTNode& varphi, unsigned int idx);
    

    //########################################
    //########################################
    //utilities for control bits.

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
    //utilities for clause sets

    ClauseList* COPY(const ClauseList& varphi);    

    ClauseList* SINGLETON(const ASTNode& varphi);    

    ClauseList* UNION(const ClauseList& varphi1, const ClauseList& varphi2);    

    void INPLACE_UNION(ClauseList* varphi1, const ClauseList& varphi2);    

    void NOCOPY_INPLACE_UNION(ClauseList* varphi1, ClauseList* varphi2);   

    ClauseList* PRODUCT(const ClauseList& varphi1, const ClauseList& varphi2);    

    //########################################
    //########################################
    //prep. for cnf conversion

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

    void doRenamingNeg(const ASTNode& varphi, ClauseList* defs);    

    //########################################
    //########################################
    //main switch for individual cnf conversion cases

    void convertFormulaToCNFPosCases(const ASTNode& varphi, ClauseList* defs);    

    void convertFormulaToCNFNegCases(const ASTNode& varphi, ClauseList* defs);

    //########################################
    //########################################
    // individual cnf conversion cases

    void convertFormulaToCNFPosPred(const ASTNode& varphi, ClauseList* defs);    

    void convertFormulaToCNFPosFALSE(const ASTNode& varphi, ClauseList* defs);    

    void convertFormulaToCNFPosTRUE(const ASTNode& varphi, ClauseList* defs);    

    void convertFormulaToCNFPosBVGETBIT(const ASTNode& varphi, ClauseList* defs);    

    void convertFormulaToCNFPosSYMBOL(const ASTNode& varphi, ClauseList* defs);    

    void convertFormulaToCNFPosNOT(const ASTNode& varphi, ClauseList* defs);    

    void convertFormulaToCNFPosAND(const ASTNode& varphi, ClauseList* defs);    

    void convertFormulaToCNFPosNAND(const ASTNode& varphi, ClauseList* defs);    

    void convertFormulaToCNFPosOR(const ASTNode& varphi, ClauseList* defs);    

    void convertFormulaToCNFPosNOR(const ASTNode& varphi, ClauseList* defs);   

    void convertFormulaToCNFPosIMPLIES(const ASTNode& varphi, ClauseList* defs);    

    void convertFormulaToCNFPosITE(const ASTNode& varphi, ClauseList* defs);    

    void convertFormulaToCNFPosXOR(const ASTNode& varphi, ClauseList* defs);    

    ClauseList* convertFormulaToCNFPosXORAux(const ASTNode& varphi, unsigned int idx, ClauseList* defs);    

    void convertFormulaToCNFNegPred(const ASTNode& varphi, ClauseList* defs);    

    void convertFormulaToCNFNegFALSE(const ASTNode& varphi, ClauseList* defs);
    

    void convertFormulaToCNFNegTRUE(const ASTNode& varphi, ClauseList* defs);    

    void convertFormulaToCNFNegBVGETBIT(const ASTNode& varphi, ClauseList* defs);    

    void convertFormulaToCNFNegSYMBOL(const ASTNode& varphi, ClauseList* defs);    

    void convertFormulaToCNFNegNOT(const ASTNode& varphi, ClauseList* defs);    

    void convertFormulaToCNFNegAND(const ASTNode& varphi, ClauseList* defs);    

    void convertFormulaToCNFNegNAND(const ASTNode& varphi, ClauseList* defs);    

    void convertFormulaToCNFNegOR(const ASTNode& varphi, ClauseList* defs);    

    void convertFormulaToCNFNegNOR(const ASTNode& varphi, ClauseList* defs);    

    void convertFormulaToCNFNegIMPLIES(const ASTNode& varphi, ClauseList* defs);

    void convertFormulaToCNFNegITE(const ASTNode& varphi, ClauseList* defs);    

    void convertFormulaToCNFNegXOR(const ASTNode& varphi, ClauseList* defs);    

    ClauseList* convertFormulaToCNFNegXORAux(const ASTNode& varphi, unsigned int idx, ClauseList* defs);    

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

  public:

    //########################################
    //########################################
    // constructor
    CNFMgr(STPMgr *bmgr);
   
    //########################################
    //########################################
    // destructor
    ~CNFMgr();
    
    //########################################
    //########################################
    // top-level conversion function

    ClauseList* convertToCNF(const ASTNode& varphi);    

    void DELETE(ClauseList* varphi);    
  }; // end of CNFMgr class
};//end of namespace
#endif
