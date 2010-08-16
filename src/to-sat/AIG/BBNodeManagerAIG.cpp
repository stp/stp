#include "BBNodeManagerAIG.h"

namespace BEEV
{

  void
  BBNodeManagerAIG::toCNF(const BBNodeAIG& top, Cnf_Dat_t*& cnfData, ToSATBase::ASTNodeToSATVar& nodeToVar, const UserDefinedFlags& uf)
  {
    assert(cnfData == NULL);

    Aig_ObjCreatePo(aigMgr, top.n);
    Aig_ManCleanup(aigMgr); // remove nodes not connected to the PO.
    Aig_ManCheck(aigMgr); // check that AIG looks ok.

    assert(Aig_ManPoNum(aigMgr) == 1);

    // UseZeroes gives assertion errors.
    // Rewriting is sometimes very slow. Can it be configured to be faster?
    // What about refactoring???

    if (uf.enable_AIG_rewrites_flag)
      {
          int nodeCount = aigMgr->nObjs[AIG_OBJ_AND];
          if (uf.stats_flag)
            cerr << "Nodes before AIG rewrite:" << nodeCount <<endl;

          Dar_LibStart();
          Aig_Man_t * pTemp;
          Dar_RwrPar_t Pars, * pPars = &Pars;
          Dar_ManDefaultRwrParams( pPars );
          //pPars->fUpdateLevel =0;
          //pPars->fUseZeros = 1;

          for (int i=0; i < 3;i++)
          {
            aigMgr = Aig_ManDup( pTemp = aigMgr, 0 );
            Aig_ManStop( pTemp );
            Dar_ManRewrite( aigMgr, pPars );

            aigMgr = Aig_ManDup( pTemp = aigMgr, 0 );
            Aig_ManStop( pTemp );

            if (uf.stats_flag)
              cerr << "After rewrite [" << i << "]  nodes:" << aigMgr->nObjs[AIG_OBJ_AND] << endl;

            if (nodeCount == aigMgr->nObjs[AIG_OBJ_AND])
              break;
          }
      }
    cnfData = Cnf_Derive(aigMgr, 0);

    BBNodeManagerAIG::SymbolToBBNode::const_iterator it;

    assert(nodeToVar.size() ==0);

    // Each symbol maps to a vector of CNF variables.
    for (it = symbolToBBNode.begin(); it != symbolToBBNode.end(); it++)
      {
        const ASTNode& n = it->first;
        const vector<BBNodeAIG> &b = it->second;
        assert (nodeToVar.find(n) == nodeToVar.end());

        const int width = (n.GetType() == BOOLEAN_TYPE) ? 1: n.GetValueWidth();

        // INT_MAX for parts of symbols that didn't get encoded.
        vector<unsigned> v(width, ~((unsigned) 0));

        for (unsigned i = 0; i < b.size(); i++)
          {
            if (!b[i].IsNull())
              {
                Aig_Obj_t * pObj;
                pObj = (Aig_Obj_t*)Vec_PtrEntry( aigMgr->vPis, b[i].symbol_index );
                v[i] = cnfData->pVarNums[pObj->Id];
              }
          }

        nodeToVar.insert(make_pair(n, v));
      }
    assert(cnfData != NULL);
  }
}


