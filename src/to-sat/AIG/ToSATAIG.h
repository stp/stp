// -*- c++ -*-
/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: June, 2010
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef TOSATAIG_H
#define TOSATAIG_H
#include <cmath>

#include "ToCNF.h"

#include "../AST/AST.h"
#include "../AST/RunTimes.h"
#include "../STPManager/STPManager.h"
#include "BitBlaster.h"
#include "BBNodeManagerAIG.h"

namespace BEEV
{

  class ToSATAIG : public ToSATBase
  {
  private:

    ASTNodeToVar nodeToVar;
  public:

    ToSATAIG(STPMgr * bm) :
      ToSATBase(bm)
    {
    }

    void ClearAllTables()
    {
      nodeToVar.clear();
    }

    ASTNodeToVar& SATVar_to_SymbolIndexMap()
    {
      return nodeToVar;
    }

    bool
    CallSAT(MINISAT::Solver& SatSolver, const ASTNode& input)
    {
      BBNodeManagerAIG mgr(bm);
      BitBlasterNew<BBNodeAIG, BBNodeManagerAIG> bb(bm);
      BitBlasterNew<BBNodeAIG, BBNodeManagerAIG>::BBNodeSet support;
      BBNodeAIG BBFormula = bb.BBForm(input, support);

      Cnf_Dat_t* cnfData = NULL;

      mgr.toCNF(BBFormula, cnfData, nodeToVar);

      Cnf_ClearMemory();
      Cnf_DataFree(cnfData);

      // TO DO Solve.
      // TODO Return the answer
      FatalError("not implemented");
      return false;


    }
  };
}

#endif
