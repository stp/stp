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

#include "../AST/AST.h"
#include "../AST/RunTimes.h"
#include "../STPManager/STPManager.h"
#include "../BitBlaster.h"
#include "BBNodeManagerAIG.h"

namespace BEEV
{

  // NB You can't use this with abstraction refinement!!!
  class ToSATAIG : public ToSATBase
  {
  private:

    ASTNodeToSATVar nodeToSATVar;
    simplifier::constantBitP::ConstantBitPropagation* cb;

    // don't assign or copy construct.
    ToSATAIG&  operator = (const ToSATAIG& other);
    ToSATAIG(const ToSATAIG& other);

  public:

    ToSATAIG(STPMgr * bm) :
      ToSATBase(bm)
    {
      cb = NULL;
    }

    ToSATAIG(STPMgr * bm, simplifier::constantBitP::ConstantBitPropagation* cb_) :
      ToSATBase(bm)
    {
      cb = cb_;
    }

    void
    ClearAllTables()
    {
      nodeToSATVar.clear();
    }

    // Used to read out the satisfiable answer.
    ASTNodeToSATVar&
    SATVar_to_SymbolIndexMap()
    {
      return nodeToSATVar;
    }

    // Can not be used with abstraction refinement.
    bool  CallSAT(SATSolver& satSolver, const ASTNode& input);

  };
}

#endif
