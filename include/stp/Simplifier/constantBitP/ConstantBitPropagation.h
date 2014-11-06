// -*- c++ -*-
/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: Jul 5, 2010
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

#ifndef CONSTANTBITPROPAGATION_H_
#define CONSTANTBITPROPAGATION_H_

#include "FixedBits.h"
#include "Dependencies.h"
#include "NodeToFixedBitsMap.h"
#include "WorkList.h"
#include "MultiplicationStats.h"

namespace BEEV
{
  class ASTNode;
  typedef unsigned int * CBV;
  class Simplifier;
}

namespace simplifier
{
  namespace constantBitP
  {

    enum Result
    {
      NO_CHANGE = 1, CHANGED, CONFLICT, NOT_IMPLEMENTED
    };

    class MultiplicationStatsMap;
    class WorkList;

    using BEEV::ASTNode;
    using BEEV::Simplifier;

    class ConstantBitPropagation
    {
      NodeFactory *nf;
      Simplifier *simplifier;

      Result status;
      WorkList *workList;
      Dependencies * dependents;

      bool topFixed;

      // A vector that's reused.
      std::vector< unsigned > previousChildrenFixedCount;

      void
      printNodeWithFixings();

      FixedBits*
      getUpdatedFixedBits(const ASTNode& n);

      FixedBits*
      getCurrentFixedBits(const ASTNode& n);

      void
      scheduleDown(const ASTNode& n);

public:
      NodeToFixedBitsMap* fixedMap;
      MultiplicationStatsMap* msm;

      bool isUnsatisfiable()
      {
        return status == CONFLICT;
      }

      // propagates.
      ConstantBitPropagation(BEEV::Simplifier* _sm, NodeFactory* _nf, const ASTNode & top);

      ~ConstantBitPropagation()
      {
        clearTables();
      }
      ;

      // Returns the node after writing in simplifications from constant Bit propagation.
      BEEV::ASTNode
      topLevelBothWays(const ASTNode& top, bool setTopToTrue = true, bool conjoinToTop=true);


      void clearTables()
      {
        delete fixedMap;
        fixedMap = NULL;
        delete dependents;
        dependents = NULL;
        delete workList;
        workList = NULL;
        delete msm;
        msm = NULL;
      }

      bool
      checkAtFixedPoint(const ASTNode& n, BEEV::ASTNodeSet & visited);

      void
      propagate();

      void
      scheduleUp(const ASTNode& n);

      void
      scheduleNode(const ASTNode& n);

      void
      setNodeToTrue(const ASTNode& top);

      ASTNodeMap
      getAllFixed();

      void initWorkList(const ASTNode n)
      {
        workList->initWorkList(n);
      }

    };
  }
}

#endif /* CONSTANTBITPROPAGATION_H_ */
