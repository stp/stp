/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: Jul 5, 2010
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

#ifndef CONSTANTBITPROPAGATION_H_
#define CONSTANTBITPROPAGATION_H_

#include "Dependencies.h"
#include "FixedBits.h"
#include "MultiplicationStats.h"
#include "NodeToFixedBitsMap.h"
#include "WorkList.h"

namespace stp
{
class ASTNode;
typedef unsigned int* CBV;
class Simplifier;
class STPMgr;
}

namespace simplifier
{
namespace constantBitP
{

enum Result
{
  NO_CHANGE = 1,
  CHANGED,
  CONFLICT,
  NOT_IMPLEMENTED
};

class MultiplicationStatsMap;
class WorkList;

using stp::ASTNode;
using stp::Simplifier;

class ConstantBitPropagation
{
  NodeFactory* nf;
  Simplifier* simplifier;
  STPMgr* mgr;

  Result status;
  WorkList* workList;
  Dependencies* dependents;

  bool topFixed;

  // A vector that's reused.
  vector<unsigned> previousChildrenFixedCount;

  void printNodeWithFixings();

  FixedBits* getUpdatedFixedBits(const ASTNode& n);

  FixedBits* getCurrentFixedBits(const ASTNode& n);

  void scheduleDown(const ASTNode& n);

public:
  NodeToFixedBitsMap* fixedMap;
  MultiplicationStatsMap* msm;

  bool isUnsatisfiable() { return status == CONFLICT; }

  // propagates.
  ConstantBitPropagation(stp::STPMgr* mgr, stp::Simplifier* _sm,
                         NodeFactory* _nf, const ASTNode& top);

  ~ConstantBitPropagation() { clearTables(); };

  // Returns the node after writing in simplifications from constant Bit
  // propagation.
  stp::ASTNode topLevelBothWays(const ASTNode& top, bool setTopToTrue = true,
                                bool conjoinToTop = true);

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

  bool checkAtFixedPoint(const ASTNode& n, stp::ASTNodeSet& visited);

  void propagate();

  void scheduleUp(const ASTNode& n);

  void scheduleNode(const ASTNode& n);

  void setNodeToTrue(const ASTNode& top);

  stp::ASTNodeMap getAllFixed();

  ASTNode bitsToNode(const ASTNode& node, const FixedBits& bits);

  void initWorkList(const ASTNode n) { workList->initWorkList(n); }

  static Result dispatchToTransferFunctions(stp::STPMgr* mgr, const Kind k,
                                            vector<FixedBits*>& children,
                                            FixedBits& output, const ASTNode n,
                                            MultiplicationStatsMap* msm = NULL);
};
}
}

#endif /* CONSTANTBITPROPAGATION_H_ */
