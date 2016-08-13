/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: March, 2011
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

/*
 * This takes the topmost propositional part of the input, simplifies it with
 *DAG aware rewritting,
 * then converts it back to ASTNodes.
 *
 *
 *  This has two problems: 1) It doesn't consider that the propositional
 *variables that are introduced,
 *  might actually represent many thousands of AIG nodes, so it doesn't do the
 *"DAG aware" part correctly.
 *  2) The startup of the DAR takes about 150M instructions, which is agggeeesss
 *for small problems.
 */

#ifndef AIGSIMPLIFYPROPOSITIONALCORE_H_
#define AIGSIMPLIFYPROPOSITIONALCORE_H_

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"

// FIXME: External libraries
#include "extlib-abc/aig.h"
#include "stp/ToSat/AIG/BBNodeManagerAIG.h"

namespace stp
{
using std::make_pair;

class AIGSimplifyPropositionalCore // not copyable
{

  ASTNodeMap varToNodeMap;
  STPMgr* bm;
  NodeFactory* nf;

public:
  AIGSimplifyPropositionalCore(STPMgr* _bm);


private:
  // Convert theory nodes to fresh variables.
  ASTNode theoryToFresh(const ASTNode& n, ASTNodeMap& fromTo);

  typedef std::map<Aig_Obj_t*, ASTNode> cacheType;

  // Convert the AIG back to an ASTNode.
  ASTNode convert(BBNodeManagerAIG& mgr, Aig_Obj_t* obj, cacheType& cache);

public:
  ASTNode topLevel(const ASTNode& top);

};
}
#endif /* AIGSIMPLIFYPROPOSITIONALCORE_H_ */
