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

// FIXME: External libraries
#include "stp/Simplifier/AIGSimplifyPropositionalCore.h"

// From ABC
#include "opt/dar/dar.h"

#include "stp/Simplifier/Simplifier.h"
#include "stp/ToSat/BitBlaster.h"

#include <iostream>

namespace stp
{
using std::make_pair;

AIGSimplifyPropositionalCore::AIGSimplifyPropositionalCore(STPMgr* _bm)
{
  bm = _bm;
  nf = _bm->defaultNodeFactory;
}

// The propositional skeleton that this pass hands to the AIG rewriter.
// Anything else of boolean type is a theory atom, and is replaced wholesale by
// a fresh propositional variable.
//
// This is deliberately a structural test rather than a list of atom kinds. A
// list silently rots as kinds are added, and an atom that isn't recognised as
// one gets descended into by theoryToFresh, which then walks into bitvector
// terms that it has no way to handle.
static bool isPropositionalConnective(const ASTNode& n)
{
  switch (n.GetKind())
  {
    case NOT:
    case AND:
    case OR:
    case NAND:
    case NOR:
    case XOR:
    case IFF:
    case IMPLIES:
      return true;

    // ITE is a connective only when it is a formula. A term-valued ITE is an
    // atom's argument, so it is never reached.
    case ITE:
      return n.GetType() == BOOLEAN_TYPE;

    default:
      return false;
  }
}

// Convert theory nodes to fresh variables.
ASTNode AIGSimplifyPropositionalCore::theoryToFresh(const ASTNode& n,
                                                    ASTNodeMap& fromTo)
{
  assert(n.GetType() == BOOLEAN_TYPE);

  if (n.isConstant() || n.GetKind() == SYMBOL)
    return n;

  ASTNodeMap::const_iterator it;
  if ((it = fromTo.find(n)) != fromTo.end())
    return it->second;

  if (!isPropositionalConnective(n))
  {
    ASTNode fresh = bm->CreateFreshVariable(0, 0, "theoryToFresh");
    varToNodeMap.insert(make_pair(fresh, n));
    fromTo.insert(make_pair(n, fresh));
    return fresh;
  }

  const Kind k = n.GetKind();

  const ASTChildren children = n.GetChildren();
  ASTVec new_children;
  new_children.reserve(children.size());

  for (auto it = children.begin(); it != children.end(); it++)
    new_children.push_back(theoryToFresh(*it, fromTo));

  ASTNode result;

  if (children != new_children)
    result = nf->CreateNode(k, new_children);
  else
    result = n;

  fromTo.insert(make_pair(n, result));
  return result;
}

// Convert the AIG back to an ASTNode.
ASTNode AIGSimplifyPropositionalCore::convert(BBNodeManagerAIG& mgr,
                                              Aig_Obj_t* obj, cacheType& cache)
{
  cacheType::const_iterator it;
  if ((it = cache.find(obj)) != cache.end())
    return it->second;

  if (Aig_IsComplement(obj))
    return nf->CreateNode(NOT, convert(mgr, Aig_Regular(obj), cache));
  else if (Aig_ObjIsAnd(obj))
  {
    // Argument evaluation order is unspecified, so convert each child into a
    // named variable first, otherwise the nodes are built in a
    // compiler-dependent order.
    const ASTNode child0 = convert(mgr, Aig_ObjChild0(obj), cache);
    const ASTNode child1 = convert(mgr, Aig_ObjChild1(obj), cache);
    ASTNode result = nf->CreateNode(AND, child0, child1);
    cache.insert(make_pair(obj, result));
    return result;
  }
  else if (obj == Aig_ManConst1(mgr.aigMgr))
    return bm->ASTTrue;
  else if (obj == Aig_ManConst0(mgr.aigMgr))
    return bm->ASTFalse;
  else if (Aig_ObjIsCo(obj))
    return convert(mgr, Aig_ObjChild0(obj), cache);
  else
  {
    // Every combinational input was put into the cache by topLevel(), so
    // reaching here means the symbol-to-input mapping is incomplete.
    assert(!Aig_ObjIsCi(obj) && "AIG input missing from the symbol map");
    FatalError("AIGSimplifyPropositionalCore: unhandled AIG object type");
  }
  assert(false);
  exit(-1);
}

ASTNode AIGSimplifyPropositionalCore::topLevel(const ASTNode& top)
{
  if (top.isConstant())
    return top;

  bm->GetRunTimes()->start(RunTimes::AIGSimplifyCore);

  ASTNodeMap fromTo;

  // Replace theory nodes with new variables.
  ASTNode replaced = theoryToFresh(top, fromTo);

  SubstitutionMap sm (bm);
  Simplifier simplifier(bm, &sm );
  BBNodeManagerAIG mgr;
  mgr.nodeBudget = bm->UserFlags.aig_node_budget;
  BitBlaster bb(&mgr, &simplifier, bm->defaultNodeFactory, &bm->UserFlags);

  // This pass is an optimisation, so an exhausted budget costs nothing but
  // the work already done: hand back the formula that came in and let the
  // ordinary bit-blaster -- which enforces the same cap -- decide the query.
  BBNodeAIG blasted;
  try
  {
    blasted = bb.BBForm(replaced);
  }
  catch (const AIGBudgetExhausted& e)
  {
    if (bm->UserFlags.stats_flag)
      std::cerr << "AIG core simplification abandoned at " << e.nodeCount
                << " nodes: node budget exhausted" << std::endl;
    mgr.stop();
    bm->GetRunTimes()->stop(RunTimes::AIGSimplifyCore);
    return top;
  }

  Aig_ObjCreateCo(mgr.aigMgr, blasted.n);
  Aig_ManCleanup(mgr.aigMgr);       // remove nodes not connected to the PO.
  assert(Aig_ManCheck(mgr.aigMgr)); // check that AIG looks ok.

  assert(Aig_ManCoNum(mgr.aigMgr) == 1);

  int initial_nodeCount = mgr.aigMgr->nObjs[AIG_OBJ_AND];
  // cerr << "Nodes before AIG rewrite:" << initial_nodeCount << endl;

  Dar_LibStart(); // About 150M instructions. Very expensive.
  Dar_RwrPar_t Pars, *pPars = &Pars;
  Dar_ManDefaultRwrParams(pPars);

  // Assertion errors occur with this enabled.
  pPars->fUseZeros = 1;

  const int iterations = 3;

  int lastNodeCount = initial_nodeCount;
  for (int i = 0; i < iterations; i++)
  {
    Aig_Man_t* pTemp;
    mgr.aigMgr = Aig_ManDupDfs(pTemp = mgr.aigMgr);
    Aig_ManStop(pTemp);
    Dar_ManRewrite(mgr.aigMgr, pPars);

    // Rewriting can leave nodes with no fanout behind, and Aig_ManDupDfs()
    // asserts that it drops none. See the same call in ToCNFAIG.cpp.
    Aig_ManCleanup(mgr.aigMgr);

    mgr.aigMgr = Aig_ManDupDfs(pTemp = mgr.aigMgr);
    Aig_ManStop(pTemp);

    // cerr << "After rewrite [" << i << "]  nodes:"
    //		<< mgr.aigMgr->nObjs[AIG_OBJ_AND] << endl;

    if (lastNodeCount == mgr.aigMgr->nObjs[AIG_OBJ_AND])
      break;
    lastNodeCount = mgr.aigMgr->nObjs[AIG_OBJ_AND];
  }

  cacheType ptrToOrig;
  // This needs to be done after bitblasting because the PI nodes will be
  // altered.

  for (BBNodeManagerAIG::SymbolToBBNode::iterator it =
           mgr.symbolToBBNode.begin();
       it != mgr.symbolToBBNode.end(); it++)
  {
    ASTNode fresh = it->first; // the fresh variable.
    assert(fresh.GetKind() == SYMBOL);

    ASTNode result;
    if (varToNodeMap.find(fresh) == varToNodeMap.end())
      result = it->first; // It's not a fresh variable. i.e. it's a
                          // propositional var. in the original formula.
    else
      result = varToNodeMap.find(fresh)->second; // what it replaced.
    assert((it->second).size() == 1); // should be a propositional variable.
    const int index =
        (it->second)[0].symbol_index; // This is the index of the pi.
    // symbol_index indexes vCis (see BBNodeManagerAIG::CreateSymbol), so this
    // is a combinational input. Not Aig_ManLi, which is the latch-input
    // accessor and reads past the end of vCos on a combinational AIG.
    assert(index < Aig_ManCiNum(mgr.aigMgr));
    Aig_Obj_t* pi = Aig_ManCi(mgr.aigMgr, index);
    ptrToOrig.insert(make_pair(pi, result));
  }

  Aig_Obj_t* pObj = (Aig_Obj_t*)Vec_PtrEntry(mgr.aigMgr->vCos, 0);

  ASTNode result = convert(mgr, pObj, ptrToOrig);

  Dar_LibStop();

  bm->GetRunTimes()->stop(RunTimes::AIGSimplifyCore);
  return result;
  // return simplifier.SimplifyFormula(result,false,NULL);
}
}
