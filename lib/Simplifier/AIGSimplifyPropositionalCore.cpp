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
#include "stp/ToSat/BBNodeManagerAIG.h"
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

// The AIG literal an object stands for: 2*id + complement, so x and !x are
// distinct keys and neither is a pointer.
static inline unsigned aigLit(Aig_Obj_t* obj)
{
  return 2u * Aig_ObjId(Aig_Regular(obj)) + (Aig_IsComplement(obj) ? 1u : 0u);
}

// Convert the AIG back to an ASTNode.
//
// Iterative, two-visit post-order. The recursive form put one frame on the
// stack for every AND node, and nothing bounds an AIG's depth: DeepDag_Test
// covers the blaster and ABC's own CNF walks but has never reached this pass,
// so the overflow here was latent rather than absent.
//
// Operands are pushed child1-then-child0 so that child0 is finished first,
// which is the order the recursive form used. Node creation order decides
// node_uid, and node_uid decides every sort that ties on node identity.
ASTNode AIGSimplifyPropositionalCore::convert(BBNodeManagerAIG& mgr,
                                              Aig_Obj_t* root, cacheType& cache)
{
  std::vector<std::pair<Aig_Obj_t*, bool>> pending(1,
                                                   std::make_pair(root, false));
  while (!pending.empty())
  {
    Aig_Obj_t* obj = pending.back().first;
    const bool expanded = pending.back().second;
    pending.pop_back();

    if (cache.find(aigLit(obj)) != cache.end())
      continue;

    if (Aig_IsComplement(obj))
    {
      Aig_Obj_t* regular = Aig_Regular(obj);
      if (!expanded)
      {
        pending.push_back(std::make_pair(obj, true));
        pending.push_back(std::make_pair(regular, false));
        continue;
      }
      cache[aigLit(obj)] =
          nf->CreateNode(NOT, cache.at(aigLit(regular)));
    }
    else if (Aig_ObjIsAnd(obj))
    {
      if (!expanded)
      {
        pending.push_back(std::make_pair(obj, true));
        pending.push_back(std::make_pair(Aig_ObjChild1(obj), false));
        pending.push_back(std::make_pair(Aig_ObjChild0(obj), false));
        continue;
      }
      cache[aigLit(obj)] = nf->CreateNode(AND, cache.at(aigLit(Aig_ObjChild0(obj))),
                                          cache.at(aigLit(Aig_ObjChild1(obj))));
    }
    else if (obj == Aig_ManConst1(mgr.aigMgr))
      cache[aigLit(obj)] = bm->ASTTrue;
    else if (obj == Aig_ManConst0(mgr.aigMgr))
      cache[aigLit(obj)] = bm->ASTFalse;
    else if (Aig_ObjIsCo(obj))
    {
      if (!expanded)
      {
        pending.push_back(std::make_pair(obj, true));
        pending.push_back(std::make_pair(Aig_ObjChild0(obj), false));
        continue;
      }
      cache[aigLit(obj)] = cache.at(aigLit(Aig_ObjChild0(obj)));
    }
    else
    {
      // Every combinational input was put into the cache by topLevel(), so
      // reaching here means the symbol-to-input mapping is incomplete.
      assert(!Aig_ObjIsCi(obj) && "AIG input missing from the symbol map");
      FatalError("AIGSimplifyPropositionalCore: unhandled AIG object type");
    }
  }
  return cache.at(aigLit(root));
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
  BitBlasterAIG bb(&mgr, &simplifier, bm->defaultNodeFactory, &bm->UserFlags);

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

  int initial_nodeCount = mgr.totalNumberOfNodes();
  // cerr << "Nodes before AIG rewrite:" << initial_nodeCount << endl;

  ensureDarLibrary();
  Dar_RwrPar_t Pars, *pPars = &Pars;
  Dar_ManDefaultRwrParams(pPars);

  // The warning that stood here -- that assertion errors occur with this
  // enabled -- was copied from ToCNFAIG.cpp, where the line is commented out.
  // It is stale in both places: over 347 query files in an assertions build
  // this path aborts on none of them and changes no answer.
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
    //		<< mgr.totalNumberOfNodes() << endl;

    if (lastNodeCount == mgr.totalNumberOfNodes())
      break;
    lastNodeCount = mgr.totalNumberOfNodes();
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
    assert(index < mgr.ciCount());
    ptrToOrig.insert(make_pair(2u * (unsigned)mgr.ciObjectId(index), result));
  }

  Aig_Obj_t* pObj = Aig_ManCo(mgr.aigMgr, 0);

  ASTNode result = convert(mgr, pObj, ptrToOrig);


  bm->GetRunTimes()->stop(RunTimes::AIGSimplifyCore);
  return result;
  // return simplifier.SimplifyFormula(result,false,NULL);
}
}
