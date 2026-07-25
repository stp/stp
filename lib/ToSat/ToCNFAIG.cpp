/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: Feb, 2010
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

#include "stp/ToSat/ToCNFAIG.h"

namespace stp
{

// Can it only add in the new variables somehow??
void addVariables(BBNodeManagerAIG& mgr, Cnf_Dat_t*& cnfData,
                  ToSATBase::ASTNodeToSATVar& nodeToVars)
{
  BBNodeManagerAIG::SymbolToBBNode::const_iterator it;
  // Each symbol maps to a vector of CNF variables.
  for (it = mgr.symbolToBBNode.begin(); it != mgr.symbolToBBNode.end(); it++)
  {
    const ASTNode& n = it->first;
    const vector<BBNodeAIG>& b = it->second;

    const int width = (n.GetType() == BOOLEAN_TYPE) ? 1 : n.GetValueWidth();

    // INT_MAX for parts of symbols that didn't get encoded.
    vector<unsigned> v(width, ~((unsigned)0));

    for (unsigned i = 0; i < b.size(); i++)
    {
      if (!b[i].IsNull())
      {
        Aig_Obj_t* pObj;
        pObj = (Aig_Obj_t*)Vec_PtrEntry(mgr.aigMgr->vCis, b[i].symbol_index);
        v[i] = cnfData->pVarNums[pObj->Id];
      }
    }
    nodeToVars.insert(make_pair(n, v));
  }
}

void ToCNFAIG::dag_aware_aig_rewrite(const bool needAbsRef,
                                     BBNodeManagerAIG& mgr)
{
  if (!needAbsRef && uf.AIG_rewrites_iterations)
  {
    Dar_LibStart();
    Dar_RwrPar_t Pars, *pPars = &Pars;
    Dar_ManDefaultRwrParams(pPars);

    // Assertion errors occur with this enabled.
    // pPars->fUseZeros = 1;

    // For mul63bit.smt2 with iterations =3 & nCutsMax = 8
    // CNF generation was taking 139 seconds, solving 10 seconds.

    // With nCutsMax =2, CNF generation takes 16 seconds, solving 10 seconds.
    // The rewriting doesn't remove as many nodes of course..
    for (int i = 0; i < uf.AIG_rewrites_iterations; i++)
    {
      int nodeCount = mgr.aigMgr->nObjs[AIG_OBJ_AND];

      Aig_Man_t* pTemp;
      mgr.aigMgr = Aig_ManDupDfs(pTemp = mgr.aigMgr);
      Aig_ManStop(pTemp);
      Dar_ManRewrite(mgr.aigMgr, pPars);

      mgr.aigMgr = Aig_ManDupDfs(pTemp = mgr.aigMgr);
      Aig_ManStop(pTemp);

      if (uf.stats_flag)
        cerr << "After rewrite [" << i
             << "]  nodes:" << mgr.aigMgr->nObjs[AIG_OBJ_AND] << endl;

      //Fixedpoint reached?
      if (nodeCount == mgr.aigMgr->nObjs[AIG_OBJ_AND])
        break;
    }
  }
}

void ToCNFAIG::toCNF(const BBNodeAIG& top, Cnf_Dat_t*& cnfData,
                     ToSATBase::ASTNodeToSATVar& nodeToVars, bool needAbsRef,
                     BBNodeManagerAIG& mgr)
{
  assert(cnfData == NULL);

  Aig_ObjCreateCo(mgr.aigMgr, top.n);
  if (!needAbsRef)
  {
    Aig_ManCleanup(mgr.aigMgr); // remove nodes not connected to the PO.
  }
  assert(Aig_ManCheck(mgr.aigMgr)); // check that AIG looks ok.

  assert(Aig_ManCoNum(mgr.aigMgr) == 1);

  // UseZeroes gives assertion errors.
  // Rewriting is sometimes very slow. Can it be configured to be faster?
  // What about refactoring???

  if (uf.stats_flag)
  {
    cerr << "Nodes before AIG rewrite:" << mgr.aigMgr->nObjs[AIG_OBJ_AND]
         << endl;
  }

  dag_aware_aig_rewrite(needAbsRef, mgr);

  if (!uf.simple_cnf)
  {
    cnfData = derive_cnf(mgr);
    if (uf.stats_flag)
      cerr << "advanced CNF" << endl;
  }
  else
  {
    cnfData = Cnf_DeriveSimple(mgr.aigMgr, 0);
    if (uf.stats_flag)
      cerr << "simple CNF" << endl;
  }
  assert(cnfData != NULL);

  fill_node_to_var(cnfData, nodeToVars, mgr);
}

// ABC's newer CNF generator. It works on a Gia_Man_t, so the AIG is converted
// first. nLutSize bounds the cuts it considers: larger means a smaller CNF for
// steeply more work.
Cnf_Dat_t* ToCNFAIG::derive_cnf_mf(BBNodeManagerAIG& mgr, int nLutSize)
{
  Gia_Man_t* pGia = Gia_ManFromAig(mgr.aigMgr);

  // fAddOrCla must be set. Cnf_Derive(pAig, 0) emits the clauses asserting the
  // COs itself, but this generator only does so on request: it adds a single
  // clause OR-ing all COs, and toCNF() has already established there is exactly
  // one, so that clause is the unit which asserts the top-level formula.
  // Without it the CNF is trivially satisfiable.
  Cnf_Dat_t* cnfData =
      (Cnf_Dat_t*)Mf_ManGenerateCnf(pGia, nLutSize, 0, 1, 0, 0);

  // pVarNums comes back indexed by Gia object id, but addVariables() and
  // fill_node_to_var() index it by Aig CI object id. Rebuild it over the Aig id
  // space so those callers need no special case; only CIs are ever looked up,
  // so everything else stays -1.
  //
  // Aig_ManObjNumMax(), not Aig_ManObjNum(): the latter subtracts nDeleted, and
  // the Aig_ManCleanup() in toCNF() deletes nodes, so ids run past the count of
  // live objects. Sizing by the count under-allocates by exactly nDeleted, and
  // fill_node_to_var() then reads off the end of the array.
  //
  // Reading Gia CI ids is safe even though this generator may derive the CNF
  // over a coarsened copy of the Gia (Gia_ManDupMuxes, when fCnfObjIds is 0):
  // both managers append CIs before any AND node, so CI ids are 1..nCi in each,
  // and pVarNums is sized by an object count that includes them.
  const int nAigObjs = Aig_ManObjNumMax(mgr.aigMgr);
  int* pRemap = ABC_ALLOC(int, nAigObjs);
  for (int i = 0; i < nAigObjs; i++)
    pRemap[i] = -1;

  Aig_Obj_t* pCi;
  int ci;
  Aig_ManForEachCi(mgr.aigMgr, pCi, ci)
    pRemap[pCi->Id] = cnfData->pVarNums[Gia_ObjId(pGia, Gia_ManCi(pGia, ci))];

  ABC_FREE(cnfData->pVarNums);
  cnfData->pVarNums = pRemap;

  // Mf_ManGenerateCnf leaves pMan pointing at the Gia, cast to Aig_Man_t*.
  // Nothing in STP reads pMan and Cnf_DataFree() does not touch it, so the Gia
  // can be released here; null the pointer so it cannot be followed.
  cnfData->pMan = NULL;
  Gia_ManStop(pGia);

  return cnfData;
}

Cnf_Dat_t* ToCNFAIG::derive_cnf(BBNodeManagerAIG& mgr)
{
  switch (uf.cnf_effort)
  {
    case UserDefinedFlags::CNF_EFFORT_VERY_LOW:
      // No cut enumeration at all: a marking pass, then clause generation.
      // This is the floor of the scale rather than Cnf_DeriveSimple() (the
      // plain Tseitin encoding the simple_cnf path above uses), because
      // Cnf_DeriveSimple buys about 12% off generation time for roughly 1.9x
      // the clauses -- measured on one input at 51.7M clauses against 27.6M
      // here. That trade is not worth a level.
      return Cnf_DeriveFast(mgr.aigMgr, 0);

    case UserDefinedFlags::CNF_EFFORT_LOW:
      return derive_cnf_mf(mgr, 3);

    case UserDefinedFlags::CNF_EFFORT_HIGH:
      return derive_cnf_mf(mgr, 6);

    case UserDefinedFlags::CNF_EFFORT_VERY_HIGH:
      return derive_cnf_mf(mgr, 8);

    case UserDefinedFlags::CNF_EFFORT_MEDIUM:
    default:
      // Cut enumeration and technology mapping, ABC's Cnf_Derive().
      return Cnf_Derive(mgr.aigMgr, 0);
  }
}

void ToCNFAIG::fill_node_to_var(Cnf_Dat_t* cnfData,
                                ToSATBase::ASTNodeToSATVar& nodeToVars,
                                BBNodeManagerAIG& mgr)
{
  BBNodeManagerAIG::SymbolToBBNode::const_iterator it;
  assert(nodeToVars.size() == 0);

  // todo. cf. with addvariables above...
  // Each symbol maps to a vector of CNF variables.
  for (it = mgr.symbolToBBNode.begin(); it != mgr.symbolToBBNode.end(); it++)
  {
    const ASTNode& n = it->first;
    const vector<BBNodeAIG>& b = it->second;
    assert(nodeToVars.find(n) == nodeToVars.end());

    const int width = (n.GetType() == BOOLEAN_TYPE) ? 1 : n.GetValueWidth();

    // INT_MAX for parts of symbols that didn't get encoded.
    vector<unsigned> v(width, ~((unsigned)0));

    for (unsigned i = 0; i < b.size(); i++)
    {
      if (!b[i].IsNull())
      {
        Aig_Obj_t* pObj;
        pObj = (Aig_Obj_t*)Vec_PtrEntry(mgr.aigMgr->vCis, b[i].symbol_index);
        v[i] = cnfData->pVarNums[pObj->Id];
      }
    }

    nodeToVars.insert(make_pair(n, v));
  }
}
}
