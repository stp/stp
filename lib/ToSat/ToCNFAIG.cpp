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
#include <iostream>

namespace stp
{

void ToCNFAIG::dag_aware_aig_rewrite(const bool needAbsRef,
                                     BBNodeManagerAIG& mgr)
{
  if (!needAbsRef && uf.AIG_rewrites_iterations)
  {
    ensureDarLibrary();
    Dar_RwrPar_t Pars, *pPars = &Pars;
    Dar_ManDefaultRwrParams(pPars);

    // Left off because it is slower, not because it is unsound. The comment
    // that stood here said assertion errors occur with it enabled; measured
    // over 250 query files in an assertions build, none do -- the abort it
    // described is the dangling-node one the Aig_ManCleanup below now
    // handles. Enabling it did cost three files that finish in under a
    // minute without it, so it stays off until someone measures the trade.
    // pPars->fUseZeros = 1;

    // For mul63bit.smt2 with iterations =3 & nCutsMax = 8
    // CNF generation was taking 139 seconds, solving 10 seconds.

    // With nCutsMax =2, CNF generation takes 16 seconds, solving 10 seconds.
    // The rewriting doesn't remove as many nodes of course..
    for (int i = 0; i < uf.AIG_rewrites_iterations; i++)
    {
      int nodeCount = mgr.totalNumberOfNodes();

      Aig_Man_t* pTemp;
      mgr.aigMgr = Aig_ManDupDfs(pTemp = mgr.aigMgr);
      Aig_ManStop(pTemp);
      Dar_ManRewrite(mgr.aigMgr, pPars);

      // Rewriting can leave a node with no fanout behind. Dar_LibBuildBest()
      // builds each replacement subgraph bottom up with Aig_And(), and a
      // trivial simplification or a structural-hash hit further up can drop
      // the reference to a node it has just created; nothing deletes it
      // afterwards, since Dar_ManRewrite() only cleans up on entry.
      //
      // Such a node is unreachable from the CO, so Aig_ManDupDfs() does not
      // copy it -- but it also asserts that it copied everything, and aborts
      // an assertions build. Delete them here instead. Only unreferenced AND
      // nodes go, so the CI order the symbol table indexes by is untouched.
      Aig_ManCleanup(mgr.aigMgr);

      mgr.aigMgr = Aig_ManDupDfs(pTemp = mgr.aigMgr);
      Aig_ManStop(pTemp);

      if (uf.stats_flag)
        cerr << "After rewrite [" << i
             << "]  nodes:" << mgr.totalNumberOfNodes() << endl;

      //Fixedpoint reached?
      if (nodeCount == mgr.totalNumberOfNodes())
        break;
    }
  }
}

void ToCNFAIG::toCNF(const BBNodeAIG& top, CNF& cnf,
                     ToSATBase::ASTNodeToSATVar& nodeToVars, bool needAbsRef,
                     BBNodeManagerAIG& mgr)
{
  assert(cnf.clauseCount() == 0);

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
    cerr << "Nodes before AIG rewrite:" << mgr.totalNumberOfNodes()
         << endl;
  }

  dag_aware_aig_rewrite(needAbsRef, mgr);

  cnf = derive_cnf(mgr);
  if (uf.stats_flag)
    cerr << (uf.simple_cnf ? "simple CNF" : "advanced CNF") << endl;

  fill_node_to_var(cnf, nodeToVars, mgr);
}

// ABC's newer CNF generator. It works on a Gia_Man_t, so the AIG is converted
// first. nLutSize bounds the cuts it considers: larger means a smaller CNF for
// steeply more work.
CNF ToCNFAIG::derive_cnf_mf(BBNodeManagerAIG& mgr, int nLutSize,
                            unsigned namedOutputs)
{
  // The two callers need either a formula (one asserted CO) or a fragment
  // (all COs named). Mf_ManGenerateCnf can express those two forms directly;
  // unlike the older generators it cannot assert a prefix while naming a
  // trailing subset.
  assert(namedOutputs == 0 ||
         namedOutputs == (unsigned)Aig_ManCoNum(mgr.aigMgr));
  Gia_Man_t* pGia = Gia_ManFromAig(mgr.aigMgr);

  // For an asserted formula, fAddOrCla must be set. Cnf_Derive(pAig, 0)
  // asserts the COs itself, but this generator only does so on request: it
  // adds a single clause OR-ing all COs, and toCNF() has already established
  // there is exactly one. A fragment instead leaves that clause out and uses
  // the CO variables below to connect its outputs to the live solver.
  const int assertOutputs = namedOutputs == 0 ? 1 : 0;
  Cnf_Dat_t* cnfData = (Cnf_Dat_t*)Mf_ManGenerateCnf(
      pGia, nLutSize, 0, assertOutputs, 0, 0);

  // pVarNums comes back indexed by Gia object id, and the only entries anyone
  // wants are the CIs' and the COs'. Project those out here; the per-object
  // array goes with the Cnf_Dat_t.
  //
  // Reading Gia CI ids is safe even though this generator may derive the CNF
  // over a coarsened copy of the Gia (Gia_ManDupMuxes, when fCnfObjIds is 0):
  // both managers append CIs before any AND node, so CI ids are 1..nCi in
  // each, and pVarNums is sized by an object count that includes them.
  CNF cnf = adoptAbcCnf(
      cnfData, (unsigned)Aig_ManCiNum(mgr.aigMgr),
      (unsigned)Aig_ManCoNum(mgr.aigMgr), [&](bool isCo, unsigned i) {
        Gia_Obj_t* o = isCo ? Gia_ManCo(pGia, (int)i) : Gia_ManCi(pGia, (int)i);
        return cnfData->pVarNums[Gia_ObjId(pGia, o)];
      });

  // Mf_ManGenerateCnf leaves pMan pointing at the Gia, cast to Aig_Man_t*.
  // Nothing in STP reads pMan and Cnf_DataFree() does not touch it, so the Gia
  // can be released here; null the pointer so it cannot be followed.
  cnfData->pMan = NULL;
  Gia_ManStop(pGia);

  return cnf;
}

CNF ToCNFAIG::derive_cnf(BBNodeManagerAIG& mgr, unsigned namedOutputs)
{
  assert(namedOutputs <= (unsigned)Aig_ManCoNum(mgr.aigMgr));

  // Every generator below one indexes pVarNums by Aig object id.
  const auto fromAig = [&](Cnf_Dat_t* d) {
    return adoptAbcCnf(d, (unsigned)Aig_ManCiNum(mgr.aigMgr),
                       (unsigned)Aig_ManCoNum(mgr.aigMgr),
                       [&](bool isCo, unsigned i) {
                         Aig_Obj_t* o = isCo ? Aig_ManCo(mgr.aigMgr, (int)i)
                                             : Aig_ManCi(mgr.aigMgr, (int)i);
                         return d->pVarNums[Aig_ObjId(o)];
                       });
  };

  if (uf.simple_cnf)
    return fromAig(Cnf_DeriveSimple(mgr.aigMgr, (int)namedOutputs));

  // AUTO: decide from the size of the AIG about to be converted.
  //
  // The scale trades generation time for a smaller CNF, and that is only worth
  // paying for when the SAT solver is what costs. On a large AIG it is not:
  // cut enumeration and technology mapping are superlinear in the AIG, while
  // the extra clauses VERY_LOW leaves behind cost a modern SAT solver very
  // little. Measured on a floating-point corpus, MEDIUM against VERY_LOW is
  // 2.26x slower on the queries that blast big -- and on one of them the
  // breakdown is 1857ms generating a 1.7M-clause CNF that MiniSat then
  // disposes of in 137ms.
  //
  // The threshold is measured rather than reasoned: see
  // tests/query-files/README-cnf-auto for the sweep it comes from.
  enum UserDefinedFlags::CNFEffort effort = uf.cnf_effort;
  if (effort == UserDefinedFlags::CNF_EFFORT_AUTO && !allowAuto)
    effort = UserDefinedFlags::CNF_EFFORT_MEDIUM;
  else if (effort == UserDefinedFlags::CNF_EFFORT_AUTO)
  {
    const unsigned nodes = (unsigned)Aig_ManNodeNum(mgr.aigMgr);
    effort = nodes >= uf.cnf_auto_threshold
                 ? UserDefinedFlags::CNF_EFFORT_VERY_LOW
                 : UserDefinedFlags::CNF_EFFORT_MEDIUM;
    if (uf.stats_flag)
      std::cerr << "cnf-auto: " << nodes << " AIG nodes, chose "
                << (effort == UserDefinedFlags::CNF_EFFORT_VERY_LOW
                        ? "very-low"
                        : "medium")
                << std::endl;
  }

  switch (effort)
  {
    case UserDefinedFlags::CNF_EFFORT_VERY_LOW:
      // No cut enumeration at all: a marking pass, then clause generation.
      // This is the floor of the scale rather than Cnf_DeriveSimple() (the
      // plain Tseitin encoding the simple_cnf path above uses), because
      // Cnf_DeriveSimple buys about 12% off generation time for roughly 1.9x
      // the clauses -- measured on one input at 51.7M clauses against 27.6M
      // here. That trade is not worth a level.
      return fromAig(Cnf_DeriveFast(mgr.aigMgr, (int)namedOutputs));

    case UserDefinedFlags::CNF_EFFORT_LOW:
      return derive_cnf_mf(mgr, 3, namedOutputs);

    case UserDefinedFlags::CNF_EFFORT_HIGH:
      return derive_cnf_mf(mgr, 6, namedOutputs);

    case UserDefinedFlags::CNF_EFFORT_VERY_HIGH:
      return derive_cnf_mf(mgr, 8, namedOutputs);

    case UserDefinedFlags::CNF_EFFORT_AUTO: // resolved above; cannot reach here
    case UserDefinedFlags::CNF_EFFORT_MEDIUM:
    default:
    {
      // Cut enumeration and technology mapping, as in ABC's Cnf_Derive().
      // That convenience wrapper reuses one process-global Cnf_Man_t, so two
      // independent STP instances deriving CNF concurrently overwrite the
      // same cut/mapping state. ABC exposes the underlying per-manager entry
      // point; keep the manager local to this conversion instead.
      Cnf_Man_t* cnfMan = Cnf_ManStart();
      Cnf_Dat_t* result =
          Cnf_DeriveWithMan(cnfMan, mgr.aigMgr, (int)namedOutputs);
      Cnf_ManStop(cnfMan);
      return fromAig(result);
    }
  }
}

void ToCNFAIG::fill_node_to_var(const CNF& cnf,
                                ToSATBase::ASTNodeToSATVar& nodeToVars,
                                BBNodeManagerAIG& mgr)
{
  BBNodeManagerAIG::SymbolToBBNode::const_iterator it;
  assert(nodeToVars.size() == 0);

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
        // 0 is CNF's "no variable"; ~0u is this map's, and the two have to be
        // translated rather than assumed equal. pVarNums said -1, which
        // became ~0u by the conversion into an unsigned, so nothing here
        // used to need saying.
        const uint32_t var = cnf.varOfCi((uint32_t)b[i].symbol_index);
        if (var != 0)
          v[i] = var;
      }
    }

    nodeToVars.insert(make_pair(n, v));
  }
}
}
