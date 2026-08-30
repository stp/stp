/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: August, 2026
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

#include "stp/ToSat/ToCNFGia.h"

#include "stp/ToSat/AbcCnfAdopt.h"

#include <iostream>
#include <vector>

namespace stp
{

void ToCNFGia::toCNF(const BBNodeGia& top, CNF& cnf,
                     ToSATBase::ASTNodeToSATVar& nodeToVars,
                     bool /*needAbsRef*/, BBNodeManagerGia& mgr)
{
  assert(cnf.clauseCount() == 0);
  assert(nodeToVars.size() == 0);
  assert(!top.IsNull());

  Gia_Man_t* const p = mgr.giaMgr;
  assert(Gia_ManCoNum(p) == 0);
  Gia_ManAppendCo(p, top.n);

  // The structural-hash table has done its work and is two int arrays over
  // the objects. Hand it back before the mapper allocates, which is the point
  // in the pipeline where the process is largest. Nothing builds a gate after
  // this; Gia_ManHashAnd asserts if anything tries.
  Gia_ManHashStop(p);

  if (uf.stats_flag)
    std::cerr << "gia: " << Gia_ManAndNum(p) << " AND nodes, "
              << Gia_ManCiNum(p) << " inputs, LUT" << nLutSize << std::endl;

  // fAddOrCla, the fourth argument, is what asserts the outputs. Cnf_Derive
  // does that itself; this generator only on request, by adding a single
  // clause OR-ing every CO -- and there is exactly one.
  //
  // No cleanup first. The ABC-Aig path runs Aig_ManCleanup here, but a node
  // outside the cone of the output is one Mf never maps, and so never gives a
  // variable or a clause to; all it costs is its share of cut enumeration,
  // measured at 2.1% of the AND nodes on the largest query in the hard set.
  // Removing them means copying the graph, and a second Gia at 12 bytes an
  // object costs more than the 2.1% is worth.
  Cnf_Dat_t* const cnfData =
      (Cnf_Dat_t*)Mf_ManGenerateCnf(p, nLutSize, 0, 1, 0, 0);

  // pVarNums is indexed by the object ids of the graph passed in -- this one.
  //
  // That holds even though the generator derives the CNF over a coarsened
  // copy (Gia_ManDupMuxes, which strashes and then cleans up, so ids do not
  // survive it). Mf_ManDeriveCnf notices the two managers differ and rebuilds
  // pVarNums against the original, bridging by CI and CO *ordinal*, which is
  // what the copy does preserve. Only the input and output entries are
  // filled; every other object reads back as ABC's -1.
  //
  // Worth knowing, because it is what makes this backend possible at all. An
  // input here is not object 1..nCi the way it is on the converted path:
  // CreateSymbol mints one the first time a symbol bit is touched and
  // CreateFreshInput mints one mid-blast per abstraction proxy, so inputs
  // land interleaved with gates -- on 375 of 388 fuzz corpus files, and with
  // an input moved by the coarsening on 186 of 193. None of it matters,
  // because no id read here is one the coarsening had a chance to move.
  cnf = adoptAbcCnf(cnfData, (unsigned)Gia_ManCiNum(p),
                    (unsigned)Gia_ManCoNum(p), [&](bool isCo, unsigned i) {
                      Gia_Obj_t* const o =
                          isCo ? Gia_ManCo(p, (int)i) : Gia_ManCi(p, (int)i);
                      return cnfData->pVarNums[Gia_ObjId(p, o)];
                    });

  // Mf leaves pMan pointing at the graph it derived over, cast to Aig_Man_t*,
  // and when it coarsened, that graph is a copy it has already stopped.
  // Nothing in STP reads pMan and Cnf_DataFree does not touch it; null the
  // pointer so a dangling one cannot be followed.
  cnfData->pMan = NULL;

  // Mf also hangs the CNF off the graph it was given. Here that graph is the
  // blaster's own manager, which outlives this call, while the CNF is about
  // to belong to `cnf` and be freed with it -- and Gia_ManStop frees pData2
  // but never pData, so nothing else clears it. Same reason as pMan above.
  p->pData = NULL;

  // Each symbol maps to the variables its bits carry. ~0u for a bit that
  // reached no variable, which is the same sentinel the other two lowerings
  // write and what the freezing pass and the model builder expect.
  for (const auto& entry : mgr.symbolToBBNode)
  {
    const ASTNode& n = entry.first;
    const std::vector<BBNodeGia>& bits = entry.second;
    assert(nodeToVars.find(n) == nodeToVars.end());

    const int width = (n.GetType() == BOOLEAN_TYPE) ? 1 : n.GetValueWidth();
    std::vector<unsigned> v(width, ~((unsigned)0));

    for (unsigned i = 0; i < bits.size(); i++)
    {
      if (bits[i].IsNull())
        continue;
      const uint32_t var = cnf.varOfCi((uint32_t)mgr.ciOrdinal(bits[i]));
      if (var != 0)
        v[i] = var;
    }
    nodeToVars.insert(std::make_pair(n, v));
  }
}

} // namespace stp
