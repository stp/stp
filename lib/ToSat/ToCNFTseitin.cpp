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

#include "stp/ToSat/ToCNFTseitin.h"

#include "stp/AIG/Tseitin.h"

namespace stp
{

void ToCNFTseitin::toCNF(const BBNodeLit& top, CNF& cnf,
                         ToSATBase::ASTNodeToSATVar& nodeToVars,
                         bool /*needAbsRef*/, BBNodeManagerLit& mgr)
{
  assert(nodeToVars.size() == 0);
  assert(mgr.mgr.outputCount() == 0);
  mgr.mgr.createOutput(top.n);

  // The structural-hash table has done its work and is about half the
  // manager's memory. Hand it back before the clause arena is allocated,
  // which is the point in the pipeline where the process is largest.
  mgr.mgr.freeStrash();

  // The three in-house rungs differ only in what the writer recovers before
  // emitting; the blast above them is the same either way.
  aig::Recover recover = aig::Recover::PatternsAndAnds;
  if (uf.cnf_effort == UserDefinedFlags::CNF_EFFORT_NEW_VERY_LOW)
    recover = aig::Recover::Nothing;
  else if (uf.cnf_effort == UserDefinedFlags::CNF_EFFORT_NEW_LOW)
    recover = aig::Recover::Patterns;

  cnf = aig::deriveTseitin(mgr.mgr, 0, recover);

  // Each symbol maps to the variables its bits carry. ~0u for a bit that
  // reached no variable, which is the same sentinel fill_node_to_var writes
  // and what the freezing pass and the model builder expect.
  for (const auto& entry : mgr.symbolToBBNode)
  {
    const ASTNode& n = entry.first;
    const std::vector<BBNodeLit>& bits = entry.second;
    assert(nodeToVars.find(n) == nodeToVars.end());

    const int width = (n.GetType() == BOOLEAN_TYPE) ? 1 : n.GetValueWidth();
    std::vector<unsigned> v(width, ~((unsigned)0));

    for (unsigned i = 0; i < bits.size(); i++)
    {
      if (bits[i].IsNull())
        continue;
      const uint32_t var = cnf.varOfCi(mgr.ciOrdinal(bits[i]));
      if (var != 0)
        v[i] = var;
    }
    nodeToVars.insert(std::make_pair(n, v));
  }

  if (uf.stats_flag)
    std::cerr << (recover == aig::Recover::Nothing    ? "new-very-low CNF"
                  : recover == aig::Recover::Patterns ? "new-low CNF"
                                                      : "new-medium CNF")
              << std::endl;
}

} // namespace stp
