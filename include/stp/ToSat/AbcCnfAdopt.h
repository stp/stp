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

#ifndef ABCCNFADOPT_H_
#define ABCCNFADOPT_H_

// From ABC
#include "sat/cnf/cnf.h"

#include "stp/AIG/CNF.h"

#include <functional>

namespace stp
{

// Take over an ABC-generated formula, projecting its per-object pVarNums down
// to the CI and CO variables that are the only ones anybody asks for. The
// clauses are adopted, not copied: ABC's layout is already the one CNF
// exposes.
//
// `objectVar` reads pVarNums for one object, which is the only thing that
// differs between the Aig-based generators and the Gia-based one -- each
// indexes that array by ids of its own manager. Shared by ToCNFAIG and
// ToCNFGia, which is why it lives here rather than on either of them.
inline CNF adoptAbcCnf(Cnf_Dat_t* cnfData, unsigned nCi, unsigned nCo,
                       const std::function<int(bool isCo, unsigned)>& objectVar)
{
  assert(cnfData != NULL);
  CNF cnf;
  cnf.adopt(cnfData, [](void* p) { Cnf_DataFree((Cnf_Dat_t*)p); },
            cnfData->pClauses, (uint64_t)cnfData->nClauses,
            (uint64_t)cnfData->nLiterals, (uint32_t)cnfData->nVars, nCi, nCo);

  // -1 is ABC's "this object has no variable" -- a CI outside the cone of the
  // outputs, or a CO that was asserted rather than named. CNF spells that 0,
  // for the reason its header gives.
  const auto var = [](int v) { return v < 0 ? 0u : (uint32_t)v; };
  for (unsigned i = 0; i < nCi; i++)
    cnf.mapCi(i, var(objectVar(false, i)));
  for (unsigned i = 0; i < nCo; i++)
    cnf.mapCo(i, var(objectVar(true, i)));
  return cnf;
}

} // namespace stp

#endif /* ABCCNFADOPT_H_ */
