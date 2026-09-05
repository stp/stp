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

#ifndef TOCNFTSEITIN_H_
#define TOCNFTSEITIN_H_

#include "stp/AIG/CNF.h"
#include "stp/AIG/Tseitin.h"
#include "stp/STPManager/UserDefinedFlags.h"
#include "stp/ToSat/BBNodeManagerLit.h"
#include "stp/ToSat/ToSATBase.h"

namespace stp
{

// The in-house AIG's route to CNF, and the whole of it: assert the formula as
// the manager's one output, run the Tseitin writer over it, and project the
// inputs back to the symbols they came from.
//
// ToCNFAIG has to do more than this because ABC's route does more: a
// dag-aware rewriting loop, a manager-to-manager copy, and a per-object
// variable map that has to be re-indexed after each of them. None of that
// applies here -- no pass rewrites this AIG, so nothing renumbers, so the
// node a symbol was blasted to is the node it still is.
class ToCNFTseitin
{
  UserDefinedFlags& uf;

public:
  explicit ToCNFTseitin(UserDefinedFlags& _uf) : uf(_uf) {}

  // The same signature as ToCNFAIG::toCNF, so one templated body drives
  // either.
  //
  // needAbsRef is taken and ignored. It exists on the ABC side to suppress
  // Aig_ManCleanup, because a cleanup renumbers and refinement has to be able
  // to name an input afterwards. This writer encodes the cone of the output
  // unconditionally and numbers every input whether it is reachable or not,
  // so there is nothing for the flag to protect.
  void toCNF(const BBNodeLit& top, CNF& cnf,
             ToSATBase::ASTNodeToSATVar& nodeToVars, bool needAbsRef,
             BBNodeManagerLit& mgr);
};

} // namespace stp

#endif
