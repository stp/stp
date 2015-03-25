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

#ifndef TOCNFAIG_H_
#define TOCNFAIG_H_

#include "extlib-abc/aig.h"
#include "extlib-abc/cnf_short.h"
#include "extlib-abc/dar.h"
#include "stp/ToSat/ToSATBase.h"
#include "stp/ToSat/AIG/BBNodeManagerAIG.h"

namespace stp
{
class ASTtoCNF;

class ToCNFAIG // not copyable
{
  UserDefinedFlags& uf;

  void dag_aware_aig_rewrite(
    const bool needAbsRef,
    BBNodeManagerAIG& mgr);

  void fill_node_to_var(
    Cnf_Dat_t* cnfData,
    ToSATBase::ASTNodeToSATVar& nodeToVars,
    BBNodeManagerAIG& mgr);

public:
  ToCNFAIG(UserDefinedFlags& _uf) : uf(_uf) {}

  void toCNF(const BBNodeAIG& top, Cnf_Dat_t*& cnfData,
             ToSATBase::ASTNodeToSATVar& nodeToVars, bool needAbsRef,
             BBNodeManagerAIG& _mgr);
};
}
#endif /* TOCNFAIG_H_ */
