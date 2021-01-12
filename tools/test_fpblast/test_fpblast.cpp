/********************************************************************
 * AUTHORS: Andrew V. Jones
 *
 * BEGIN DATE: January 2021
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

#include "stp/FloatBlaster/symbolic_fp.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/STPManager/STPManager.h"
#include "stp/c_interface.h"

using namespace stp;
using namespace stp::symbolic_fp;

STPMgr* mgr;
VC vc;

void foo(STPMgr* bm)
{
  vc = vc_createValidityCheckerReuse(bm);

  // 32-bit BV type
  Expr bvt = vc_bvType(vc, 32);

  // create our variable x
  Expr x = vc_varExpr(vc, "x", bvt);
  ASTNode* a_x = (ASTNode*)x;
  a_x->SetExpWidth(8);
  a_x->SetSigWidth(24);

  // create our variable y
  Expr y = vc_varExpr(vc, "y", bvt);
  ASTNode* a_y = (ASTNode*)y;
  a_y->SetExpWidth(8);
  a_y->SetSigWidth(24);

  // create our zero/one constants
  Expr zero = vc_bvConstExprFromLL(vc, 32, 0);
  Expr one = vc_bvConstExprFromLL(vc, 32, 1);

  ASTNode blasted = blast_fpeq(*a_x, *a_y);

#if 0
  Expr x_zero = vc_eqExpr(vc, (Expr*)a_x, zero);
  vc_assertFormula(vc, x_zero);
  Expr y_zero = vc_eqExpr(vc, (Expr*)a_y, zero);
  vc_assertFormula(vc, y_zero);
#endif

  vc_assertFormula(vc, vc_notExpr(vc, (Expr*)&blasted));

  // The query we're going to check
  Expr query = vc_falseExpr(vc);

  // Check our query
  int res = vc_query_with_timeout(vc, query, -1, -1);

  // Should give zero (== SAT)
  assert(res == 0);

  // Interrogate the model
  unsigned int val_for_x = getBVUnsignedLongLong(vc_getCounterExample(vc, x));
  unsigned int val_for_y = getBVUnsignedLongLong(vc_getCounterExample(vc, y));

  std::cout << val_for_x << " " << val_for_y << std::endl;

  float float_for_x;
  *(unsigned int*)&float_for_x = val_for_x;
  float float_for_y;
  *(unsigned int*)&float_for_y = val_for_y;

  std::cout << float_for_x << " " << float_for_y << std::endl;

  exit(0);
}

int main(void)
{
  stp::STPMgr stp;
  mgr = &stp;

  foo(mgr);

  return 1;
}

// EOF
