/********************************************************************
 * AUTHORS: Andrew Teylu
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

#include <bitset>

#include "stp/AST/AST.h"
#include "stp/NodeFactory/TypeChecker.h"
#include "stp/Printer/AssortedPrinters.h"
#include "stp/Printer/printers.h"
#include "stp/STPManager/STP.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Util/GitSHA1.h"
#include "stp/cpp_interface.h"

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

  init_vc(bm);

  const unsigned int w = 4;
  const unsigned int exp_width(2 * w);
  const unsigned int sig_width(3 * exp_width);
  const unsigned int bw(sig_width + exp_width);
  std::cout << bw << std::endl;
  assert(bw == 32);
  const unsigned int needle = 8;

  std::cout << bw << std::endl;

  // bw-bit BV type
  Expr bvt = vc_bvType(vc, bw);

  // create our variable x
  Expr x = vc_varExpr(vc, "x", bvt);
  ASTNode* a_x = (ASTNode*)x;
  a_x->SetExpWidth(exp_width);
  a_x->SetSigWidth(sig_width);

  // create our variable y
  Expr y = vc_varExpr(vc, "y", bvt);
  ASTNode* a_y = (ASTNode*)y;
  a_y->SetExpWidth(exp_width);
  a_y->SetSigWidth(sig_width);

  roundingMode rm(traits::RNE());

  ASTNode blasted_add = blast_fpadd(rm, *a_x, *a_y);
  blasted_add.SetExpWidth(exp_width);
  blasted_add.SetSigWidth(sig_width);

  // Expr random = vc_bvConstExprFromLL(vc, bw, 689963008);
  Expr random = vc_bvConstExprFromLL(vc, bw, needle);
  ASTNode* a_random = (ASTNode*)random;
  ASTNode fp_const(bm->CreateFPConst(*a_random, exp_width, sig_width));

#if 0
  // create our zero/one constants
  Expr zero = vc_bvConstExprFromLL(vc, bw, 0);
  Expr one = vc_bvConstExprFromLL(vc, bw, 1);

  ASTNode blasted = blast_fpeq(blasted_add, fp_const);

  Expr x_zero = vc_eqExpr(vc, (Expr*)a_x, zero);
  vc_assertFormula(vc, x_zero);
  Expr y_zero = vc_eqExpr(vc, (Expr*)a_y, zero);
  vc_assertFormula(vc, y_zero);
#endif

  // std::cout << blasted_add << std::endl;
  //

  // Expr eq = vc_eqExpr(vc, (Expr*)&blasted_add, (Expr*)&fp_const);

  ASTNode* side;
  ASTNode round = round_trip(*a_x, &side);
  printer::SMTLIB2_PrintBack(std::cout, *(ASTNode*)&round, bm);
  Expr eq = vc_eqExpr(vc, (Expr*)&round, (Expr*)a_x);
  Expr moo = vc_notExpr(vc, eq);
  // vc_assertFormula(vc, (Expr*)side);
  vc_assertFormula(vc, moo);
#if 0

  Expr to_check = nullptr;
  Expr not_valid = vc_notExpr(vc, (Expr*)side);
  vc_assertFormula(vc, not_valid);
  std::cout << *(ASTNode*)not_valid << std::endl;
  printer::SMTLIB2_PrintBack(std::cout, *(ASTNode*)not_valid, bm);
#endif

  // std::cout << *side << std::endl;

  // vc_assertFormula(vc, (Expr*)&blasted);

#if 0
  std::cout << "eq" << std::endl;
  to_check = eq;
  std::cout << *(ASTNode*)to_check << std::endl;
  printer::SMTLIB2_PrintBack(std::cout, *(ASTNode*)to_check, bm);
  std::cout << "!eq" << std::endl;

  std::cout << "moo" << std::endl;
  to_check = moo;
  std::cout << *(ASTNode*)to_check << std::endl;
  printer::SMTLIB2_PrintBack(std::cout, *(ASTNode*)to_check, bm);
  std::cout << "!moo" << std::endl;
#endif

  // vc_assertFormula(vc, vc_eqExpr(vc, y, zero));
  // vc_assertFormula(vc, vc_eqExpr(vc, x, random));

  // The query we're going to check
  Expr query = vc_falseExpr(vc);

  // Check our query
  int res = vc_query_with_timeout(vc, query, -1, -1);

  // Should give zero (== SAT)
  assert(res == 0);

  // Interrogate the model
  unsigned int val_for_x = getBVUnsignedLongLong(vc_getCounterExample(vc, x));
  unsigned int val_for_y = getBVUnsignedLongLong(vc_getCounterExample(vc, y));
  (void)val_for_y;

#if 0
  std::cout << val_for_x << " " << val_for_y << std::endl;

  float float_for_x;
  *(unsigned int*)&float_for_x = val_for_x;
  float float_for_y;
  *(unsigned int*)&float_for_y = val_for_y;

  std::cout << float_for_x << " " << float_for_y << std::endl;
#endif

  std::bitset<bw> bits_for_x(val_for_x);
  std::bitset<bw> bits_for_random(needle);

  std::cout << "Value for x:      ";
  std::cout << bits_for_x.to_string() << std::endl;
  std::cout << "Value for random: ";
  std::cout << bits_for_random.to_string() << std::endl;

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
