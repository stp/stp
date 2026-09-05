/********************************************************************
 * AUTHORS: Andrew Teylu
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

#include "stp/fp.hpp"
#include "stp/uf.hpp"

int main()
{
  VC checker = vc_createValidityChecker();
  if (checker == nullptr)
    return 1;

  stp::uf::Context context(checker);
  stp::uf::Function function = context.declareUninterpretedFunction(
      "installed_cpp_f", {stp::uf::Sort::bitVector(8)},
      stp::uf::Sort::bitVector(8));
  Expr argument = vc_bvConstExprFromInt(checker, 8, 42);
  Expr application = function({argument});
  bool correctKind = getExprKind(application) == UF_APPLY;

  // Every sort the facade can name has to materialize through the installed
  // header alone, floating-point and rounding-mode included.
  stp::uf::Function mixed = context.declareUninterpretedFunction(
      "installed_cpp_g",
      {stp::uf::Sort::roundingMode(), stp::uf::Sort::floatingPoint(8, 24)},
      stp::uf::Sort::floatingPoint(8, 24));
  Type single = vc_fpType(checker, 8, 24);
  Expr mode = vc_fpRoundingMode(checker, VC_RM_RNE);
  Expr nan = vc_fpNaN(checker, single);
  Expr floatApplication = mixed({mode, nan});
  correctKind = correctKind && getExprKind(floatApplication) == UF_APPLY &&
                vc_getExpWidth(floatApplication) == 8 &&
                vc_getSigWidth(floatApplication) == 24;

  vc_DeleteExpr(floatApplication);
  vc_DeleteExpr(nan);
  vc_DeleteExpr(mode);
  vc_DeleteExpr(single);
  vc_DeleteExpr(application);
  vc_DeleteExpr(argument);
  vc_Destroy(checker);
  return correctKind ? 0 : 2;
}
