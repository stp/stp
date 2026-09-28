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

#include "stp/c_interface.h"

int main(void)
{
  VC checker = vc_createValidityChecker();
  if (checker == 0)
    return 1;

  vc_setFlag(checker, 'u');
  Type bv8 = vc_bvType(checker, 8);
  UFDeclHandle function = vc_declareUninterpretedFunction(
      checker, "installed_c_f", &bv8, 1, bv8);
  vc_DeleteExpr(bv8);
  if (function == 0)
  {
    vc_Destroy(checker);
    return 2;
  }

  Expr argument = vc_bvConstExprFromInt(checker, 8, 42);
  Expr arguments[] = {argument};
  Expr application =
      vc_applyUninterpretedFunction(checker, function, arguments, 1);
  if (application == 0 || getExprKind(application) != UF_APPLY)
  {
    vc_DeleteExpr(application);
    vc_DeleteExpr(argument);
    vc_Destroy(checker);
    return 3;
  }

  vc_DeleteExpr(application);
  vc_DeleteExpr(argument);
  vc_Destroy(checker);
  return 0;
}
