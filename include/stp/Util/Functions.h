/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: 11/04/2012
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

// FIXME: This header seems dead. Remove it
#ifndef FUNCTIONS_H_
#define FUNCTIONS_H_

#include "stp/Simplifier/constantBitP/FixedBits.h"
#include "stp/Interface/cpp_interface.h"
#include "stp/Simplifier/constantBitP/ConstantBitP_TransferFunctions.h"
#include "stp/Simplifier/constantBitP/ConstantBitPropagation.h"
#include <list>

using simplifier::constantBitP::FixedBits;
using namespace simplifier::constantBitP;

using namespace BEEV;

Result multiply(vector<FixedBits*>& children, FixedBits& output);

Result unsignedDivide(vector<FixedBits*>& children, FixedBits& output);

Result signedDivide(vector<FixedBits*>& children, FixedBits& output);

Result signedRemainder(vector<FixedBits*>& children, FixedBits& output);

Result signedModulus(vector<FixedBits*>& children, FixedBits& output);

Result unsignedModulus(vector<FixedBits*>& children, FixedBits& output);

int bvOrF(int a, int b);
int bvXOrF(int a, int b);
int bvAndF(int a, int b);
int rightSF(int a, int b);
int leftSF(int a, int b);
int plusF(int a, int b);
int multiplyF(int a, int b);
int divideF(int a, int b);
int subF(int a, int b);
int eqF(int a, int b);
int ltF(int a, int b);
int remF(int a, int b);

struct Functions
{
  struct Function
  {
    Kind k;
    string name;
    Result (*fn)(vector<FixedBits*>&, FixedBits&);
    int (*op)(int o1, int o2);

    Function(Kind k_, string name_,
             Result (*fn_)(vector<FixedBits*>&, FixedBits&),
             int (*op_)(int o1, int o2))
    {
      name = name_;
      k = k_;
      fn = fn_;
      op = op_;
    }
  };

  std::list<Function> l;

  /*

      exhaustively_check(i, BVRIGHTSHIFT, &bvRightShiftBothWays, &rightSF);
      exhaustively_check(i, BVPLUS, &bvAddBothWays, &plusF);

      exhaustively_check(i, BVAND, &bvAndBothWays, &bvandF);
      exhaustively_check(i, BVOR, &bvOrBothWays, &bvorF);
      }
      */

  Functions()
  {
    l.push_back(Function(BVSGE, "signed greater than equals",
                         &bvSignedGreaterThanEqualsBothWays, NULL));
    l.push_back(
        Function(BVLT, "unsigned less than", &bvLessThanBothWays, &ltF));
    l.push_back(Function(EQ, "equals", &bvEqualsBothWays, &eqF));
    l.push_back(Function(BVXOR, "bit-vector xor", &bvXorBothWays, &bvXOrF));
    l.push_back(Function(BVOR, "bit-vector or", &bvOrBothWays, &bvOrF));
    l.push_back(Function(BVAND, "bit-vector and", &bvAndBothWays, &bvAndF));
    l.push_back(
        Function(BVRIGHTSHIFT, "right shift", &bvRightShiftBothWays, &rightSF));
    l.push_back(
        Function(BVLEFTSHIFT, "left shift", &bvLeftShiftBothWays, &leftSF));
    l.push_back(Function(BVSRSHIFT, "arithmetic shift",
                         &bvArithmeticRightShiftBothWays, NULL));
    l.push_back(Function(BVPLUS, "addition", &bvAddBothWays, &plusF));
    l.push_back(Function(BVSUB, "subtraction", &bvSubtractBothWays, &subF));
    l.push_back(Function(BVMULT, "multiplication", &multiply, &multiplyF));
    l.push_back(
        Function(BVDIV, "unsigned division", &unsignedDivide, &divideF));
    l.push_back(Function(BVMOD, "unsigned remainder", &unsignedModulus, &remF));
    l.push_back(Function(SBVDIV, "signed division", &signedDivide, NULL));
    l.push_back(Function(SBVREM, "signed remainder", &signedRemainder, NULL));
  }
};

#endif /* FUNCTIONS_H_ */
