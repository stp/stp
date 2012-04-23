/*
 * Functions.h
 *
 *  Created on: 11/04/2012
 *      Author: thansen
 */

#ifndef FUNCTIONS_H_
#define FUNCTIONS_H_

#include "../simplifier/constantBitP/FixedBits.h"
#include "../cpp_interface/cpp_interface.h"
#include "../simplifier/constantBitP/ConstantBitP_TransferFunctions.h"
#include "../simplifier/constantBitP/ConstantBitPropagation.h"
#include <list>

using simplifier::constantBitP::FixedBits;
using namespace simplifier::constantBitP;

using namespace BEEV;

Result
multiply(vector<FixedBits*>& children, FixedBits& output);


Result
unsignedDivide(vector<FixedBits*>& children, FixedBits& output);


Result
signedDivide(vector<FixedBits*>& children, FixedBits& output);


Result
signedRemainder(vector<FixedBits*>& children, FixedBits& output);

Result
signedModulus(vector<FixedBits*>& children, FixedBits& output);

Result
unsignedModulus(vector<FixedBits*>& children, FixedBits& output);

int bvOrF(int a, int b)
{
  return a | b;
}

int bvXOrF(int a, int b)
{
  return a ^ b;
}

int bvAndF(int a, int b)
{
  return a &b;
}

int rightSF(int a, int b)
{
  if (b >= sizeof(int)*8)
    return 0;

  return a>>b;
}

int leftSF(int a, int b)
{
  if (b >= sizeof(int)*8)
    return 0;

  return a<<b;
}

int plusF(int a, int b)
{
  return a+b;
}

int multiplyF(int a, int b)
{
  return a*b;
}

int divideF(int a, int b)
{
  if (b==0)
    return 1;
  return a/b;
}


int subF(int a, int b)
{
  return a-b;
}

int eqF(int a, int b)
{
  return (a==b)? 1:0;
}

int ltF(int a, int b)
{
  return (a<b)? 1:0;
}

int remF(int a, int b)
{
  if (b ==0)
    return a;
  return (a %b);
}


struct Functions
{
  struct Function
  {
    Kind k;
    string name;
    Result (*fn)(vector<FixedBits*>&, FixedBits&);
    int(*op)(int o1, int o2);

    Function (Kind k_, string name_, Result (*fn_)(vector<FixedBits*>&, FixedBits&), int(*op_)(int o1, int o2) )
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
    //l.push_back(Function(BVSGE, "signed greater than equals", &bvSignedGreaterThanEqualsBothWays));
    l.push_back(Function(BVLT, "unsigned less than", &bvLessThanBothWays, &ltF));
    l.push_back(Function(EQ, "equals", &bvEqualsBothWays, &eqF));
    l.push_back(Function(BVXOR, "bit-vector xor", &bvXorBothWays, &bvXOrF));
    l.push_back(Function(BVOR, "bit-vector or", &bvOrBothWays, &bvOrF ));
    l.push_back(Function(BVAND, "bit-vector and", &bvAndBothWays, &bvAndF));
    l.push_back(Function(BVRIGHTSHIFT, "right shift", &bvRightShiftBothWays, &rightSF));
    l.push_back(Function(BVLEFTSHIFT, "left shift", &bvLeftShiftBothWays, &leftSF));
    //l.push_back(Function(BVSRSHIFT, "arithmetic shift", &bvArithmeticRightShiftBothWays));
    l.push_back(Function(BVPLUS, "addition", &bvAddBothWays, &plusF));
    l.push_back(Function(BVSUB, "subtraction", &bvSubtractBothWays, &subF));
    l.push_back(Function(BVMULT, "multiplication", &multiply, &multiplyF));
    l.push_back(Function(BVDIV, "unsigned division", &unsignedDivide, &divideF));
    l.push_back(Function(BVMOD, "unsigned remainder", &unsignedModulus, &remF));
    //l.push_back(Function(SBVDIV, "signed division", &signedDivide));
    //l.push_back(Function(SBVREM, "signed remainder",&signedRemainder ));
  }




};

#endif /* FUNCTIONS_H_ */
