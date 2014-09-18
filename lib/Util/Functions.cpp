#include "stp/Util/Functions.h"
/*
 * Functions.cpp
 *
 *  Created on: 11/04/2012
 *      Author: thansen
 */

Result
multiply(vector<FixedBits*>& children, FixedBits& output)
{
  return bvMultiplyBothWays(children, output, ParserBM, 0);
}

Result
unsignedDivide(vector<FixedBits*>& children, FixedBits& output)
{
  return bvUnsignedDivisionBothWays(children, output, ParserBM);
}


Result
signedDivide(vector<FixedBits*>& children, FixedBits& output)
{
  return bvSignedDivisionBothWays(children, output, ParserBM);
}

Result
signedRemainder(vector<FixedBits*>& children, FixedBits& output)
{
  return bvSignedRemainderBothWays(children, output, ParserBM);
}

Result
signedModulus(vector<FixedBits*>& children, FixedBits& output)
{
  return bvSignedModulusBothWays(children, output, ParserBM);
}

Result
unsignedModulus(vector<FixedBits*>& children, FixedBits& output)
{
  return bvUnsignedModulusBothWays(children, output, ParserBM);
}



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
