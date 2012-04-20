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



struct Functions
{
  struct Function
  {
    Kind k;
    string name;
    Result (*fn)(vector<FixedBits*>&, FixedBits&);

    Function (Kind k_, string name_, Result (*fn_)(vector<FixedBits*>&, FixedBits&) )
    {
      name = name_;
      k = k_;
      fn = fn_;
    }
  };

  std::list<Function> l;


  Functions()
  {
    l.push_back(Function(BVSGE, "signed greater than equals", &bvSignedGreaterThanEqualsBothWays));
    l.push_back(Function(BVLT, "unsigned less than", &bvLessThanEqualsBothWays));
    l.push_back(Function(EQ, "equals", &bvEqualsBothWays));
    l.push_back(Function(BVXOR, "bit-vector xor", &bvXorBothWays));
    l.push_back(Function(BVOR, "bit-vector or", &bvOrBothWays));
    l.push_back(Function(BVAND, "bit-vector and", &bvAndBothWays));
    l.push_back(Function(BVRIGHTSHIFT, "right shift", &bvRightShiftBothWays));
    l.push_back(Function(BVLEFTSHIFT, "left shift", &bvLeftShiftBothWays));
    l.push_back(Function(BVSRSHIFT, "arithmetic shift", &bvArithmeticRightShiftBothWays));
    l.push_back(Function(BVPLUS, "addition", &bvAddBothWays));
    l.push_back(Function(BVMULT, "multiplication", &multiply));
    l.push_back(Function(BVDIV, "unsigned division", &unsignedDivide));
    l.push_back(Function(BVMOD, "unsigned remainder", &unsignedModulus));
    l.push_back(Function(SBVDIV, "signed division", &signedDivide));
    l.push_back(Function(SBVREM, "signed remainder",&signedRemainder ));
}



};

#endif /* FUNCTIONS_H_ */
