/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: 10/04/2012
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
#ifndef RELATIONS_H_
#define RELATIONS_H_

#include <ctime>
#include <vector>
#include "s/AST/AST.h"
#include "stp/Simplifier/constantBitP/FixedBits.h"
#include "stp/Simplifier/constantBitP/MersenneTwister.h"

#include "stp/Simplifier/constantBitP/ConstantBitP_TransferFunctions.h"
#include "extlib-constbv/constantbv.h"

#include "stp/AST/ASTKind.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Interface/cpp_interface.h"
#include <list>

using simplifier::constantBitP::FixedBits;
using namespace simplifier::constantBitP;


struct Relations
{
  struct Relation
  {
    FixedBits a,b,output;
    int initial;
    Relation(FixedBits a_, FixedBits b_, FixedBits output_)
    : a(a_), b(b_), output(output_)
    {
      initial = a.countFixed() + b.countFixed() + output.countFixed();
    }
  };

    list<Relation> relations;

    Relations (int iterations, int bitWidth,Kind k, STPMgr*beev, int probabilityOfFixing)
    {
      MTRand rand;

      for (int i = 0; i < iterations; i++)
        {
        FixedBits a = FixedBits::createRandom(bitWidth, 100, rand);
        FixedBits b = FixedBits::createRandom(bitWidth, 100, rand);

        assert(a.isTotallyFixed());
        assert(b.isTotallyFixed());
        ASTVec c;
        c.push_back(beev->CreateBVConst(a.GetBVConst(), bitWidth));
        c.push_back(beev->CreateBVConst(b.GetBVConst(), bitWidth));
        ASTNode result = NonMemberBVConstEvaluator(beev, k, c, bitWidth);
        FixedBits output = FixedBits::concreteToAbstract(result);

        for (int i = 0; i < a.getWidth(); i++)
          {
          if (rand.randInt() % 100 >= probabilityOfFixing)
            a.setFixed(i, false);
          if (rand.randInt() % 100 >= probabilityOfFixing)
            b.setFixed(i, false);
          }
        for (int i = 0; i < output.getWidth(); i++)
          if (rand.randInt() % 100 >= probabilityOfFixing)
            output.setFixed(i, false);

        Relation r(a, b, output);
        relations.push_back(r);
        }
    }
};


#endif /* RELATIONS_H_ */
