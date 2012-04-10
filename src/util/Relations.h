/*
 * Relations.h
 *
 *  Created on: 10/04/2012
 *      Author: thansen
 */

#ifndef RELATIONS_H_
#define RELATIONS_H_

#include <ctime>
#include <vector>
#include "../AST/AST.h"
#include "../simplifier/constantBitP/FixedBits.h"
#include "../simplifier/constantBitP/MersenneTwister.h"

#include "../simplifier/constantBitP/ConstantBitP_TransferFunctions.h"
#include "../extlib-constbv/constantbv.h"

#include "../AST/ASTKind.h"
#include "../STPManager/STPManager.h"
#include "../cpp_interface/cpp_interface.h"
#include <list>

using namespace std;
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
