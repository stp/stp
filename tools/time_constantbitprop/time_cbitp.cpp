/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: November, 2005
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

// Times how long running constant bit propagation takes per transfer function.

#include <ctime>
#include <vector>
#include <list>
#include <iomanip>

#include "extlib-constbv/constantbv.h"
#include "stp/AST/AST.h"
#include "stp/AST/ASTKind.h"
#include "stp/cpp_interface.h"
#include "stp/cpp_interface.h"
#include "stp/Parser/LetMgr.h"
#include "stp/Simplifier/constantBitP/ConstantBitP_TransferFunctions.h"
#include "stp/Simplifier/constantBitP/FixedBits.h"
#include "stp/Simplifier/constantBitP/MersenneTwister.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Util/Relations.h"
#include "stp/Util/StopWatch.h"

using simplifier::constantBitP::FixedBits;
using namespace simplifier::constantBitP;

const int iterations = 50000;
const unsigned bitWidth = 65;

stp::STPMgr* beev;

void runSimple(Result (*transfer)(vector<FixedBits*>&, FixedBits&),
               const int probabilityOfFixing, ostream& output, Kind k)
{

  int initially_fixed = 0;
  int finally_fixed = 0;

  Relations r(iterations, bitWidth, k, beev, probabilityOfFixing);

  Stopwatch s;

  list<Relations::Relation>::iterator it = r.relations.begin();
  while (it != r.relations.end())
  {
    Relations::Relation& rel = *it;
    FixedBits& a = rel.a;
    FixedBits& b = rel.b;
    FixedBits& output = rel.output;

    vector<FixedBits*> children;
    children.push_back(&a);
    children.push_back(&b);

    if (false)
    {
      std::cerr << a;
      std::cerr << b;
      std::cerr << output;
      std::cerr << std::endl;
    }

    Result r = transfer(children, output);

    if (false)
    {
        std::cerr << "after" << a;
        std::cerr << b;
        std::cerr << output;
        std::cerr << std::endl;
    }

    assert(r != CONFLICT);

    const int final = a.countFixed() + b.countFixed() + output.countFixed();
    assert(final >= rel.initial);
    finally_fixed += final;
    initially_fixed += rel.initial;

    it++;
  }

  clock_t t = s.stop2();

  cerr << std::fixed;
  cerr << "&" << std::setprecision(2) << (float(t) / CLOCKS_PER_SEC) << "s";
  output << " &" << initially_fixed << " & " << finally_fixed - initially_fixed
         << endl;

  return;
}

simplifier::constantBitP::Result signedModulus(vector<FixedBits*>& children,
                                               FixedBits& output)
{
  return bvSignedModulusBothWays(children, output, beev);
}

simplifier::constantBitP::Result signedRemainder(vector<FixedBits*>& children,
                                                 FixedBits& output)
{
  return bvSignedRemainderBothWays(children, output, beev);
}

simplifier::constantBitP::Result unsignedModulus(vector<FixedBits*>& children,
                                                 FixedBits& output)
{
  return bvUnsignedModulusBothWays(children, output, beev);
}


simplifier::constantBitP::Result unsignedDivision(vector<FixedBits*>& children,
                                                  FixedBits& output)
{
  return bvUnsignedDivisionBothWays(children, output, beev);
}

simplifier::constantBitP::Result signedDivision(vector<FixedBits*>& children,
                                                FixedBits& output)
{
  return bvSignedDivisionBothWays(children, output, beev);
}

simplifier::constantBitP::Result multiply(vector<FixedBits*>& children,
                                          FixedBits& output)
{
  return bvMultiplyBothWays(children, output, beev);
}

//
void run_with_various_prob(Result (*transfer)(vector<FixedBits*>&, FixedBits&),
                           ostream& output, Kind kind = stp::UNDEFINED)
{
  runSimple(transfer, 1, cerr, kind);
  runSimple(transfer, 5, cerr, kind);
  runSimple(transfer, 50, cerr, kind);
  output << "\\\\" << endl;
}

int main(void)
{
  beev = new stp::STPMgr();

  stp::Cpp_interface interface(*beev, beev->defaultNodeFactory);
  interface.startup();
  stp::GlobalParserBM = beev;

  ostream& output = cerr;

  output << "%"
         << "iterations" << iterations<< std::endl;
  output << "%"
         << "bit-width" << bitWidth << std::endl;

  output << "signed greater than equals" << endl;
  run_with_various_prob(&bvSignedGreaterThanEqualsBothWays, output, stp::BVSGE);

  output << "unsigned less than" << endl;
  run_with_various_prob(&bvLessThanBothWays, output, stp::BVLT);

  output << "equals" << endl;
  run_with_various_prob(bvEqualsBothWays, output, stp::EQ);

  output << "bit-vector xor" << endl;
  run_with_various_prob(bvXorBothWays, output, stp::BVXOR);

  output << "bit-vector or" << endl;
  run_with_various_prob(bvOrBothWays, output, stp::BVOR);

  output << "bit-vector and" << endl;
  run_with_various_prob(bvAndBothWays, output, stp::BVAND);

  output << "right shift" << endl;
  run_with_various_prob(bvRightShiftBothWays, output, stp::BVRIGHTSHIFT);

  output << "left shift" << endl;
  run_with_various_prob(bvLeftShiftBothWays, output, stp::BVLEFTSHIFT);

  output << "arithmetic shift" << endl;
  run_with_various_prob(bvArithmeticRightShiftBothWays, output, stp::BVSRSHIFT);

  output << "addition" << endl;
  run_with_various_prob(bvAddBothWays, output, stp::BVPLUS);

  output << "multiplication" << endl;
  run_with_various_prob(multiply, output, stp::BVMULT);

  output << "unsigned remainder" << endl;
  run_with_various_prob(unsignedModulus, output, stp::BVMOD);

  output << "unsigned division" << endl;
  run_with_various_prob(unsignedDivision, output, stp::BVDIV);

  output << "signed division" << endl;
  run_with_various_prob(signedDivision, output, stp::SBVDIV);

  output << "signed remainder" << endl;
  run_with_various_prob(signedRemainder, output, stp::SBVREM);

  output << "signed modulus" << endl;
  run_with_various_prob(signedModulus, output, stp::SBVMOD);

  return 1;
}
