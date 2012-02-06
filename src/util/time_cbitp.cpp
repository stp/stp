#include <ctime>
#include <vector>
#include "../AST/AST.h"
#include "../simplifier/constantBitP/FixedBits.h"
#include "../simplifier/constantBitP/ConstantBitP_TransferFunctions.h"
#include "../extlib-constbv/constantbv.h"
#include "../simplifier/constantBitP/MersenneTwister.h"
#include "../AST/ASTKind.h"
#include "../STPManager/STPManager.h"
#include "../cpp_interface/cpp_interface.h"

using namespace std;
using simplifier::constantBitP::FixedBits;
using namespace simplifier::constantBitP;


const int iterations = 100000;
const unsigned bitWidth = 64;

BEEV::STPMgr* beev;


// Create a random assignment to fixed bits.
FixedBits createRandom(const int length, const int probabilityOfSetting, MTRand& trand)
  {
    assert( 0 <= probabilityOfSetting);
    assert( 100 >= probabilityOfSetting);

    FixedBits result(length, false);

    // I'm not sure if the random number generator is generating just 32 bit numbers??
    int i = 0;
    int randomV = trand.randInt();

    int pool = 32;

    while (i < length)
      {
        if (pool < 8)
          {
            randomV = trand.randInt();
            pool = 32;
          }

        int val = (randomV & 127);
        randomV >>= 7;
        pool = pool - 7;

        if (val >= 100)
        continue;

        if (val < probabilityOfSetting)
          {
            switch (randomV & 1)
              {
                case 0:
                result.setFixed(i, true);
                result.setValue(i, false);
                break;
                case 1:
                result.setFixed(i, true);
                result.setValue(i, true);
                break;
                default:
                BEEV::FatalError(LOCATION "never.");

              }
            randomV >>= 1;
          }
        i++;

      }
    return result;
  }

class Stopwatch
{
public:
	Stopwatch() :
		start(std::clock())
	{
	}
	void stop()
	{
		clock_t total = clock() - start;
		cerr << "ticks: " << total << " " << (float(total) / CLOCKS_PER_SEC) << "s" << endl;
	}
	void stop2()
	{
		clock_t total = clock() - start;
		cerr << (float(total) / CLOCKS_PER_SEC) << "s";
	}

private:
	std::clock_t start;
};



void run(Result(*transfer)(vector<FixedBits*>&, FixedBits&), const int probabilityOfFixing, ostream& output)
{
	Stopwatch s;

	int unsatisfiableCount = 0;
	int satisfiableCount = 0;

	unsigned calls = 0;

	MTRand rand;

	unsigned long totalOutputBits = 0;
	unsigned long totalOutputOneBits = 0;
	unsigned long totalFixedOutputBits = 0;

	for (int i = 0; i < iterations; i++)
	{
		vector<FixedBits*> children;

		FixedBits a = createRandom(bitWidth, probabilityOfFixing, rand);
		FixedBits b = createRandom(bitWidth, probabilityOfFixing, rand);

		FixedBits output = createRandom(bitWidth, probabilityOfFixing, rand);

		for (unsigned i = 0; i < bitWidth; i++)
		{
			totalOutputBits++;
			if (output.isFixed(i))
			{
				totalFixedOutputBits++;
				if (output.getValue(i))
					totalOutputOneBits++;
			}
		}

		children.push_back(&a);
		children.push_back(&b);

		bool done = false;
		bool first = true;
		top: while (!done)
		{
			calls++;
			Result r = transfer(children, output);

			if (CONFLICT == r)
			{
				unsatisfiableCount++;
				done = true;
				if (!first)
					throw "BAD";
			}
			else
			{
				first = false;
				for (unsigned i = 0; i < bitWidth; i++)
				{
					if (!a.isFixed(i))
					{
						a.setFixed(i, true);
						a.setValue(i, false);
						goto top;
					}
					if (!b.isFixed(i))
					{
						b.setFixed(i, true);
						b.setValue(i, false);
						goto top;
					}
					if (!output.isFixed(i))
					{
						output.setFixed(i, true);
						output.setValue(i, false);
						goto top;
					}
				}
				satisfiableCount++;
				break;
			}
		}
	}

	output << "Iterations: " << iterations << endl;
	output << "BitWidth: " << bitWidth << endl;
	output << "Calls to transfer: " << calls << endl;
	output << "Probability of fixing: " << probabilityOfFixing << endl;
	output << "unsatisfiable count: " << unsatisfiableCount << endl;
	output << "satisfiable count: " << satisfiableCount << endl;
	output << "total: " << totalOutputBits << endl;
	output << "total fixed: " << totalFixedOutputBits << endl;
	output << "total One Bits fixed: " << totalOutputOneBits << endl;

	s.stop();

	return;
}

void runSimple(Result(*transfer)(vector<FixedBits*>&, FixedBits&), const int probabilityOfFixing, ostream& output)
{
	Stopwatch s;

	int conflicts = 0;

	MTRand rand;

	int initially_fixed = 0;
	int finally_fixed = 0;

	for (int i = 0; i < iterations; i++)
	{
		vector<FixedBits*> children;

		FixedBits a = createRandom(bitWidth, probabilityOfFixing, rand);
		FixedBits b = createRandom(bitWidth, probabilityOfFixing, rand);
		FixedBits output = createRandom(bitWidth, probabilityOfFixing, rand);

		int initial =  a.countFixed() + b.countFixed() + output.countFixed();


		children.push_back(&a);
		children.push_back(&b);

		Result r = transfer(children, output);

		if (r == CONFLICT)
			conflicts++;
		else
		  {
	                finally_fixed += a.countFixed() + b.countFixed() + output.countFixed();
	                initially_fixed += initial;
		  }
	}

	output << "&";
	s.stop2();
	output <<  "& " << conflicts << " &" << finally_fixed-initially_fixed <<   endl;

	return;
}



simplifier::constantBitP::Result signedModulus(vector<FixedBits*>& children,
                FixedBits& output)
{
        return bvSignedModulusBothWays(children, output,beev);
}

simplifier::constantBitP::Result unsignedDivision(vector<FixedBits*>& children,
                FixedBits& output)
{
        return bvUnsignedDivisionBothWays(children, output,beev);
}


simplifier::constantBitP::Result divide(vector<FixedBits*>& children,
                FixedBits& output)
{
        return bvUnsignedDivisionBothWays(children, output,beev);
}


simplifier::constantBitP::Result multiply(vector<FixedBits*>& children,
                FixedBits& output)
{
        return bvMultiplyBothWays(children, output, beev);
}

//
void run_with_various_prob (Result(*transfer)(vector<FixedBits*>&, FixedBits&), ostream& output)
{
        int prob;

        for (int i = 0; i <= 2; i++)
        {
                if (i == 0)
                        prob = 1;
                if (i == 1)
                        prob = 5;
                if (i==2)
                        prob = 50;

               // output  << prob;
                runSimple(transfer, prob, cerr);
        }
        output << "\\\\" << endl;
}

simplifier::constantBitP::Result no_op(vector<FixedBits*>& children,
                FixedBits& output)
{
  return NO_CHANGE;
}

int
main(void)
{
  beev = new BEEV::STPMgr();

  Cpp_interface interface(*beev, beev->defaultNodeFactory);
  interface.startup();

  srand(time(NULL));
  BEEV::ParserBM = beev;

  ostream& output = cerr;

  output << "no_op&" << endl;
  run_with_various_prob(no_op, output);

  output << "right shift&" << endl;
  run_with_various_prob(bvRightShiftBothWays, output);

  output << "arithmetic shift&" << endl;
  run_with_various_prob(bvArithmeticRightShiftBothWays, output);

  output << "multiplication&" << endl;
  run_with_various_prob(multiply, output);

  output << "unsigned division&" << endl;
  run_with_various_prob(unsignedDivision, output);

  output << "bit-vector xor&" << endl;
  run_with_various_prob(bvXorBothWays, output);

  output << "addition&" << endl;
  run_with_various_prob(bvAddBothWays, output);

  output << "%" << "iterations" << iterations;
  output << "%" << "bit-width" << iterations;
  return 1;
}


