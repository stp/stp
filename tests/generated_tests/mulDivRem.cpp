#include <cstdint>
#include <iostream>
#include <cstdlib>
#include <cassert>
#include <cmath>
#include "../constantbv/constantbv.h"
#include "../AST/AST.h"

/*
 * Generates random (a op b = c) triples to check that solver.
 * Only for complicated instructions like modulus, remainder and divide.
 */

using std::endl;
using std::cout;
using std::cerr;
using namespace BEEV;
using namespace CONSTANTBV;

int width = 16;
typedef uint16_t uns;
typedef int16_t sig;

const bool debug = false;

uns getUnsignedResult(uns a, Kind k, uns b)
{
	uns gold;

	if (BVMULT == k)
	{
		return a * b;
	}
	else if (BVMOD == k)
	{
		return a % b;
	}
	else if (BVDIV == k)
	{
		return a / b;
	}
	cerr << "not implemetned" << endl;
	exit(2);

}

sig getSignedResult(sig a, Kind k, sig b)
{
	sig gold;

	if (SBVMOD == k)
	{
		sig Q_prime = (sig) (trunc((double) a / (double) b));
		if ((a < 0) != (b < 0))
		{
			Q_prime = Q_prime - 1;
		}

		gold = a - Q_prime * b;
		if (debug)
			fprintf(stderr, "a=%d; b=%d; Q_prime=%d\n", a, b, Q_prime);
	}
	else if (SBVREM == k)
	{
		gold = a % b;
	}
	else if (SBVDIV == k)
	{
		gold = a / b;
	}
	else
	{
		cerr << "not implemetned" << endl;
		exit(2);
	}
	return gold;

}

void go(int count, uns a, uns b, uns result, char* name)
{
	cout << ":extrafuns ((a" << count << " BitVec[" << width << "])) " << endl;
	cout << ":extrafuns ((b" << count << " BitVec[" << width << "])) " << endl;
	cout << ":extrafuns ((op" << count << " BitVec[" << width << "])) " << endl;

	cout << ":assumption (= ";
	cout << "(" << name << " ";
	if ((rand() % 3) == 0)
		cout << "a" << count << " ";
	else
		cout << "bv" << a << "[" << width << "] ";

	if ((rand() % 3) == 0)
		cout << "b" << count << " ";
	else
		cout << "bv" << b << "[" << width << "]";
	cout << " ) ";

	if ((rand() % 3) == 0)
		cout << "op" << count << " ";
	else
		cout << "bv" << result << "[" << width << "]";

	cout << ")" << endl;
}

void testSolver(void)
{
	cout << "(" << endl;
	cout << "benchmark blah" << endl;
	cout << ":logic QF_BV" << endl;
	cout << ":source {automatically generated}" << endl;
	cout << ":status sat" << endl;

	uns a, b;
	sig aS, bS;

	do
	{
		a = rand();
		b = rand();
		aS = rand();
		bS = rand();
	} while (bS == 0 || b == 0);

	switch (rand() % 6)
	{
		case 0:
			go(0, a, b, getUnsignedResult(a, BVMULT, b), "bvmul");
			break;
		case 1:
			go(1, a, b, getUnsignedResult(a, BVDIV, b), "bvudiv");
			break;
		case 2:
			go(2, a, b, getUnsignedResult(a, BVMOD, b), "bvurem");
			break;
		case 3:
			go(3, aS, bS, getSignedResult(aS, SBVDIV, bS), "bvsdiv");
			break;
		case 4:
			go(4, aS, bS, getSignedResult(aS, SBVREM, bS), "bvsrem");
			break;
		case 5:
			go(5, aS, bS, getSignedResult(aS, SBVMOD, bS), "bvsmod");
			break;

	}
	cout << ")" << endl;
}

int main(int argc, char**argv)
{
	int nonce;
	if (argc >= 2)
		nonce = atoi(argv[1]);
	else
		nonce = 1;
	int seed = time(0) * nonce;
	if (debug)
	{
		cerr << "Seed = " << seed << endl;
	}
	srand(seed);

	BitVector_Boot();

	if (false)
	{
		testConstEval(SBVMOD);
		testConstEval(SBVREM);
		testConstEval(SBVDIV);
	}
	testSolver();

	return 0;
}

