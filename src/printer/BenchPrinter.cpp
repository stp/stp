#include "printers.h"
#include <string>
#include "ASTKind.h"

/*
 * Bench format  which the ABC logic synthesis tool can read.
 * No more than 2-arity seem to be accepted.
 */

namespace printer
{
using std::string;
using namespace BEEV;

string name(const Kind k)
{
	return _kind_names[k];
}

string bvconstToString(const ASTNode& n)
{
	assert (n.GetKind() == BVCONST);
	std::stringstream output;
	output << *n.GetBVConst();
	return output.str();
}

// ABC doesn't like spaces, nor brackets. in variable names.
//  TODO CHECK that this doesn't cause duplicate names
string symbolToString(const ASTNode &n)
{
	assert(n.GetKind() == SYMBOL);
	std::stringstream output;
	n.nodeprint(output);

	string result = output.str();
	replace(result.begin(), result.end(), ' ', '_');
	replace(result.begin(), result.end(), '(', '_');
	replace(result.begin(), result.end(), ')', '_');

	return result;

}

string Bench_Print1(ostream &os, const ASTNode& n, hash_set<int> *alreadyOutput)
{
	if (n.GetValueWidth() > 1 && (n.GetKind() != SYMBOL))
	{
		// some of the nodes have a width of zero (oddly), but they are probably ok.
		cerr << "width" << n.GetValueWidth();
		cerr << n;
		assert(n.GetValueWidth() == 1);
	}

	assert(!n.IsNull());

	std::stringstream output;
	if (n.GetKind() == BVCONST)
		return bvconstToString(n);

	if (n.GetKind() == SYMBOL)
		return symbolToString(n);

	if (n.GetKind() == BVGETBIT)
	{
		assert(n[1].GetKind() == BVCONST);
		std::stringstream nn;
		nn << Bench_Print1(os, n[0], alreadyOutput) << "_" << bvconstToString(
				n[1]);
		return nn.str();
	}

	std::stringstream thisNode;
	thisNode << "n" << n.GetNodeNum();

	if (alreadyOutput->find(n.GetNodeNum()) != alreadyOutput->end())
		return thisNode.str();

	alreadyOutput->insert(n.GetNodeNum());

	assert(n.Degree() > 0);

	// The bench format doesn't accept propositional ITEs.
	if (n.GetKind() == ITE)
	{
		assert(n.Degree() == 3);
		string p = Bench_Print1(os, n[0], alreadyOutput);
		string p1 = Bench_Print1(os, n[1], alreadyOutput);
		string p2 = Bench_Print1(os, n[2], alreadyOutput);

		os << thisNode.str() << "_1 = AND(" << p << "," << p1 << ")" << endl;
		os << thisNode.str() << "_2" << " = NOT(" << p << ")," << endl;
		os << thisNode.str() << "_3" << " = AND(" << thisNode.str() << "_2"
				<< "," << p2 << ")" << endl;
		os << thisNode.str() << "=" << "OR(," << thisNode.str() << "_1" << ","
				<< thisNode.str() << "_3)" << endl;
	}
	else
	{
		if (n.Degree() > 2)
		{
			if(n.GetKind() != AND && n.GetKind() != XOR && n.GetKind() != OR) // must be associative.
			{
				cerr << name(n.GetKind());
			}

			output << thisNode.str() << "_1" <<  "=" << name(n.GetKind()) << "(" << Bench_Print1(os, n[0], alreadyOutput)
					<< "," << Bench_Print1(os, n[1], alreadyOutput) << ")" << endl;


			for (unsigned i = 2; i < n.Degree()-1/*note minus one.*/; i++)
			{
				output << thisNode.str() << "_" << i << "=" << name(n.GetKind()) << "(" << Bench_Print1(os, n[i], alreadyOutput)
						<< "," << thisNode.str() << "_" << (i-1) << ")" << endl;
			}

			output << thisNode.str() << "=" << name(n.GetKind()) << "(" << Bench_Print1(os, n[n.Degree()-1], alreadyOutput)
				    << "," << thisNode.str() << "_" << (n.Degree()-2) << ")" << endl;

			os << output.str();
		}
		else
		{
			output << thisNode.str() << "=" << name(n.GetKind()) << "(";
			for (unsigned i = 0; i < n.Degree(); i++)
			{
				if (i >= 1)
					output << " , ";
				output << Bench_Print1(os, n[i], alreadyOutput);

			}
			os << output.str() << ")" << endl;
		}
	}
	return thisNode.str();
}

void OutputInputs(ostream &os, const ASTNode& n, hash_set<int> *alreadyOutput)
{
	if (alreadyOutput->find(n.GetNodeNum()) != alreadyOutput->end())
		return;

	alreadyOutput->insert(n.GetNodeNum());

	if (n.GetKind() == BVGETBIT)
	{
		assert(n[1].GetKind() == BVCONST);
		std::stringstream nn;
		n[0].nodeprint(nn);
		nn << "_" << bvconstToString(n[1]);
		os << "INPUT(" << nn.str() << ")" << endl;
		return;
	}

	// A boolean symbol.
	if (n.GetKind() == SYMBOL)
	{
		os << "INPUT(" << symbolToString(n) << ")" << endl;
		return;
	}

	for (unsigned i = 0; i < n.Degree(); i++)
	{
		OutputInputs(os, n[i], alreadyOutput);
	}
}

ostream& Bench_Print(ostream &os, const ASTNode n)
{
	hash_set<int> alreadyOutput;

	OutputInputs(os, n, &alreadyOutput);
	alreadyOutput.clear();

	os << "OUTPUT(" << "n" << n.GetNodeNum() << ")" << endl;
	string top = Bench_Print1(os, n, &alreadyOutput);
	return os;
}
}
;
