#include "printers.h"

namespace printer
{

using std::string;
using namespace BEEV;

string functionToSMTLIBName(const BEEV::Kind k);
void SMTLIB_Print1(ostream& os, const BEEV::ASTNode n, int indentation, bool letize);

void outputBitVec(const ASTNode n, ostream& os)
{
	Kind k = n.GetKind();
	const ASTVec &c = n.GetChildren();
	ASTNode op;

	if (BITVECTOR == k)
	{
		op = c[0];
	}
	else if (BVCONST == k)
	{
		op = n;
	}
	else
		FatalError("nsadfsdaf");

	// CONSTANTBV::BitVector_to_Dec returns a signed representation by default.
	// Prepend with zero to convert to unsigned.

	os << "bv";
	CBV unsign = CONSTANTBV::BitVector_Concat(n.GetBeevMgr().CreateZeroConst(1).GetBVConst(), op.GetBVConst());
	unsigned char * str = CONSTANTBV::BitVector_to_Dec(unsign);
	CONSTANTBV::BitVector_Destroy(unsign);
	os << str << "[" << op.GetValueWidth() << "]";
	CONSTANTBV::BitVector_Dispose(str);
}

void SMTLIB_Print1(ostream& os, const ASTNode n, int indentation, bool letize)
{
	//os << spaces(indentation);
	//os << endl << spaces(indentation);
	if (!n.IsDefined())
	{
		os << "<undefined>";
		return;
	}

	//if this node is present in the letvar Map, then print the letvar
	BeevMgr &bm = n.GetBeevMgr();

	//this is to print letvars for shared subterms inside the printing
	//of "(LET v0 = term1, v1=term1@term2,...
	if ((bm.NodeLetVarMap1.find(n) != bm.NodeLetVarMap1.end()) && !letize)
	{
		SMTLIB_Print1(os, (bm.NodeLetVarMap1[n]), indentation, letize);
		return;
	}

	//this is to print letvars for shared subterms inside the actual
	//term to be printed
	if ((bm.NodeLetVarMap.find(n) != bm.NodeLetVarMap.end()) && letize)
	{
		SMTLIB_Print1(os, (bm.NodeLetVarMap[n]), indentation, letize);
		return;
	}

	//otherwise print it normally
	Kind kind = n.GetKind();
	const ASTVec &c = n.GetChildren();
	switch (kind)
	{
		case BITVECTOR:
		case BVCONST:
			outputBitVec(n, os);
			break;

		case SYMBOL:
			n.nodeprint(os);
			break;
		case FALSE:
			os << "false";
			break;
		case TRUE:
			os << "true";
			break;

		case BVSX:
		case BVZX:
		{
			unsigned int amount = GetUnsignedConst(c[1]);
			if (BVZX == kind)
				os << "(zero_extend[";
			else
				os << "(sign_extend[";

			os << amount << "]";
			SMTLIB_Print1(os, c[0], indentation, letize);
			os << ")";
		}
			break;
		case BVEXTRACT:
		{
			unsigned int upper = GetUnsignedConst(c[1]);
			unsigned int lower = GetUnsignedConst(c[2]);
			assert(upper >= lower);
			os << "(extract[" << upper << ":" << lower << "] ";
			SMTLIB_Print1(os, c[0], indentation, letize);
			os << ")";
		}
			break;
		default:
		{
			os << "(" << functionToSMTLIBName(kind);

			ASTVec::const_iterator iend = c.end();
			for (ASTVec::const_iterator i = c.begin(); i != iend; i++)
			{
				os << " ";
				SMTLIB_Print1(os, *i, 0, letize);
			}

			os << ")";
		}
	}
}

// copied from Presentation Langauge printer.
ostream& SMTLIB_Print(ostream &os, const ASTNode n, const int indentation)
{
	// Clear the PrintMap
	BeevMgr& bm = n.GetBeevMgr();
	bm.PLPrintNodeSet.clear();
	bm.NodeLetVarMap.clear();
	bm.NodeLetVarVec.clear();
	bm.NodeLetVarMap1.clear();

	//pass 1: letize the node
	n.LetizeNode();

	//pass 2:
	//
	//2. print all the let variables and their counterpart expressions
	//2. as follows (LET var1 = expr1, var2 = expr2, ...
	//
	//3. Then print the Node itself, replacing every occurence of
	//3. expr1 with var1, expr2 with var2, ...
	//os << "(";
	if (0 < bm.NodeLetVarMap.size())
	{
		//ASTNodeMap::iterator it=bm.NodeLetVarMap.begin();
		//ASTNodeMap::iterator itend=bm.NodeLetVarMap.end();
		std::vector<pair<ASTNode, ASTNode> >::iterator it = bm.NodeLetVarVec.begin();
		std::vector<pair<ASTNode, ASTNode> >::iterator itend = bm.NodeLetVarVec.end();

		os << "(LET ";
		//print the let var first
		SMTLIB_Print1(os, it->first, indentation, false);
		os << " = ";
		//print the expr
		SMTLIB_Print1(os, it->second, indentation, false);

		//update the second map for proper printing of LET
		bm.NodeLetVarMap1[it->second] = it->first;

		for (it++; it != itend; it++)
		{
			os << "," << endl;
			//print the let var first
			SMTLIB_Print1(os, it->first, indentation, false);
			os << " = ";
			//print the expr
			SMTLIB_Print1(os, it->second, indentation, false);

			//update the second map for proper printing of LET
			bm.NodeLetVarMap1[it->second] = it->first;
		}

		os << " IN " << endl;
		SMTLIB_Print1(os, n, indentation, true);
		os << ") ";
	}
	else
		SMTLIB_Print1(os, n, indentation, false);

	os << endl;
	return os;
}

string functionToSMTLIBName(const Kind k)
{
	switch (k)
	{
		case AND:
		case BVAND:
		case BVNAND:
		case BVNOR:
		case BVOR:
		case BVSGE:
		case BVSGT:
		case BVSLE:
		case BVSLT:
		case BVSUB:
		case BVXOR:
		case ITE:
		case NAND:
		case NOR:
		case NOT:
		case OR:
		case XOR:
		case IFF:
			return _kind_names[k];

		case BVCONCAT:
			return "concat";
		case BVDIV:
			return "bvudiv";
		case BVGT:
			return "bvugt";
		case BVGE:
			return "bvuge";
		case BVLE:
			return "bvule";
		case BVLEFTSHIFT:
			return "bvshl";
		case BVLT:
			return "bvult";
		case BVMOD:
			return "bvurem";
		case BVMULT:
			return "bvmul";
		case BVNEG:
			return "bvnot"; // CONFUSSSSINNG. (1/2)
		case BVPLUS:
			return "bvadd";
		case BVRIGHTSHIFT:
			return "bvlshr"; // logical
		case BVSRSHIFT:
			return "bvashr"; // arithmetic.
		case BVUMINUS:
			return "bvneg"; // CONFUSSSSINNG. (2/2)
		case EQ:
			return "=";
		case READ:
			return "select";
		case WRITE:
			return "store";
		case SBVDIV:
			return "bvsdiv";
		case SBVREM:
			return "bvsrem";

		default:
		{
			cerr << "Unknown name when outputting:";
			FatalError(_kind_names[k]);
			return ""; // to quieten compiler/
		}
	}
}

}
