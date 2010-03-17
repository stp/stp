/********************************************************************
 * AUTHORS: Trevor Hansen, Vijay Ganesh
 *
 * BEGIN DATE: July, 2009
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
// -*- c++ -*-

#include "printers.h"
#include <cassert>
#include <cctype>

// Outputs in the SMTLIB format. If you want something that can be parsed by other tools call
// SMTLIB_PrintBack(). SMTLIB_Print() prints just an expression.
// Wierdly is seems that only terms, not formulas can be LETized.

namespace printer
{

  using std::string;
  using namespace BEEV;

  string functionToSMTLIBName(const BEEV::Kind k);
  void SMTLIB_Print1(ostream& os, const BEEV::ASTNode n, int indentation,	bool letize);
  void printVarDeclsToStream(ASTNodeSet& symbols, ostream& os);


  static string tolower(const char * name)
  {
    string s(name);
    for (size_t i = 0; i < s.size(); ++i)
      s[i] = ::tolower(s[i]);
    return s;
  }
  
//Map from ASTNodes to LetVars
ASTNodeMap NodeLetVarMap;

//This is a vector which stores the Node to LetVars pairs. It
//allows for sorted printing, as opposed to NodeLetVarMap
std::vector<pair<ASTNode, ASTNode> > NodeLetVarVec;

//a partial Map from ASTNodes to LetVars. Needed in order to
//correctly print shared subterms inside the LET itself
ASTNodeMap NodeLetVarMap1;

  // Initial version intended to print the whole thing back.
void SMTLIB_PrintBack(ostream &os, const ASTNode& n)
{
    os << "(" << endl;
    os << "benchmark blah" << endl;
	os << ":logic QF_AUFBV" << endl;
	ASTNodeSet visited, symbols;
	buildListOfSymbols(n, visited, symbols);
	printVarDeclsToStream(symbols, os);
	os << ":formula ";
    SMTLIB_Print(os, n, 0);
    os << ")" << endl;
  }

void printVarDeclsToStream(ASTNodeSet& symbols, ostream& os)
{
	for (ASTNodeSet::const_iterator i = symbols.begin(), iend = symbols.end(); i
			!= iend; i++)
	{
      const BEEV::ASTNode& a = *i;

      // Should be a symbol.
      assert(a.GetKind()== SYMBOL);

		switch (a.GetType())
		{
      case BEEV::BITVECTOR_TYPE:

        os << ":extrafuns (( ";
        a.nodeprint(os);
        os << " BitVec[" << a.GetValueWidth() << "]";
        os << " ))" << endl;
        break;
      case BEEV::ARRAY_TYPE:
        os << ":extrafuns (( ";
        a.nodeprint(os);
        os << " Array[" << a.GetIndexWidth();
        os << ":" << a.GetValueWidth() << "] ))" << endl;
        break;
      case BEEV::BOOLEAN_TYPE:
        os << ":extrapreds (( ";
        a.nodeprint(os);
        os << "))" << endl;
        break;
      default:
        BEEV::FatalError("printVarDeclsToStream: Unsupported type",a);
        break;
      }
    }
  } //printVarDeclsToStream

  void outputBitVec(const ASTNode n, ostream& os)
  {
	const Kind k = n.GetKind();
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
	CBV unsign = CONSTANTBV::BitVector_Concat(
			n.GetSTPMgr()->CreateZeroConst(1).GetBVConst(), op.GetBVConst());
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
    //this is to print letvars for shared subterms inside the printing
    //of "(LET v0 = term1, v1=term1@term2,...
	if ((NodeLetVarMap1.find(n) != NodeLetVarMap1.end()) && !letize)
      {
		SMTLIB_Print1(os, (NodeLetVarMap1[n]), indentation, letize);
        return;
      }

    //this is to print letvars for shared subterms inside the actual
    //term to be printed
	if ((NodeLetVarMap.find(n) != NodeLetVarMap.end()) && letize)
      {
		SMTLIB_Print1(os, (NodeLetVarMap[n]), indentation, letize);
        return;
      }

    //otherwise print it normally
	const Kind kind = n.GetKind();
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
      case NAND: // No NAND, NOR in smtlib format.
      case NOR:
    	  assert(c.size() ==2);
    	  os << "(" << "not ";
    	  if (NAND == kind )
    		  os << "(" << "and ";
    	  else
    		  os << "(" << "or ";
    	  SMTLIB_Print1(os, c[0], 0, letize);
    	  os << " " ;
    	  SMTLIB_Print1(os, c[1], 0, letize);
    	  os << "))";
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

		os << (amount - c[0].GetValueWidth()) << "]";
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
  		// SMT-LIB only allows these functions to have two parameters.
  		if ((BVPLUS == kind || kind == BVOR || kind == BVAND)  && n.Degree() > 2)
  		{
  			string close = "";

  			for (int i =0; i < c.size()-1; i++)
  			{
  				os << "(" << functionToSMTLIBName(kind);
  				os << " ";
  				SMTLIB_Print1(os, c[i], 0, letize);
  				os << " ";
  				close += ")";
  			}
  			SMTLIB_Print1(os, c[c.size()-1], 0, letize);
  			os << close;
  		}
  		else
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
  }

void LetizeNode(const ASTNode& n, ASTNodeSet& PLPrintNodeSet)
{
	const Kind kind = n.GetKind();

	if (kind == SYMBOL || kind == BVCONST || kind == FALSE || kind == TRUE)
		return;

	const ASTVec &c = n.GetChildren();
	for (ASTVec::const_iterator it = c.begin(), itend = c.end(); it != itend; it++)
	{
		const ASTNode& ccc = *it;

		const Kind k = ccc.GetKind();
		if (k == SYMBOL || k == BVCONST || k == FALSE || k == TRUE)
			continue;

		if (PLPrintNodeSet.find(ccc) == PLPrintNodeSet.end())
		{
			//If branch: if *it is not in NodeSet then,
			//
			//1. add it to NodeSet
			//
			//2. Letize its childNodes
			PLPrintNodeSet.insert(ccc);
			LetizeNode(ccc, PLPrintNodeSet);
		}
		else
		{
			//0. Else branch: Node has been seen before
			//
			//1. Check if the node has a corresponding letvar in the
			//1. NodeLetVarMap.
			//
			//2. if no, then create a new var and add it to the
			//2. NodeLetVarMap
			if (ccc.GetType() == BITVECTOR_TYPE && NodeLetVarMap.find(ccc)
					== NodeLetVarMap.end())
			{
				//Create a new symbol. Get some name. if it conflicts with a
				//declared name, too bad.
				int sz = NodeLetVarMap.size();
				ostringstream oss;
				oss << "?let_k_" << sz;

				ASTNode CurrentSymbol = n.GetSTPMgr()->CreateSymbol(
						oss.str().c_str());
				CurrentSymbol.SetValueWidth(n.GetValueWidth());
				CurrentSymbol.SetIndexWidth(n.GetIndexWidth());
				/* If for some reason the variable being created here is
				 * already declared by the user then the printed output will
				 * not be a legal input to the system. too bad. I refuse to
				 * check for this.  [Vijay is the author of this comment.]
				 */

				NodeLetVarMap[ccc] = CurrentSymbol;
				std::pair<ASTNode, ASTNode>
						node_letvar_pair(CurrentSymbol, ccc);
				NodeLetVarVec.push_back(node_letvar_pair);
			}
		}
	}
} //end of LetizeNode()

  // copied from Presentation Langauge printer.
  ostream& SMTLIB_Print(ostream &os, const ASTNode n, const int indentation)
  {
    // Clear the maps
	NodeLetVarMap.clear();
	NodeLetVarVec.clear();
	NodeLetVarMap1.clear();

    //pass 1: letize the node
	{
		ASTNodeSet PLPrintNodeSet;
		LetizeNode(n, PLPrintNodeSet);
	}

    //pass 2:
    //
    //2. print all the let variables and their counterpart expressions
    //2. as follows (LET var1 = expr1, var2 = expr2, ...
    //
    //3. Then print the Node itself, replacing every occurence of
    //3. expr1 with var1, expr2 with var2, ...
    //os << "(";
	if (0 < NodeLetVarMap.size())
      {
		std::vector<pair<ASTNode, ASTNode> >::iterator it =
				NodeLetVarVec.begin();
		const std::vector<pair<ASTNode, ASTNode> >::iterator itend =
				NodeLetVarVec.end();

		os << "(let (";
        //print the let var first
        SMTLIB_Print1(os, it->first, indentation, false);
		os << " ";
        //print the expr
        SMTLIB_Print1(os, it->second, indentation, false);
		os << " )";

        //update the second map for proper printing of LET
		NodeLetVarMap1[it->second] = it->first;

		string closing = "";
        for (it++; it != itend; it++)
          {
			os << " " << endl;
			os << "(let (";
            //print the let var first
            SMTLIB_Print1(os, it->first, indentation, false);
			os << " ";
            //print the expr
            SMTLIB_Print1(os, it->second, indentation, false);
			os << ")";
            //update the second map for proper printing of LET
			NodeLetVarMap1[it->second] = it->first;
			closing += ")";
          }

		os << " ( " << endl;
        SMTLIB_Print1(os, n, indentation, true);
		os << closing;
		os << " ) ) ";

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
      case IMPLIES:
	{
        return tolower(_kind_names[k]);
	}

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
