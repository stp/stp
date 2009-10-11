// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include "printers.h"

namespace printer
{

  using std::string;
  using namespace BEEV;

  void PL_Print1(ostream& os, const ASTNode& n,int indentation, bool letize)
  {
    //os << spaces(indentation);
    //os << endl << spaces(indentation);
    if (!n.IsDefined())
      {
        os << "<undefined>";
        return;
      }

    //if this node is present in the letvar Map, then print the letvar
    STPMgr *bm = n.GetSTPMgr();

    //this is to print letvars for shared subterms inside the printing
    //of "(LET v0 = term1, v1=term1@term2,...
    if ((bm->NodeLetVarMap1.find(n) != bm->NodeLetVarMap1.end()) && !letize)
      {
        PL_Print1(os, (bm->NodeLetVarMap1[n]), indentation, letize);
        return;
      }

    //this is to print letvars for shared subterms inside the actual
    //term to be printed
    if ((bm->NodeLetVarMap.find(n) != bm->NodeLetVarMap.end()) && letize)
      {
        PL_Print1(os, (bm->NodeLetVarMap[n]), indentation, letize);
        return;
      }

    //otherwise print it normally
    Kind kind = n.GetKind();
    const ASTVec &c = n.GetChildren();
    switch (kind)
      {
      case BVGETBIT:
        PL_Print1(os, c[0], indentation, letize);
        os << "{";
        PL_Print1(os, c[1],indentation, letize);
        os << "}";
        break;
      case BITVECTOR:
        os << "BITVECTOR(";
        unsigned char * str;
        str = CONSTANTBV::BitVector_to_Hex(c[0].GetBVConst());
        os << str << ")";
        CONSTANTBV::BitVector_Dispose(str);
        break;
      case BOOLEAN:
        os << "BOOLEAN";
        break;
      case FALSE:
      case TRUE:
        os << kind;
        break;
      case BVCONST:
      case SYMBOL:
        n.nodeprint(os, true);
        break;
      case READ:
        PL_Print1(os, c[0], indentation, letize);
        os << "[";
        PL_Print1(os, c[1], indentation, letize);
        os << "]";
        break;
      case WRITE:
        os << "(";
        PL_Print1(os, c[0], indentation, letize);
        os << " WITH [";
        PL_Print1(os, c[1], indentation, letize);
        os << "] := ";
        PL_Print1(os, c[2], indentation, letize);
        os << ")";
        os << endl;
        break;
      case BVUMINUS:
        os << kind << "( ";
        PL_Print1(os, c[0], indentation, letize);
        os << ")";
        break;
      case NOT:
        os << "NOT(";
        PL_Print1(os, c[0], indentation, letize);
        os << ") " << endl;
        break;
      case BVNEG:
        os << " ~(";
        PL_Print1(os, c[0], indentation, letize);
        os << ")";
        break;
      case BVCONCAT:
        os << "(";
        PL_Print1(os, c[0], indentation, letize);
        os << " @ ";
        PL_Print1(os, c[1], indentation, letize);
        os << ")" << endl;
        break;
      case BVOR:
        os << "(";
        PL_Print1(os, c[0], indentation, letize);
        os << " | ";
        PL_Print1(os, c[1], indentation, letize);
        os << ")";
        break;
      case BVAND:
        os << "(";
        PL_Print1(os, c[0], indentation, letize);
        os << " & ";
        PL_Print1(os, c[1], indentation, letize);
        os << ")";
        break;
      case BVEXTRACT:
        PL_Print1(os, c[0], indentation, letize);
        os << "[";
        os << GetUnsignedConst(c[1]);
        os << ":";
        os << GetUnsignedConst(c[2]);
        os << "]";
        break;
      case BVLEFTSHIFT:
        os << "(";
        PL_Print1(os, c[0], indentation, letize);
        os << " << ";
        os << GetUnsignedConst(c[1]);
        os << ")";
        break;
      case BVRIGHTSHIFT:
        os << "(";
        PL_Print1(os, c[0], indentation, letize);
        os << " >> ";
        os << GetUnsignedConst(c[1]);
        os << ")";
        break;
      case BVMULT:
      case BVSUB:
      case BVPLUS:
      case SBVDIV:
      case SBVREM:
      case BVDIV:
      case BVMOD:
        os << kind << "(";
        os << n.GetValueWidth();
        for (ASTVec::const_iterator it = c.begin(), itend = c.end(); it != itend; it++)
          {
            os << ", " << endl;
            PL_Print1(os, *it, indentation, letize);
          }
        os << ")" << endl;
        break;
      case ITE:
        os << "IF(";
        PL_Print1(os, c[0], indentation, letize);
        os << ")" << endl;
        os << "THEN ";
        PL_Print1(os, c[1], indentation, letize);
        os << endl << "ELSE ";
        PL_Print1(os, c[2], indentation, letize);
        os << endl << "ENDIF";
        break;
      case PARAMBOOL:
	PL_Print1(os, c[0], indentation, letize);
	os << "(";
	PL_Print1(os, c[1], indentation, letize);
	os << ")";
	break;
      case FOR:
	// if(expand_finitefor_flag) 
	// 	  {
	// 	    ASTNode expandedfor = bm->Expand_FiniteLoop_TopLevel(n);
	// 	    PL_Print1(os, expandedfor, indentation, letize);
	// 	  }
	// 	else 
	  {
	    os << "FOR(";
	    PL_Print1(os, c[0], indentation, letize);
	    os << ";";
	    PL_Print1(os, c[1], indentation, letize);
	    os << ";";
	    PL_Print1(os, c[2], indentation, letize);
	    os << ";";
	    PL_Print1(os, c[3], indentation, letize);
	    os << ";";
	    os << "EXCEPT ";
	    PL_Print1(os, c[4], indentation, letize);
	    os << "){ \n";
	    PL_Print1(os, c[5], indentation, letize);
	    os << "} \n";
	  }
	break;
      case BVLT:
      case BVLE:
      case BVGT:
      case BVGE:
      case BVXOR:
      case BVNAND:
      case BVNOR:
      case BVXNOR:
        os << kind << "(";
        PL_Print1(os, c[0], indentation, letize);
        os << ",";
        PL_Print1(os, c[1], indentation, letize);
        os << ")" << endl;
        break;
      case BVSLT:
        os << "SBVLT" << "(";
        PL_Print1(os, c[0], indentation, letize);
        os << ",";
        PL_Print1(os, c[1], indentation, letize);
        os << ")" << endl;
        break;
      case BVSLE:
        os << "SBVLE" << "(";
        PL_Print1(os, c[0], indentation, letize);
        os << ",";
        PL_Print1(os, c[1], indentation, letize);
        os << ")" << endl;
        break;
      case BVSGT:
        os << "SBVGT" << "(";
        PL_Print1(os, c[0], indentation, letize);
        os << ",";
        PL_Print1(os, c[1], indentation, letize);
        os << ")" << endl;
        break;
      case BVSGE:
        os << "SBVGE" << "(";
        PL_Print1(os, c[0], indentation, letize);
        os << ",";
        PL_Print1(os, c[1], indentation, letize);
        os << ")" << endl;
        break;
      case EQ:
        PL_Print1(os,c[0], indentation, letize);
        os << " = ";
        PL_Print1(os, c[1], indentation, letize);
        os << endl;
        break;
      case AND:
      case OR:
      case NAND:
      case NOR:
      case XOR:
        {
          os << "(";
          PL_Print1(os, c[0], indentation, letize);
          ASTVec::const_iterator it = c.begin();
          ASTVec::const_iterator itend = c.end();

          it++;
          for (; it != itend; it++)
            {
              os << " " << kind << " ";
              PL_Print1(os, *it, indentation, letize);
              os << endl;
            }
          os << ")";
          break;
        }
      case IFF:
        os << "(";
        os << "(";
        PL_Print1(os, c[0], indentation, letize);
        os << ")";
        os << " <=> ";
        os << "(";
        PL_Print1(os,c[1], indentation, letize);
        os << ")";
        os << ")";
        os << endl;
        break;
      case IMPLIES:
        os << "(";
        os << "(";
        PL_Print1(os, c[0], indentation, letize);
        os << ")";
        os << " => ";
        os << "(";
        PL_Print1(os, c[1], indentation, letize);
        os << ")";
        os << ")";
        os << endl;
        break;
      case BVSX:
      case BVZX:
        os << kind << "(";
        PL_Print1(os, c[0], indentation, letize);
        os << ",";
        os << n.GetValueWidth();
        os << ")" << endl;
        break;
      default:
        //remember to use LispPrinter here. Otherwise this function will
        //go into an infinite loop. Recall that "<<" is overloaded to
        //the lisp printer. FatalError uses lispprinter
        FatalError("PL_Print1: printing not implemented for this kind: ", n);
        break;
      }
  } //end of PL_Print1()


  //print in PRESENTATION LANGUAGE
  //
  //two pass algorithm:
  //
  //1. In the first pass, letize this Node, N: i.e. if a node
  //1. appears more than once in N, then record this fact.
  //
  //2. In the second pass print a "global let" and then print N
  //2. as follows: Every occurence of a node occuring more than
  //2. once is replaced with the corresponding let variable.
  ostream& PL_Print(ostream &os,  const ASTNode& n, int indentation)
  {
    // Clear the PrintMap
    STPMgr* bm = n.GetSTPMgr();
    bm->PLPrintNodeSet.clear();
    bm->NodeLetVarMap.clear();
    bm->NodeLetVarVec.clear();
    bm->NodeLetVarMap1.clear();

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
    if (0 < bm->NodeLetVarMap.size())
      {
        //ASTNodeMap::iterator it=bm->NodeLetVarMap.begin();
        //ASTNodeMap::iterator itend=bm->NodeLetVarMap.end();
        std::vector<pair<ASTNode, ASTNode> >::iterator it = bm->NodeLetVarVec.begin();
        std::vector<pair<ASTNode, ASTNode> >::iterator itend = bm->NodeLetVarVec.end();

        os << "(LET ";
        //print the let var first
        PL_Print1(os, it->first, indentation, false);
        os << " = ";
        //print the expr
        PL_Print1(os, it->second, indentation, false);

        //update the second map for proper printing of LET
        bm->NodeLetVarMap1[it->second] = it->first;

        for (it++; it != itend; it++)
          {
            os << "," << endl;
            //print the let var first
            PL_Print1(os, it->first, indentation, false);
            os << " = ";
            //print the expr
            PL_Print1(os, it->second, indentation, false);

            //update the second map for proper printing of LET
            bm->NodeLetVarMap1[it->second] = it->first;
          }

        os << " IN " << endl;
        PL_Print1(os, n, indentation, true);
        os << ") ";
      }
    else
      PL_Print1(os,n, indentation, false);
    //os << " )";
    os << " ";
    return os;
  } //end of PL_Print()
}
