/********************************************************************
 * AUTHORS: Trevor Hansen, Vijay Ganesh
 *
 * BEGIN DATE: July, 2009
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
 * OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 ********************************************************************/
// -*- c++ -*-

#include "stp/Printer/printers.h"
#include <cassert>
#include <cctype>
#include "stp/Printer/SMTLIBPrinter.h"

// Outputs in the SMTLIB format. If you want something that can be parsed by other tools call
// SMTLIB_PrintBack(). SMTLIB_Print() prints just an expression.

namespace printer
{

  using std::string;
  using namespace BEEV;

  void SMTLIB2_Print1(ostream& os, const BEEV::ASTNode n, int indentation,	bool letize);
  void printVarDeclsToStream(ASTNodeSet& symbols, ostream& os);

void SMTLIB2_PrintBack(ostream &os, const ASTNode& n, const bool definately_bv)
{
	if (!definately_bv && containsArrayOps(n))
		os << "(set-logic QF_ABV)\n";
	else
		os << "(set-logic QF_BV)\n";

	os << "(set-info :smt-lib-version 2.0)\n";


	if (input_status == TO_BE_SATISFIABLE) {
		os << "(set-info :status sat)\n";
	}
	else if (input_status == TO_BE_UNSATISFIABLE) {
		os << "(set-info :status unsat)\n";
	} else
		os << "(set-info :status unknown)\n";

	ASTNodeSet visited, symbols;
	buildListOfSymbols(n, visited, symbols);
	printVarDeclsToStream(symbols, os);
	os << "(assert ";
    SMTLIB_Print(os, n, 0, &SMTLIB2_Print1, false);
    os << ")\n";
    // os << "(check-sat)" << endl;
    // os << "(exit)\n";
  }

void printVarDeclsToStream(ASTNodeSet& symbols, ostream& os)
{
	for (ASTNodeSet::const_iterator i = symbols.begin(), iend = symbols.end(); i
			!= iend; i++)
	{
      const BEEV::ASTNode& a = *i;
      os << "(declare-fun ";

      // Should be a symbol.
      assert(a.GetKind()== SYMBOL);
      os << "|";
      a.nodeprint(os);
      os << "|";

		switch (a.GetType())
		{
      case BEEV::BITVECTOR_TYPE:
    	  os << " () (";
    	  os << "_ BitVec " << a.GetValueWidth() << ")";

        break;
      case BEEV::ARRAY_TYPE:
    	  os << " () (";
    	  os << "Array (_ BitVec " << a.GetIndexWidth()  << ") (_ BitVec " << a.GetValueWidth() << ") )";
        break;
      case BEEV::BOOLEAN_TYPE:
        os << " () Bool ";
        break;
      default:
        BEEV::FatalError("printVarDeclsToStream: Unsupported type",a);
        break;
      }
  	  os << ")\n";
    }
  } //printVarDeclsToStream

  void outputBitVecSMTLIB2(const ASTNode n, ostream& os)
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

    os << "(_ bv";
	CBV unsign = CONSTANTBV::BitVector_Concat(
			n.GetSTPMgr()->CreateZeroConst(1).GetBVConst(), op.GetBVConst());
    unsigned char * str = CONSTANTBV::BitVector_to_Dec(unsign);
    CONSTANTBV::BitVector_Destroy(unsign);
    os << str << " " << op.GetValueWidth() << ")";
    CONSTANTBV::BitVector_Dispose(str);
  }

  void SMTLIB2_Print1(ostream& os, const ASTNode n, int indentation, bool letize)
  {
    //os << spaces(indentation);
    //os << endl << spaces(indentation);
    if (!n.IsDefined())
      {
        FatalError("<undefined>");
        return;
      }

    //if this node is present in the letvar Map, then print the letvar
    //this is to print letvars for shared subterms inside the printing
    //of "(LET v0 = term1, v1=term1@term2,...
	if ((NodeLetVarMap1.find(n) != NodeLetVarMap1.end()) && !letize)
      {
		SMTLIB2_Print1(os, (NodeLetVarMap1[n]), indentation, letize);
        return;
      }

    //this is to print letvars for shared subterms inside the actual
    //term to be printed
	if ((NodeLetVarMap.find(n) != NodeLetVarMap.end()) && letize)
      {
		SMTLIB2_Print1(os, (NodeLetVarMap[n]), indentation, letize);
        return;
      }

    //otherwise print it normally
	const Kind kind = n.GetKind();
    const ASTVec &c = n.GetChildren();
    switch (kind)
      {
      case BITVECTOR:
      case BVCONST:
    	  outputBitVecSMTLIB2(n, os);
        break;
      case SYMBOL:
        os << "|";
        n.nodeprint(os);
        os << "|";
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
    	  SMTLIB2_Print1(os, c[0], 0, letize);
    	  os << " " ;
    	  SMTLIB2_Print1(os, c[1], 0, letize);
    	  os << "))";
    	  break;
      case TRUE:
        os << "true";
        break;
      case BVSX:
      case BVZX:
        {
          unsigned int amount = c[1].GetUnsignedConst();
          if (BVZX == kind)
            os << "((_ zero_extend ";
          else
            os << "((_ sign_extend ";

          os << (amount - c[0].GetValueWidth()) << ") ";
          SMTLIB2_Print1(os, c[0], indentation, letize);
          os << ")";
        }
        break;
      case BVEXTRACT:
        {
          unsigned int upper = c[1].GetUnsignedConst();
          unsigned int lower = c[2].GetUnsignedConst();
          assert(upper >= lower);
          os << "((_ extract " << upper << " " << lower << ") ";
          SMTLIB2_Print1(os, c[0], indentation, letize);
          os << ")";
        }
        break;
  	default:
  	{
  	    if ((kind == AND  || kind == OR|| kind == XOR) && n.Degree() == 1)
  	    {
  	    	FatalError("Wrong number of arguments to operation (must be >1).", n);
  	    }

  		// SMT-LIB only allows these functions to have two parameters.
  		if ((kind == AND  || kind == OR|| kind == XOR || BVPLUS == kind || kind == BVOR || kind == BVAND)  && n.Degree() > 2)
  		{
  			string close = "";

  			for (long int i =0; i < (long int)c.size()-1; i++)
  			{
  				os << "(" << functionToSMTLIBName(kind,false);
  				os << " ";
  				SMTLIB2_Print1(os, c[i], 0, letize);
  				os << " ";
  				close += ")";
  			}
  			SMTLIB2_Print1(os, c[c.size()-1], 0, letize);
  			os << close;
  		}
  		else
  		{
  			os << "(" << functionToSMTLIBName(kind,false);

  			ASTVec::const_iterator iend = c.end();
  			for (ASTVec::const_iterator i = c.begin(); i != iend; i++)
  			{
  				os << " ";
  				SMTLIB2_Print1(os, *i, 0, letize);
  			}

  			os << ")";
  		}
  	}
      }
  }
}
