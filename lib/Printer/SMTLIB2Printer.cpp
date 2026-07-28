/********************************************************************
 * AUTHORS: Trevor Hansen, Vijay Ganesh
 *
 * BEGIN DATE: July, 2009
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

#include "stp/FloatBlaster/rounding_modes.h"
#include "stp/Printer/SMTLIBPrinter.h"
#include "stp/Printer/printers.h"
#include <cassert>
#include <cctype>

// Outputs in the SMTLIB format. If you want something that can be parsed by
// other tools call
// SMTLIB_PrintBack(). SMTLIB_Print() prints just an expression.

namespace printer
{

using std::string;
using namespace stp;

void printVarDeclsToStream(ASTNodeSet& symbols, ostream& os);

const char* roundingModeName(unsigned encoding)
{
  using namespace stp::symbolic_fp;
  switch (encoding)
  {
    case ROUND_NEAREST_TIES_TO_EVEN:
      return "RNE";
    case ROUND_TOWARD_POSITIVE:
      return "RTP";
    case ROUND_TOWARD_NEGATIVE:
      return "RTN";
    case ROUND_TOWARD_ZERO:
      return "RTZ";
    case ROUND_NEAREST_TIES_TO_AWAY:
      return "RNA";
    default:
      return NULL; // not one-hot
  }
}

// A rounding mode in operand position: the five constants print by name;
// anything else -- a RoundingMode variable, an ite -- prints as itself.
static void printRoundingModeSMTLIB2(ostream& os, const ASTNode& rm,
                                     bool letize)
{
  if (rm.GetKind() == stp::BVCONST && rm.GetValueWidth() == 5)
  {
    if (const char* name = roundingModeName(rm.GetUnsignedConst()))
    {
      os << name;
      return;
    }
  }
  SMTLIB2_Print1(os, rm, 0, letize);
}

void SMTLIB2_PrintBack(ostream& os, const ASTNode& n, STPMgr* mgr,
                       const bool definately_bv)
{
  const bool has_arrays = !definately_bv && containsArrayOps(n, mgr);
  const bool has_fp = mgr->has_floating_point;
  if (has_fp)
    os << (has_arrays ? "(set-logic QF_ABVFP)\n" : "(set-logic QF_BVFP)\n");
  else
    os << (has_arrays ? "(set-logic QF_ABV)\n" : "(set-logic QF_BV)\n");

  os << "(set-info :smt-lib-version 2.0)\n";

  if (input_status == TO_BE_SATISFIABLE)
  {
    os << "(set-info :status sat)\n";
  }
  else if (input_status == TO_BE_UNSATISFIABLE)
  {
    os << "(set-info :status unsat)\n";
  }
  else
    os << "(set-info :status unknown)\n";

  ASTNodeSet visited, symbols;
  buildListOfSymbols(n, visited, symbols);
  printVarDeclsToStream(symbols, os);
  os << "(assert ";
  SMTLIB_Print(os, mgr, n, 0, &SMTLIB2_Print1, false);
  os << ")\n";
  // os << "(check-sat)" << endl;
  // os << "(exit)\n";
}

void printVarDeclsToStream(ASTNodeSet& symbols, ostream& os)
{
  for (ASTNodeSet::const_iterator i = symbols.begin(), iend = symbols.end();
       i != iend; i++)
  {
    const stp::ASTNode& a = *i;
    os << "(declare-fun ";

    // Should be a symbol.
    assert(a.GetKind() == SYMBOL);
    os << "|";
    a.nodeprint(os);
    os << "|";

    switch (a.GetType())
    {
      case stp::BITVECTOR_TYPE:
        os << " () (";
        os << "_ BitVec " << a.GetValueWidth() << ")";

        break;
      case stp::ARRAY_TYPE:
        os << " () (";
        os << "Array (_ BitVec " << a.GetIndexWidth() << ") ";
        // An array of floats carries the element format on the array symbol.
        if (a.GetExpWidth() != 0)
          os << "(_ FloatingPoint " << a.GetExpWidth() << " " << a.GetSigWidth()
             << ") )";
        else
          os << "(_ BitVec " << a.GetValueWidth() << ") )";
        break;
      case stp::BOOLEAN_TYPE:
        os << " () Bool ";
        break;
      case stp::FLOATINGPOINT_TYPE:
      {
        os << " () (";
        os << "_ FloatingPoint " << a.GetExpWidth() << " " << a.GetSigWidth()
           << ") ";
        break;
      }
      default:
        stp::FatalError("printVarDeclsToStream: Unsupported type", a);
        break;
    }
    os << ")\n";
  }
} // printVarDeclsToStream

void outputBitVecSMTLIB2(const ASTNode n, ostream& os)
{
  const Kind k = n.GetKind();
  const ASTChildren c = n.GetChildren();
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

  // CONSTANTBV::BitVector_to_Dec is very slow on 30,000 bits because it does lots of divisions.

  if (op.GetValueWidth() % 4 == 0)
  {
    os << " #x";
    unsigned char* str = CONSTANTBV::BitVector_to_Hex(n.GetBVConst());
    os << str;
    CONSTANTBV::BitVector_Dispose(str);
  }
  else
  {
    os << " #b";
    unsigned char* str = CONSTANTBV::BitVector_to_Bin(n.GetBVConst());
    os << str;
    CONSTANTBV::BitVector_Dispose(str);
  }
}

void outputFloatingPointSMTLIB2(const ASTNode n, ostream& os,
                                unsigned int exp_width, unsigned int sig_width)
{
  const Kind k = n.GetKind();

  if (BVCONST != k)
  {
    FatalError("Expecting BV const");
  }

  unsigned int* const_bv = n.GetBVConst();
  uint32_t underlying_size = bits_(const_bv);
  unsigned int fp_width = sig_width + exp_width;

  if (fp_width != underlying_size)
  {
    FatalError("BV does not match size of FP");
  }

  unsigned char* str = CONSTANTBV::BitVector_to_Bin(n.GetBVConst());
  std::string as_str(reinterpret_cast<char*>(str));
  CONSTANTBV::BitVector_Dispose(str);

  if (as_str.length() != underlying_size)
  {
    FatalError("String does not match size of FP");
  }

  // The stored significand field is sb - 1 bits: the hidden bit is not
  // packed. (This used to ask substr for sb characters and lean on substr's
  // clamping at end-of-string.)
  std::string sign_bit = as_str.substr(0, 1);
  std::string exp_bits = as_str.substr(1, exp_width);
  std::string sig_bits = as_str.substr(1 + exp_width, sig_width - 1);

  std::string rejoined = sign_bit + exp_bits + sig_bits;

  if (rejoined != as_str)
  {
    FatalError("Rejoined string does not match original string");
  }

  // Every NaN pattern prints as the one canonical quiet NaN -- the spelling
  // NaN constants intern to and blasted operations emit. SMT-LIB has a
  // single NaN, so the sign and payload bits carry nothing at the value
  // level; but a SAT model is free to pick any pattern for a float that is
  // only known to be NaN, and printing those bits would leak the carrier's
  // choice and make model text vary with solver internals. cvc5 and
  // bitwuzla print this same spelling.
  if (exp_bits.find('0') == std::string::npos &&
      sig_bits.find('1') != std::string::npos)
  {
    sign_bit = "0";
    sig_bits.assign(sig_bits.size(), '0');
    sig_bits[0] = '1';
  }

  os << "(fp ";
  os << "#b" << sign_bit << " ";
  os << "#b" << exp_bits << " ";
  os << "#b" << sig_bits << "";
  os << ")";
}

void outputFloatingPointSMTLIB2(const ASTNode n, ostream& os,
                                const ASTNode term)
{
  if (term.GetType() != stp::FLOATINGPOINT_TYPE)
  {
    FatalError("Expecting FP term");
  }

  outputFloatingPointSMTLIB2(n, os, term.GetExpWidth(), term.GetSigWidth());
}

void SMTLIB2_Print1(ostream& os, const ASTNode n, int indentation, bool letize)
{
  // os << spaces(indentation);
  // os << endl << spaces(indentation);
  if (!n.IsDefined())
  {
    FatalError("<undefined>");
    return;
  }

  // if this node is present in the letvar Map, then print the letvar
  // this is to print letvars for shared subterms inside the printing
  // of "(LET v0 = term1, v1=term1@term2,...
  if ((NodeLetVarMap1.find(n) != NodeLetVarMap1.end()) && !letize)
  {
    SMTLIB2_Print1(os, (NodeLetVarMap1[n]), indentation, letize);
    return;
  }

  // this is to print letvars for shared subterms inside the actual
  // term to be printed
  if ((NodeLetVarMap.find(n) != NodeLetVarMap.end()) && letize)
  {
    SMTLIB2_Print1(os, (NodeLetVarMap[n]), indentation, letize);
    return;
  }

  // otherwise print it normally
  const Kind kind = n.GetKind();
  const ASTChildren c = n.GetChildren();
  switch (kind)
  {
    case BITVECTOR:
    case BVCONST:
      // A float constant is stored as its packed bits, but denotes a float:
      // print it in (fp ...) syntax, not as a bitvector literal.
      if (n.GetType() == stp::FLOATINGPOINT_TYPE)
        outputFloatingPointSMTLIB2(n, os, n);
      else
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
      assert(c.size() == 2);
      os << "("
         << "not ";
      if (NAND == kind)
        os << "("
           << "and ";
      else
        os << "("
           << "or ";
      SMTLIB2_Print1(os, c[0], 0, letize);
      os << " ";
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
    // The rounded operations lead with their rounding mode, which prints by
    // name (RNE...) when it is one of the five constants.
    case FP_ADD:
    case FP_SUB:
    case FP_MUL:
    case FP_DIV:
    case FP_FMA:
    case FP_SQRT:
    case FP_ROUNDTOINTEGRAL:
    {
      os << "(" << functionToSMTLIBName(kind, false) << " ";
      printRoundingModeSMTLIB2(os, c[0], letize);
      for (size_t i = 1; i < c.size(); i++)
      {
        os << " ";
        SMTLIB2_Print1(os, c[i], 0, letize);
      }
      os << ")";
    }
    break;
    case FP_MIN:
    case FP_MAX:
    {
      // A totalised node carries a third, internal child (the (+0, -0)
      // choice); the SMT-LIB form has exactly two operands.
      os << "(" << functionToSMTLIBName(kind, false);
      for (size_t i = 0; i < 2; i++)
      {
        os << " ";
        SMTLIB2_Print1(os, c[i], 0, letize);
      }
      os << ")";
    }
    break;
    case FP_TOFP:
    {
      // Children: (eb, sb, bits) reinterprets; (eb, sb, rm, source) converts.
      os << "((_ to_fp " << c[0].GetUnsignedConst() << " "
         << c[1].GetUnsignedConst() << ")";
      if (c.size() == 4)
      {
        os << " ";
        printRoundingModeSMTLIB2(os, c[2], letize);
        os << " ";
        SMTLIB2_Print1(os, c[3], 0, letize);
      }
      else
      {
        os << " ";
        SMTLIB2_Print1(os, c[2], 0, letize);
      }
      os << ")";
    }
    break;
    // Spelled `to_fp` -- SMT-LIB overloads the name on the operand's sort;
    // the separate kind is ours, so that the sort survives blasting.
    case FP_TOFP_SIGNED:
    {
      os << "((_ to_fp " << c[0].GetUnsignedConst() << " "
         << c[1].GetUnsignedConst() << ") ";
      printRoundingModeSMTLIB2(os, c[2], letize);
      os << " ";
      SMTLIB2_Print1(os, c[3], 0, letize);
      os << ")";
    }
    break;
    case FP_TOFP_UNSIGNED:
    {
      os << "((_ to_fp_unsigned " << c[0].GetUnsignedConst() << " "
         << c[1].GetUnsignedConst() << ") ";
      printRoundingModeSMTLIB2(os, c[2], letize);
      os << " ";
      SMTLIB2_Print1(os, c[3], 0, letize);
      os << ")";
    }
    break;
    case FP_TO_UBV:
    case FP_TO_SBV:
    {
      // Children: (width, rm, float[, unspecified-value]); the totalised
      // fourth child is internal.
      os << "((_ " << (kind == FP_TO_UBV ? "fp.to_ubv" : "fp.to_sbv") << " "
         << c[0].GetUnsignedConst() << ") ";
      printRoundingModeSMTLIB2(os, c[1], letize);
      os << " ";
      SMTLIB2_Print1(os, c[2], 0, letize);
      os << ")";
    }
    break;
    case FP_TO_IEEE_BV:
      FatalError("SMTLIB2: a float-to-IEEE-bits node (an API-only operation) "
                 "has no SMT-LIB spelling",
                 n);
      break;
    default:
    {
      if ((kind == AND || kind == OR || kind == XOR) && n.Degree() == 1)
      {
        FatalError("Wrong number of arguments to operation (must be >1).", n);
      }

      // SMT-LIB only allows these functions to have two parameters.
      if ((kind == AND || kind == OR || kind == XOR || BVPLUS == kind ||
           kind == BVOR || kind == BVAND) &&
          n.Degree() > 2)
      {
        string close = "";

        for (long int i = 0; i < (long int)c.size() - 1; i++)
        {
          os << "(" << functionToSMTLIBName(kind, false);
          os << " ";
          SMTLIB2_Print1(os, c[i], 0, letize);
          os << " ";
          close += ")";
        }
        SMTLIB2_Print1(os, c[c.size() - 1], 0, letize);
        os << close;
      }
      else
      {
        os << "(" << functionToSMTLIBName(kind, false);

        auto iend = c.end();
        for (auto i = c.begin(); i != iend; i++)
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
