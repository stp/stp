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
#include <map>

// Outputs in the SMTLIB format. If you want something that can be parsed by
// other tools call
// SMTLIB_PrintBack(). SMTLIB_Print() prints just an expression.

namespace printer
{

using std::string;
using namespace stp;

// The sorts a term uses that its nodes cannot state: which of its 5-bit
// bitvectors are rounding modes, and what an array's index and element sorts
// really are.
//
// Read off the term rather than asked of the manager. STPMgr does keep
// registries of all four -- declared RoundingMode symbols and the three array
// sorts -- but they are frame-scoped, and the parser tears every frame down
// when it reaches end of file. By the time anything prints a whole formula
// back they are empty, and every one of these would print as its carrier: a
// mode as (_ BitVec 5), a RoundingMode-indexed array as (Array (_ BitVec 5)
// ...), a float-indexed one as (Array (_ BitVec 32) ...). The printed form
// then does not parse, because the operations ask for the sort and not the
// width (STPMgr::isRoundingModeSortedTerm).
//
// A float *element* needs none of this: the array node carries the element
// format itself.
struct UsedSorts
{
  ASTNodeSet rounding_modes; // terms in rounding-mode position
  ASTNodeSet rm_element_arrays;
  ASTNodeSet rm_index_arrays;
  std::map<ASTNode, std::pair<unsigned int, unsigned int>> fp_index_arrays;
};

// Which child of a floating-point operation carries its rounding mode, or -1
// for the operations that take none.
//
// A position table, because "a 5-bit bitvector inside a floating-point
// operation" is not the same test. The to_fp family converts *from a
// bitvector*, of whatever width the input chose -- five included -- so in
// ((_ to_fp_unsigned 8 24) RNE bv) the source operand is the same shape as
// the mode beside it, and calling both modes declares bv as RoundingMode. The
// printed form then re-parses with bv pinned to the five encodings, which is
// a different formula from the one printed.
static int roundingModeChild(const ASTNode& n)
{
  switch (n.GetKind())
  {
    case FP_ADD:
    case FP_SUB:
    case FP_MUL:
    case FP_DIV:
    case FP_FMA:
    case FP_SQRT:
    case FP_ROUNDTOINTEGRAL:
      return 0;

    // (m, rm, x) before totalisation, (m, rm, x, unspecified) after.
    case FP_TO_UBV:
    case FP_TO_SBV:
      return 1;

    // (e, s, rm, expr) with a mode; (e, s, bits), the bit-pattern
    // reinterpretation, takes none.
    case FP_TOFP:
      return n.Degree() == 4 ? 2 : -1;

    // (e, s, rm, bits) always: the source is an integer in a bitvector.
    case FP_TOFP_SIGNED:
    case FP_TOFP_UNSIGNED:
      return 2;

    default:
      return -1;
  }
}

// The shapes a mode can arrive in, mirroring STPMgr::isRoundingModeSortedTerm
// so that what prints as a mode is exactly what re-parses as one: a symbol, a
// read from a RoundingMode-element array, or an ite over either. A literal
// needs nothing -- it prints by name. Walking into the ite is what the shape
// test alone missed: the mode inside (ite c RTZ r) is not itself a child of
// the operation, so r printed as (_ BitVec 5) and the printed form no longer
// parsed. The ite is recorded too, so pass two can see it as an array index.
static void noteRoundingMode(const ASTNode& rm, STPMgr* mgr, UsedSorts& out)
{
  switch (rm.GetKind())
  {
    case SYMBOL:
      out.rounding_modes.insert(rm);
      break;
    case READ:
    {
      out.rounding_modes.insert(rm);
      // A mode read out of an array makes that array's elements modes.
      const ASTNode base = mgr->arrayBaseSymbol(rm[0]);
      if (!base.IsNull())
        out.rm_element_arrays.insert(base);
      break;
    }
    case ITE:
      out.rounding_modes.insert(rm);
      noteRoundingMode(rm[1], mgr, out);
      noteRoundingMode(rm[2], mgr, out);
      break;
    default:
      break;
  }
}

// Pass one: what is used as a rounding mode.
static void collectRoundingModeUses(const ASTNode& n, STPMgr* mgr,
                                    ASTNodeSet& visited, UsedSorts& out)
{
  if (!visited.insert(n).second)
    return;

  const int rm = roundingModeChild(n);
  if (rm >= 0 && static_cast<size_t>(rm) < n.Degree())
    noteRoundingMode(n[rm], mgr, out);

  for (size_t i = 0; i < n.Degree(); i++)
    collectRoundingModeUses(n[i], mgr, visited, out);
}

// Pass two: what the arrays are indexed by. Needs pass one's answer, since a
// RoundingMode index is only recognisable as a term already known to be a
// mode. An index that is only ever a mode *literal* stays a plain 5-bit
// constant here -- inherently ambiguous with a bitvector-indexed array, and
// harmless, since the printed form still replays as the same constant.
static void collectArrayIndexSorts(const ASTNode& n, STPMgr* mgr,
                                   ASTNodeSet& visited, UsedSorts& out)
{
  if (!visited.insert(n).second)
    return;

  const Kind k = n.GetKind();
  if ((k == READ || k == WRITE) && n.Degree() >= 2)
  {
    const ASTNode base = mgr->arrayBaseSymbol(n[0]);
    const ASTNode& index = n[1];
    if (!base.IsNull())
    {
      if (index.GetType() == FLOATINGPOINT_TYPE)
        out.fp_index_arrays[base] =
            std::make_pair(index.GetExpWidth(), index.GetSigWidth());
      else if (out.rounding_modes.find(index) != out.rounding_modes.end())
        out.rm_index_arrays.insert(base);
    }
  }

  for (size_t i = 0; i < n.Degree(); i++)
    collectArrayIndexSorts(n[i], mgr, visited, out);
}

void printVarDeclsToStream(STPMgr* mgr, ASTNodeSet& symbols,
                           const UsedSorts& used, ostream& os);

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

  UsedSorts used;
  {
    ASTNodeSet seen;
    collectRoundingModeUses(n, mgr, seen, used);
  }
  {
    ASTNodeSet seen;
    collectArrayIndexSorts(n, mgr, seen, used);
  }

  printVarDeclsToStream(mgr, symbols, used, os);
  os << "(assert ";
  SMTLIB_Print(os, mgr, n, 0, &SMTLIB2_Print1, false);
  os << ")\n";
  // os << "(check-sat)" << endl;
  // os << "(exit)\n";
}

void printVarDeclsToStream(STPMgr* mgr, ASTNodeSet& symbols,
                           const UsedSorts& used, ostream& os)
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

    // The sorts the node cannot say for itself: a RoundingMode is a plain
    // 5-bit bitvector, and an array's index sort is only ever a width. Print
    // them and the declaration replays; print the carrier and it does not --
    // every operation that takes a rounding mode asks for the sort, not the
    // width (see STPMgr::isRoundingModeSortedTerm), so the printed form would
    // no longer parse.
    switch (a.GetType())
    {
      case stp::BITVECTOR_TYPE:
        if (mgr->isRoundingModeSymbol(a) ||
            used.rounding_modes.find(a) != used.rounding_modes.end())
        {
          os << " () RoundingMode";
          break;
        }
        os << " () (";
        os << "_ BitVec " << a.GetValueWidth() << ")";

        break;
      case stp::ARRAY_TYPE:
      {
        unsigned int idx_exp = 0;
        unsigned int idx_sig = 0;
        const auto fp_index = used.fp_index_arrays.find(a);

        os << " () (";
        os << "Array ";
        if (fp_index != used.fp_index_arrays.end())
          os << "(_ FloatingPoint " << fp_index->second.first << " "
             << fp_index->second.second << ") ";
        else if (mgr->arrayHasFpIndex(a, idx_exp, idx_sig))
          os << "(_ FloatingPoint " << idx_exp << " " << idx_sig << ") ";
        else if (mgr->arrayHasRmIndex(a) ||
                 used.rm_index_arrays.find(a) != used.rm_index_arrays.end())
          os << "RoundingMode ";
        else
          os << "(_ BitVec " << a.GetIndexWidth() << ") ";

        // An array of floats carries the element format on the array symbol.
        if (mgr->arrayHasRmElement(a) ||
            used.rm_element_arrays.find(a) != used.rm_element_arrays.end())
          os << "RoundingMode )";
        else if (a.GetExpWidth() != 0)
          os << "(_ FloatingPoint " << a.GetExpWidth() << " " << a.GetSigWidth()
             << ") )";
        else
          os << "(_ BitVec " << a.GetValueWidth() << ") )";
        break;
      }
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
