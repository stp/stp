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

// Outputs in the SMT-LIB2 format. If you want something that can be parsed
// by other tools call SMTLIB2_PrintBack(). SMTLIB_Print() prints just an
// expression.

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
//
// `noted` is this walk's own visited set, and is not the one the enclosing
// pass uses: the two walk the same nodes for different purposes, and the
// enclosing walk reaches a mode operand as an ordinary child as well, so one
// shared set would let whichever arrived first suppress the other. It has to
// be a set all the same. Terms are a DAG, the ite arms are frequently shared,
// and this only ever inserts into `out`, so a second visit can add nothing --
// but without the set the recursion is 2^depth. Nested shared mode ites cost
// 0.01s at depth 20 and 3.95s at depth 28, a clean doubling per level.
static void noteRoundingMode(const ASTNode& rm, STPMgr* mgr, ASTNodeSet& noted,
                             UsedSorts& out)
{
  if (!noted.insert(rm).second)
    return;

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
      noteRoundingMode(rm[1], mgr, noted, out);
      noteRoundingMode(rm[2], mgr, noted, out);
      break;
    default:
      break;
  }
}

// Pass one: what is used as a rounding mode.
static void collectRoundingModeUses(const ASTNode& n, STPMgr* mgr,
                                    ASTNodeSet& visited, ASTNodeSet& noted,
                                    UsedSorts& out)
{
  if (!visited.insert(n).second)
    return;

  const int rm = roundingModeChild(n);
  if (rm >= 0 && static_cast<size_t>(rm) < n.Degree())
    noteRoundingMode(n[rm], mgr, noted, out);

  for (size_t i = 0; i < n.Degree(); i++)
    collectRoundingModeUses(n[i], mgr, visited, noted, out);
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

void SMTLIB2_PrintBack(ostream& os, const ASTNode& n, STPMgr* mgr,
                       const bool definately_bv)
{
  const bool has_arrays = !definately_bv && containsArrayOps(n, mgr);
  // Logic selection describes this expression, not every term ever interned
  // by the manager. Include RoundingMode-only formulas: that source sort is
  // part of the FP theory even when no FloatingPoint value occurs.
  const bool has_fp = containsFloatingPointTheory(n, mgr);
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
    ASTNodeSet seen, noted;
    collectRoundingModeUses(n, mgr, seen, noted, used);
  }
  {
    ASTNodeSet seen;
    collectArrayIndexSorts(n, mgr, seen, used);
  }

  printVarDeclsToStream(mgr, symbols, used, os);
  os << "(assert ";
  SMTLIB_Print(os, mgr, n, 0);
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

// Thin wrapper over the shared traversal. Declared in printers.h because
// get-assertions prints the asserted formulas through it.
void SMTLIB2_Print1(ostream& os, const ASTNode n, int indentation, bool letize)
{
  SMTLIB_Print1(os, n, indentation, letize);
}
}
