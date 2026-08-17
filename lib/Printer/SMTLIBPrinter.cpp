/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: May, 2010
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

#include "stp/Printer/SMTLIBPrinter.h"
#include "stp/Printer/printers.h"
#include <cassert>

// Functions shared between the printers: the letize pass used by all of
// them, and the traversal shared by the version1 and version2 SMT-LIB
// printers.

namespace printer
{
using namespace stp;
using std::pair;
using std::endl;
using std::string;

static string tolower(const char* name)
{
  string s(name);
  for (size_t i = 0; i < s.size(); ++i)
    s[i] = ::tolower(s[i]);
  return s;
}

// Map from ASTNodes to LetVars
THREAD_LOCAL_IE stp::ASTNodeMap NodeLetVarMap;

// This is a vector which stores the Node to LetVars pairs. It
// allows for sorted printing, as opposed to NodeLetVarMap
THREAD_LOCAL_IE vector<pair<ASTNode, ASTNode>> NodeLetVarVec;

// a partial Map from ASTNodes to LetVars. Needed in order to
// correctly print shared subterms inside the LET itself
THREAD_LOCAL_IE stp::ASTNodeMap NodeLetVarMap1;

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
  SMTLIB_Print1(os, rm, 0, letize, false);
}

// Prints one node, in SMT-LIB1 syntax when smtlib1 is set and in SMT-LIB2
// syntax otherwise. The two dialects share the whole traversal; they differ
// in exactly five places, each marked "dialect:" below. The floating-point
// cases are not among them: SMT-LIB1 has no FP theory, so those nodes only
// ever reach here with smtlib1 clear.
void SMTLIB_Print1(ostream& os, const ASTNode n, int indentation, bool letize,
                   bool smtlib1)
{
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
    SMTLIB_Print1(os, (NodeLetVarMap1[n]), indentation, letize, smtlib1);
    return;
  }

  // this is to print letvars for shared subterms inside the actual
  // term to be printed
  if ((NodeLetVarMap.find(n) != NodeLetVarMap.end()) && letize)
  {
    SMTLIB_Print1(os, (NodeLetVarMap[n]), indentation, letize, smtlib1);
    return;
  }

  // otherwise print it normally
  const Kind kind = n.GetKind();
  const ASTChildren c = n.GetChildren();
  switch (kind)
  {
    case BITVECTOR:
    case BVCONST:
      // dialect 1: the bitvector constant spelling.
      if (smtlib1)
        outputBitVec(n, os);
      // A rounding mode and a float are both stored as packed bits but
      // denote neither: print them by mode name and in (fp ...) syntax
      // rather than as bitvector literals.
      else if (n.GetSourceSort().kind() == stp::SourceSort::Kind::RoundingMode)
      {
        const char* name = roundingModeName(n.GetUnsignedConst());
        if (name == NULL)
          FatalError("invalid RoundingMode literal", n);
        os << name;
      }
      else if (n.GetType() == stp::FLOATINGPOINT_TYPE)
        outputFloatingPointSMTLIB2(n, os, n);
      else
        outputBitVecSMTLIB2(n, os);
      break;
    case SYMBOL:
      // dialect 2: SMT-LIB2 quotes symbols so that STP's names, which can
      // contain characters SMT-LIB2 reserves, survive a round trip.
      if (smtlib1)
        n.nodeprint(os);
      else
      {
        os << "|";
        n.nodeprint(os);
        os << "|";
      }
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
      SMTLIB_Print1(os, c[0], 0, letize, smtlib1);
      os << " ";
      SMTLIB_Print1(os, c[1], 0, letize, smtlib1);
      os << "))";
      break;
    case TRUE:
      os << "true";
      break;
    case BVSX:
    case BVZX:
    {
      unsigned int amount = c[1].GetUnsignedConst();
      // dialect 3: indexed identifier syntax.
      if (smtlib1)
        os << (BVZX == kind ? "(zero_extend[" : "(sign_extend[");
      else
        os << (BVZX == kind ? "((_ zero_extend " : "((_ sign_extend ");

      os << (amount - c[0].GetValueWidth()) << (smtlib1 ? "]" : ") ");
      SMTLIB_Print1(os, c[0], indentation, letize, smtlib1);
      os << ")";
    }
    break;
    case BVEXTRACT:
    {
      unsigned int upper = c[1].GetUnsignedConst();
      unsigned int lower = c[2].GetUnsignedConst();
      assert(upper >= lower);
      // dialect 4: indexed identifier syntax.
      if (smtlib1)
        os << "(extract[" << upper << ":" << lower << "] ";
      else
        os << "((_ extract " << upper << " " << lower << ") ";
      SMTLIB_Print1(os, c[0], indentation, letize, smtlib1);
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
        SMTLIB_Print1(os, c[i], 0, letize, false);
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
        SMTLIB_Print1(os, c[i], 0, letize, false);
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
        SMTLIB_Print1(os, c[3], 0, letize, false);
      }
      else
      {
        os << " ";
        SMTLIB_Print1(os, c[2], 0, letize, false);
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
      SMTLIB_Print1(os, c[3], 0, letize, false);
      os << ")";
    }
    break;
    case FP_TOFP_UNSIGNED:
    {
      os << "((_ to_fp_unsigned " << c[0].GetUnsignedConst() << " "
         << c[1].GetUnsignedConst() << ") ";
      printRoundingModeSMTLIB2(os, c[2], letize);
      os << " ";
      SMTLIB_Print1(os, c[3], 0, letize, false);
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
      SMTLIB_Print1(os, c[2], 0, letize, false);
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
      // dialect 5: a handful of operators were renamed between the versions,
      // which functionToSMTLIBName() takes care of.
      if ((kind == AND || kind == OR || kind == XOR) && n.Degree() == 1)
      {
        FatalError("Wrong number of arguments to operation (must be >1).", n);
      }

      // SMT-LIB only allows these functions to have two parameters.
      if ((kind == AND || kind == OR || kind == XOR || BVPLUS == kind ||
           kind == BVMULT || kind == BVOR || kind == BVAND) &&
          n.Degree() > 2)
      {
        string close = "";

        for (size_t i = 0; i + 1 < c.size(); i++)
        {
          os << "(" << functionToSMTLIBName(kind, smtlib1);
          os << " ";
          SMTLIB_Print1(os, c[i], 0, letize, smtlib1);
          os << " ";
          close += ")";
        }
        SMTLIB_Print1(os, c[c.size() - 1], 0, letize, smtlib1);
        os << close;
      }
      else
      {
        os << "(" << functionToSMTLIBName(kind, smtlib1);

        auto iend = c.end();
        for (auto i = c.begin(); i != iend; i++)
        {
          os << " ";
          SMTLIB_Print1(os, *i, 0, letize, smtlib1);
        }

        os << ")";
      }
    }
  }
}

// copied from Presentation Langauge printer.
ostream& SMTLIB_Print(ostream& os, STPMgr* mgr, const ASTNode n,
                      const int indentation, bool smtlib1)
{
  // Clear the maps
  NodeLetVarMap.clear();
  NodeLetVarVec.clear();
  NodeLetVarMap1.clear();

  // pass 1: letize the node
  {
    ASTNodeSet seen;
    // The last argument: SMT-LIB1 can only let-bind terms, not formulas.
    LetizeState st = {seen, NodeLetVarMap, NodeLetVarVec, "?let_k_", smtlib1};
    LetizeNode(n, st, mgr);
  }

  // pass 2:
  //
  // 2. print all the let variables and their counterpart expressions
  // 2. as follows (LET var1 = expr1, var2 = expr2, ...
  //
  // 3. Then print the Node itself, replacing every occurence of
  // 3. expr1 with var1, expr2 with var2, ...
  // os << "(";
  if (0 < NodeLetVarMap.size())
  {
    vector<pair<ASTNode, ASTNode>>::iterator it = NodeLetVarVec.begin();
    const vector<pair<ASTNode, ASTNode>>::iterator itend = NodeLetVarVec.end();

    os << "(let (";
    if (!smtlib1)
      os << "(";
    // print the let var first
    SMTLIB_Print1(os, it->first, indentation, false, smtlib1);
    os << " ";
    // print the expr
    SMTLIB_Print1(os, it->second, indentation, false, smtlib1);
    os << " )";
    if (!smtlib1)
      os << ")";

    // update the second map for proper printing of LET
    NodeLetVarMap1[it->second] = it->first;

    string closing = "";
    for (it++; it != itend; it++)
    {
      os << " " << endl;
      os << "(let (";
      if (!smtlib1)
        os << "(";
      // print the let var first
      SMTLIB_Print1(os, it->first, indentation, false, smtlib1);
      os << " ";
      // print the expr
      SMTLIB_Print1(os, it->second, indentation, false, smtlib1);
      os << ")";
      if (!smtlib1)
        os << ")";

      // update the second map for proper printing of LET
      NodeLetVarMap1[it->second] = it->first;
      closing += ")";
    }
    os << endl;
    SMTLIB_Print1(os, n, indentation, true, smtlib1);
    os << closing;
    os << " )  ";
  }
  else
    SMTLIB_Print1(os, n, indentation, false, smtlib1);

  os << endl;
  return os;
}

void LetizeNode(const ASTNode& n, LetizeState& st, STPMgr* stp)
{
  if (n.isAtom())
    return;

  const ASTChildren c = n.GetChildren();
  for (auto it = c.begin(), itend = c.end(); it != itend;
       it++)
  {
    const ASTNode& ccc = *it;
    if (ccc.isAtom())
      continue;

    if (st.seen.find(ccc) == st.seen.end())
    {
      // If branch: if *it is not in NodeSet then,
      //
      // 1. add it to NodeSet
      //
      // 2. Letize its childNodes
      st.seen.insert(ccc);
      LetizeNode(ccc, st, stp);
    }
    else
    {
      // 0. Else branch: Node has been seen before
      //
      // 1. Check if the node has a corresponding letvar in the
      // 1. letVarMap.
      //
      // 2. if no, then create a new var and add it to the
      // 2. letVarMap
      if ((!st.termsOnly || ccc.GetType() == BITVECTOR_TYPE) &&
          st.letVarMap.find(ccc) == st.letVarMap.end())
      {
        // Create a new symbol. Get some name. if it conflicts with a
        // declared name, too bad.
        int sz = st.letVarMap.size();
        std::ostringstream oss;
        oss << st.prefix << sz;

        // Note the widths come from the parent, not from ccc.
        ASTNode CurrentSymbol = stp->CreateSymbol(
            oss.str().c_str(), n.GetIndexWidth(), n.GetValueWidth());
        /* If for some reason the variable being created here is
         * already declared by the user then the printed output will
         * not be a legal input to the system. too bad. I refuse to
         * check for this.  [Vijay is the author of this comment.]
         */

        st.letVarMap[ccc] = CurrentSymbol;
        std::pair<ASTNode, ASTNode> node_letvar_pair(CurrentSymbol, ccc);
        st.letVarVec.push_back(node_letvar_pair);
      }
    }
  }
}

string functionToSMTLIBName(const Kind k, bool smtlib1)
{
  switch (k)
  {
    case IFF:
      if (smtlib1)
        return "iff";
      else
        return "=";
    case IMPLIES:
      if (smtlib1)
        return "implies";
      else
        return "=>";
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
    case BVUADDO:
    case BVSADDO:
    case BVUMULO:
    case BVSMULO:
    case BVUSUBO:
    case BVSSUBO:
    case BVXOR:
    case ITE:
    case NAND:
    case NOR:
    case NOT:
    case OR:
    case XOR:
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
    case BVNOT:
      return "bvnot";
    case BVPLUS:
      return "bvadd";
    case BVRIGHTSHIFT:
      return "bvlshr"; // logical
    case BVSRSHIFT:
      return "bvashr"; // arithmetic.
    case BVUMINUS:
      return "bvneg";
    case EQ:
    case ARRAY_EQ:
      return "=";
    case READ:
      return "select";
    case WRITE:
      return "store";
    case SBVDIV:
      return "bvsdiv";
    case SBVREM:
      return "bvsrem";
    case SBVMOD:
      return "bvsmod";

    // Floating point (SMT-LIB 2 only; there is no SMT-LIB 1 FP theory).
    // The indexed operators (to_fp, fp.to_ubv...) print through their own
    // cases in SMTLIB2_Print1, not through this name map.
    case FP_ABS:
      return "fp.abs";
    case FP_NEG:
      return "fp.neg";
    case FP_ADD:
      return "fp.add";
    case FP_SUB:
      return "fp.sub";
    case FP_MUL:
      return "fp.mul";
    case FP_DIV:
      return "fp.div";
    case FP_FMA:
      return "fp.fma";
    case FP_SQRT:
      return "fp.sqrt";
    case FP_REM:
      return "fp.rem";
    case FP_ROUNDTOINTEGRAL:
      return "fp.roundToIntegral";
    case FP_MIN:
      return "fp.min";
    case FP_MAX:
      return "fp.max";
    case FP_LEQ:
      return "fp.leq";
    case FP_LT:
      return "fp.lt";
    case FP_GEQ:
      return "fp.geq";
    case FP_GT:
      return "fp.gt";
    case FP_EQ:
      return "fp.eq";
    case FP_ISNORMAL:
      return "fp.isNormal";
    case FP_ISSUBNORMAL:
      return "fp.isSubnormal";
    case FP_ISZERO:
      return "fp.isZero";
    case FP_ISINFINITE:
      return "fp.isInfinite";
    case FP_ISNAN:
      return "fp.isNaN";
    case FP_ISNEGATIVE:
      return "fp.isNegative";
    case FP_ISPOSITIVE:
      return "fp.isPositive";
    case FP_SMT_EQ:
      return "=";

    default:
    {
      std::cerr << "Unknown name when outputting:";
      FatalError(_kind_names[k]);
      return ""; // to quieten compiler/
    }
  }
}
}
