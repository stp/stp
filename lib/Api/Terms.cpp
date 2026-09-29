/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: September, 2026
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

// Terms.cpp -- the Term value type: the public view of an engine node, the
// typed value readers, printing and substitution.

#include "Internal.h"

#include "../Lra/ASTRealConstAccess.h"
#include "stp/Extensionality/ExtensionalityContext.h"
#include "stp/FloatBlaster/DecimalLiteral.h"
#include "stp/FloatBlaster/FloatBlaster.h"
#include "stp/FloatBlaster/rounding_modes.h"
#include "stp/Printer/printers.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/UninterpretedFunctions/UFDecl.h"

#include <algorithm>
#include <cmath>
#include <cstring>
#include <functional>
#include <new>
#include <ostream>
#include <sstream>

namespace stp
{
namespace api
{
namespace detail
{

// ------------------------------------------------------------ kind table

namespace
{
const KindSpec kKindSpecs[] = {
#include "gen/kind_table.inc"
};
} // namespace

const KindSpec& kind_spec(Kind k)
{
  const std::size_t i = static_cast<std::size_t>(k);
  if (i >= static_cast<std::size_t>(Kind::NUM_KINDS))
    fail(ErrorCode::INVALID_ARGUMENT, "kind", "not a kind: " + std::to_string(i));
  return kKindSpecs[i];
}

// ------------------------------------------------------------ the view

namespace
{
ASTNode c32(ManagerImpl* m, unsigned v)
{
  return m->bm->CreateBVConst(32, v);
}

// Whether a node's source sort is floating-point (a packed float).
bool is_fp_node(const ASTNode& n)
{
  return n.GetSourceSort().kind() == SourceSort::Kind::FloatingPoint;
}
} // namespace

Kind kind_of(ManagerImpl* m, const ASTNode& n)
{
  // A conversion to a Real is an encoding over its operand's bits, whose
  // root names the operand (STPMgr::CreateFpToReal).
  if (n.GetKind() == ITE && !m->bm->FpToRealOperand(n).IsNull())
    return Kind::FP_TO_REAL;
  switch (n.GetKind())
  {
    case SYMBOL:
      if (m->is_const_array(n))
        return Kind::CONST_ARRAY;
      return Kind::CONSTANT;
    case BVCONST:
    case TRUE:
    case FALSE:
    case REAL_CONST:
      return Kind::VALUE;
    case ITE: return Kind::ITE;
    case EQ:
    case IFF:
    case FP_SMT_EQ:
    case ARRAY_EQ:
      return Kind::EQUAL;
    case DISTINCT: return Kind::DISTINCT;
    case UF_APPLY: return Kind::APPLY;
    case NOT: return Kind::NOT;
    case AND: return Kind::AND;
    case OR: return Kind::OR;
    case XOR: return Kind::XOR;
    case IMPLIES: return Kind::IMPLIES;
    case NAND:
    case NOR:
      return Kind::NOT;
    case BOOLEXTRACT: return Kind::EQUAL;
    case PARAMBOOL: return Kind::CONSTANT;
    case BVNOT: return Kind::BV_NOT;
    case BVAND: return Kind::BV_AND;
    case BVOR: return Kind::BV_OR;
    case BVXOR: return Kind::BV_XOR;
    case BVNAND: return Kind::BV_NAND;
    case BVNOR: return Kind::BV_NOR;
    case BVXNOR: return Kind::BV_XNOR;
    case BVPLUS: return Kind::BV_ADD;
    case BVSUB: return Kind::BV_SUB;
    case BVUMINUS: return Kind::BV_NEG;
    case BVMULT: return Kind::BV_MUL;
    case BVDIV: return Kind::BV_UDIV;
    case BVMOD: return Kind::BV_UREM;
    case SBVDIV: return Kind::BV_SDIV;
    case SBVREM: return Kind::BV_SREM;
    case SBVMOD: return Kind::BV_SMOD;
    case BVLEFTSHIFT: return Kind::BV_SHL;
    case BVRIGHTSHIFT: return Kind::BV_LSHR;
    case BVSRSHIFT: return Kind::BV_ASHR;
    case BVCONCAT: return Kind::BV_CONCAT;
    case BVEXTRACT: return Kind::BV_EXTRACT;
    case BVSX: return Kind::BV_SIGN_EXTEND;
    case BVZX: return Kind::BV_ZERO_EXTEND;
    case BVLT: return Kind::BV_ULT;
    case BVLE: return Kind::BV_ULE;
    case BVGT: return Kind::BV_UGT;
    case BVGE: return Kind::BV_UGE;
    case BVSLT: return Kind::BV_SLT;
    case BVSLE: return Kind::BV_SLE;
    case BVSGT: return Kind::BV_SGT;
    case BVSGE: return Kind::BV_SGE;
    case BVUADDO: return Kind::BV_UADDO;
    case BVSADDO: return Kind::BV_SADDO;
    case BVUMULO: return Kind::BV_UMULO;
    case BVSMULO: return Kind::BV_SMULO;
    case BVUSUBO: return Kind::BV_USUBO;
    case BVSSUBO: return Kind::BV_SSUBO;
    case READ: return Kind::SELECT;
    case WRITE: return Kind::STORE;
    case FP_ABS: return Kind::FP_ABS;
    case FP_NEG: return Kind::FP_NEG;
    case FP_ADD: return Kind::FP_ADD;
    case FP_SUB: return Kind::FP_SUB;
    case FP_MUL: return Kind::FP_MUL;
    case FP_DIV: return Kind::FP_DIV;
    case FP_FMA: return Kind::FP_FMA;
    case FP_SQRT: return Kind::FP_SQRT;
    case FP_REM: return Kind::FP_REM;
    case FP_ROUNDTOINTEGRAL: return Kind::FP_RTI;
    case FP_MIN: return Kind::FP_MIN;
    case FP_MAX: return Kind::FP_MAX;
    case FP_EQ: return Kind::FP_EQ;
    case FP_LT: return Kind::FP_LT;
    case FP_LEQ: return Kind::FP_LEQ;
    case FP_GT: return Kind::FP_GT;
    case FP_GEQ: return Kind::FP_GEQ;
    case FP_ISNORMAL: return Kind::FP_IS_NORMAL;
    case FP_ISSUBNORMAL: return Kind::FP_IS_SUBNORMAL;
    case FP_ISZERO: return Kind::FP_IS_ZERO;
    case FP_ISINFINITE: return Kind::FP_IS_INF;
    case FP_ISNAN: return Kind::FP_IS_NAN;
    case FP_ISNEGATIVE: return Kind::FP_IS_NEG;
    case FP_ISPOSITIVE: return Kind::FP_IS_POS;
    case FP_TOFP:
    {
      if (n.Degree() == 3)
        return Kind::FP_TO_FP_FROM_BV;
      const ASTNode& src = n[3];
      if (src.isRealTerm())
        return Kind::FP_TO_FP_FROM_REAL;
      return is_fp_node(src) ? Kind::FP_TO_FP_FROM_FP : Kind::FP_TO_FP_FROM_BV;
    }
    case FP_TOFP_SIGNED: return Kind::FP_TO_FP_FROM_SBV;
    case FP_TOFP_UNSIGNED: return Kind::FP_TO_FP_FROM_UBV;
    case FP_TO_UBV: return Kind::FP_TO_UBV;
    case FP_TO_SBV: return Kind::FP_TO_SBV;
    case FP_TO_IEEE_BV: return Kind::FP_TO_IEEE_BV;
    case REAL_ADD: return Kind::REAL_ADD;
    case REAL_SUB: return Kind::REAL_SUB;
    case REAL_NEG: return Kind::REAL_NEG;
    case REAL_MUL: return Kind::REAL_MUL;
    case REAL_DIV: return Kind::REAL_DIV;
    case REAL_LT: return Kind::REAL_LT;
    case REAL_LE: return Kind::REAL_LE;
    case REAL_GT: return Kind::REAL_GT;
    case REAL_GE: return Kind::REAL_GE;
    default:
      break;
  }
  fail_internal("Term::kind", std::string("an engine node of kind ") +
                                  std::to_string(static_cast<int>(n.GetKind())) +
                                  " has no public kind");
}

View view_of(ManagerImpl* m, const ASTNode& n)
{
  View v;
  v.kind = kind_of(m, n);
  if (v.kind == Kind::FP_TO_REAL)
  {
    v.children.push_back(m->bm->FpToRealOperand(n));
    return v;
  }
  const ASTChildren kids = n.GetChildren();
  switch (n.GetKind())
  {
    case SYMBOL:
    {
      if (m->is_const_array(n))
        v.children.push_back(m->const_array_default(n));
      return v;
    }
    case NAND:
    case NOR:
    {
      ASTVec inner(kids.begin(), kids.end());
      v.children.push_back(
          m->bm->hashingNodeFactory->CreateNode(n.GetKind() == NAND ? AND : OR, inner));
      return v;
    }
    case BOOLEXTRACT:
    {
      const unsigned i = kids[1].GetUnsignedConst();
      v.children.push_back(
          m->bm->hashingNodeFactory->CreateTerm(BVEXTRACT, 1, kids[0], c32(m, i), c32(m, i)));
      v.children.push_back(m->bm->CreateOneConst(1));
      return v;
    }
    case PARAMBOOL:
      return v;
    case BVEXTRACT:
      v.children.push_back(kids[0]);
      v.indices = {kids[1].GetUnsignedConst(), kids[2].GetUnsignedConst()};
      return v;
    case BVSX:
    case BVZX:
      v.children.push_back(kids[0]);
      v.indices = {n.GetValueWidth() - kids[0].GetValueWidth()};
      return v;
    case FP_MIN:
    case FP_MAX:
      v.children.assign(kids.begin(), kids.begin() + 2);
      return v;
    case FP_TOFP:
    case FP_TOFP_SIGNED:
    case FP_TOFP_UNSIGNED:
      v.indices = {kids[0].GetUnsignedConst(), kids[1].GetUnsignedConst()};
      v.children.assign(kids.begin() + 2, kids.end());
      return v;
    case FP_TO_UBV:
    case FP_TO_SBV:
      v.indices = {kids[0].GetUnsignedConst()};
      v.children.push_back(kids[1]);
      v.children.push_back(kids[2]);
      return v;
    default:
      v.children.assign(kids.begin(), kids.end());
      return v;
  }
}

// ------------------------------------------------------------ value readers

std::string bv_bits_of(const ASTNode& c)
{
  unsigned char* s = CONSTANTBV::BitVector_to_Bin(c.GetBVConst());
  std::string out(reinterpret_cast<const char*>(s));
  CONSTANTBV::BitVector_Dispose(s);
  const unsigned width = c.GetValueWidth();
  if (out.size() > width)
    out = out.substr(out.size() - width);
  else if (out.size() < width)
    out = std::string(width - out.size(), '0') + out;
  return out;
}

std::vector<std::uint64_t> bv_limbs_of(const ASTNode& c)
{
  const std::string bits = bv_bits_of(c);
  const std::size_t width = bits.size();
  std::vector<std::uint64_t> limbs((width + 63) / 64, 0);
  for (std::size_t i = 0; i < width; ++i)
    if (bits[width - 1 - i] == '1')
      limbs[i / 64] |= std::uint64_t(1) << (i % 64);
  return limbs;
}

FloatValue fp_value_of(const ASTNode& c, std::uint32_t e, std::uint32_t s)
{
  FloatValue v;
  v.exp_size = e;
  v.sig_size = s;
  const std::string bits = bv_bits_of(c); // MSB first: sign, exponent, significand
  v.sign = bits[0] == '1';
  // the exponent's low 64 bits (Term::to_fp refuses a wider one), and its
  // class read off all of it
  v.biased_exponent = 0;
  bool exp_ones = true, exp_zero = true;
  for (std::uint32_t i = 0; i < e; ++i)
  {
    const bool set = bits[1 + i] == '1';
    exp_ones = exp_ones && set;
    exp_zero = exp_zero && !set;
    v.biased_exponent = (v.biased_exponent << 1) | (set ? 1u : 0u);
  }
  const std::uint32_t t = s - 1;
  v.significand.assign((t + 63) / 64, 0);
  bool sig_zero = true;
  for (std::uint32_t i = 0; i < t; ++i)
  {
    const bool set = bits[bits.size() - 1 - i] == '1';
    if (set)
    {
      v.significand[i / 64] |= std::uint64_t(1) << (i % 64);
      sig_zero = false;
    }
  }
  if (exp_ones)
    v.cls = sig_zero ? FloatValue::Class::INF : FloatValue::Class::NOT_A_NUMBER;
  else if (exp_zero)
    v.cls = sig_zero ? FloatValue::Class::ZERO : FloatValue::Class::SUBNORMAL;
  else
    v.cls = FloatValue::Class::NORMAL;
  return v;
}

RoundingMode rm_of(const ASTNode& c, const char* fn)
{
  switch (c.GetUnsignedConst())
  {
    case symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN: return RoundingMode::RNE;
    case symbolic_fp::ROUND_NEAREST_TIES_TO_AWAY: return RoundingMode::RNA;
    case symbolic_fp::ROUND_TOWARD_POSITIVE: return RoundingMode::RTP;
    case symbolic_fp::ROUND_TOWARD_NEGATIVE: return RoundingMode::RTN;
    case symbolic_fp::ROUND_TOWARD_ZERO: return RoundingMode::RTZ;
    default:
      break;
  }
  fail_internal(fn, "a rounding-mode carrier that names no mode");
}

RationalValue rational_of(const ASTNode& c)
{
  RationalValue r;
  r.numerator = lra::detail::realNumerator(NodeAccess::raw(c));
  r.denominator = lra::detail::realDenominator(NodeAccess::raw(c));
  if (r.denominator.empty())
    r.denominator = "1";
  return r;
}

// ------------------------------------------------------------ printing

namespace
{
// What the CVC presentation language cannot spell: a float, a Real, an
// application of a declared function. Its printer treats those as fatal, so
// they are refused here first.
bool contains_cvc_unprintable(const ASTNode& root)
{
  ASTNodeSet seen;
  std::vector<ASTNode> stack{root};
  while (!stack.empty())
  {
    const ASTNode n = stack.back();
    stack.pop_back();
    if (!seen.insert(n).second)
      continue;
    if (n.GetSourceSort().usesFloatingPointTheory() || n.isRealTerm() || n.GetKind() == UF_APPLY)
      return true;
    for (const ASTNode& c : n.GetChildren())
      stack.push_back(c);
  }
  return false;
}
} // namespace

namespace
{
// The API's own SMT-LIB 2 printer over the public view: symbols by their
// declared names (quoted only where SMT-LIB requires), lowercase hex, one
// space between tokens, no let-sharing. The engine's printer is kept for the
// let-shared form.
class Smt2Printer
{
public:
  Smt2Printer(ManagerImpl* m, std::string& out) : m_(m), out_(out) {}

  void print(const ASTNode& n)
  {
    if (n.isConstant())
    {
      value(n);
      return;
    }
    const View v = view_of(m_, n);
    switch (v.kind)
    {
      case Kind::CONSTANT:
        out_ += symbol_name(n);
        return;
      case Kind::CONST_ARRAY:
        out_ += "((as const " + m_->sort_text(m_->sort_of_node(n, "Term::str")) + ") ";
        print(v.children[0]);
        out_ += ")";
        return;
      case Kind::APPLY:
        out_ += "(" + symbol_name(v.children[0]);
        for (std::size_t i = 1; i < v.children.size(); ++i)
        {
          out_ += " ";
          print(v.children[i]);
        }
        out_ += ")";
        return;
      default:
        break;
    }
    out_ += "(" + head(v);
    for (const ASTNode& c : v.children)
    {
      out_ += " ";
      print(c);
    }
    out_ += ")";
  }

private:
  std::string symbol_name(const ASTNode& n) const
  {
    auto it = m_->names_by_node.find(n);
    if (it != m_->names_by_node.end())
      return quote_symbol(it->second);
    if (const UFDecl* d = m_->decl_of(n))
      return quote_symbol(d->name());
    return quote_symbol(n.GetName());
  }

  std::string head(const View& v) const
  {
    std::string idx;
    for (std::uint32_t i : v.indices)
      idx += " " + std::to_string(i);
    switch (v.kind)
    {
      case Kind::BV_EXTRACT: return "(_ extract" + idx + ")";
      case Kind::BV_ZERO_EXTEND: return "(_ zero_extend" + idx + ")";
      case Kind::BV_SIGN_EXTEND: return "(_ sign_extend" + idx + ")";
      case Kind::BV_REPEAT: return "(_ repeat" + idx + ")";
      case Kind::BV_ROTATE_LEFT: return "(_ rotate_left" + idx + ")";
      case Kind::BV_ROTATE_RIGHT: return "(_ rotate_right" + idx + ")";
      case Kind::FP_TO_FP_FROM_BV:
      case Kind::FP_TO_FP_FROM_FP:
      case Kind::FP_TO_FP_FROM_SBV:
      case Kind::FP_TO_FP_FROM_REAL: return "(_ to_fp" + idx + ")";
      case Kind::FP_TO_FP_FROM_UBV: return "(_ to_fp_unsigned" + idx + ")";
      case Kind::FP_TO_UBV: return "(_ fp.to_ubv" + idx + ")";
      case Kind::FP_TO_SBV: return "(_ fp.to_sbv" + idx + ")";
      default: return std::string(kind_spec(v.kind).smtlib);
    }
  }

  void value(const ASTNode& n)
  {
    if (n.GetKind() == TRUE)
    {
      out_ += "true";
      return;
    }
    if (n.GetKind() == FALSE)
    {
      out_ += "false";
      return;
    }
    if (n.GetKind() == REAL_CONST)
    {
      const RationalValue q = rational_of(n);
      const bool negative = !q.numerator.empty() && q.numerator[0] == '-';
      const std::string mag = negative ? q.numerator.substr(1) : q.numerator;
      // The engine's own spelling (its get-value prints `(/ 1 2)` and
      // `(- 3)`): a numeral is a Real constant in every Real logic, and the
      // parser reads it back exactly.
      const std::string text =
          q.denominator == "1" ? mag : "(/ " + mag + " " + q.denominator + ")";
      out_ += negative ? "(- " + text + ")" : text;
      return;
    }
    const SourceSort ss = n.GetSourceSort();
    switch (ss.kind())
    {
      case SourceSort::Kind::FloatingPoint:
      {
        const std::string bits = bv_bits_of(n);
        const std::uint32_t e = ss.exponentWidth();
        out_ += "(fp #b" + bits.substr(0, 1) + " #b" + bits.substr(1, e) + " #b" +
                bits.substr(1 + e) + ")";
        return;
      }
      case SourceSort::Kind::RoundingMode:
        out_ += to_string(rm_of(n, "Term::str"));
        return;
      case SourceSort::Kind::Uninterpreted:
        out_ += quote_symbol(ss.name() + "!" + std::to_string(bv_limbs_of(n)[0]));
        return;
      default:
        break;
    }
    const std::string bits = bv_bits_of(n);
    if (bits.size() % 4 == 0)
    {
      out_ += "#x";
      for (std::size_t i = 0; i < bits.size(); i += 4)
      {
        int v = 0;
        for (int b = 0; b < 4; ++b)
          v = (v << 1) | (bits[i + b] - '0');
        out_ += "0123456789abcdef"[v];
      }
    }
    else
      out_ += "#b" + bits;
  }

  ManagerImpl* m_;
  std::string& out_;
};
} // namespace

std::string print_term(ManagerImpl* m, const ASTNode& n, Format f, bool share)
{
  m->check_alive("Term::to_string");
  std::ostringstream os;
  // The unshared SMT-LIB form is the API's own rendering.
  if ((f == Format::AUTO || f == Format::SMTLIB2) && !share)
  {
    std::string out;
    Smt2Printer(m, out).print(n);
    return out;
  }
  // An element of a declared sort has no literal syntax; print it as an
  // abstract value named by its sort and index, the way solvers do.
  if (n.isConstant() && n.GetKind() == BVCONST &&
      n.GetSourceSort().kind() == SourceSort::Kind::Uninterpreted &&
      (f == Format::AUTO || f == Format::SMTLIB2))
  {
    const std::uint64_t index = bv_limbs_of(n)[0];
    return quote_symbol(n.GetSourceSort().name() + "!" + std::to_string(index));
  }
  // A function symbol's engine name is an internal identity; it prints as
  // the name it was declared under, as Term::symbol() reports it.
  if (n.GetKind() == SYMBOL && (f == Format::AUTO || f == Format::SMTLIB2))
    if (const UFDecl* d = m->decl_of(n))
      return quote_symbol(d->name());
  // the engine's printers, inside an engine scope
  return engine_call(m, "Term::to_string", [&]() -> std::string {
    switch (f)
    {
      case Format::AUTO:
      case Format::SMTLIB2:
        if (share)
          printer::SMTLIB2_PrintTerm(os, m->bm, n);
        else
          printer::SMTLIB2_Print1(os, n, 0, false);
        break;
      case Format::CVC:
        if (contains_cvc_unprintable(n))
          fail(ErrorCode::UNSUPPORTED, "Term::to_string",
               "the CVC presentation language has no floating-point, Real or "
               "uninterpreted-function syntax");
        printer::PL_Print(os, n, m->bm);
        break;
      case Format::DOT:
        printer::Dot_Print(os, n);
        break;
      case Format::GDL:
        printer::GDL_Print(os, n);
        break;
      case Format::SMTLIB1:
        fail(ErrorCode::UNSUPPORTED, "Term::to_string", "there is no SMT-LIB 1 printer");
    }
    return os.str();
  });
}

// ------------------------------------------------------------ rebuilding

// Rebuild `n` with new children through `f`, keeping its widths and
// floating-point format. Shared by simplify, substitute and the evaluator.
ASTNode rebuild_node(ManagerImpl* m, NodeFactory* f, const ASTNode& n, const ASTVec& kids)
{
  const Kind_t k = n.GetKind();
  if (k == UF_APPLY)
  {
    std::string diagnostic;
    ASTVec actuals(kids.begin() + 1, kids.end());
    const UFDecl* decl = m->decl_of(kids[0]);
    if (decl == nullptr)
      fail_internal("rebuild", "an application without a declaration");
    ASTNode out = m->bm->getUFContext()->apply(decl, actuals, &diagnostic);
    if (out.GetKind() == UNDEFINED)
      fail_internal("rebuild", diagnostic);
    return out;
  }
  if (n.isRealTerm())
    return m->bm->CreateRealTerm(k, kids);
  if (n.GetType() == BOOLEAN_TYPE)
  {
    if (kids.size() == 2 && (kids[0].isRealTerm() || kids[1].isRealTerm()) &&
        (k == EQ || k == REAL_LT || k == REAL_LE || k == REAL_GT || k == REAL_GE))
      return m->bm->CreateRealPredicate(k, kids[0], kids[1]);
    return f->CreateNode(k, kids);
  }
  if (n.GetType() == ARRAY_TYPE)
  {
    ASTNode out = f->CreateArrayTerm(k, n.GetIndexWidth(), n.GetValueWidth(), kids);
    if (n.GetExpWidth() != 0 && out.GetExpWidth() == 0)
      out = FloatBlaster::withFormat(m->bm, out, n.GetExpWidth(), n.GetSigWidth());
    return out;
  }
  ASTNode out = f->CreateTerm(k, n.GetValueWidth(), kids);
  if (n.GetExpWidth() != 0)
    out = FloatBlaster::withFormat(m->bm, out, n.GetExpWidth(), n.GetSigWidth());
  return out;
}

} // namespace detail

using detail::ManagerImpl;

// ============================================================ Term

Term::Term() noexcept : mgr_(nullptr), node_(nullptr) {}

Term::Term(detail::ManagerImpl* m, void* node) noexcept : mgr_(m), node_(node)
{
  if (mgr_)
    mgr_->retain();
  detail::NodeAccess::retain(static_cast<ASTInternal*>(node_));
}

Term::Term(const Term& o) noexcept : mgr_(o.mgr_), node_(o.node_)
{
  if (mgr_)
    mgr_->retain();
  detail::NodeAccess::retain(static_cast<ASTInternal*>(node_));
}

Term::Term(Term&& o) noexcept : mgr_(o.mgr_), node_(o.node_)
{
  o.mgr_ = nullptr;
  o.node_ = nullptr;
}

Term& Term::operator=(const Term& o) noexcept
{
  if (this == &o)
    return *this;
  if (o.mgr_)
    o.mgr_->retain();
  detail::NodeAccess::retain(static_cast<ASTInternal*>(o.node_));
  detail::NodeAccess::release(static_cast<ASTInternal*>(node_));
  if (mgr_)
    mgr_->release();
  mgr_ = o.mgr_;
  node_ = o.node_;
  return *this;
}

Term& Term::operator=(Term&& o) noexcept
{
  if (this != &o)
  {
    detail::NodeAccess::release(static_cast<ASTInternal*>(node_));
    if (mgr_)
      mgr_->release();
    mgr_ = o.mgr_;
    node_ = o.node_;
    o.mgr_ = nullptr;
    o.node_ = nullptr;
  }
  return *this;
}

Term::~Term()
{
  // the node first, the manager it lives in second
  detail::NodeAccess::release(static_cast<ASTInternal*>(node_));
  if (mgr_)
    mgr_->release();
}

bool Term::is_null() const noexcept
{
  return node_ == nullptr;
}

namespace
{
ManagerImpl* live(const Term& t, const char* fn)
{
  if (t.is_null())
    detail::fail(ErrorCode::NULL_HANDLE, fn, "the term is null", 0);
  ManagerImpl* m = t.impl_manager();
  m->check_alive(fn);
  return m;
}

const ASTNode value_node(const Term& t, const char* fn)
{
  live(t, fn);
  const ASTNode n = detail::node_of(t);
  if (!n.isConstant())
    detail::fail(ErrorCode::NOT_A_VALUE, fn,
                 std::string("the term is not a value (kind ") +
                     to_string(detail::kind_of(t.impl_manager(), n)) +
                     "); evaluate it in a model first",
                 0, {t});
  return n;
}

const ASTNode bv_value_node(const Term& t, const char* fn)
{
  const ASTNode n = value_node(t, fn);
  if (n.GetSourceSort().kind() != SourceSort::Kind::BitVector)
    detail::fail(ErrorCode::SORT_MISMATCH, fn, "expected a bit-vector value", 0, {t},
                 {t.sort()});
  return n;
}
} // namespace

Kind Term::kind() const
{
  ManagerImpl* m = live(*this, "Term::kind");
  return detail::kind_of(m, detail::node_of(*this));
}

Sort Term::sort() const
{
  ManagerImpl* m = live(*this, "Term::sort");
  return Sort(m, m->sort_of_node(detail::node_of(*this), "Term::sort"));
}

std::size_t Term::num_children() const
{
  ManagerImpl* m = live(*this, "Term::num_children");
  return detail::view_of(m, detail::node_of(*this)).children.size();
}

Term Term::child(std::size_t i) const
{
  ManagerImpl* m = live(*this, "Term::child");
  const detail::View v = detail::view_of(m, detail::node_of(*this));
  if (i >= v.children.size())
    detail::fail(ErrorCode::INDEX_OUT_OF_RANGE, "Term::child",
                 "index " + std::to_string(i) + " out of range [0, " +
                     std::to_string(v.children.size()) + ")",
                 0, {*this});
  return detail::make_term(m, v.children[i]);
}

std::vector<Term> Term::children() const
{
  ManagerImpl* m = live(*this, "Term::children");
  const detail::View v = detail::view_of(m, detail::node_of(*this));
  std::vector<Term> out;
  out.reserve(v.children.size());
  for (const ASTNode& c : v.children)
    out.push_back(detail::make_term(m, c));
  return out;
}

std::vector<std::uint32_t> Term::indices() const
{
  ManagerImpl* m = live(*this, "Term::indices");
  return detail::view_of(m, detail::node_of(*this)).indices;
}

std::uint64_t Term::id() const noexcept
{
  if (is_null())
    return 0;
  const ASTNode n = detail::node_of(*this);
  try
  {
    // weakly: the node's last release withdraws the id
    mgr_->bm->ExposeNode(n);
  }
  catch (...)
  {
    // out of memory registering the id: the id is still correct, only
    // term_from_id may not resolve it
  }
  return n.GetNodeNum();
}

TermManager Term::manager() const
{
  live(*this, "Term::manager");
  return TermManager(mgr_);
}

bool Term::is_value() const noexcept
{
  return !is_null() && detail::node_of(*this).isConstant();
}

bool Term::is_const() const noexcept
{
  if (is_null())
    return false;
  const ASTNode n = detail::node_of(*this);
  return (n.GetKind() == SYMBOL && !mgr_->is_const_array(n)) ||
         n.GetKind() == PARAMBOOL;
}

std::optional<std::string> Term::symbol() const
{
  ManagerImpl* m = live(*this, "Term::symbol");
  const ASTNode n = detail::node_of(*this);
  if (n.GetKind() != SYMBOL)
    return std::nullopt;
  auto it = m->names_by_node.find(n);
  if (it != m->names_by_node.end())
    return it->second;
  if (const UFDecl* d = m->decl_of(n))
    return d->name();
  if (m->is_const_array(n))
    return std::nullopt;
  return std::string(n.GetName());
}

// -- readers

bool Term::to_bool() const
{
  const ASTNode n = value_node(*this, "Term::to_bool");
  if (n.GetKind() == TRUE)
    return true;
  if (n.GetKind() == FALSE)
    return false;
  detail::fail(ErrorCode::SORT_MISMATCH, "Term::to_bool", "expected a Boolean value", 0, {*this},
               {sort()});
}

bool Term::fits_uint64() const
{
  const ASTNode n = bv_value_node(*this, "Term::fits_uint64");
  const std::string bits = detail::bv_bits_of(n);
  if (bits.size() <= 64)
    return true;
  return bits.find('1') == std::string::npos || bits.find('1') >= bits.size() - 64;
}

bool Term::fits_int64() const
{
  const ASTNode n = bv_value_node(*this, "Term::fits_int64");
  const std::string bits = detail::bv_bits_of(n);
  if (bits.size() <= 64)
    return true;
  // every bit above the low 64 must equal bit 63 (sign extension)
  const char sign = bits[bits.size() - 64];
  return bits.substr(0, bits.size() - 64).find(sign == '1' ? '0' : '1') == std::string::npos;
}

std::uint64_t Term::to_uint64() const
{
  const ASTNode n = bv_value_node(*this, "Term::to_uint64");
  if (!fits_uint64())
    detail::fail(ErrorCode::DOES_NOT_FIT, "Term::to_uint64",
                 "the value does not fit 64 bits; use the string, limb or bytes reader", 0,
                 {*this}, {sort()});
  return detail::bv_limbs_of(n)[0];
}

std::int64_t Term::to_int64() const
{
  const ASTNode n = bv_value_node(*this, "Term::to_int64");
  if (!fits_int64())
    detail::fail(ErrorCode::DOES_NOT_FIT, "Term::to_int64",
                 "the value does not fit a signed 64-bit integer; use the string, limb or "
                 "bytes reader",
                 0, {*this}, {sort()});
  const std::string bits = detail::bv_bits_of(n);
  std::uint64_t raw = detail::bv_limbs_of(n)[0];
  const std::size_t width = bits.size();
  if (width < 64 && bits[0] == '1')
    raw |= ~std::uint64_t(0) << width; // sign-extend the term's own width
  std::int64_t out;
  std::memcpy(&out, &raw, sizeof out);
  return out;
}

std::string Term::to_bv_string(int base, bool pad) const
{
  const ASTNode n = bv_value_node(*this, "Term::to_bv_string");
  const std::string bits = detail::bv_bits_of(n);
  switch (base)
  {
    case 2:
    {
      if (pad)
        return bits;
      const std::size_t first = bits.find('1');
      return first == std::string::npos ? "0" : bits.substr(first);
    }
    case 16:
    {
      const std::size_t digits = (bits.size() + 3) / 4;
      std::string padded = std::string(digits * 4 - bits.size(), '0') + bits;
      std::string out;
      for (std::size_t i = 0; i < digits; ++i)
      {
        int v = 0;
        for (int b = 0; b < 4; ++b)
          v = (v << 1) | (padded[i * 4 + b] - '0');
        out.push_back("0123456789abcdef"[v]);
      }
      if (!pad)
      {
        const std::size_t first = out.find_first_not_of('0');
        out = first == std::string::npos ? "0" : out.substr(first);
      }
      return out;
    }
    case 10:
    {
      // Unsigned, like the other bases: the constant library's own decimal
      // printer reads the top bit as a sign, which is to_int64's job.
      std::string out = "0";
      for (char bit : bits)
      {
        int carry = bit - '0';
        for (std::size_t j = out.size(); j-- > 0;)
        {
          const int v = (out[j] - '0') * 2 + carry;
          out[j] = static_cast<char>('0' + v % 10);
          carry = v / 10;
        }
        if (carry)
          out.insert(out.begin(), static_cast<char>('0' + carry));
      }
      return out;
    }
    default:
      break;
  }
  detail::fail(ErrorCode::INVALID_ARGUMENT, "Term::to_bv_string", "base must be 2, 10 or 16", 0);
}

std::vector<std::uint64_t> Term::to_bv_limbs() const
{
  return detail::bv_limbs_of(bv_value_node(*this, "Term::to_bv_limbs"));
}

std::vector<std::uint8_t> Term::to_bv_bytes(bool little_endian) const
{
  const ASTNode n = bv_value_node(*this, "Term::to_bv_bytes");
  const std::string bits = detail::bv_bits_of(n);
  const std::size_t count = (bits.size() + 7) / 8;
  std::vector<std::uint8_t> out(count, 0);
  for (std::size_t i = 0; i < bits.size(); ++i)
    if (bits[bits.size() - 1 - i] == '1')
      out[i / 8] |= static_cast<std::uint8_t>(1u << (i % 8));
  if (!little_endian)
    std::reverse(out.begin(), out.end());
  return out;
}

FloatValue Term::to_fp() const
{
  const ASTNode n = value_node(*this, "Term::to_fp");
  const SourceSort ss = n.GetSourceSort();
  if (ss.kind() != SourceSort::Kind::FloatingPoint)
    detail::fail(ErrorCode::SORT_MISMATCH, "Term::to_fp", "expected a floating-point value", 0,
                 {*this}, {sort()});
  if (ss.exponentWidth() > 64)
    detail::fail(ErrorCode::DOES_NOT_FIT, "Term::to_fp",
                 "a FloatValue holds an exponent of at most 64 bits; read the bits through "
                 "fp_to_ieee_bv",
                 0, {*this}, {sort()});
  return detail::fp_value_of(n, ss.exponentWidth(), ss.significandWidth());
}

RoundingMode Term::to_rm() const
{
  const ASTNode n = value_node(*this, "Term::to_rm");
  if (n.GetSourceSort().kind() != SourceSort::Kind::RoundingMode)
    detail::fail(ErrorCode::SORT_MISMATCH, "Term::to_rm", "expected a rounding-mode value", 0,
                 {*this}, {sort()});
  return detail::rm_of(n, "Term::to_rm");
}

RationalValue Term::to_rational() const
{
  const ASTNode n = value_node(*this, "Term::to_rational");
  if (n.GetKind() != REAL_CONST)
    detail::fail(ErrorCode::SORT_MISMATCH, "Term::to_rational", "expected a Real value", 0,
                 {*this}, {sort()});
  return detail::rational_of(n);
}

std::uint64_t Term::to_uninterpreted_index() const
{
  const ASTNode n = value_node(*this, "Term::to_uninterpreted_index");
  if (n.GetSourceSort().kind() != SourceSort::Kind::Uninterpreted)
    detail::fail(ErrorCode::SORT_MISMATCH, "Term::to_uninterpreted_index",
                 "expected a value of a declared sort", 0, {*this}, {sort()});
  return detail::bv_limbs_of(n)[0];
}

// -- sugar

Term Term::operator[](const Term& index) const
{
  return select(*this, index);
}

Term Term::operator()(std::initializer_list<Term> args) const
{
  return (*this)(std::vector<Term>(args));
}

Term Term::operator()(const std::vector<Term>& args) const
{
  std::vector<Term> all;
  all.reserve(args.size() + 1);
  all.push_back(*this);
  all.insert(all.end(), args.begin(), args.end());
  return apply(all);
}

Term Term::substitute(const std::vector<std::pair<Term, Term>>& map) const
{
  ManagerImpl* m = live(*this, "Term::substitute");
  std::unordered_map<ASTNode, ASTNode, ASTNode::ASTNodeHasher> memo;
  for (std::size_t i = 0; i < map.size(); ++i)
  {
    const Term& from = map[i].first;
    const Term& to = map[i].second;
    if (from.is_null() || to.is_null())
      detail::fail(ErrorCode::NULL_HANDLE, "Term::substitute", "a term in the map is null", 0);
    if (from.impl_manager() != m || to.impl_manager() != m)
      detail::fail(ErrorCode::FOREIGN_MANAGER, "Term::substitute",
                   "a term in the map belongs to another term manager", 0);
    if (from.sort() != to.sort())
      detail::fail(ErrorCode::SORT_MISMATCH, "Term::substitute",
                   "a replacement has a different sort from the term it replaces", 0,
                   {from, to}, {from.sort(), to.sort()});
    memo[detail::node_of(from)] = detail::node_of(to);
  }
  // The tree replaced in is the public one: each node is taken apart as
  // kind(), children() and indices() show it and, when a child changed, is
  // built again by the constructors. So a substitution meets the checks that
  // building the term by hand does (a Real division by zero is UNSUPPORTED,
  // not the engine's fatal error), a constant array's default is replaced in
  // as the child it is, and what the engine keeps as a child but the public
  // tree does not show -- an extract's bounds, say -- is never touched.
  // Bottom up with a stack of its own, so that depth costs no recursion.
  struct Frame
  {
    ASTNode node;
    detail::View view;
    bool expanded;
  };
  const ASTNode root = detail::node_of(*this);
  detail::engine_call(m, "Term::substitute", [&] {
    std::vector<Frame> stack;
    stack.push_back({root, {}, false});
    while (!stack.empty())
    {
      if (memo.count(stack.back().node) != 0)
      {
        stack.pop_back();
        continue;
      }
      if (!stack.back().expanded)
      {
        Frame& f = stack.back();
        f.view = detail::view_of(m, f.node);
        f.expanded = true;
        const std::vector<ASTNode> kids = f.view.children; // f dies with the pushes below
        for (auto it = kids.rbegin(); it != kids.rend(); ++it)
          if (memo.count(*it) == 0)
            stack.push_back({*it, {}, false});
        continue;
      }
      const Frame f = stack.back();
      stack.pop_back();
      std::vector<ASTNode> kids;
      kids.reserve(f.view.children.size());
      bool changed = false;
      for (const ASTNode& c : f.view.children)
      {
        kids.push_back(memo.at(c));
        changed = changed || !(kids.back() == c);
      }
      ASTNode out = f.node;
      if (changed)
      {
        const std::optional<std::uint32_t> sort =
            f.view.kind == Kind::CONST_ARRAY
                ? std::optional<std::uint32_t>(m->sort_of_node(f.node, "Term::substitute"))
                : std::nullopt;
        out = detail::build_term(m, "Term::substitute", f.view.kind, kids, f.view.indices, sort);
      }
      memo.emplace(f.node, out);
    }
  });
  return detail::make_term(m, memo.at(root));
}

std::string Term::str() const
{
  ManagerImpl* m = live(*this, "Term::str");
  return detail::print_term(m, detail::node_of(*this), Format::SMTLIB2, false);
}

std::string Term::to_string(Format f, bool share) const
{
  ManagerImpl* m = live(*this, "Term::to_string");
  return detail::print_term(m, detail::node_of(*this), f, share);
}

bool Term::same_as(const Term& o) const noexcept
{
  return node_ == o.node_;
}

bool Term::Less::operator()(const Term& a, const Term& b) const noexcept
{
  if (a.impl_manager() != b.impl_manager())
    return a.impl_manager() < b.impl_manager();
  if (a.is_null() || b.is_null())
    return a.is_null() && !b.is_null();
  return detail::node_of(a).GetNodeNum() < detail::node_of(b).GetNodeNum();
}

Term operator==(const Term& a, const Term& b)
{
  return eq(a, b);
}

Term operator!=(const Term& a, const Term& b)
{
  return distinct(a, b);
}

std::ostream& operator<<(std::ostream& os, const Term& t)
{
  if (t.is_null())
    return os << "<null term>";
  return os << t.str();
}

// ============================================================ FloatValue, RationalValue

std::string FloatValue::bits() const
{
  std::string out;
  out.push_back(sign ? '1' : '0');
  for (std::uint32_t i = exp_size; i-- > 0;)
    out.push_back(((biased_exponent >> i) & 1) ? '1' : '0');
  const std::uint32_t t = sig_size - 1;
  for (std::uint32_t i = t; i-- > 0;)
  {
    const std::uint64_t limb = i / 64 < significand.size() ? significand[i / 64] : 0;
    out.push_back(((limb >> (i % 64)) & 1) ? '1' : '0');
  }
  return out;
}

std::optional<double> FloatValue::to_double() const
{
  if (exp_size > 11 || sig_size > 53)
    return std::nullopt;
  if (cls == Class::NOT_A_NUMBER)
    return std::nan("");
  const double s = sign ? -1.0 : 1.0;
  if (cls == Class::INF)
    return s * HUGE_VAL;
  if (cls == Class::ZERO)
    return s * 0.0;
  // value = (-1)^sign * (hidden + fraction/2^(t)) * 2^(exp - bias)
  const std::uint32_t t = sig_size - 1;
  const std::uint64_t frac = significand.empty() ? 0 : significand[0];
  const int bias = (1 << (exp_size - 1)) - 1;
  double mant = static_cast<double>(frac) / std::ldexp(1.0, static_cast<int>(t));
  int exponent;
  if (cls == Class::SUBNORMAL)
    exponent = 1 - bias;
  else
  {
    mant += 1.0;
    exponent = static_cast<int>(biased_exponent) - bias;
  }
  return s * std::ldexp(mant, exponent);
}

std::optional<RationalValue> FloatValue::to_rational() const
{
  if (cls == Class::NOT_A_NUMBER || cls == Class::INF)
    return std::nullopt;
  RationalValue r;
  if (cls == Class::ZERO)
  {
    r.numerator = "0";
    r.denominator = "1";
    return r;
  }
  const char* fn = "FloatValue::to_rational";
  if (exp_size < 2 || exp_size > 64 || sig_size < 2 ||
      significand.size() < (std::uint64_t{sig_size} - 1 + 63) / 64)
    detail::fail(ErrorCode::INVALID_ARGUMENT, fn,
                 "the fields do not describe a value of a floating-point format");
  // value = m * 2^e2, m the integer significand (with the hidden bit of a
  // normal value), e2 = exponent - bias - t
  const std::uint32_t t = sig_size - 1;
  const std::uint64_t bias = (std::uint64_t{1} << (exp_size - 1)) - 1;
  const std::uint64_t exponent = cls == Class::SUBNORMAL ? 1 : biased_exponent;
  // Past this many bits a numerator or denominator is refused rather than
  // written out: about five million decimal digits.
  constexpr std::uint64_t limit = std::uint64_t{1} << 24;
  const std::uint64_t distance = exponent >= bias ? exponent - bias : bias - exponent;
  if (distance > limit || t > limit)
    detail::fail(ErrorCode::UNSUPPORTED, fn,
                 "the exact rational of this value has more than 2^24 bits");
  std::int64_t e2 = (exponent >= bias ? static_cast<std::int64_t>(distance)
                                      : -static_cast<std::int64_t>(distance)) -
                    static_cast<std::int64_t>(t);
  std::string m;
  m.reserve(t + 1);
  m.push_back(cls == Class::SUBNORMAL ? '0' : '1');
  for (std::uint32_t i = t; i-- > 0;)
    m.push_back(((significand[i / 64] >> (i % 64)) & 1) != 0 ? '1' : '0');
  // trailing zero bits move into the exponent
  const std::size_t last = m.find_last_of('1');
  if (last == std::string::npos)
  {
    r.numerator = "0";
    r.denominator = "1";
    return r;
  }
  e2 += static_cast<std::int64_t>(m.size() - 1 - last);
  m.erase(last + 1);
  std::string num, den = "1", err;
  const bool ok =
      binaryTimesPowerOfTwoToDecimal(m, e2 > 0 ? static_cast<std::uint64_t>(e2) : 0, num, err) &&
      (e2 >= 0 || binaryTimesPowerOfTwoToDecimal("1", static_cast<std::uint64_t>(-e2), den, err));
  if (!ok)
    throw std::bad_alloc(); // the digits are well formed: only memory can fail
  r.numerator = (sign ? "-" : "") + num;
  r.denominator = den;
  return r;
}

bool RationalValue::fits_int64() const
{
  auto fits = [](const std::string& s) {
    try
    {
      std::size_t used = 0;
      (void)std::stoll(s, &used);
      return used == s.size();
    }
    catch (...)
    {
      return false;
    }
  };
  return fits(numerator) && fits(denominator);
}

std::int64_t RationalValue::num64() const
{
  if (!fits_int64())
    detail::fail(ErrorCode::DOES_NOT_FIT, "RationalValue::num64",
                 "the numerator does not fit a signed 64-bit integer");
  return std::stoll(numerator);
}

std::int64_t RationalValue::den64() const
{
  if (!fits_int64())
    detail::fail(ErrorCode::DOES_NOT_FIT, "RationalValue::den64",
                 "the denominator does not fit a signed 64-bit integer");
  return std::stoll(denominator);
}

double RationalValue::to_double() const
{
  try
  {
    return std::stod(numerator) / std::stod(denominator);
  }
  catch (...)
  {
    return std::nan("");
  }
}

std::string RationalValue::str() const
{
  if (denominator == "1")
    return numerator;
  return numerator + "/" + denominator;
}

} // namespace api
} // namespace stp

std::size_t std::hash<stp::api::Term>::operator()(const stp::api::Term& t) const noexcept
{
  if (t.is_null())
    return 0;
  const std::uint64_t id = stp::api::detail::node_of(t).GetNodeNum();
  const std::uint64_t mgr = t.impl_manager()->id;
  return static_cast<std::size_t>((id * 0x9E3779B97F4A7C15ull) ^ (mgr * 0xC2B2AE3D27D4EB4Full));
}

std::size_t std::hash<stp::api::Sort>::operator()(const stp::api::Sort& s) const noexcept
{
  if (s.is_null())
    return 0;
  return static_cast<std::size_t>((s.id() * 0x9E3779B97F4A7C15ull) ^
                                  (s.impl_manager()->id * 0xC2B2AE3D27D4EB4Full));
}
