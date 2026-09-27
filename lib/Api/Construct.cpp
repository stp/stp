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

// Construct.cpp -- term construction: the type checker for every public kind
// and the mapping of each onto the engine's node kinds; the named
// constructors, the literal helpers and the operators.

#include "Internal.h"

#include "stp/Extensionality/ExtensionalityContext.h"
#include "stp/FloatBlaster/DecimalLiteral.h"
#include "stp/FloatBlaster/FloatBlaster.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/UninterpretedFunctions/UFDecl.h"

#include <cmath>
#include <cstring>

namespace stp
{
namespace api
{
namespace detail
{

namespace
{

struct Ctx
{
  ManagerImpl* m;
  const char* fn;
  Kind k;
  const std::vector<ASTNode>& args;
  const std::vector<std::uint32_t>& idx;

  STPMgr* bm() const { return m->bm; }
  NodeFactory* f() const { return m->factory(); }
  Term term(std::size_t i) const { return make_term(m, args[i]); }
  std::uint32_t sort(std::size_t i) const { return m->sort_of_node(args[i], fn); }
  const SortRec& rec(std::size_t i) const { return m->rec(sort(i)); }
  SortKind skind(std::size_t i) const { return rec(i).kind; }

  [[noreturn]] void mismatch(std::size_t i, const std::string& expected) const
  {
    fail(ErrorCode::SORT_MISMATCH, fn,
         std::string("argument ") + std::to_string(i) + " has sort " +
             m->sort_text(sort(i)) + ", expected " + expected + " (" +
             kind_spec(k).name + ": " + kind_spec(k).sig + ")",
         static_cast<int>(i), {term(i)}, {make_sort(m, sort(i))});
  }
  [[noreturn]] void unsupported(const std::string& what) const
  {
    std::vector<Term> ts;
    for (std::size_t i = 0; i < args.size(); ++i)
      ts.push_back(term(i));
    fail(ErrorCode::UNSUPPORTED, fn, what, std::nullopt, ts);
  }

  void expect_bool(std::size_t i) const
  {
    if (skind(i) != SortKind::BOOL)
      mismatch(i, "Bool");
  }
  std::uint32_t expect_bv(std::size_t i) const
  {
    if (skind(i) != SortKind::BV)
      mismatch(i, "a bit-vector");
    return rec(i).a;
  }
  void expect_fp(std::size_t i) const
  {
    if (skind(i) != SortKind::FP)
      mismatch(i, "a floating-point number");
  }
  void expect_rm(std::size_t i) const
  {
    if (skind(i) != SortKind::RM)
      mismatch(i, "a rounding mode");
  }
  void expect_real(std::size_t i) const
  {
    if (skind(i) != SortKind::REAL)
      mismatch(i, "a Real");
  }
  void expect_array(std::size_t i) const
  {
    if (skind(i) != SortKind::ARRAY)
      mismatch(i, "an array");
  }
  void expect_same(std::size_t i, std::size_t j) const
  {
    if (sort(i) != sort(j))
      fail(ErrorCode::SORT_MISMATCH, fn,
           std::string("argument ") + std::to_string(j) + " has sort " + m->sort_text(sort(j)) +
               ", expected " + m->sort_text(sort(i)) + " to match argument " +
               std::to_string(i) + " (" + kind_spec(k).name + ": " + kind_spec(k).sig + ")",
           static_cast<int>(j), {term(i), term(j)},
           {make_sort(m, sort(j)), make_sort(m, sort(i))});
  }
  void expect_all_same_from(std::size_t first) const
  {
    for (std::size_t i = first + 1; i < args.size(); ++i)
      expect_same(first, i);
  }
  void expect_all_bv_same() const
  {
    expect_bv(0);
    expect_all_same_from(0);
  }
  void expect_all_fp_same(std::size_t first) const
  {
    expect_fp(first);
    expect_all_same_from(first);
  }

  ASTNode c32(unsigned v) const { return bm()->CreateBVConst(32, v); }

  ASTNode bv_term(Kind_t ek, std::uint32_t width, const ASTVec& kids) const
  {
    return f()->CreateTerm(ek, width, kids);
  }
  ASTNode node(Kind_t ek, const ASTVec& kids) const { return f()->CreateNode(ek, kids); }
  ASTNode fp_term(Kind_t ek, std::size_t fmt_arg, const ASTVec& kids) const
  {
    const SortRec& r = rec(fmt_arg);
    return FloatBlaster::withFormat(bm(), f()->CreateTerm(ek, r.a + r.b, kids), r.a, r.b);
  }
};

ASTNode real_term(const Ctx& c, Kind_t ek, const ASTVec& kids)
{
  try
  {
    return c.bm()->CreateRealTerm(ek, kids);
  }
  catch (const stp::EngineFatal&)
  {
    throw;
  }
  catch (const std::exception& failure)
  {
    c.unsupported(std::string("Real arithmetic: ") + failure.what());
  }
}

ASTNode real_pred(const Ctx& c, Kind_t ek, const ASTNode& a, const ASTNode& b)
{
  try
  {
    return c.bm()->CreateRealPredicate(ek, a, b);
  }
  catch (const stp::EngineFatal&)
  {
    throw;
  }
  catch (const std::exception& failure)
  {
    c.unsupported(std::string("Real arithmetic: ") + failure.what());
  }
}

ASTNode concat2(const Ctx& c, const ASTNode& a, const ASTNode& b)
{
  return c.f()->CreateTerm(BVCONCAT, a.GetValueWidth() + b.GetValueWidth(), a, b);
}

ASTNode extract(const Ctx& c, const ASTNode& x, unsigned hi, unsigned lo)
{
  return c.f()->CreateTerm(BVEXTRACT, hi - lo + 1, x, c.c32(hi), c.c32(lo));
}

// An equality of two operands of the same sort, by sort.
ASTNode equality(const Ctx& c, std::size_t i, std::size_t j)
{
  const ASTNode& a = c.args[i];
  const ASTNode& b = c.args[j];
  switch (c.skind(i))
  {
    case SortKind::BOOL: return c.node(IFF, {a, b});
    case SortKind::FP: return c.node(FP_SMT_EQ, {a, b});
    case SortKind::REAL: return real_pred(c, EQ, a, b);
    case SortKind::ARRAY:
    {
      if (c.m->array_equality_off)
        c.unsupported("array equality was switched off (array-equality = off)");
      // The factory builds the opaque ARRAY_EQ node; the solve boundary lowers it.
      c.bm()->UserFlags.enable_array_equality = true;
      c.m->array_equality_seen = true;
      return c.node(EQ, {a, b});
    }
    case SortKind::FUN:
      c.unsupported("equality between functions");
    default:
      return c.node(EQ, {a, b});
  }
}

ASTNode to_fp_node(const Ctx& c, Kind_t ek, std::uint32_t e, std::uint32_t s, const ASTNode* rm,
                   const ASTNode& src)
{
  ASTVec kids;
  kids.push_back(c.c32(e));
  kids.push_back(c.c32(s));
  if (rm != nullptr)
    kids.push_back(*rm);
  kids.push_back(src);
  return FloatBlaster::withFormat(c.bm(), c.f()->CreateTerm(ek, e + s, kids), e, s);
}

ASTNode fp_from_real_value(const Ctx& c, std::uint32_t e, std::uint32_t s, const ASTNode& rm,
                           const ASTNode& real)
{
  if (rm.GetKind() != BVCONST)
    c.unsupported("converting a Real to a float needs a rounding-mode value, not a symbolic "
                  "mode");
  if (real.GetKind() != REAL_CONST)
    c.unsupported("converting a Real to a float needs a Real value; the engine folds this "
                  "conversion exactly and has no symbolic form (capabilities: "
                  "kind.FP_TO_FP_FROM_REAL = values-only)");
  const RationalValue q = rational_of(real);
  std::string num = q.numerator;
  bool negative = false;
  if (!num.empty() && num[0] == '-')
  {
    negative = true;
    num.erase(0, 1);
  }
  std::string bits, err;
  if (!rationalToPackedFPBits(num, q.denominator, negative, e, s, rm.GetUnsignedConst(), bits,
                              err))
    c.unsupported(err);
  return c.m->fp_const_from_bits(e, s, c.m->bv_const_bits(e + s, bits));
}

} // namespace

ASTNode build_term_impl(ManagerImpl* m, const char* fn, Kind k, const std::vector<ASTNode>& args,
                        const std::vector<std::uint32_t>& idx,
                        std::optional<std::uint32_t> result_sort);

// Every construction funnels through here, inside an engine scope: the
// factories' rewrite rules are engine code, and an invariant they trip is
// INTERNAL and poisons the manager rather than ending the process.
ASTNode build_term(ManagerImpl* m, const char* fn, Kind k, const std::vector<ASTNode>& args,
                   const std::vector<std::uint32_t>& idx,
                   std::optional<std::uint32_t> result_sort)
{
  return engine_call(m, fn, [&] { return build_term_impl(m, fn, k, args, idx, result_sort); });
}

ASTNode build_term_impl(ManagerImpl* m, const char* fn, Kind k, const std::vector<ASTNode>& args,
                        const std::vector<std::uint32_t>& idx,
                        std::optional<std::uint32_t> result_sort)
{
  const KindSpec& spec = kind_spec(k);
  const int n = static_cast<int>(args.size());
  if (n < spec.min_arity || (spec.max_arity >= 0 && n > spec.max_arity))
  {
    std::string expected = spec.max_arity < 0 ? "at least " + std::to_string(spec.min_arity)
                           : spec.min_arity == spec.max_arity
                               ? std::to_string(spec.min_arity)
                               : std::to_string(spec.min_arity) + " to " + std::to_string(spec.max_arity);
    std::vector<Term> ts;
    for (const ASTNode& a : args)
      ts.push_back(make_term(m, a));
    fail(ErrorCode::ARITY, fn,
         std::string(spec.name) + " takes " + expected + " arguments, " + std::to_string(n) +
             " given",
         std::nullopt, ts);
  }
  if (static_cast<int>(idx.size()) != spec.indices)
    fail(ErrorCode::ARITY, fn,
         std::string(spec.name) + " takes " + std::to_string(spec.indices) + " indices, " +
             std::to_string(idx.size()) + " given");
  for (const ASTNode& a : args)
    if (!a.IsOwnedBy(m->bm))
      fail(ErrorCode::FOREIGN_MANAGER, fn, "a term belongs to another term manager");

  const Ctx c{m, fn, k, args, idx};
  ASTVec kids(args.begin(), args.end());

  switch (k)
  {
    case Kind::VALUE:
    case Kind::CONSTANT:
      fail(ErrorCode::INVALID_ARGUMENT, fn,
           std::string(spec.name) + " is not constructed by mk_term: use the value "
                                    "constructors, declare or mk_fresh");

    // ------------------------------------------------------------ core
    case Kind::ITE:
    {
      c.expect_bool(0);
      c.expect_same(1, 2);
      switch (c.skind(1))
      {
        case SortKind::BOOL: return c.node(ITE, kids);
        case SortKind::REAL: return real_term(c, ITE, kids);
        case SortKind::FUN: c.unsupported("an if-then-else between functions");
        case SortKind::ARRAY:
        {
          const SortRec& r = c.rec(1);
          const SortRec& er = m->rec(r.element);
          ASTNode out = c.f()->CreateArrayTerm(ITE, args[1].GetIndexWidth(),
                                               args[1].GetValueWidth(), kids);
          if (er.kind == SortKind::FP && out.GetExpWidth() == 0)
            out = FloatBlaster::withFormat(m->bm, out, er.a, er.b);
          return out;
        }
        case SortKind::FP: return c.fp_term(ITE, 1, kids);
        default: return c.bv_term(ITE, args[1].GetValueWidth(), kids);
      }
    }
    case Kind::EQUAL:
      c.expect_same(0, 1);
      return equality(c, 0, 1);
    case Kind::DISTINCT:
    {
      c.expect_all_same_from(0);
      const SortKind sk = c.skind(0);
      if (sk == SortKind::BV || sk == SortKind::BOOL || sk == SortKind::RM ||
          sk == SortKind::UNINTERPRETED)
        return c.node(DISTINCT, kids);
      if (sk == SortKind::FUN)
        c.unsupported("distinct over functions");
      // pairwise for the sorts whose equality is not the carrier's
      ASTVec conj;
      for (std::size_t i = 0; i < args.size(); ++i)
        for (std::size_t j = i + 1; j < args.size(); ++j)
          conj.push_back(c.node(NOT, {equality(c, i, j)}));
      return conj.size() == 1 ? conj[0] : c.node(AND, conj);
    }
    case Kind::APPLY:
    {
      if (c.skind(0) != SortKind::FUN)
        c.mismatch(0, "a function symbol");
      const SortRec& fr = c.rec(0);
      if (fr.domain.size() != args.size() - 1)
        fail(ErrorCode::ARITY, fn,
             "the function takes " + std::to_string(fr.domain.size()) + " arguments, " +
                 std::to_string(args.size() - 1) + " given",
             std::nullopt, {c.term(0)});
      for (std::size_t i = 1; i < args.size(); ++i)
        if (c.sort(i) != fr.domain[i - 1])
          c.mismatch(i, m->sort_text(fr.domain[i - 1]));
      const UFDecl* decl = m->decl_of(args[0]);
      if (decl == nullptr)
        c.mismatch(0, "a declared function symbol");
      std::string diagnostic;
      ASTVec actuals(kids.begin() + 1, kids.end());
      // An application is always constructible (uninterpreted-functions only
      // forces the machinery on or off at the check): the engine's apply
      // wants the switch on, as declare does.
      m->bm->UserFlags.enable_uninterpreted_functions = true;
      ASTNode out = m->bm->getUFContext()->apply(decl, actuals, &diagnostic);
      if (out.GetKind() == UNDEFINED)
        fail(ErrorCode::INVALID_ARGUMENT, fn, diagnostic);
      return out;
    }

    // ------------------------------------------------------------ Bool
    case Kind::NOT:
      c.expect_bool(0);
      return c.node(NOT, kids);
    case Kind::AND:
    case Kind::OR:
    case Kind::XOR:
      for (std::size_t i = 0; i < args.size(); ++i)
        c.expect_bool(i);
      if (args.size() == 1)
        return args[0];
      return c.node(k == Kind::AND ? AND : k == Kind::OR ? OR : XOR, kids);
    case Kind::IMPLIES:
      c.expect_bool(0);
      c.expect_bool(1);
      return c.node(IMPLIES, kids);

    // ------------------------------------------------------------ BV bitwise
    case Kind::BV_NOT:
      return c.bv_term(BVNOT, c.expect_bv(0), kids);
    case Kind::BV_AND:
    case Kind::BV_OR:
    case Kind::BV_XOR:
    {
      c.expect_all_bv_same();
      const std::uint32_t w = c.rec(0).a;
      return c.bv_term(k == Kind::BV_AND ? BVAND : k == Kind::BV_OR ? BVOR : BVXOR, w, kids);
    }
    case Kind::BV_NAND:
    case Kind::BV_NOR:
    case Kind::BV_XNOR:
    {
      c.expect_all_bv_same();
      const std::uint32_t w = c.rec(0).a;
      const ASTNode inner =
          c.bv_term(k == Kind::BV_NAND ? BVAND : k == Kind::BV_NOR ? BVOR : BVXOR, w, kids);
      return c.bv_term(BVNOT, w, {inner});
    }

    // ------------------------------------------------------------ BV arithmetic
    case Kind::BV_NEG:
      return c.bv_term(BVUMINUS, c.expect_bv(0), kids);
    case Kind::BV_ADD:
    case Kind::BV_MUL:
    {
      c.expect_all_bv_same();
      return c.bv_term(k == Kind::BV_ADD ? BVPLUS : BVMULT, c.rec(0).a, kids);
    }
    case Kind::BV_SUB:
    case Kind::BV_UDIV:
    case Kind::BV_UREM:
    case Kind::BV_SDIV:
    case Kind::BV_SREM:
    case Kind::BV_SMOD:
    case Kind::BV_SHL:
    case Kind::BV_LSHR:
    case Kind::BV_ASHR:
    {
      c.expect_all_bv_same();
      Kind_t ek = BVSUB;
      switch (k)
      {
        case Kind::BV_SUB: ek = BVSUB; break;
        case Kind::BV_UDIV: ek = BVDIV; break;
        case Kind::BV_UREM: ek = BVMOD; break;
        case Kind::BV_SDIV: ek = SBVDIV; break;
        case Kind::BV_SREM: ek = SBVREM; break;
        case Kind::BV_SMOD: ek = SBVMOD; break;
        case Kind::BV_SHL: ek = BVLEFTSHIFT; break;
        case Kind::BV_LSHR: ek = BVRIGHTSHIFT; break;
        default: ek = BVSRSHIFT; break;
      }
      return c.bv_term(ek, c.rec(0).a, kids);
    }

    // ------------------------------------------------------------ BV structure
    case Kind::BV_CONCAT:
    {
      for (std::size_t i = 0; i < args.size(); ++i)
        c.expect_bv(i);
      ASTNode out = args[0];
      for (std::size_t i = 1; i < args.size(); ++i)
        out = concat2(c, out, args[i]);
      return out;
    }
    case Kind::BV_EXTRACT:
    {
      const std::uint32_t w = c.expect_bv(0);
      const std::uint32_t hi = idx[0], lo = idx[1];
      if (hi >= w || lo > hi)
        fail(ErrorCode::INDEX_OUT_OF_RANGE, fn,
             "extract [" + std::to_string(hi) + ", " + std::to_string(lo) +
                 "] needs width > hi >= lo (width " + std::to_string(w) + ")",
             std::nullopt, {c.term(0)});
      return extract(c, args[0], hi, lo);
    }
    case Kind::BV_ZERO_EXTEND:
    case Kind::BV_SIGN_EXTEND:
    {
      const std::uint32_t w = c.expect_bv(0);
      if (idx[0] == 0)
        return args[0];
      const std::uint32_t nw = w + idx[0];
      return c.bv_term(k == Kind::BV_ZERO_EXTEND ? BVZX : BVSX, nw, {args[0], c.c32(nw)});
    }
    case Kind::BV_REPEAT:
    {
      c.expect_bv(0);
      if (idx[0] == 0)
        fail(ErrorCode::INDEX_OUT_OF_RANGE, fn, "repeat needs k >= 1", std::nullopt, {c.term(0)});
      ASTNode out = args[0];
      for (std::uint32_t i = 1; i < idx[0]; ++i)
        out = concat2(c, out, args[0]);
      return out;
    }
    case Kind::BV_ROTATE_LEFT:
    case Kind::BV_ROTATE_RIGHT:
    {
      const std::uint32_t w = c.expect_bv(0);
      std::uint32_t r = idx[0] % w;
      if (k == Kind::BV_ROTATE_RIGHT)
        r = (w - r) % w;
      if (r == 0)
        return args[0];
      // rotate left by r: low w-r bits move up, top r bits move down
      return concat2(c, extract(c, args[0], w - 1 - r, 0), extract(c, args[0], w - 1, w - r));
    }

    // ------------------------------------------------------------ BV comparison
    case Kind::BV_COMP:
    {
      c.expect_all_bv_same();
      const ASTNode e = c.node(EQ, kids);
      return c.bv_term(ITE, 1, {e, m->bm->CreateOneConst(1), m->bm->CreateZeroConst(1)});
    }
    case Kind::BV_ULT:
    case Kind::BV_ULE:
    case Kind::BV_UGT:
    case Kind::BV_UGE:
    case Kind::BV_SLT:
    case Kind::BV_SLE:
    case Kind::BV_SGT:
    case Kind::BV_SGE:
    case Kind::BV_UADDO:
    case Kind::BV_SADDO:
    case Kind::BV_UMULO:
    case Kind::BV_SMULO:
    case Kind::BV_USUBO:
    case Kind::BV_SSUBO:
    {
      c.expect_all_bv_same();
      Kind_t ek = BVLT;
      switch (k)
      {
        case Kind::BV_ULT: ek = BVLT; break;
        case Kind::BV_ULE: ek = BVLE; break;
        case Kind::BV_UGT: ek = BVGT; break;
        case Kind::BV_UGE: ek = BVGE; break;
        case Kind::BV_SLT: ek = BVSLT; break;
        case Kind::BV_SLE: ek = BVSLE; break;
        case Kind::BV_SGT: ek = BVSGT; break;
        case Kind::BV_SGE: ek = BVSGE; break;
        case Kind::BV_UADDO: ek = BVUADDO; break;
        case Kind::BV_SADDO: ek = BVSADDO; break;
        case Kind::BV_UMULO: ek = BVUMULO; break;
        case Kind::BV_SMULO: ek = BVSMULO; break;
        case Kind::BV_USUBO: ek = BVUSUBO; break;
        default: ek = BVSSUBO; break;
      }
      return c.node(ek, kids);
    }
    case Kind::BV_NEGO:
    {
      const std::uint32_t w = c.expect_bv(0);
      std::string bits(w, '0');
      bits[0] = '1';
      return c.node(EQ, {args[0], m->bv_const_bits(w, bits)});
    }
    case Kind::BV_SDIVO:
    {
      c.expect_all_bv_same();
      const std::uint32_t w = c.rec(0).a;
      std::string bits(w, '0');
      bits[0] = '1';
      return c.node(AND, {c.node(EQ, {args[0], m->bv_const_bits(w, bits)}),
                          c.node(EQ, {args[1], m->bm->CreateMaxConst(w)})});
    }
    case Kind::BV_REDAND:
    {
      const std::uint32_t w = c.expect_bv(0);
      const ASTNode all = c.node(EQ, {args[0], m->bm->CreateMaxConst(w)});
      return c.bv_term(ITE, 1, {all, m->bm->CreateOneConst(1), m->bm->CreateZeroConst(1)});
    }
    case Kind::BV_REDOR:
    {
      const std::uint32_t w = c.expect_bv(0);
      const ASTNode none = c.node(EQ, {args[0], m->bm->CreateZeroConst(w)});
      return c.bv_term(ITE, 1, {none, m->bm->CreateZeroConst(1), m->bm->CreateOneConst(1)});
    }

    // ------------------------------------------------------------ arrays
    case Kind::SELECT:
    {
      c.expect_array(0);
      const SortRec& r = c.rec(0);
      if (c.sort(1) != r.index)
        c.mismatch(1, m->sort_text(r.index));
      // A read of a constant array (through any store chain and ite) folds
      // to the default in the engine's hashing factory, in both
      // construction modes.
      const SortRec& er = c.m->rec(r.element);
      ASTNode out = c.f()->CreateTerm(READ, args[0].GetValueWidth(), args[0], args[1]);
      if (er.kind == SortKind::FP && out.GetExpWidth() == 0)
        out = FloatBlaster::withFormat(c.bm(), out, er.a, er.b);
      return out;
    }
    case Kind::STORE:
    {
      c.expect_array(0);
      const SortRec& r = c.rec(0);
      if (c.sort(1) != r.index)
        c.mismatch(1, m->sort_text(r.index));
      if (c.sort(2) != r.element)
        c.mismatch(2, m->sort_text(r.element));
      const SortRec& er = m->rec(r.element);
      ASTNode out = c.f()->CreateArrayTerm(WRITE, args[0].GetIndexWidth(), args[0].GetValueWidth(),
                                           kids);
      if (er.kind == SortKind::FP && out.GetExpWidth() == 0)
        out = FloatBlaster::withFormat(m->bm, out, er.a, er.b);
      return out;
    }
    case Kind::CONST_ARRAY:
    {
      if (!result_sort.has_value())
        fail(ErrorCode::INVALID_ARGUMENT, fn, "CONST_ARRAY needs its array sort (result_sort)");
      const SortRec& r = m->rec(*result_sort);
      if (r.kind != SortKind::ARRAY)
        fail(ErrorCode::SORT_MISMATCH, fn, "the result sort of CONST_ARRAY must be an array sort",
             std::nullopt, {}, {make_sort(m, *result_sort)});
      if (c.sort(0) != r.element)
        c.mismatch(0, m->sort_text(r.element));
      // The engine registers the symbol with its default and interns by
      // (sort, default), so the same request from a script or another
      // call gives the same term.
      return m->bm->CreateConstArray(r.source, args[0]);
    }

    // ------------------------------------------------------------ FP arithmetic
    case Kind::FP_ABS:
    case Kind::FP_NEG:
      c.expect_fp(0);
      return c.fp_term(k == Kind::FP_ABS ? FP_ABS : FP_NEG, 0, kids);
    case Kind::FP_ADD:
    case Kind::FP_SUB:
    case Kind::FP_MUL:
    case Kind::FP_DIV:
    case Kind::FP_FMA:
    {
      c.expect_rm(0);
      c.expect_all_fp_same(1);
      Kind_t ek = FP_ADD;
      switch (k)
      {
        case Kind::FP_ADD: ek = FP_ADD; break;
        case Kind::FP_SUB: ek = FP_SUB; break;
        case Kind::FP_MUL: ek = FP_MUL; break;
        case Kind::FP_DIV: ek = FP_DIV; break;
        default: ek = FP_FMA; break;
      }
      return c.fp_term(ek, 1, kids);
    }
    case Kind::FP_SQRT:
    case Kind::FP_RTI:
      c.expect_rm(0);
      c.expect_fp(1);
      return c.fp_term(k == Kind::FP_SQRT ? FP_SQRT : FP_ROUNDTOINTEGRAL, 1, kids);
    case Kind::FP_REM:
    {
      c.expect_all_fp_same(0);
      const SortRec& r = c.rec(0);
      // fp.rem's circuit unrolls one divide step per representable exponent
      if (r.a >= 12 && ((std::uint64_t(1) << r.a) + r.b - 4) > 2304)
        c.unsupported("fp.rem is not supported for this format (capabilities: fp.rem.limit)");
      return c.fp_term(FP_REM, 0, kids);
    }
    case Kind::FP_MIN:
    case Kind::FP_MAX:
      c.expect_all_fp_same(0);
      return c.fp_term(k == Kind::FP_MIN ? FP_MIN : FP_MAX, 0, kids);

    // ------------------------------------------------------------ FP predicates
    case Kind::FP_EQ:
    case Kind::FP_LT:
    case Kind::FP_LEQ:
    case Kind::FP_GT:
    case Kind::FP_GEQ:
    {
      c.expect_all_fp_same(0);
      Kind_t ek = FP_EQ;
      switch (k)
      {
        case Kind::FP_EQ: ek = FP_EQ; break;
        case Kind::FP_LT: ek = FP_LT; break;
        case Kind::FP_LEQ: ek = FP_LEQ; break;
        case Kind::FP_GT: ek = FP_GT; break;
        default: ek = FP_GEQ; break;
      }
      return c.node(ek, kids);
    }
    case Kind::FP_IS_NORMAL:
    case Kind::FP_IS_SUBNORMAL:
    case Kind::FP_IS_ZERO:
    case Kind::FP_IS_INF:
    case Kind::FP_IS_NAN:
    case Kind::FP_IS_NEG:
    case Kind::FP_IS_POS:
    {
      c.expect_fp(0);
      Kind_t ek = FP_ISNORMAL;
      switch (k)
      {
        case Kind::FP_IS_NORMAL: ek = FP_ISNORMAL; break;
        case Kind::FP_IS_SUBNORMAL: ek = FP_ISSUBNORMAL; break;
        case Kind::FP_IS_ZERO: ek = FP_ISZERO; break;
        case Kind::FP_IS_INF: ek = FP_ISINFINITE; break;
        case Kind::FP_IS_NAN: ek = FP_ISNAN; break;
        case Kind::FP_IS_NEG: ek = FP_ISNEGATIVE; break;
        default: ek = FP_ISPOSITIVE; break;
      }
      return c.node(ek, kids);
    }

    // ------------------------------------------------------------ FP construction and conversion
    case Kind::FP_FP:
    {
      const std::uint32_t sw = c.expect_bv(0);
      const std::uint32_t ew = c.expect_bv(1);
      const std::uint32_t mw = c.expect_bv(2);
      if (sw != 1)
        c.mismatch(0, "a 1-bit sign");
      if (ew < 2 || mw < 1)
        fail(ErrorCode::SORT_MISMATCH, fn,
             "fp needs an exponent of at least 2 bits and a significand of at least 1 bit",
             1, {c.term(1), c.term(2)});
      const ASTNode bits = concat2(c, concat2(c, args[0], args[1]), args[2]);
      return to_fp_node(c, FP_TOFP, ew, mw + 1, nullptr, bits);
    }
    case Kind::FP_TO_FP_FROM_BV:
    {
      const std::uint32_t w = c.expect_bv(0);
      if (idx[0] < 2 || idx[1] < 2)
        fail(ErrorCode::INDEX_OUT_OF_RANGE, fn, "a floating-point format needs e >= 2 and s >= 2");
      if (w != idx[0] + idx[1])
        c.mismatch(0, "a bit-vector of " + std::to_string(idx[0] + idx[1]) + " bits");
      return to_fp_node(c, FP_TOFP, idx[0], idx[1], nullptr, args[0]);
    }
    case Kind::FP_TO_FP_FROM_FP:
    case Kind::FP_TO_FP_FROM_SBV:
    case Kind::FP_TO_FP_FROM_UBV:
    case Kind::FP_TO_FP_FROM_REAL:
    {
      c.expect_rm(0);
      if (idx[0] < 2 || idx[1] < 2)
        fail(ErrorCode::INDEX_OUT_OF_RANGE, fn, "a floating-point format needs e >= 2 and s >= 2");
      if (k == Kind::FP_TO_FP_FROM_FP)
      {
        c.expect_fp(1);
        return to_fp_node(c, FP_TOFP, idx[0], idx[1], &args[0], args[1]);
      }
      if (k == Kind::FP_TO_FP_FROM_REAL)
      {
        c.expect_real(1);
        return fp_from_real_value(c, idx[0], idx[1], args[0], args[1]);
      }
      c.expect_bv(1);
      return to_fp_node(c, k == Kind::FP_TO_FP_FROM_SBV ? FP_TOFP_SIGNED : FP_TOFP_UNSIGNED,
                        idx[0], idx[1], &args[0], args[1]);
    }
    case Kind::FP_TO_UBV:
    case Kind::FP_TO_SBV:
    {
      c.expect_rm(0);
      c.expect_fp(1);
      if (idx[0] == 0)
        fail(ErrorCode::INDEX_OUT_OF_RANGE, fn, "fp.to_ubv/fp.to_sbv need a positive width");
      return c.bv_term(k == Kind::FP_TO_UBV ? FP_TO_UBV : FP_TO_SBV, idx[0],
                       {c.c32(idx[0]), args[0], args[1]});
    }
    case Kind::FP_TO_REAL:
    {
      c.expect_fp(0);
      // The engine's one construction, which the SMT-LIB 2 frontend shares: a
      // float value folds to its exact Real value whatever the manager's
      // simplify setting; NaN and the infinities select a Real constant of
      // their own per format; anything else is the exact encoding, which
      // kind() and the printers read back as (fp.to_real x).
      try
      {
        return c.bm()->CreateFpToReal(kids[0]);
      }
      catch (const stp::EngineFatal&)
      {
        throw;
      }
      catch (const std::exception& failure)
      {
        c.unsupported(failure.what());
      }
    }
    case Kind::FP_TO_IEEE_BV:
    {
      c.expect_fp(0);
      const SortRec& r = c.rec(0);
      return c.bv_term(FP_TO_IEEE_BV, r.a + r.b, kids);
    }

    // ------------------------------------------------------------ Real
    case Kind::REAL_ADD:
    case Kind::REAL_SUB:
    case Kind::REAL_MUL:
    case Kind::REAL_DIV:
    {
      for (std::size_t i = 0; i < args.size(); ++i)
        c.expect_real(i);
      Kind_t ek = REAL_ADD;
      switch (k)
      {
        case Kind::REAL_ADD: ek = REAL_ADD; break;
        case Kind::REAL_SUB: ek = REAL_SUB; break;
        case Kind::REAL_MUL: ek = REAL_MUL; break;
        default: ek = REAL_DIV; break;
      }
      if (ek == REAL_MUL && args[0].GetKind() != REAL_CONST && args[1].GetKind() != REAL_CONST)
        c.unsupported("Real multiplication must be linear: one operand must be a value "
                      "(capabilities: real.nonlinear = false)");
      if (ek == REAL_DIV && args[1].GetKind() != REAL_CONST)
        c.unsupported("Real division needs a non-zero value as its divisor");
      // The engine's own check for an exact zero divisor is a FatalError.
      if (ek == REAL_DIV && rational_of(args[1]).numerator == "0")
        c.unsupported("Real division by zero is not a term the engine can build "
                      "(the divisor must be a non-zero value)");
      return real_term(c, ek, kids);
    }
    case Kind::REAL_NEG:
      c.expect_real(0);
      return real_term(c, REAL_NEG, kids);
    case Kind::REAL_LT:
    case Kind::REAL_LE:
    case Kind::REAL_GT:
    case Kind::REAL_GE:
    {
      c.expect_real(0);
      c.expect_real(1);
      Kind_t ek = REAL_LT;
      switch (k)
      {
        case Kind::REAL_LT: ek = REAL_LT; break;
        case Kind::REAL_LE: ek = REAL_LE; break;
        case Kind::REAL_GT: ek = REAL_GT; break;
        default: ek = REAL_GE; break;
      }
      return real_pred(c, ek, args[0], args[1]);
    }
    case Kind::NUM_KINDS:
      break;
  }
  fail(ErrorCode::INVALID_ARGUMENT, fn, "not a kind");
}

// ------------------------------------------------------------ named constructors

Term mk_named(Kind k, const char* fn, const std::vector<Term>& args)
{
  ManagerImpl* m = nullptr;
  for (std::size_t i = 0; i < args.size(); ++i)
  {
    if (args[i].is_null())
      fail(ErrorCode::NULL_HANDLE, fn, "the term is null", static_cast<int>(i));
    if (m == nullptr)
      m = args[i].impl_manager();
    else if (args[i].impl_manager() != m)
      fail(ErrorCode::FOREIGN_MANAGER, fn, "the term belongs to another term manager",
           static_cast<int>(i), {args[i]});
  }
  if (m == nullptr)
    fail(ErrorCode::ARITY, fn, "no arguments");
  m->check_alive(fn);
  std::vector<ASTNode> nodes;
  nodes.reserve(args.size());
  for (const Term& t : args)
    nodes.push_back(node_of(t));
  return make_term(m, build_term(m, fn, k, nodes, {}, std::nullopt));
}

Term rm_term(const Term& like, RoundingMode rm)
{
  if (like.is_null())
    fail(ErrorCode::NULL_HANDLE, "rounding mode", "the term is null");
  return make_term(like.impl_manager(), like.impl_manager()->rm_const(rm));
}

namespace
{
std::string decimal_of_u64(std::uint64_t v)
{
  return std::to_string(v);
}

std::string mul_pow2_dec(std::string dec, int k)
{
  for (int i = 0; i < k; ++i)
  {
    int carry = 0;
    for (std::size_t j = dec.size(); j-- > 0;)
    {
      const int v = (dec[j] - '0') * 2 + carry;
      dec[j] = static_cast<char>('0' + v % 10);
      carry = v / 10;
    }
    if (carry)
      dec.insert(dec.begin(), static_cast<char>('0' + carry));
  }
  return dec;
}

// The exact rational of a finite double: numerator, denominator, sign.
bool double_to_rational(double d, std::string& num, std::string& den, bool& negative)
{
  if (!std::isfinite(d))
    return false;
  std::uint64_t raw;
  std::memcpy(&raw, &d, sizeof raw);
  negative = (raw >> 63) != 0;
  const int biased = static_cast<int>((raw >> 52) & 0x7ff);
  std::uint64_t mantissa = raw & ((std::uint64_t(1) << 52) - 1);
  if (biased == 0 && mantissa == 0)
  {
    num = "0";
    den = "1";
    return true;
  }
  int exponent;
  if (biased == 0)
    exponent = -1074;
  else
  {
    mantissa |= std::uint64_t(1) << 52;
    exponent = biased - 1075;
  }
  while ((mantissa & 1) == 0)
  {
    mantissa >>= 1;
    ++exponent;
  }
  if (exponent >= 0)
  {
    num = mul_pow2_dec(decimal_of_u64(mantissa), exponent);
    den = "1";
  }
  else
  {
    num = decimal_of_u64(mantissa);
    den = mul_pow2_dec("1", -exponent);
  }
  return true;
}

ASTNode fp_literal_from_rational(ManagerImpl* m, const char* fn, const SortRec& r,
                                 const std::string& num, const std::string& den, bool negative,
                                 const ASTNode* rm)
{
  unsigned mode = rm_encoding(m->config.default_rounding_mode);
  if (rm != nullptr)
  {
    if (rm->GetKind() != BVCONST)
      fail(ErrorCode::UNSUPPORTED, fn,
           "a literal beside a floating-point term needs a rounding-mode value, not a "
           "symbolic mode");
    mode = rm->GetUnsignedConst();
  }
  std::string bits, err;
  if (!rationalToPackedFPBits(num, den, negative, r.a, r.b, mode, bits, err))
    fail(ErrorCode::UNSUPPORTED, fn, err);
  return m->fp_const_from_bits(r.a, r.b, m->bv_const_bits(r.a + r.b, bits));
}
} // namespace

ASTNode literal_for(ManagerImpl* m, const char* fn, std::uint32_t sort, std::int64_t v,
                    bool is_signed, std::uint64_t uv, const ASTNode* rm)
{
  const SortRec& r = m->rec(sort);
  switch (r.kind)
  {
    case SortKind::BV:
    {
      const std::uint32_t w = r.a;
      if (is_signed && v < 0)
      {
        if (w < 64 && v < -(std::int64_t(1) << (w - 1)))
          fail(ErrorCode::VALUE_OUT_OF_RANGE, fn,
               "literal " + std::to_string(v) + " does not fit the two's complement range of " +
                   std::to_string(w) + " bits",
               std::nullopt, {}, {make_sort(m, sort)});
        std::string bits(w, '1');
        const std::uint64_t raw = static_cast<std::uint64_t>(v);
        for (std::uint32_t i = 0; i < w && i < 64; ++i)
          bits[w - 1 - i] = ((raw >> i) & 1) ? '1' : '0';
        return m->bv_const_bits(w, bits);
      }
      const std::uint64_t magnitude = is_signed ? static_cast<std::uint64_t>(v) : uv;
      if (w < 64 && (magnitude >> w) != 0)
        fail(ErrorCode::VALUE_OUT_OF_RANGE, fn,
             "literal " + std::to_string(magnitude) + " does not fit " + std::to_string(w) +
                 " bits",
             std::nullopt, {}, {make_sort(m, sort)});
      return m->bv_const(w, magnitude);
    }
    case SortKind::REAL:
      return m->real_const(fn, is_signed ? std::to_string(v) : std::to_string(uv));
    case SortKind::FP:
    {
      const bool negative = is_signed && v < 0;
      const std::uint64_t magnitude =
          is_signed ? (v < 0 ? std::uint64_t(0) - static_cast<std::uint64_t>(v)
                             : static_cast<std::uint64_t>(v))
                    : uv;
      return fp_literal_from_rational(m, fn, r, decimal_of_u64(magnitude), "1", negative, rm);
    }
    default:
      break;
  }
  fail(ErrorCode::SORT_MISMATCH, fn,
       "an integer literal cannot stand beside a term of sort " + m->sort_text(sort),
       std::nullopt, {}, {make_sort(m, sort)});
}

ASTNode float_literal_for(ManagerImpl* m, const char* fn, std::uint32_t sort, double v,
                          const ASTNode* rm)
{
  const SortRec& r = m->rec(sort);
  switch (r.kind)
  {
    case SortKind::FP:
    {
      if (v != v)
        return m->bm->CreateFPSpecialConst(FPSpecial::NaN, r.a, r.b);
      if (std::isinf(v))
        return m->bm->CreateFPSpecialConst(v > 0 ? FPSpecial::PlusInfinity : FPSpecial::MinusInfinity,
                                           r.a, r.b);
      if (v == 0.0)
        return m->bm->CreateFPSpecialConst(std::signbit(v) ? FPSpecial::MinusZero : FPSpecial::PlusZero,
                                           r.a, r.b);
      std::string num, den;
      bool negative;
      double_to_rational(v, num, den, negative);
      return fp_literal_from_rational(m, fn, r, num, den, negative, rm);
    }
    case SortKind::REAL:
    {
      std::string num, den;
      bool negative;
      if (!double_to_rational(v, num, den, negative))
        fail(ErrorCode::INVALID_ARGUMENT, fn, "a Real literal must be finite");
      return m->real_const(fn, (negative ? "-" : "") + num + "/" + den);
    }
    default:
      break;
  }
  fail(ErrorCode::SORT_MISMATCH, fn,
       "a floating-point literal cannot stand beside a term of sort " + m->sort_text(sort),
       std::nullopt, {}, {make_sort(m, sort)});
}

namespace
{
ManagerImpl* live_like(const Term& like, const char* fn)
{
  if (like.is_null())
    fail(ErrorCode::NULL_HANDLE, fn, "the term is null");
  ManagerImpl* m = like.impl_manager();
  m->check_alive(fn);
  return m;
}
} // namespace

Term int_literal_signed(const Term& like, std::int64_t v)
{
  ManagerImpl* m = live_like(like, "literal");
  return make_term(m, literal_for(m, "literal", m->sort_of_node(node_of(like), "literal"), v,
                                  true, 0, nullptr));
}
Term int_literal_unsigned(const Term& like, std::uint64_t v)
{
  ManagerImpl* m = live_like(like, "literal");
  return make_term(m, literal_for(m, "literal", m->sort_of_node(node_of(like), "literal"), 0,
                                  false, v, nullptr));
}
Term int_literal_signed(const Term& like, std::int64_t v, const Term& rm)
{
  ManagerImpl* m = live_like(like, "literal");
  const ASTNode r = node_of(rm);
  return make_term(m, literal_for(m, "literal", m->sort_of_node(node_of(like), "literal"), v,
                                  true, 0, &r));
}
Term int_literal_unsigned(const Term& like, std::uint64_t v, const Term& rm)
{
  ManagerImpl* m = live_like(like, "literal");
  const ASTNode r = node_of(rm);
  return make_term(m, literal_for(m, "literal", m->sort_of_node(node_of(like), "literal"), 0,
                                  false, v, &r));
}
Term float_literal(const Term& like, double v)
{
  ManagerImpl* m = live_like(like, "literal");
  return make_term(m, float_literal_for(m, "literal", m->sort_of_node(node_of(like), "literal"),
                                        v, nullptr));
}
Term float_literal(const Term& like, double v, const Term& rm)
{
  ManagerImpl* m = live_like(like, "literal");
  const ASTNode r = node_of(rm);
  return make_term(m, float_literal_for(m, "literal", m->sort_of_node(node_of(like), "literal"),
                                        v, &r));
}

// ------------------------------------------------------------ operators

namespace
{
SortKind sort_kind_of(const Term& t, const char* fn)
{
  ManagerImpl* m = live_like(t, fn);
  return m->rec(m->sort_of_node(node_of(t), fn)).kind;
}

Term with_default_rm(const Term& a, Kind k, const char* fn, const std::vector<Term>& rest)
{
  std::vector<Term> args;
  args.push_back(rm_term(a, a.impl_manager()->config.default_rounding_mode));
  args.insert(args.end(), rest.begin(), rest.end());
  return mk_named(k, fn, args);
}
} // namespace

Term op_add(const Term& a, const Term& b)
{
  switch (sort_kind_of(a, "operator+"))
  {
    case SortKind::BV: return mk_named(Kind::BV_ADD, "operator+", {a, b});
    case SortKind::REAL: return mk_named(Kind::REAL_ADD, "operator+", {a, b});
    case SortKind::FP: return with_default_rm(a, Kind::FP_ADD, "operator+", {a, b});
    default: break;
  }
  fail(ErrorCode::SORT_MISMATCH, "operator+", "+ needs bit-vector, Real or floating-point terms",
       0, {a, b});
}
Term op_sub(const Term& a, const Term& b)
{
  switch (sort_kind_of(a, "operator-"))
  {
    case SortKind::BV: return mk_named(Kind::BV_SUB, "operator-", {a, b});
    case SortKind::REAL: return mk_named(Kind::REAL_SUB, "operator-", {a, b});
    case SortKind::FP: return with_default_rm(a, Kind::FP_SUB, "operator-", {a, b});
    default: break;
  }
  fail(ErrorCode::SORT_MISMATCH, "operator-", "- needs bit-vector, Real or floating-point terms",
       0, {a, b});
}
Term op_mul(const Term& a, const Term& b)
{
  switch (sort_kind_of(a, "operator*"))
  {
    case SortKind::BV: return mk_named(Kind::BV_MUL, "operator*", {a, b});
    case SortKind::REAL: return mk_named(Kind::REAL_MUL, "operator*", {a, b});
    case SortKind::FP: return with_default_rm(a, Kind::FP_MUL, "operator*", {a, b});
    default: break;
  }
  fail(ErrorCode::SORT_MISMATCH, "operator*", "* needs bit-vector, Real or floating-point terms",
       0, {a, b});
}
Term op_div(const Term& a, const Term& b)
{
  switch (sort_kind_of(a, "operator/"))
  {
    case SortKind::BV:
      fail(ErrorCode::SORT_MISMATCH, "operator/",
           "/ is ambiguous on bit-vectors: use bvudiv or bvsdiv", 0, {a, b});
    case SortKind::REAL: return mk_named(Kind::REAL_DIV, "operator/", {a, b});
    case SortKind::FP: return with_default_rm(a, Kind::FP_DIV, "operator/", {a, b});
    default: break;
  }
  fail(ErrorCode::SORT_MISMATCH, "operator/", "/ needs Real or floating-point terms", 0, {a, b});
}
Term op_neg(const Term& a)
{
  switch (sort_kind_of(a, "operator-"))
  {
    case SortKind::BV: return mk_named(Kind::BV_NEG, "operator-", {a});
    case SortKind::REAL: return mk_named(Kind::REAL_NEG, "operator-", {a});
    case SortKind::FP: return mk_named(Kind::FP_NEG, "operator-", {a});
    default: break;
  }
  fail(ErrorCode::SORT_MISMATCH, "operator-", "unary - needs a bit-vector, Real or floating-point term",
       0, {a});
}

} // namespace detail

// ------------------------------------------------------------ the generated named constructors

#include "gen/kind_ctors.inc"

// ------------------------------------------------------------ the indexed constructors

namespace
{
Term indexed1(Kind k, const char* fn, std::uint32_t i, const Term& t)
{
  if (t.is_null())
    detail::fail(ErrorCode::NULL_HANDLE, fn, "the term is null", 1);
  detail::ManagerImpl* m = t.impl_manager();
  m->check_alive(fn);
  return detail::make_term(m, detail::build_term(m, fn, k, {detail::node_of(t)}, {i}, std::nullopt));
}

detail::ManagerImpl* fp_sort_manager(const Sort& fp, const char* fn)
{
  if (fp.is_null())
    detail::fail(ErrorCode::NULL_HANDLE, fn, "the sort is null", 0);
  detail::ManagerImpl* m = fp.impl_manager();
  m->check_alive(fn);
  if (m->rec(fp.impl_index()).kind != SortKind::FP)
    detail::fail(ErrorCode::SORT_MISMATCH, fn, "expected a floating-point sort", 0, {}, {fp});
  return m;
}

Term to_fp_impl(const Sort& fp, const Term& rm, const Term& src, const char* fn, bool unsigned_bv)
{
  detail::ManagerImpl* m = fp_sort_manager(fp, fn);
  if (rm.is_null() || src.is_null())
    detail::fail(ErrorCode::NULL_HANDLE, fn, "the term is null", rm.is_null() ? 1 : 2);
  if (rm.impl_manager() != m || src.impl_manager() != m)
    detail::fail(ErrorCode::FOREIGN_MANAGER, fn, "the term belongs to another term manager",
                 rm.impl_manager() != m ? 1 : 2);
  const detail::SortRec& r = m->rec(fp.impl_index());
  Kind k;
  if (unsigned_bv)
    k = Kind::FP_TO_FP_FROM_UBV;
  else
  {
    switch (m->rec(m->sort_of_node(detail::node_of(src), fn)).kind)
    {
      case SortKind::FP: k = Kind::FP_TO_FP_FROM_FP; break;
      case SortKind::REAL: k = Kind::FP_TO_FP_FROM_REAL; break;
      case SortKind::BV: k = Kind::FP_TO_FP_FROM_SBV; break;
      default:
        detail::fail(ErrorCode::SORT_MISMATCH, fn,
                     "to_fp converts a floating-point number, a Real or a signed bit-vector", 2,
                     {src}, {src.sort()});
    }
  }
  return detail::make_term(m, detail::build_term(m, fn, k, {detail::node_of(rm), detail::node_of(src)},
                                                 {r.a, r.b}, std::nullopt));
}
} // namespace

Term extract(std::uint32_t hi, std::uint32_t lo, const Term& t)
{
  if (t.is_null())
    detail::fail(ErrorCode::NULL_HANDLE, "extract", "the term is null", 2);
  detail::ManagerImpl* m = t.impl_manager();
  m->check_alive("extract");
  return detail::make_term(m, detail::build_term(m, "extract", Kind::BV_EXTRACT, {detail::node_of(t)},
                                                 {hi, lo}, std::nullopt));
}
Term zero_extend(std::uint32_t k, const Term& t) { return indexed1(Kind::BV_ZERO_EXTEND, "zero_extend", k, t); }
Term sign_extend(std::uint32_t k, const Term& t) { return indexed1(Kind::BV_SIGN_EXTEND, "sign_extend", k, t); }
Term repeat(std::uint32_t k, const Term& t) { return indexed1(Kind::BV_REPEAT, "repeat", k, t); }
Term rotate_left(std::uint32_t k, const Term& t) { return indexed1(Kind::BV_ROTATE_LEFT, "rotate_left", k, t); }
Term rotate_right(std::uint32_t k, const Term& t) { return indexed1(Kind::BV_ROTATE_RIGHT, "rotate_right", k, t); }

Term bit(const Term& bv, std::uint32_t i)
{
  const Term one = detail::make_term(bv.impl_manager(), bv.impl_manager()->bm->CreateOneConst(1));
  return eq(extract(i, i, bv), one);
}
Term bool_to_bv1(const Term& b)
{
  if (b.is_null())
    detail::fail(ErrorCode::NULL_HANDLE, "bool_to_bv1", "the term is null", 0);
  detail::ManagerImpl* m = b.impl_manager();
  const Term one = detail::make_term(m, m->bm->CreateOneConst(1));
  const Term zero = detail::make_term(m, m->bm->CreateZeroConst(1));
  return ite(b, one, zero);
}
Term bv1_to_bool(const Term& bv1)
{
  if (bv1.is_null())
    detail::fail(ErrorCode::NULL_HANDLE, "bv1_to_bool", "the term is null", 0);
  detail::ManagerImpl* m = bv1.impl_manager();
  const std::uint32_t s = m->sort_of_node(detail::node_of(bv1), "bv1_to_bool");
  if (m->rec(s).kind != SortKind::BV || m->rec(s).a != 1)
    detail::fail(ErrorCode::SORT_MISMATCH, "bv1_to_bool", "expected a 1-bit bit-vector", 0, {bv1},
                 {bv1.sort()});
  return eq(bv1, detail::make_term(m, m->bm->CreateOneConst(1)));
}
Term array_from_bytes(TermManager& tm, const std::vector<std::uint8_t>& bytes,
                      std::uint32_t index_width)
{
  const Sort idx = tm.mk_bv_sort(index_width);
  const Sort elem = tm.mk_bv_sort(8);
  const Sort arr = tm.mk_array_sort(idx, elem);
  if (index_width < 64 && bytes.size() > (std::uint64_t(1) << index_width))
    detail::fail(ErrorCode::VALUE_OUT_OF_RANGE, "array_from_bytes",
                 "more bytes than the index width can address", 1);
  Term out = tm.mk_const_array(arr, tm.mk_bv(8, 0));
  for (std::size_t i = 0; i < bytes.size(); ++i)
    out = store(out, tm.mk_bv(index_width, i), tm.mk_bv(8, bytes[i]));
  return out;
}
Term to_fp(const Sort& fp, const Term& rm, const Term& src)
{
  return to_fp_impl(fp, rm, src, "to_fp", false);
}
Term to_fp(const Sort& fp, RoundingMode rm, const Term& src)
{
  detail::ManagerImpl* m = fp_sort_manager(fp, "to_fp");
  return to_fp_impl(fp, detail::make_term(m, m->rm_const(rm)), src, "to_fp", false);
}
Term to_fp_unsigned(const Sort& fp, const Term& rm, const Term& bv)
{
  return to_fp_impl(fp, rm, bv, "to_fp_unsigned", true);
}
Term to_fp_unsigned(const Sort& fp, RoundingMode rm, const Term& bv)
{
  detail::ManagerImpl* m = fp_sort_manager(fp, "to_fp_unsigned");
  return to_fp_impl(fp, detail::make_term(m, m->rm_const(rm)), bv, "to_fp_unsigned", true);
}
Term to_fp_from_bits(const Sort& fp, const Term& bv)
{
  detail::ManagerImpl* m = fp_sort_manager(fp, "to_fp_from_bits");
  if (bv.is_null())
    detail::fail(ErrorCode::NULL_HANDLE, "to_fp_from_bits", "the term is null", 1);
  const detail::SortRec& r = m->rec(fp.impl_index());
  return detail::make_term(m, detail::build_term(m, "to_fp_from_bits", Kind::FP_TO_FP_FROM_BV,
                                                 {detail::node_of(bv)}, {r.a, r.b}, std::nullopt));
}
Term fp_to_ubv(std::uint32_t w, const Term& rm, const Term& f)
{
  if (rm.is_null() || f.is_null())
    detail::fail(ErrorCode::NULL_HANDLE, "fp_to_ubv", "the term is null", rm.is_null() ? 1 : 2);
  detail::ManagerImpl* m = f.impl_manager();
  return detail::make_term(m, detail::build_term(m, "fp_to_ubv", Kind::FP_TO_UBV,
                                                 {detail::node_of(rm), detail::node_of(f)}, {w},
                                                 std::nullopt));
}
Term fp_to_sbv(std::uint32_t w, const Term& rm, const Term& f)
{
  if (rm.is_null() || f.is_null())
    detail::fail(ErrorCode::NULL_HANDLE, "fp_to_sbv", "the term is null", rm.is_null() ? 1 : 2);
  detail::ManagerImpl* m = f.impl_manager();
  return detail::make_term(m, detail::build_term(m, "fp_to_sbv", Kind::FP_TO_SBV,
                                                 {detail::node_of(rm), detail::node_of(f)}, {w},
                                                 std::nullopt));
}
Term fp_to_ubv(std::uint32_t w, RoundingMode rm, const Term& f)
{
  return fp_to_ubv(w, detail::rm_term(f, rm), f);
}
Term fp_to_sbv(std::uint32_t w, RoundingMode rm, const Term& f)
{
  return fp_to_sbv(w, detail::rm_term(f, rm), f);
}

} // namespace api
} // namespace stp
