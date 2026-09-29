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

/* fp.to_real: the exact Real value of a float, as linear Real arithmetic.
 *
 * A finite float of format (eb, sb) with sign s, biased exponent E and stored
 * significand bits f_0 .. f_(sb-2) is
 *
 *   (-1)^s * M * 2^(max(E, 1) - bias - (sb - 1)),   bias = 2^(eb-1) - 1,
 *
 * where M is the significand as an integer: the stored bits, plus the hidden
 * bit 2^(sb-1) unless E is zero (a subnormal or a zero, whose exponent is
 * read as 1). Split E as t * 2^(eb-1) + L, with t its top bit, and the power
 * of two is 2^(L + 1 - (sb-1)) * (t ? 1 : 2^-(2^(eb-1))). The encoding keeps
 * that shape and stays linear by giving every product a constant factor:
 *
 *   V_0     = sum_i ite(f_i, 2^(i + 2 - sb), 0) + ite(E /= 0, 2, 0)
 *   V_(j+1) = ite(e'_j, 2^(2^j) * V_j, V_j)             j = 0 .. eb-2
 *   A       = ite(t, V_(eb-1), 2^-(2^(eb-1)) * V_(eb-1))
 *   F       = ite(s, -A, A)
 *
 * with e'_j the exponent's bit j, except that e'_0 also holds when E is zero:
 * that is what reads a zero exponent as 1. The exponent is applied one bit at
 * a time, a chain of eb if-then-elses whose factors are constants, so the
 * term has sb + eb + 3 of them and depth eb + 4 whatever the format; an
 * if-then-else per exponent value would need 2^eb, each one a variable the
 * arithmetic has to name, bound and refute. The significand's weights are
 * small, and every intermediate value stays inside the format's own range:
 * the only wide constants are the eb factors, up to 2^(2^(eb-2)) and
 * 2^-(2^(eb-1)) -- the exact arithmetic interns each one at the cost of its
 * decimal digits, so the layout keeps them few.
 *
 * NaN, +oo and -oo are selected around F, each onto a Real constant of its
 * own per format; the root tests the operand for NaN against the format's
 * NaN constant, which is what FpToRealOperand reads the operand back from.
 * The root is built by the hashing factory so that shape survives whatever
 * the default factory would rewrite, and the three constants are introduced
 * symbols, so no public boundary can name them: a term with that shape is a
 * conversion this file built, or a rebuilding of one.
 *
 * A float value folds instead: to its exact Real value when finite, and to
 * the root over the value when it is NaN or an infinity -- the constant it
 * selects is not a value, and the root keeps it out of reach.
 *
 * LinkFpToReal is the solve-time half. The Real arithmetic sees a conversion
 * only once the SAT search has fixed every bit it reads, so on its own the
 * search has to find by refutation which float a bound on the conversion
 * admits -- one candidate at a time. Against a constant, or against the
 * conversion of another float of the same format, a comparison of finite
 * floats IS a floating-point comparison, and saying so lets the SAT search
 * see the comparison while it chooses the bits. */

#include "stp/STPManager/STPManager.h"

#include "stp/FloatBlaster/DecimalLiteral.h"
#include "stp/FloatBlaster/rounding_modes.h"

#include <map>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace stp
{

// The constants one format needs, made on first use and kept for the
// manager's life: the three Real constants for NaN, +oo and -oo; the float
// values they stand for; the significand's weights; the exponent's factors.
struct FpToRealFormat
{
  ASTNode nan, plus_infinity, minus_infinity;
  ASTNode nan_value, plus_infinity_value, minus_infinity_value;
  // weights[i] = 2^(i + 2 - sb) for i < sb-1; weights[sb-1] = 2
  ASTVec weights;
  // factors[j] = 2^(2^j), j < eb-1
  ASTVec factors;
  // 2^-(2^(eb-1)): the scale when the exponent's top bit is clear
  ASTNode low_half;
};

struct FpToRealState
{
  std::map<std::pair<unsigned, unsigned>, FpToRealFormat> formats;
  // special constant's node number -> (format, which: 0 NaN, 1 +oo, 2 -oo)
  std::map<uint64_t, std::pair<std::pair<unsigned, unsigned>, int>> specials;
};

void DestroyFpToRealState(FpToRealState* state)
{
  delete state;
}

namespace
{

std::string formatSuffix(unsigned exp_width, unsigned sig_width)
{
  return std::to_string(exp_width) + "x" + std::to_string(sig_width);
}

// 2^k for k >= 0, by squaring. Each product is a constant, so CreateRealTerm
// folds it; a format whose constants exceed the number limits fails here,
// before any node of the encoding exists.
ASTNode powerOfTwo(STPMgr& bm, uint64_t k)
{
  ASTNode result = bm.CreateRealConst("1");
  ASTNode base = bm.CreateRealConst("2");
  while (k != 0)
  {
    if (k & 1)
      result = bm.CreateRealTerm(REAL_MUL, ASTVec{result, base});
    k >>= 1;
    if (k != 0)
      base = bm.CreateRealTerm(REAL_MUL, ASTVec{base, base});
  }
  return result;
}

} // namespace

FpToRealFormat& STPMgr::FpToRealFormatFor(unsigned exp_width,
                                          unsigned sig_width)
{
  if (exp_width < 2 || sig_width < 2)
    throw std::invalid_argument(
        "fp.to_real: a floating-point format needs at least 2 exponent and 2 "
        "significand bits");
  // The largest factor is 2^(2^(eb-1)); the exact arithmetic caps any value
  // well below 2^(2^63), which is where a shift below would overflow, so a
  // format this wide is refused by the arithmetic long before that.
  if (exp_width > 32)
    throw std::runtime_error(
        "fp.to_real: an exponent of " + std::to_string(exp_width) +
        " bits needs exact values beyond the Real arithmetic's number limits");

  if (fp_to_real_state == nullptr)
    fp_to_real_state = new FpToRealState();
  const std::pair<unsigned, unsigned> key(exp_width, sig_width);
  const auto found = fp_to_real_state->formats.find(key);
  if (found != fp_to_real_state->formats.end())
    return found->second;

  // Every constant first: if one exceeds the number limits, nothing of this
  // format is kept.
  FpToRealFormat f;
  try
  {
    const ASTNode one = CreateRealConst("1");
    const ASTNode two = CreateRealConst("2");
    f.weights.reserve(sig_width);
    ASTNode weight = CreateRealTerm(
        REAL_DIV, ASTVec{one, powerOfTwo(*this, sig_width - 2)});
    for (unsigned i = 0; i + 1 < sig_width; ++i)
    {
      f.weights.push_back(weight);
      weight = CreateRealTerm(REAL_MUL, ASTVec{weight, two});
    }
    f.weights.push_back(two); // the hidden bit, 2^(sb-1) * 2^(2-sb)
    f.factors.reserve(exp_width - 1);
    ASTNode factor = two;
    for (unsigned j = 0; j + 1 < exp_width; ++j)
    {
      f.factors.push_back(factor);
      factor = CreateRealTerm(REAL_MUL, ASTVec{factor, factor});
    }
    // factor is now 2^(2^(eb-1))
    f.low_half = CreateRealTerm(REAL_DIV, ASTVec{one, factor});
  }
  catch (const std::bad_alloc&)
  {
    throw;
  }
  catch (const std::exception& refused)
  {
    throw std::runtime_error(
        "fp.to_real: the exact values of (_ FloatingPoint " +
        std::to_string(exp_width) + " " + std::to_string(sig_width) +
        ") exceed the Real arithmetic's number limits (" + refused.what() +
        ")");
  }

  // The three constants: introduced, so that the model printers skip them
  // and the API adopts none of them as a declaration, and with a reserved
  // name, so that no declaration can reach them. Internal identities are not
  // indexed by name, so a lookup cannot find them either.
  const std::string suffix = formatSuffix(exp_width, sig_width);
  const auto mint = [&](const char* which) {
    const std::string name = std::string("@fp.to_real_") + which + "_" + suffix;
    const ASTNode symbol =
        CreateInternalSourceSymbol(name.c_str(), SourceSort::real());
    noteIntroducedSymbol(symbol);
    noteReal();
    return symbol;
  };
  f.nan = mint("nan");
  f.plus_infinity = mint("+oo");
  f.minus_infinity = mint("-oo");
  f.nan_value = CreateFPSpecialConst(FPSpecial::NaN, exp_width, sig_width);
  f.plus_infinity_value =
      CreateFPSpecialConst(FPSpecial::PlusInfinity, exp_width, sig_width);
  f.minus_infinity_value =
      CreateFPSpecialConst(FPSpecial::MinusInfinity, exp_width, sig_width);

  fp_to_real_state->specials[f.nan.GetNodeNum()] = {key, 0};
  fp_to_real_state->specials[f.plus_infinity.GetNodeNum()] = {key, 1};
  fp_to_real_state->specials[f.minus_infinity.GetNodeNum()] = {key, 2};
  fp_to_real_special_ids.insert(f.nan.GetNodeNum());
  fp_to_real_special_ids.insert(f.plus_infinity.GetNodeNum());
  fp_to_real_special_ids.insert(f.minus_infinity.GetNodeNum());
  return fp_to_real_state->formats.emplace(key, std::move(f)).first->second;
}

ASTNode STPMgr::FpToRealOfValue(const ASTNode& value, unsigned exp_width,
                                unsigned sig_width)
{
  if (value.GetKind() != BVCONST ||
      value.GetValueWidth() != exp_width + sig_width)
    throw std::invalid_argument("fp.to_real: expected a float value");
  const FpToRealFormat& f = FpToRealFormatFor(exp_width, sig_width);
  const CBV bits = value.GetBVConst();
  const unsigned width = exp_width + sig_width;
  const bool negative = CONSTANTBV::BitVector_bit_test(bits, width - 1);
  bool exponent_ones = true, exponent_zero = true, fraction_zero = true;
  for (unsigned j = 0; j < exp_width; ++j)
  {
    const bool set = CONSTANTBV::BitVector_bit_test(bits, sig_width - 1 + j);
    exponent_ones = exponent_ones && set;
    exponent_zero = exponent_zero && !set;
  }
  for (unsigned i = 0; i + 1 < sig_width; ++i)
    fraction_zero = fraction_zero && !CONSTANTBV::BitVector_bit_test(bits, i);
  if (exponent_ones)
    return fraction_zero ? (negative ? f.minus_infinity : f.plus_infinity)
                         : f.nan;

  // The encoding's arithmetic over known bits; every step folds.
  ASTVec addends;
  for (unsigned i = 0; i + 1 < sig_width; ++i)
    if (CONSTANTBV::BitVector_bit_test(bits, i))
      addends.push_back(f.weights[i]);
  if (!exponent_zero)
    addends.push_back(f.weights[sig_width - 1]);
  ASTNode v = addends.empty()      ? CreateRealConst("0")
              : addends.size() == 1 ? addends[0]
                                    : CreateRealTerm(REAL_ADD, addends);
  for (unsigned j = 0; j + 1 < exp_width; ++j)
  {
    const bool set = CONSTANTBV::BitVector_bit_test(bits, sig_width - 1 + j) ||
                     (j == 0 && exponent_zero);
    if (set)
      v = CreateRealTerm(REAL_MUL, ASTVec{f.factors[j], v});
  }
  if (!CONSTANTBV::BitVector_bit_test(bits, width - 2))
    v = CreateRealTerm(REAL_MUL, ASTVec{f.low_half, v});
  if (negative)
    v = CreateRealTerm(REAL_NEG, ASTVec{v});
  return v;
}

ASTNode STPMgr::CreateFpToReal(const ASTNode& x)
{
  const SourceSort sort = x.IsNull() ? SourceSort() : x.GetSourceSort();
  if (sort.kind() != SourceSort::Kind::FloatingPoint)
    throw std::invalid_argument("fp.to_real takes a floating-point operand");
  if (!x.IsOwnedBy(this))
    throw std::invalid_argument(
        "fp.to_real: the operand belongs to another manager");
  const unsigned eb = sort.exponentWidth();
  const unsigned sb = sort.significandWidth();
  const unsigned width = eb + sb;
  const FpToRealFormat& f = FpToRealFormatFor(eb, sb);

  if (x.GetKind() == BVCONST)
  {
    const ASTNode folded = FpToRealOfValue(x, eb, sb);
    if (!IsFpToRealSpecial(folded))
      return folded;
  }

  NodeFactory* nf = defaultNodeFactory;
  const ASTNode zero = CreateRealConst("0");
  // An if-then-else over Reals, taking the branch a settled condition names.
  const auto ite = [&](const ASTNode& c, const ASTNode& a, const ASTNode& b) {
    if (c == ASTTrue || a == b)
      return a;
    if (c == ASTFalse)
      return b;
    return CreateRealTerm(ITE, ASTVec{c, a, b});
  };

  ASTNode inner;
  if (x.GetKind() == BVCONST)
  {
    // NaN or an infinity: the finite part is never selected.
    const ASTNode folded = FpToRealOfValue(x, eb, sb);
    inner = folded == f.nan ? zero : folded;
  }
  else
  {
    const ASTNode ieee = nf->CreateTerm(FP_TO_IEEE_BV, width, x);
    const ASTNode bit_one = CreateOneConst(1);
    const auto bit = [&](unsigned i) {
      const ASTNode index = CreateBVConst(32, i);
      return nf->CreateNode(
          EQ, nf->CreateTerm(BVEXTRACT, 1, ieee, index, index), bit_one);
    };
    const ASTNode exponent_zero = nf->CreateNode(
        EQ,
        nf->CreateTerm(BVEXTRACT, eb, ieee, CreateBVConst(32, width - 2),
                       CreateBVConst(32, sb - 1)),
        CreateZeroConst(eb));

    ASTVec addends;
    for (unsigned i = 0; i + 1 < sb; ++i)
    {
      const ASTNode t = ite(bit(i), f.weights[i], zero);
      if (t != zero)
        addends.push_back(t);
    }
    {
      const ASTNode hidden =
          ite(nf->CreateNode(NOT, exponent_zero), f.weights[sb - 1], zero);
      if (hidden != zero)
        addends.push_back(hidden);
    }
    ASTNode v = addends.empty()      ? zero
                : addends.size() == 1 ? addends[0]
                                      : CreateRealTerm(REAL_ADD, addends);
    for (unsigned j = 0; j + 1 < eb; ++j)
    {
      ASTNode c = bit(sb - 1 + j);
      if (j == 0)
        c = nf->CreateNode(OR, c, exponent_zero);
      v = ite(c, CreateRealTerm(REAL_MUL, ASTVec{f.factors[j], v}), v);
    }
    v = ite(bit(width - 2), v, CreateRealTerm(REAL_MUL, ASTVec{f.low_half, v}));
    const ASTNode sign = bit(width - 1);
    const ASTNode finite = ite(sign, CreateRealTerm(REAL_NEG, ASTVec{v}), v);
    inner = ite(nf->CreateNode(FP_ISINFINITE, x),
                ite(sign, f.minus_infinity, f.plus_infinity), finite);
  }

  // The root, through the hashing factory: its shape is the conversion's
  // identity (FpToRealOperand), so no rewrite may touch it.
  HashingNodeFactory* hf = hashingNodeFactory;
  noteReal();
  return hf->CreateNode(ITE, hf->CreateNode(FP_ISNAN, x), f.nan, inner);
}

ASTNode STPMgr::FpToRealOperand(const ASTNode& n) const
{
  if (fp_to_real_state == nullptr || n.IsNull() || n.GetKind() != ITE ||
      n.Degree() != 3 || n[0].GetKind() != FP_ISNAN ||
      n[1].GetKind() != SYMBOL || !IsFpToRealSpecial(n[1]))
    return ASTNode();
  const auto found = fp_to_real_state->specials.find(n[1].GetNodeNum());
  if (found == fp_to_real_state->specials.end() || found->second.second != 0)
    return ASTNode();
  const ASTNode operand = n[0][0];
  const SourceSort sort = operand.GetSourceSort();
  if (sort.kind() != SourceSort::Kind::FloatingPoint ||
      sort.exponentWidth() != found->second.first.first ||
      sort.significandWidth() != found->second.first.second)
    return ASTNode();
  return operand;
}

// ---------------------------------------------------------------- linking

namespace
{

// A Real term as a * root + b, for at most one fp.to_real root: what a
// comparison needs to be read as one on the root's operand.
struct LinearForm
{
  bool ok = false;
  ASTNode root; // null: no root
  ASTNode a;    // REAL_CONST coefficient of the root (zero without one)
  ASTNode b;    // REAL_CONST
};

bool isZero(const ASTNode& c)
{
  return c.GetKind() == REAL_CONST && c.GetRealNumerator() == "0";
}

bool isNegative(const ASTNode& c)
{
  const std::string n = c.GetRealNumerator();
  return !n.empty() && n[0] == '-';
}

class Linker
{
public:
  // `definitions`: Real symbols the query equates, at its top level, with a
  // term -- what each such symbol is in every model of the query.
  Linker(STPMgr& bm, const ASTNodeMap& definitions)
      : bm_(bm), definitions_(definitions), zero_(bm.CreateRealConst("0")),
        one_(bm.CreateRealConst("1"))
  {
  }

  LinearForm form(const ASTNode& t, int depth = 0)
  {
    LinearForm out;
    if (depth > 64)
      return out;
    if (t.GetKind() == REAL_CONST)
    {
      out.ok = true;
      out.a = zero_;
      out.b = t;
      return out;
    }
    if (!bm_.FpToRealOperand(t).IsNull())
    {
      out.ok = true;
      out.root = t;
      out.a = one_;
      out.b = zero_;
      return out;
    }
    switch (t.GetKind())
    {
      case SYMBOL:
      {
        const auto defined = definitions_.find(t);
        if (defined == definitions_.end())
          return out;
        return form(defined->second, depth + 1);
      }
      case REAL_NEG:
        return scale(form(t[0], depth + 1), bm_.CreateRealConst("-1"));
      case REAL_MUL:
        if (t[0].GetKind() == REAL_CONST)
          return scale(form(t[1], depth + 1), t[0]);
        if (t[1].GetKind() == REAL_CONST)
          return scale(form(t[0], depth + 1), t[1]);
        return out;
      case REAL_DIV:
        if (t[1].GetKind() != REAL_CONST || isZero(t[1]))
          return out;
        return scale(form(t[0], depth + 1),
                     bm_.CreateRealTerm(REAL_DIV, ASTVec{one_, t[1]}));
      case REAL_ADD:
      case REAL_SUB:
      {
        if (t.GetKind() == REAL_SUB && t.Degree() == 1)
          return scale(form(t[0], depth + 1), bm_.CreateRealConst("-1"));
        LinearForm sum;
        sum.ok = true;
        sum.a = zero_;
        sum.b = zero_;
        for (std::size_t i = 0; i < t.Degree(); ++i)
        {
          LinearForm part = form(t[i], depth + 1);
          if (t.GetKind() == REAL_SUB && i != 0)
            part = scale(part, bm_.CreateRealConst("-1"));
          sum = add(sum, part);
          if (!sum.ok)
            return sum;
        }
        return sum;
      }
      default:
        return out;
    }
  }

  // lhs - rhs
  LinearForm difference(const LinearForm& lhs, const LinearForm& rhs)
  {
    return add(lhs, scale(rhs, bm_.CreateRealConst("-1")));
  }

  ASTNode rounded(const ASTNode& operand, const ASTNode& c, unsigned mode)
  {
    const SourceSort sort = operand.GetSourceSort();
    const unsigned eb = sort.exponentWidth();
    const unsigned sb = sort.significandWidth();
    std::string numerator = c.GetRealNumerator();
    const bool negative = !numerator.empty() && numerator[0] == '-';
    if (negative)
      numerator.erase(0, 1);
    std::string bits, err;
    if (!rationalToPackedFPBits(numerator, c.GetRealDenominator(), negative,
                                eb, sb, mode, bits, err))
      return ASTNode();
    return bm_.CreateFPConst(bm_.CreateBVConst(bits, 2, (int)(eb + sb)), eb,
                             sb);
  }

  ASTNode finite(const ASTNode& operand)
  {
    NodeFactory* nf = bm_.defaultNodeFactory;
    return nf->CreateNode(
        AND, nf->CreateNode(NOT, nf->CreateNode(FP_ISNAN, operand)),
        nf->CreateNode(NOT, nf->CreateNode(FP_ISINFINITE, operand)));
  }

private:
  LinearForm scale(LinearForm f, const ASTNode& k)
  {
    if (!f.ok)
      return f;
    f.a = bm_.CreateRealTerm(REAL_MUL, ASTVec{f.a, k});
    f.b = bm_.CreateRealTerm(REAL_MUL, ASTVec{f.b, k});
    return f;
  }

  LinearForm add(const LinearForm& x, const LinearForm& y)
  {
    LinearForm out;
    if (!x.ok || !y.ok)
      return out;
    if (!x.root.IsNull() && !y.root.IsNull() && x.root != y.root)
      return out; // two different conversions: not one root's comparison
    out.ok = true;
    out.root = x.root.IsNull() ? y.root : x.root;
    out.a = bm_.CreateRealTerm(REAL_ADD, ASTVec{x.a, y.a});
    out.b = bm_.CreateRealTerm(REAL_ADD, ASTVec{x.b, y.b});
    return out;
  }

  STPMgr& bm_;
  const ASTNodeMap& definitions_;
  const ASTNode zero_, one_;
};

bool isRealPredicate(const ASTNode& n)
{
  switch (n.GetKind())
  {
    case REAL_LT:
    case REAL_LE:
    case REAL_GT:
    case REAL_GE:
      return n.Degree() == 2;
    case EQ:
      return n.Degree() == 2 &&
             n[0].GetSourceSort().kind() == SourceSort::Kind::Real &&
             n[1].GetSourceSort().kind() == SourceSort::Kind::Real;
    default:
      return false;
  }
}

} // namespace

ASTNode STPMgr::LinkFpToReal(const ASTNode& input)
{
  if (fp_to_real_state == nullptr || input.IsNull())
    return input;

  // The Real predicates of the query, each once. A conversion is entered at
  // its operand only: its own nodes hold none.
  ASTVec predicates;
  {
    ASTNodeSet seen;
    std::vector<ASTNode> stack(1, input);
    while (!stack.empty())
    {
      const ASTNode n = stack.back();
      stack.pop_back();
      if (!seen.insert(n).second)
        continue;
      if (isRealPredicate(n))
        predicates.push_back(n);
      const ASTNode operand = FpToRealOperand(n);
      if (!operand.IsNull())
      {
        stack.push_back(operand);
        continue;
      }
      for (const ASTNode& c : n.GetChildren())
        stack.push_back(c);
    }
  }

  // A Real symbol the query's top level equates with a term stands for that
  // term in every model, so a comparison of the symbol is one of the term:
  // (= r (fp.to_real x)) with (< r 1.5) links the second through the first.
  // The first equation for each symbol, and never one that mentions it on
  // both sides (form() bounds the depth of any chain).
  ASTNodeMap definitions;
  {
    std::vector<ASTNode> stack(1, input);
    ASTNodeSet seen;
    while (!stack.empty())
    {
      const ASTNode n = stack.back();
      stack.pop_back();
      if (!seen.insert(n).second)
        continue;
      if (n.GetKind() == AND)
      {
        for (const ASTNode& c : n.GetChildren())
          stack.push_back(c);
        continue;
      }
      if (n.GetKind() != EQ || n.Degree() != 2)
        continue;
      for (int side = 0; side < 2; ++side)
      {
        const ASTNode& symbol = n[side];
        const ASTNode& term = n[1 - side];
        if (symbol.GetKind() == SYMBOL &&
            symbol.GetSourceSort().kind() == SourceSort::Kind::Real &&
            term.GetSourceSort().kind() == SourceSort::Kind::Real &&
            term != symbol && definitions.count(symbol) == 0)
        {
          definitions[symbol] = term;
          break;
        }
      }
    }
  }

  Linker linker(*this, definitions);
  NodeFactory* nf = defaultNodeFactory;
  ASTVec facts;
  for (const ASTNode& p : predicates)
  {
    const Kind k = p.GetKind();

    // Two conversions of one format: the comparison of their operands.
    {
      const ASTNode x = FpToRealOperand(p[0]);
      const ASTNode y = FpToRealOperand(p[1]);
      if (!x.IsNull() && !y.IsNull())
      {
        if (x == y || x.GetSourceSort() != y.GetSourceSort())
          continue;
        const Kind fk = k == REAL_LT   ? FP_LT
                        : k == REAL_LE ? FP_LEQ
                        : k == REAL_GT ? FP_GT
                        : k == REAL_GE ? FP_GEQ
                                       : FP_EQ;
        facts.push_back(nf->CreateNode(
            IMPLIES,
            nf->CreateNode(AND, linker.finite(x), linker.finite(y)),
            nf->CreateNode(IFF, p, nf->CreateNode(fk, x, y))));
        continue;
      }
    }

    // One conversion against a constant: a * root + b ~ 0.
    const LinearForm d =
        linker.difference(linker.form(p[0]), linker.form(p[1]));
    if (!d.ok || d.root.IsNull() || isZero(d.a))
      continue;
    const ASTNode operand = FpToRealOperand(d.root);
    // root ~' c, with c = -b / a and ~' the relation, reversed when a < 0.
    const ASTNode c = CreateRealTerm(
        REAL_DIV, ASTVec{CreateRealTerm(REAL_NEG, ASTVec{d.b}), d.a});
    Kind rel = k;
    if (isNegative(d.a))
      rel = k == REAL_LT   ? REAL_GT
            : k == REAL_LE ? REAL_GE
            : k == REAL_GT ? REAL_LT
            : k == REAL_GE ? REAL_LE
                           : EQ;

    // For a finite float v and a real c:
    //   v > c  iff v > RTN(c)      v >= c iff v >= RTP(c)
    //   v < c  iff v < RTP(c)      v <= c iff v <= RTN(c)
    //   v = c  iff RTN(c) = RTP(c) (c is a float) and v = RTN(c)
    // RTN(c) is the largest float at most c, RTP(c) the smallest at least
    // c; beyond the finite range they are the infinities the directed modes
    // give, and each identity above still holds for every finite v.
    const ASTNode down = linker.rounded(operand, c, symbolic_fp::ROUND_TOWARD_NEGATIVE);
    const ASTNode up = linker.rounded(operand, c, symbolic_fp::ROUND_TOWARD_POSITIVE);
    if (down.IsNull() || up.IsNull())
      continue; // a format the exact conversion does not cover
    ASTNode comparison;
    switch (rel)
    {
      case REAL_GT: comparison = nf->CreateNode(FP_GT, operand, down); break;
      case REAL_GE: comparison = nf->CreateNode(FP_GEQ, operand, up); break;
      case REAL_LT: comparison = nf->CreateNode(FP_LT, operand, up); break;
      case REAL_LE: comparison = nf->CreateNode(FP_LEQ, operand, down); break;
      default:
        comparison = down == up ? nf->CreateNode(FP_EQ, operand, down)
                                : ASTFalse;
        break;
    }
    facts.push_back(nf->CreateNode(
        IMPLIES, linker.finite(operand), nf->CreateNode(IFF, p, comparison)));
  }

  if (facts.empty())
    return input;
  facts.push_back(input);
  return nf->CreateNode(AND, facts);
}

} // namespace stp
