/***********
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
**********************/

/*
 * The constant evaluator, exhaustively at small widths, against an
 * independent oracle written in plain integer arithmetic.
 *
 * The other exhaustive tests (and propagator_bench's precision phase) use
 * NonMemberBVConstEvaluator itself as their ground truth, so they prove
 * the analyses agree with the evaluator but cannot catch the evaluator's
 * own semantics changing. This one can: nothing here goes through
 * constantbv except the code under test.
 *
 * Both entry points are checked on every input: the node-level
 * NonMemberBVConstEvaluator, and the bit-vector-level overload /
 * NonMemberBVConstPredicateEvaluator that the value-set analysis uses.
 */

#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include <gtest/gtest.h>
#include <vector>

using stp::ASTNode;
using stp::ASTVec;
using stp::Kind;

namespace
{

const unsigned MAX_WIDTH = 6; // exhaustive over both operands up to here.

uint64_t mask(unsigned w)
{
  return (1ull << w) - 1;
}

int64_t toSigned(uint64_t v, unsigned w)
{
  return (int64_t)(v << (64 - w)) >> (64 - w);
}

stp::CBV makeCBV(unsigned width, uint64_t value)
{
  stp::CBV result = CONSTANTBV::BitVector_Create(width, true);
  for (unsigned i = 0; i < width; i++)
    if ((value >> i) & 1)
      CONSTANTBV::BitVector_Bit_On(result, i);
  return result;
}

uint64_t fromCBV(const stp::CBV v)
{
  uint64_t result = 0;
  for (unsigned i = 0; i < bits_(v); i++)
    if (CONSTANTBV::BitVector_bit_test(v, i))
      result |= 1ull << i;
  return result;
}

struct Context
{
  stp::STPMgr mgr;

  ASTNode constant(unsigned width, uint64_t value)
  {
    return mgr.CreateBVConst(width, value);
  }

  // The node-level evaluator's result as a number.
  uint64_t evalNode(Kind k, const ASTVec& children, unsigned outWidth)
  {
    const ASTNode r =
        stp::NonMemberBVConstEvaluator(&mgr, k, children, outWidth);
    if (stp::TRUE == r.GetKind())
      return 1;
    if (stp::FALSE == r.GetKind())
      return 0;
    return fromCBV(r.GetBVConst());
  }

  // The bit-vector-level evaluator's result as a number, and the width it
  // came back with.
  uint64_t evalCBV(Kind k, const std::vector<uint64_t>& values,
                   const std::vector<unsigned>& widths, unsigned outWidth,
                   unsigned& resultWidth)
  {
    std::vector<stp::CBV> args;
    for (size_t i = 0; i < values.size(); i++)
      args.push_back(makeCBV(widths[i], values[i]));

    const stp::CBV r = stp::NonMemberBVConstEvaluator(k, args, outWidth);
    resultWidth = bits_(r);
    const uint64_t result = fromCBV(r);

    CONSTANTBV::BitVector_Destroy(r);
    for (const stp::CBV a : args)
      CONSTANTBV::BitVector_Destroy(a);
    return result;
  }

  bool predicateCBV(Kind k, uint64_t a, unsigned wa, uint64_t b, unsigned wb)
  {
    stp::CBV ca = makeCBV(wa, a);
    stp::CBV cb = makeCBV(wb, b);
    const bool result = stp::NonMemberBVConstPredicateEvaluator(k, ca, cb);
    CONSTANTBV::BitVector_Destroy(ca);
    CONSTANTBV::BitVector_Destroy(cb);
    return result;
  }
};

// The oracle for the terms whose children all have the node's width.
uint64_t oracleTerm(Kind k, const std::vector<uint64_t>& v, unsigned w)
{
  const uint64_t m = mask(w);
  const uint64_t x = v[0];
  const uint64_t y = v.size() > 1 ? v[1] : 0;
  const int64_t sx = toSigned(x, w);
  const int64_t sy = v.size() > 1 ? toSigned(y, w) : 0;

  switch (k)
  {
    case stp::BVNOT:
      return ~x & m;
    case stp::BVUMINUS:
      return (uint64_t)(-sx) & m;

    case stp::BVAND:
    {
      uint64_t r = m;
      for (const uint64_t a : v)
        r &= a;
      return r;
    }
    case stp::BVOR:
    {
      uint64_t r = 0;
      for (const uint64_t a : v)
        r |= a;
      return r;
    }
    case stp::BVXOR:
    {
      uint64_t r = 0;
      for (const uint64_t a : v)
        r ^= a;
      return r;
    }
    case stp::BVPLUS:
    {
      uint64_t r = 0;
      for (const uint64_t a : v)
        r += a;
      return r & m;
    }
    case stp::BVMULT:
    {
      uint64_t r = 1;
      for (const uint64_t a : v)
        r = (r * a) & m;
      return r;
    }
    case stp::BVSUB:
      return (x - y) & m;

    // Division by zero is defined in SMT-LIB; see the BVDIV and SBVDIV
    // cases of consteval.cpp.
    case stp::BVDIV:
      return y == 0 ? m : x / y;
    case stp::BVMOD:
      return y == 0 ? x : x % y;
    case stp::SBVDIV:
      if (sy == 0)
        return sx < 0 ? 1 : m;
      return (uint64_t)(sx / sy) & m;
    case stp::SBVREM:
      if (sy == 0)
        return x;
      return (uint64_t)(sx % sy) & m;
    case stp::SBVMOD:
    {
      // Truncated remainder, then pulled onto the divisor's side of zero:
      // the result is either zero or has the divisor's sign.
      if (sy == 0)
        return x;
      int64_t r = sx % sy;
      if (r != 0 && (r < 0) != (sy < 0))
        r += sy;
      return (uint64_t)r & m;
    }

    // Shifting by the width or more pushes everything out.
    case stp::BVLEFTSHIFT:
      return y >= w ? 0 : (x << y) & m;
    case stp::BVRIGHTSHIFT:
      return y >= w ? 0 : x >> y;
    case stp::BVSRSHIFT:
      if (y >= w)
        return sx < 0 ? m : 0;
      return (uint64_t)(sx >> y) & m;

    default:
      ADD_FAILURE() << "not a term kind: " << k;
      return 0;
  }
}

// The oracle for the predicates over two width-w bit-vectors.
bool oraclePredicate(Kind k, uint64_t x, uint64_t y, unsigned w)
{
  const int64_t sx = toSigned(x, w);
  const int64_t sy = toSigned(y, w);
  const int64_t lo = -(1ll << (w - 1));
  const int64_t hi = (1ll << (w - 1)) - 1;

  switch (k)
  {
    case stp::EQ:
      return x == y;
    case stp::BVLT:
      return x < y;
    case stp::BVLE:
      return x <= y;
    case stp::BVGT:
      return x > y;
    case stp::BVGE:
      return x >= y;
    case stp::BVSLT:
      return sx < sy;
    case stp::BVSLE:
      return sx <= sy;
    case stp::BVSGT:
      return sx > sy;
    case stp::BVSGE:
      return sx >= sy;

    case stp::BVUADDO:
      return x + y > mask(w);
    case stp::BVSADDO:
      return sx + sy < lo || sx + sy > hi;
    case stp::BVUSUBO:
      return x < y;
    case stp::BVSSUBO:
      return sx - sy < lo || sx - sy > hi;
    case stp::BVUMULO:
      return x * y > mask(w);
    case stp::BVSMULO:
      return sx * sy < lo || sx * sy > hi;

    default:
      ADD_FAILURE() << "not a predicate kind: " << k;
      return false;
  }
}

TEST(ConstantEvaluator_Exhaustive, terms)
{
  Context c;

  const std::vector<Kind> unary = {stp::BVNOT, stp::BVUMINUS};
  const std::vector<Kind> binary = {
      stp::BVAND,       stp::BVOR,          stp::BVXOR,   stp::BVPLUS,
      stp::BVSUB,       stp::BVMULT,        stp::BVDIV,   stp::BVMOD,
      stp::SBVDIV,      stp::SBVREM,        stp::SBVMOD,  stp::BVLEFTSHIFT,
      stp::BVRIGHTSHIFT, stp::BVSRSHIFT};
  // The n-ary ones, at three children as well.
  const std::vector<Kind> ternary = {stp::BVAND, stp::BVOR, stp::BVXOR,
                                     stp::BVPLUS, stp::BVMULT};

  for (unsigned w = 1; w <= MAX_WIDTH; w++)
    for (uint64_t x = 0; x <= mask(w); x++)
    {
      for (const Kind k : unary)
      {
        const uint64_t expected = oracleTerm(k, {x}, w);
        EXPECT_EQ(expected, c.evalNode(k, {c.constant(w, x)}, w))
            << k << " " << w << " " << x;
        unsigned rw;
        EXPECT_EQ(expected, c.evalCBV(k, {x}, {w}, w, rw));
        EXPECT_EQ(w, rw);
      }

      for (uint64_t y = 0; y <= mask(w); y++)
      {
        for (const Kind k : binary)
        {
          const uint64_t expected = oracleTerm(k, {x, y}, w);
          EXPECT_EQ(expected,
                    c.evalNode(k, {c.constant(w, x), c.constant(w, y)}, w))
              << k << " " << w << " " << x << " " << y;
          unsigned rw;
          EXPECT_EQ(expected, c.evalCBV(k, {x, y}, {w, w}, w, rw))
              << k << " " << w << " " << x << " " << y;
          EXPECT_EQ(w, rw);
        }

        if (w <= 3)
          for (uint64_t z = 0; z <= mask(w); z++)
            for (const Kind k : ternary)
            {
              const uint64_t expected = oracleTerm(k, {x, y, z}, w);
              EXPECT_EQ(expected,
                        c.evalNode(k, {c.constant(w, x), c.constant(w, y),
                                       c.constant(w, z)},
                                   w))
                  << k << " " << w << " " << x << " " << y << " " << z;
              unsigned rw;
              EXPECT_EQ(expected, c.evalCBV(k, {x, y, z}, {w, w, w}, w, rw));
            }
      }
    }
}

TEST(ConstantEvaluator_Exhaustive, extendsExtractConcat)
{
  Context c;

  // Zero- and sign-extension, from every width to every wider-or-equal one.
  for (unsigned w1 = 1; w1 <= 4; w1++)
    for (unsigned w2 = w1; w2 <= MAX_WIDTH; w2++)
      for (uint64_t x = 0; x <= mask(w1); x++)
      {
        const uint64_t zx = x;
        const uint64_t sx = (uint64_t)toSigned(x, w1) & mask(w2);

        for (const Kind k : {stp::BVZX, stp::BVSX})
        {
          const uint64_t expected = stp::BVZX == k ? zx : sx;
          EXPECT_EQ(expected,
                    c.evalNode(k, {c.constant(w1, x), c.constant(32, w2)}, w2))
              << k << " " << w1 << "->" << w2 << " " << x;
          unsigned rw;
          EXPECT_EQ(expected, c.evalCBV(k, {x, w2}, {w1, 32}, w2, rw));
          EXPECT_EQ(w2, rw);
        }
      }

  // Extraction, over every hi >= low pair.
  for (unsigned w = 1; w <= MAX_WIDTH; w++)
    for (uint64_t x = 0; x <= mask(w); x++)
      for (unsigned hi = 0; hi < w; hi++)
        for (unsigned low = 0; low <= hi; low++)
        {
          const unsigned len = hi - low + 1;
          const uint64_t expected = (x >> low) & mask(len);
          EXPECT_EQ(expected,
                    c.evalNode(stp::BVEXTRACT,
                               {c.constant(w, x), c.constant(32, hi),
                                c.constant(32, low)},
                               len))
              << w << " " << x << " [" << hi << ":" << low << "]";
          unsigned rw;
          EXPECT_EQ(expected, c.evalCBV(stp::BVEXTRACT, {x, hi, low},
                                        {w, 32, 32}, len, rw));
          EXPECT_EQ(len, rw);
        }

  // Concatenation: the first child is the high part.
  for (unsigned w1 = 1; w1 <= 4; w1++)
    for (unsigned w2 = 1; w2 <= 4; w2++)
      for (uint64_t x = 0; x <= mask(w1); x++)
        for (uint64_t y = 0; y <= mask(w2); y++)
        {
          const uint64_t expected = (x << w2) | y;
          EXPECT_EQ(expected,
                    c.evalNode(stp::BVCONCAT,
                               {c.constant(w1, x), c.constant(w2, y)},
                               w1 + w2))
              << w1 << "+" << w2 << " " << x << " " << y;
          unsigned rw;
          EXPECT_EQ(expected,
                    c.evalCBV(stp::BVCONCAT, {x, y}, {w1, w2}, w1 + w2, rw));
          EXPECT_EQ(w1 + w2, rw);
        }
}

TEST(ConstantEvaluator_Exhaustive, predicates)
{
  Context c;

  const std::vector<Kind> predicates = {
      stp::EQ,      stp::BVLT,    stp::BVLE,    stp::BVGT,
      stp::BVGE,    stp::BVSLT,   stp::BVSLE,   stp::BVSGT,
      stp::BVSGE,   stp::BVUADDO, stp::BVSADDO, stp::BVUSUBO,
      stp::BVSSUBO, stp::BVUMULO, stp::BVSMULO};

  for (unsigned w = 1; w <= MAX_WIDTH; w++)
    for (uint64_t x = 0; x <= mask(w); x++)
      for (uint64_t y = 0; y <= mask(w); y++)
        for (const Kind k : predicates)
        {
          const bool expected = oraclePredicate(k, x, y, w);
          EXPECT_EQ(expected ? 1u : 0u,
                    c.evalNode(k, {c.constant(w, x), c.constant(w, y)}, 0))
              << k << " " << w << " " << x << " " << y;
          EXPECT_EQ(expected, c.predicateCBV(k, x, w, y, w))
              << k << " " << w << " " << x << " " << y;
        }

  // Boolean extraction of every bit.
  for (unsigned w = 1; w <= MAX_WIDTH; w++)
    for (uint64_t x = 0; x <= mask(w); x++)
      for (unsigned i = 0; i < w; i++)
      {
        const bool expected = (x >> i) & 1;
        EXPECT_EQ(expected ? 1u : 0u,
                  c.evalNode(stp::BOOLEXTRACT,
                             {c.constant(w, x), c.constant(32, i)}, 0));
        EXPECT_EQ(expected, c.predicateCBV(stp::BOOLEXTRACT, x, w, i, 32));
      }
}

TEST(ConstantEvaluator_Exhaustive, booleansAndITE)
{
  Context c;
  const ASTNode t = c.mgr.ASTTrue;
  const ASTNode f = c.mgr.ASTFalse;
  const auto node = [&](bool b) { return b ? t : f; };

  for (unsigned x = 0; x <= 1; x++)
    EXPECT_EQ(x ? 0u : 1u, c.evalNode(stp::NOT, {node(x)}, 0));

  for (unsigned x = 0; x <= 1; x++)
    for (unsigned y = 0; y <= 1; y++)
    {
      EXPECT_EQ((x && y) ? 1u : 0u, c.evalNode(stp::AND, {node(x), node(y)}, 0));
      EXPECT_EQ((x || y) ? 1u : 0u, c.evalNode(stp::OR, {node(x), node(y)}, 0));
      EXPECT_EQ((x && y) ? 0u : 1u,
                c.evalNode(stp::NAND, {node(x), node(y)}, 0));
      EXPECT_EQ((x || y) ? 0u : 1u, c.evalNode(stp::NOR, {node(x), node(y)}, 0));
      EXPECT_EQ((x ^ y) ? 1u : 0u, c.evalNode(stp::XOR, {node(x), node(y)}, 0));
      EXPECT_EQ((x == y) ? 1u : 0u,
                c.evalNode(stp::IFF, {node(x), node(y)}, 0));
      EXPECT_EQ((!x || y) ? 1u : 0u,
                c.evalNode(stp::IMPLIES, {node(x), node(y)}, 0));

      // Three children for the n-ary connectives.
      for (unsigned z = 0; z <= 1; z++)
      {
        EXPECT_EQ((x && y && z) ? 1u : 0u,
                  c.evalNode(stp::AND, {node(x), node(y), node(z)}, 0));
        EXPECT_EQ((x || y || z) ? 1u : 0u,
                  c.evalNode(stp::OR, {node(x), node(y), node(z)}, 0));
        EXPECT_EQ((x && y && z) ? 0u : 1u,
                  c.evalNode(stp::NAND, {node(x), node(y), node(z)}, 0));
        EXPECT_EQ((x || y || z) ? 0u : 1u,
                  c.evalNode(stp::NOR, {node(x), node(y), node(z)}, 0));
        EXPECT_EQ((x ^ y ^ z) ? 1u : 0u,
                  c.evalNode(stp::XOR, {node(x), node(y), node(z)}, 0));
      }
    }

  // ITE picks the branch its condition names.
  for (unsigned cond = 0; cond <= 1; cond++)
  {
    EXPECT_EQ(cond ? 5u : 9u,
              c.evalNode(stp::ITE,
                         {node(cond), c.constant(4, 5), c.constant(4, 9)}, 4));
    EXPECT_EQ(cond ? 1u : 0u, c.evalNode(stp::ITE, {node(cond), t, f}, 0));
  }
}

} // namespace
