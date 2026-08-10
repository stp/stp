/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: July 2026
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

// Unit tests for stp::symbolic_fp::bitVector, the bit-vector backend that
// symfpu builds floating-point circuits out of, and for the float-to-integer
// conversions layered on it.
//
// symfpu exercises only part of this interface, and a wrong answer in the part
// it does use shows up as a mis-rounded float many layers away -- so these are
// worth checking directly. Each operation is applied to constants and the
// resulting term folded, so the answer can be compared with one worked out by
// hand. Written after finding that bitVector<true>::minValue returned 0
// rather than the most negative value.

#include "stp/FloatBlaster/symbolic_fp.h"
#include "stp/STPManager/STPManager.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/AST/AST.h"

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <string>

using namespace stp;
using namespace stp::symbolic_fp;

static STPMgr* bm = nullptr;
static int failures = 0;
static int checks = 0;

// Fold a term to a constant and return its value.
static uint64_t value_of(const ASTNode& n)
{
  const ASTNode c = NonMemberBVConstEvaluator(bm, n);
  if (c.GetKind() != BVCONST)
  {
    printf("    (not a constant!)\n");
    return ~0ull;
  }
  // GetUnsignedConst only handles <= 32 bits; read the bits directly.
  uint64_t v = 0;
  const unsigned w = c.GetValueWidth();
  for (unsigned i = 0; i < w && i < 64; i++)
    if (CONSTANTBV::BitVector_bit_test(c.GetBVConst(), i))
      v |= (1ull << i);
  return v;
}

static void check(const char* what, uint64_t got, uint64_t want)
{
  checks++;
  const bool ok = (got == want);
  if (!ok)
    failures++;
  printf("  %-46s got=%-12llu want=%-12llu %s\n", what,
         (unsigned long long)got, (unsigned long long)want,
         ok ? "ok" : "** MISMATCH **");
}

// symfpu states its properties through PRECONDITION/POSTCONDITION/INVARIANT,
// and calls them with either a plain bool or a prop. This backend redefines
// all three (see symbolic_fp.h): a prop here is a circuit constructor whose
// result nothing can check while the circuit is being built, so constructing
// it at all is pure waste -- while the bool properties are real checks and
// must keep firing. These two counters pin both halves.
static int props_constructed = 0;
static int bools_evaluated = 0;

// Never actually called, and that is the assertion: the property macros
// discard a prop argument without evaluating it, so props_constructed must
// stay at zero. Clang sees an internal function with no call site and warns
// that it will not be emitted, which here is the expected outcome.
[[maybe_unused]] static proposition countedProp()
{
  ++props_constructed;
  return proposition(true);
}

static bool countedBool()
{
  ++bools_evaluated;
  return true;
}

static void check_width(const char* what, unsigned got, unsigned want)
{
  checks++;
  const bool ok = (got == want);
  if (!ok)
    failures++;
  printf("  %-46s width=%-10u want=%-10u %s\n", what, got, want,
         ok ? "ok" : "** MISMATCH **");
}

// Every float here is a Float32; blast_fp_to_bv now takes that format
// explicitly rather than reading it back off the operand node.
static const floatingPointTypeInfo binary32(8, 24);

// Build a Float32 constant from its IEEE bits.
static ASTNode f32(uint32_t bits)
{
  ASTNode n = bm->CreateBVConst(32, bits);
  return bm->CreateFPConst(n, 8, 24);
}

// fp.to_ubv/fp.to_sbv from packed bits. The solver keeps its floats unpacked
// between operations and only this tool wants a one-shot packed form, so the
// decode is spelled out here rather than kept as a second entry point in the
// backend -- there is one lowering table now, and this is not another one.
static ASTNode blast_fp_to_bv(const floatingPointTypeInfo& size,
                              const ASTNode& rm, const ASTNode& expr,
                              bitWidthType target_width, const ASTNode& undef,
                              bool is_signed)
{
  return unpacked::toBV(size, rm, unpacked::decode(size, expr), target_width,
                        undef, is_signed);
}

static uint32_t bits_of(float f)
{
  uint32_t u;
  memcpy(&u, &f, 4);
  return u;
}

template <bool S> static bitVector<S> mk(unsigned w, unsigned v)
{
  return bitVector<S>(w, v);
}

int main()
{
  bm = new STPMgr();
  GlobalParserBM = bm;
  auto* nf = new SimplifyingNodeFactory(*bm->hashingNodeFactory, *bm);
  bm->defaultNodeFactory = nf;
  symbolic_fp::init(bm);

  printf("== constructors and constants ==\n");
  check("ubv(8, 5)", value_of(mk<false>(8, 5)), 5);
  check("ubv::zero(8)", value_of(bitVector<false>::zero(8)), 0);
  check("ubv::one(8)", value_of(bitVector<false>::one(8)), 1);
  check("ubv::allOnes(8)", value_of(bitVector<false>::allOnes(8)), 0xFF);
  check("ubv::maxValue(8)", value_of(bitVector<false>::maxValue(8)), 0xFF);
  check("ubv::minValue(8)", value_of(bitVector<false>::minValue(8)), 0);
  check("sbv::maxValue(8)", value_of(bitVector<true>::maxValue(8)), 0x7F);
  check("sbv::minValue(8)", value_of(bitVector<true>::minValue(8)), 0x80);

  printf("== arithmetic ==\n");
  check("ubv 5 + 3", value_of(mk<false>(8, 5) + mk<false>(8, 3)), 8);
  check("ubv 5 - 3", value_of(mk<false>(8, 5) - mk<false>(8, 3)), 2);
  check("ubv 5 * 3", value_of(mk<false>(8, 5) * mk<false>(8, 3)), 15);
  check("ubv 15 / 3", value_of(mk<false>(8, 15) / mk<false>(8, 3)), 5);
  check("ubv 17 % 5", value_of(mk<false>(8, 17) % mk<false>(8, 5)), 2);
  check("sbv -7 % 3 (remainder)",
        value_of(mk<true>(8, 0xF9) % mk<true>(8, 3)), 0xFF);
  check("sbv 7 % -3 (remainder)",
        value_of(mk<true>(8, 7) % mk<true>(8, 0xFD)), 1);
  check("sbv -7 % -3 (remainder)",
        value_of(mk<true>(8, 0xF9) % mk<true>(8, 0xFD)), 0xFF);
  check("ubv -(5)", value_of(-mk<false>(8, 5)), 0xFB);
  check("ubv ~(5)", value_of(~mk<false>(8, 5)), 0xFA);
  check("ubv 5.increment()", value_of(mk<false>(8, 5).increment()), 6);
  check("ubv 5.decrement()", value_of(mk<false>(8, 5).decrement()), 4);

  printf("== modular arithmetic ==\n");
  check("ubv 250 modularAdd 10", value_of(mk<false>(8, 250).modularAdd(mk<false>(8, 10))), 4);
  check("ubv 5 modularSubtract 10", value_of(mk<false>(8, 5).modularSubtract(mk<false>(8, 10))), 251);
  check("ubv 255 modularIncrement", value_of(mk<false>(8, 255).modularIncrement()), 0);
  check("ubv 0 modularDecrement", value_of(mk<false>(8, 0).modularDecrement()), 255);
  check("ubv 5 modularNegate", value_of(mk<false>(8, 5).modularNegate()), 251);
  check("ubv 1 modularLeftShift 3", value_of(mk<false>(8, 1).modularLeftShift(mk<false>(8, 3))), 8);
  check("ubv 128 modularRightShift 3", value_of(mk<false>(8, 128).modularRightShift(mk<false>(8, 3))), 16);

  printf("== bitwise and shifts ==\n");
  check("ubv 0xF0 | 0x0F", value_of(mk<false>(8, 0xF0) | mk<false>(8, 0x0F)), 0xFF);
  check("ubv 0xF3 & 0x0F", value_of(mk<false>(8, 0xF3) & mk<false>(8, 0x0F)), 0x03);
  check("ubv 1 << 4", value_of(mk<false>(8, 1) << mk<false>(8, 4)), 16);
  check("ubv 128 >> 4", value_of(mk<false>(8, 128) >> mk<false>(8, 4)), 8);
  check("sbv 0x80 >> 3 (arithmetic)", value_of(mk<true>(8, 0x80) >> mk<true>(8, 3)), 0xF0);
  check("sbv 0x80 signExtendRightShift 3",
        value_of(mk<true>(8, 0x80).signExtendRightShift(mk<true>(8, 3))), 0xF0);

  printf("== width manipulation ==\n");
  check("ubv 5 extend(4)", value_of(mk<false>(8, 5).extend(4)), 5);
  check_width("ubv 5 extend(4) width", mk<false>(8, 5).extend(4).getWidth(), 12);
  check("ubv 5 extend(0)", value_of(mk<false>(8, 5).extend(0)), 5);
  check_width("ubv 5 extend(0) width", mk<false>(8, 5).extend(0).getWidth(), 8);
  check("sbv -5 extend(4)", value_of(mk<true>(8, 0xFB).extend(4)), 0xFFB);
  check_width("sbv -5 extend(4) width", mk<true>(8, 0xFB).extend(4).getWidth(), 12);
  check("sbv 5 extend(0)", value_of(mk<true>(8, 5).extend(0)), 5);
  check("ubv 0x1FF contract(4)", value_of(mk<false>(12, 0x1FF).contract(4)), 0xFF);
  check_width("ubv contract(4) width", mk<false>(12, 0x1FF).contract(4).getWidth(), 8);
  check("ubv 5 resize(16)", value_of(mk<false>(8, 5).resize(16)), 5);
  check_width("ubv 5 resize(16) width", mk<false>(8, 5).resize(16).getWidth(), 16);
  check("ubv 0x1FF resize(8)", value_of(mk<false>(12, 0x1FF).resize(8)), 0xFF);
  check("ubv 5 resize(8) (no change)", value_of(mk<false>(8, 5).resize(8)), 5);
  check("ubv 5 matchWidth(w16)",
        value_of(mk<false>(8, 5).matchWidth(mk<false>(16, 0))), 5);
  check_width("ubv 5 matchWidth(w16) width",
              mk<false>(8, 5).matchWidth(mk<false>(16, 0)).getWidth(), 16);
  check("sbv -5 matchWidth(w16)",
        value_of(mk<true>(8, 0xFB).matchWidth(mk<true>(16, 0))), 0xFFFB);
  check("ubv 5 matchWidth(same)",
        value_of(mk<false>(8, 5).matchWidth(mk<false>(8, 0))), 5);
  check("ubv 0xAB append 0xCD",
        value_of(mk<false>(8, 0xAB).append(mk<false>(8, 0xCD))), 0xABCD);
  check("ubv 0xABCD extract(15,8)",
        value_of(mk<false>(16, 0xABCD).extract(15, 8)), 0xAB);
  check("ubv 0xABCD extract(7,0)",
        value_of(mk<false>(16, 0xABCD).extract(7, 0)), 0xCD);
  check("ubv 0xABCD extract(11,4)",
        value_of(mk<false>(16, 0xABCD).extract(11, 4)), 0xBC);

  printf("== sign conversion ==\n");
  check("ubv 0xFB toSigned", value_of(mk<false>(8, 0xFB).toSigned()), 0xFB);
  check("sbv 0xFB toUnsigned", value_of(mk<true>(8, 0xFB).toUnsigned()), 0xFB);

  printf("== predicates (1 = true) ==\n");
  auto p = [](const proposition& q) -> uint64_t {
    const ASTNode n = q;
    return (n == GlobalParserBM->ASTTrue) ? 1
           : (n == GlobalParserBM->ASTFalse)
               ? 0
               : value_of(n) /* not folded */;
  };
  check("ubv 0xFF isAllOnes", p(mk<false>(8, 0xFF).isAllOnes()), 1);
  check("ubv 0xFE isAllOnes", p(mk<false>(8, 0xFE).isAllOnes()), 0);
  check("ubv 0 isAllZeros", p(mk<false>(8, 0).isAllZeros()), 1);
  check("ubv 1 isAllZeros", p(mk<false>(8, 1).isAllZeros()), 0);
  check("ubv 5 == 5", p(mk<false>(8, 5) == mk<false>(8, 5)), 1);
  check("ubv 5 == 6", p(mk<false>(8, 5) == mk<false>(8, 6)), 0);
  check("ubv 5 < 6", p(mk<false>(8, 5) < mk<false>(8, 6)), 1);
  check("ubv 6 < 5", p(mk<false>(8, 6) < mk<false>(8, 5)), 0);
  check("ubv 5 <= 5", p(mk<false>(8, 5) <= mk<false>(8, 5)), 1);
  check("ubv 6 > 5", p(mk<false>(8, 6) > mk<false>(8, 5)), 1);
  check("ubv 5 >= 5", p(mk<false>(8, 5) >= mk<false>(8, 5)), 1);
  check("ubv 0xFF > 1 (unsigned)", p(mk<false>(8, 0xFF) > mk<false>(8, 1)), 1);
  check("sbv 0xFF < 1 (signed, -1 < 1)", p(mk<true>(8, 0xFF) < mk<true>(8, 1)), 1);
  check("sbv 0xFF > 1 (signed, -1 > 1 false)", p(mk<true>(8, 0xFF) > mk<true>(8, 1)), 0);
  check("sbv 0x80 <= 0x7F (signed min <= max)",
        p(mk<true>(8, 0x80) <= mk<true>(8, 0x7F)), 1);
  check("sbv 0x7F >= 0x80 (signed max >= min)",
        p(mk<true>(8, 0x7F) >= mk<true>(8, 0x80)), 1);

  const roundingMode rtz(traits::RTZ());
  const roundingMode rne(traits::RNE());

  // A distinctive undefined value, so it is obvious when it leaks out.
  const bitVector<false> undef_u(32, 0xDEAD);
  const bitVector<true> undef_s(32, 0xDEAD);

  printf("== convertFloatToUBV (RTZ), undef = 0xDEAD ==\n");
  const struct
  {
    float in;
    uint64_t want;
    const char* name;
  } ucases[] = {
      {4.0f, 4, "to_ubv(4.0)"},       {0.0f, 0, "to_ubv(0.0)"},
      {1.0f, 1, "to_ubv(1.0)"},       {7.9f, 7, "to_ubv(7.9) trunc"},
      {255.0f, 255, "to_ubv(255.0)"}, {65536.0f, 65536, "to_ubv(65536.0)"},
      {-1.0f, 0xDEAD, "to_ubv(-1.0) undefined"},
  };

  for (const auto& c : ucases)
  {
    const ASTNode r =
        blast_fp_to_bv(binary32, rtz, f32(bits_of(c.in)), 32, undef_u,
                       /* is_signed */ false);
    check(c.name, value_of(r), c.want);
  }

  printf("== convertFloatToSBV (RTZ), undef = 0xDEAD ==\n");
  const struct
  {
    float in;
    uint64_t want;
    const char* name;
  } scases[] = {
      {4.0f, 4, "to_sbv(4.0)"},
      {-4.0f, 0xFFFFFFFC, "to_sbv(-4.0)"},
      {0.0f, 0, "to_sbv(0.0)"},
      {-1.0f, 0xFFFFFFFF, "to_sbv(-1.0)"},
      {7.9f, 7, "to_sbv(7.9) trunc"},
      {-7.9f, 0xFFFFFFF9, "to_sbv(-7.9) trunc toward zero"},
  };

  for (const auto& c : scases)
  {
    const ASTNode r =
        blast_fp_to_bv(binary32, rtz, f32(bits_of(c.in)), 32, undef_s,
                       /* is_signed */ true);
    check(c.name, value_of(r), c.want);
  }

  printf("== convertFloatToUBV (RNE) ==\n");
  {
    const ASTNode r =
        blast_fp_to_bv(binary32, rne, f32(bits_of(7.5f)), 32, undef_u, false);
    check("to_ubv RNE(7.5) -> 8 (ties to even)", value_of(r), 8);
  }
  {
    const ASTNode r =
        blast_fp_to_bv(binary32, rne, f32(bits_of(4.0f)), 32, undef_u, false);
    check("to_ubv RNE(4.0)", value_of(r), 4);
  }

  printf("== narrow target widths ==\n");
  {
    const ASTNode r = blast_fp_to_bv(binary32, rtz, f32(bits_of(4.0f)), 8,
                                     bitVector<false>(8, 0xAB), false);
    check("to_ubv(4.0) width 8", value_of(r), 4);
  }

  printf("== symbolic undefined value (as at formula level) ==\n");
  {
    // The array read the totalising pass introduces becomes a plain symbol
    // once the array transformer has run, so this is what the blaster really
    // sees. The result should still fold to the converted value, because the
    // "is it undefined?" condition is constant-false for 4.0.
    ASTNode sym = bm->defaultNodeFactory->CreateSymbol("undef_sym", 0, 32);
    const ASTNode r = blast_fp_to_bv(binary32, rtz, f32(bits_of(4.0f)), 32,
                                     bitVector<false>(sym), false);
    printf("  result kind = %s, width = %u\n",
           _kind_names[r.GetKind()], r.GetValueWidth());
    check("to_ubv(4.0) with symbolic undef", value_of(r), 4);
  }

  printf("== symfpu property hooks ==\n");
  {
    // A prop-valued property must not be constructed at all. symfpu's default
    // expansion is a plain call, so the argument would be fully built and then
    // dropped by an overload that can do nothing with it -- and valid()/
    // wellFormed(), which is what these arguments are, are reached from
    // nowhere else in symfpu. Every node of that is dead, in every build
    // configuration, and it is a large fraction of what lowering constructs.
    props_constructed = 0;
    PRECONDITION(countedProp());
    POSTCONDITION(countedProp());
    INVARIANT(countedProp());
    check("prop properties construct nothing", props_constructed, 0);

    // A bool-valued property is a real check on a width or a flag symfpu has
    // already settled, so it must still be evaluated -- and asserted, in a
    // build with assertions on. Suppressing these too would be a regression,
    // which is why this is a type question and not a blanket suppression.
    bools_evaluated = 0;
    PRECONDITION(countedBool());
    POSTCONDITION(countedBool());
    INVARIANT(countedBool());
    check("bool properties are still evaluated", bools_evaluated, 3);
  }

  printf("\n%d checks, %d failures\n", checks, failures);
  return failures != 0;
}
