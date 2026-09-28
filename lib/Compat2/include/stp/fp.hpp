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

// Header-only C++ convenience wrappers over STP's C floating-point API.
//
// The C API (c_interface.h) is already callable from C++; this adds RAII and
// operator overloading so floating-point problems read idiomatically:
//
//     stp::fp::Solver s;
//     stp::fp::Float x = s.fp("x", 11, 53);      // an IEEE double variable
//     s.add(x > 0.0);
//     s.add((x * x).eq(4.0));
//     if (s.check())
//         double v = s.model(x);                 // 2.0
//
// Anything not wrapped here is one .raw() away from the C API (Float::raw()
// gives the Expr, Solver::raw() the VC), and the two interoperate freely.
//
// Error behaviour: conditions these wrappers detect themselves -- mixed
// formats, widths they cannot decode, a solver error -- throw
// std::invalid_argument/std::runtime_error. Misuse that reaches the C layer
// (an invalid rounding mode, a non-float operand) aborts the process via
// STP's FatalError, as the C API documents; it does not unwind.
//
// Lifetime: Float and Bool are lightweight handles into their Solver's
// checker. They are freely copyable, but must not outlive the Solver.

#ifndef STP_FP_HPP
#define STP_FP_HPP

#include "stp/c_interface.h"

#include <cmath>
#include <cstdint>
#include <cstring>
#include <limits>
#include <stdexcept>
#include <string>

namespace stp
{
namespace fp
{

// A Boolean expression: the result of a floating-point comparison or
// classification, and what Solver::add asserts.
class Bool
{
public:
  Bool(VC vc, Expr e) : vc_(vc), e_(e) {}
  Expr raw() const { return e_; }

  Bool operator!() const { return Bool(vc_, vc_notExpr(vc_, e_)); }
  Bool operator&&(const Bool& o) const { return Bool(vc_, vc_andExpr(vc_, e_, o.e_)); }
  Bool operator||(const Bool& o) const { return Bool(vc_, vc_orExpr(vc_, e_, o.e_)); }

private:
  VC vc_;
  Expr e_;
};

// A floating-point expression of format (exp_width, sig_width). The arithmetic
// operators round under the rounding mode captured when it was made (the
// solver's, default RNE). A double operand is coerced to a constant of this
// expression's format.
//
// The wrapper works with the five concrete modes only, which is what
// programs need. For a *symbolic* rounding mode, drop to the C API:
// vc_fpRoundingModeVar makes a properly constrained RoundingMode variable,
// and vc_fpAddExpr and friends accept it alongside raw() operands.
class Float
{
public:
  Float(VC vc, Expr e, int eb, int sb, VCRoundingMode rm)
      : vc_(vc), e_(e), eb_(eb), sb_(sb), rm_(rm)
  {
  }

  Expr raw() const { return e_; }
  int exp_width() const { return eb_; }
  int sig_width() const { return sb_; }

  // Reinterpret as packed IEEE bits: an (eb + sb)-bit bitvector Expr. Use the
  // C API (vc_bvExtract) to pull out fields -- the exponent is bits
  // [sb-1 .. sb+eb-2], the significand bits [0 .. sb-2].
  Expr to_ieee_bits() const { return vc_fpToIEEEBV(vc_, e_); }

  // Round to a `width`-bit unsigned / signed integer (a bitvector Expr) under
  // this expression's rounding mode.
  Expr to_ubv(int width) const { return vc_fpToUBVExpr(vc_, width, rm(), e_); }
  Expr to_sbv(int width) const { return vc_fpToSBVExpr(vc_, width, rm(), e_); }

  // A constant of this expression's format from a Python-style double.
  Float constant(double d) const
  {
    return Float(vc_,
                 vc_fpConstFromDouble(vc_, vc_fpType(vc_, eb_, sb_), rm(), d),
                 eb_, sb_, rm_);
  }

  // Arithmetic (rounding-mode aware). Mixed formats throw: convert first.
  Float operator+(const Float& o) const { same(o); return wrap(vc_fpAddExpr(vc_, rm(), e_, o.e_)); }
  Float operator-(const Float& o) const { same(o); return wrap(vc_fpSubExpr(vc_, rm(), e_, o.e_)); }
  Float operator*(const Float& o) const { same(o); return wrap(vc_fpMulExpr(vc_, rm(), e_, o.e_)); }
  Float operator/(const Float& o) const { same(o); return wrap(vc_fpDivExpr(vc_, rm(), e_, o.e_)); }
  Float operator+(double d) const { return *this + constant(d); }
  Float operator-(double d) const { return *this - constant(d); }
  Float operator*(double d) const { return *this * constant(d); }
  Float operator/(double d) const { return *this / constant(d); }

  Float operator-() const { return wrap(vc_fpNegExpr(vc_, e_)); }
  Float abs() const { return wrap(vc_fpAbsExpr(vc_, e_)); }
  Float sqrt() const { return wrap(vc_fpSqrtExpr(vc_, rm(), e_)); }
  Float round_to_integral() const { return wrap(vc_fpRoundToIntegralExpr(vc_, rm(), e_)); }
  Float rem(const Float& o) const { same(o); return wrap(vc_fpRemExpr(vc_, e_, o.e_)); }
  Float min(const Float& o) const { same(o); return wrap(vc_fpMinExpr(vc_, e_, o.e_)); }
  Float max(const Float& o) const { same(o); return wrap(vc_fpMaxExpr(vc_, e_, o.e_)); }
  Float fma(const Float& b, const Float& c) const
  {
    same(b);
    same(c);
    return wrap(vc_fpFMAExpr(vc_, rm(), e_, b.e_, c.e_));
  }

  // Comparisons -> Bool. IEEE ordered comparisons (any NaN operand is false);
  // == is fp.eq (so +0 == -0), != its negation.
  Bool operator<(const Float& o) const { same(o); return Bool(vc_, vc_fpLtExpr(vc_, e_, o.e_)); }
  Bool operator<=(const Float& o) const { same(o); return Bool(vc_, vc_fpLeqExpr(vc_, e_, o.e_)); }
  Bool operator>(const Float& o) const { same(o); return Bool(vc_, vc_fpGtExpr(vc_, e_, o.e_)); }
  Bool operator>=(const Float& o) const { same(o); return Bool(vc_, vc_fpGeqExpr(vc_, e_, o.e_)); }
  Bool eq(const Float& o) const { same(o); return Bool(vc_, vc_fpEqExpr(vc_, e_, o.e_)); }
  Bool ne(const Float& o) const { same(o); return Bool(vc_, vc_notExpr(vc_, vc_fpEqExpr(vc_, e_, o.e_))); }
  Bool operator==(const Float& o) const { return eq(o); }
  Bool operator!=(const Float& o) const { return ne(o); }
  Bool operator<(double d) const { return *this < constant(d); }
  Bool operator<=(double d) const { return *this <= constant(d); }
  Bool operator>(double d) const { return *this > constant(d); }
  Bool operator>=(double d) const { return *this >= constant(d); }
  Bool eq(double d) const { return eq(constant(d)); }
  Bool ne(double d) const { return ne(constant(d)); }
  Bool operator==(double d) const { return eq(d); }
  Bool operator!=(double d) const { return ne(d); }

  // Classifications -> Bool.
  Bool is_nan() const { return Bool(vc_, vc_fpIsNaNExpr(vc_, e_)); }
  Bool is_infinite() const { return Bool(vc_, vc_fpIsInfiniteExpr(vc_, e_)); }
  Bool is_zero() const { return Bool(vc_, vc_fpIsZeroExpr(vc_, e_)); }
  Bool is_normal() const { return Bool(vc_, vc_fpIsNormalExpr(vc_, e_)); }
  Bool is_subnormal() const { return Bool(vc_, vc_fpIsSubnormalExpr(vc_, e_)); }
  Bool is_negative() const { return Bool(vc_, vc_fpIsNegativeExpr(vc_, e_)); }
  Bool is_positive() const { return Bool(vc_, vc_fpIsPositiveExpr(vc_, e_)); }

private:
  Float wrap(Expr e) const { return Float(vc_, e, eb_, sb_, rm_); }
  Expr rm() const { return vc_fpRoundingMode(vc_, rm_); }
  void same(const Float& o) const
  {
    if (eb_ != o.eb_ || sb_ != o.sb_)
      throw std::invalid_argument(
          "stp::fp: mixed floating-point formats; convert one operand first");
  }

  VC vc_;
  Expr e_;
  int eb_, sb_;
  VCRoundingMode rm_;
};

// Free-function spellings, found by argument-dependent lookup: abs(x), sqrt(x).
inline Float abs(const Float& f) { return f.abs(); }
inline Float sqrt(const Float& f) { return f.sqrt(); }

// Mixed arithmetic and comparison with the double on the left, so 2.0 + x
// works like x + 2.0.
inline Float operator+(double d, const Float& f) { return f.constant(d) + f; }
inline Float operator-(double d, const Float& f) { return f.constant(d) - f; }
inline Float operator*(double d, const Float& f) { return f.constant(d) * f; }
inline Float operator/(double d, const Float& f) { return f.constant(d) / f; }
inline Bool operator<(double d, const Float& f) { return f > d; }
inline Bool operator<=(double d, const Float& f) { return f >= d; }
inline Bool operator>(double d, const Float& f) { return f < d; }
inline Bool operator>=(double d, const Float& f) { return f <= d; }
inline Bool operator==(double d, const Float& f) { return f == d; }
inline Bool operator!=(double d, const Float& f) { return f != d; }

// A validity checker that owns its VC (RAII). Non-copyable.
class Solver
{
public:
  Solver() : vc_(vc_createValidityChecker()), owned_(true), rm_(VC_RM_RNE) {}
  // Wrap an existing VC without taking ownership (it is not destroyed).
  explicit Solver(VC vc) : vc_(vc), owned_(false), rm_(VC_RM_RNE) {}
  ~Solver()
  {
    if (owned_)
      vc_Destroy(vc_);
  }
  Solver(const Solver&) = delete;
  Solver& operator=(const Solver&) = delete;
  Solver(Solver&& o) noexcept : vc_(o.vc_), owned_(o.owned_), rm_(o.rm_)
  {
    o.owned_ = false;
  }
  Solver& operator=(Solver&& o) noexcept
  {
    if (this != &o)
    {
      if (owned_)
        vc_Destroy(vc_);
      vc_ = o.vc_;
      owned_ = o.owned_;
      rm_ = o.rm_;
      o.owned_ = false;
    }
    return *this;
  }

  VC raw() const { return vc_; }
  void set_rounding_mode(VCRoundingMode rm) { rm_ = rm; }
  VCRoundingMode rounding_mode() const { return rm_; }

  // Variables and constants.
  Float fp(const std::string& name, int eb, int sb)
  {
    return Float(vc_, vc_varExpr(vc_, name.c_str(), vc_fpType(vc_, eb, sb)), eb,
                 sb, rm_);
  }
  Float fpval(int eb, int sb, double value)
  {
    return Float(vc_,
                 vc_fpConstFromDouble(vc_, vc_fpType(vc_, eb, sb),
                                      vc_fpRoundingMode(vc_, rm_), value),
                 eb, sb, rm_);
  }
  Float fp_from_bits(int eb, int sb, uint64_t bits)
  {
    return Float(vc_,
                 vc_fpConstFromBits(vc_, eb, sb,
                                    vc_bvConstExprFromLL(vc_, eb + sb, bits)),
                 eb, sb, rm_);
  }
  Float fp_nan(int eb, int sb)
  {
    return Float(vc_, vc_fpNaN(vc_, vc_fpType(vc_, eb, sb)), eb, sb, rm_);
  }
  Float fp_inf(int eb, int sb, bool negative = false)
  {
    Type t = vc_fpType(vc_, eb, sb);
    return Float(vc_, negative ? vc_fpMinusInfinity(vc_, t)
                               : vc_fpPlusInfinity(vc_, t),
                 eb, sb, rm_);
  }
  Float fp_zero(int eb, int sb, bool negative = false)
  {
    Type t = vc_fpType(vc_, eb, sb);
    return Float(vc_,
                 negative ? vc_fpMinusZero(vc_, t) : vc_fpPlusZero(vc_, t), eb,
                 sb, rm_);
  }

  // Solving. check() is true iff the assertions are satisfiable; a solver
  // unknown result or error throws rather than masquerading as unsatisfiable.
  void add(const Bool& b) { vc_assertFormula(vc_, b.raw()); }
  bool check()
  {
    const int r = vc_query(vc_, vc_falseExpr(vc_));
    if (r == 0)
      return true;
    if (r == 1)
      return false;
    throw std::runtime_error(
        "stp::fp::Solver::check: solver error or unknown result (vc_query "
        "returned " +
        std::to_string(r) + ")");
  }

  // Model values. model() returns a native double for the half, single and
  // double formats (all exactly representable as a double); model_bits()
  // returns the packed IEEE bits for formats up to 64 bits wide -- the C API
  // reads the value through a 64-bit integer, and a wider format would
  // silently saturate, so it is rejected instead.
  uint64_t model_bits(const Float& f)
  {
    if (f.exp_width() + f.sig_width() > 64)
      throw std::runtime_error(
          "stp::fp::Solver::model_bits: format wider than 64 bits; read the "
          "bits through to_ieee_bits() and vc_bvExtract");
    return getBVUnsignedLongLong(vc_getCounterExample(vc_, f.raw()));
  }
  double model(const Float& f)
  {
    const uint64_t bits = model_bits(f);
    if (f.exp_width() == 11 && f.sig_width() == 53)
    {
      double d;
      std::memcpy(&d, &bits, sizeof(d));
      return d;
    }
    if (f.exp_width() == 8 && f.sig_width() == 24)
    {
      const uint32_t b = static_cast<uint32_t>(bits);
      float x;
      std::memcpy(&x, &b, sizeof(x));
      return x;
    }
    if (f.exp_width() == 5 && f.sig_width() == 11)
    {
      // Unpack binary16 by hand (C++ has no portable native type for it).
      const uint32_t b = static_cast<uint32_t>(bits);
      const bool sign = (b >> 15) & 1;
      const int e = (b >> 10) & 0x1F;
      const int m = b & 0x3FF;
      double v;
      if (e == 0x1F)
        v = m ? std::numeric_limits<double>::quiet_NaN()
              : std::numeric_limits<double>::infinity();
      else if (e == 0)
        v = std::ldexp(static_cast<double>(m), -24); // subnormal
      else
        v = std::ldexp(static_cast<double>(m + 1024), e - 25);
      return sign ? -v : v;
    }
    throw std::runtime_error(
        "stp::fp::Solver::model: only the half, single and double formats "
        "decode to a double; use model_bits() for other formats");
  }

private:
  VC vc_;
  bool owned_;
  VCRoundingMode rm_;
};

} // namespace fp
} // namespace stp

#endif // STP_FP_HPP
