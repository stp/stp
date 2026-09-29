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

// c_interface2_terms.cpp -- libstp2's constructors: the types, the symbols,
// and the Boolean, bit-vector, array, floating-point and Real terms of
// stp/c_interface.h, each over the named 3.x constructor of stp/stp.h.
//
// Every sort check a 2.x constructor made in ordinary (release) code is made
// here too, with the same message, because clients and tests key on them; a
// refusal the 3.x constructor itself makes (a width mismatch, an
// unsupported combination) takes the same fatal path with the 3.x text.

#include "Compat2.h"

#include <cinttypes>
#include <cstdio>
#include <cstring>
#include <string>
#include <vector>

using namespace compat2;

namespace
{

// ------------------------------------------------------------ the operand checks

std::string message(const char* who, const char* what)
{
  return std::string("CInterface: ") + who + what;
}

bool check_bool(const char* who, stp_term t)
{
  if (is_bool(stp_term_sort(t)))
    return true;
  fatal(message(who, " requires Boolean operands: "));
  return false;
}

bool check_bv(const char* who, stp_term t)
{
  const stp_sort s = stp_term_sort(t);
  if (is_bv(s))
    return true;
  std::string what = " requires bitvector operands";
  if (is_fp(s))
    what += "; use vc_fpToIEEEBV to expose a float's packed bits";
  what += ": ";
  fatal(message(who, what.c_str()));
  return false;
}

bool check_same(const char* who, stp_term a, stp_term b)
{
  if (stp_term_sort(a) == stp_term_sort(b))
    return true;
  fatal(message(who, " requires operands of the same sort: "));
  return false;
}

// 2.x refused an operand from another checker before any sort check, with
// this wording (its acceptance tests pin it). A null handle is term_of's
// report, not this one's.
bool check_owned(VCImpl* vc, const char* who, Expr e)
{
  Handle* h = handle(e);
  if (h == nullptr || h->vc == vc)
    return true;
  fatal(std::string("CInterface: ") + who + " received an Expr owned by a different validity checker");
  return false;
}

bool check_rm(const char* who, stp_term rm)
{
  if (is_rm(stp_term_sort(rm)))
    return true;
  fatal(message(who, ": expected a rounding mode: "));
  return false;
}

bool check_fp(stp_term t)
{
  if (is_fp(stp_term_sort(t)))
    return true;
  fatal("CInterface: floating-point operation applied to a non-float operand: ");
  return false;
}

// The redundant bit-width argument of the 2.x arithmetic constructors.
bool check_width(const char* who, int n_bits, stp_term t)
{
  const std::uint32_t w = bv_width(stp_term_sort(t));
  if (n_bits >= 0 && static_cast<std::uint32_t>(n_bits) == w)
    return true;
  fatal(message(who, (": the bit-width argument (" + std::to_string(n_bits) +
                      ") differs from the operands' width (" + std::to_string(w) + ")")
                         .c_str()));
  return false;
}

// A term a 3.x constructor just built (+1), or NULL with the 3.x refusal
// reported on the fatal path.
Expr built(VCImpl* vc, stp_term t, const char* who, bool checker_owned = false)
{
  if (t == nullptr)
  {
    fatal(message(who, (": " + take_error(vc)).c_str()));
    return nullptr;
  }
  return wrap(vc, t, checker_owned);
}

// Both operands of a binary bit-vector term / predicate.
bool bv_pair(const char* who, Expr l, Expr r, stp_term& a, stp_term& b)
{
  a = term_of(l, who);
  b = term_of(r, who);
  return a != nullptr && b != nullptr && check_bv(who, a) && check_bv(who, b);
}

bool bool_pair(const char* who, Expr l, Expr r, stp_term& a, stp_term& b)
{
  a = term_of(l, who);
  b = term_of(r, who);
  return a != nullptr && b != nullptr && check_bool(who, a) && check_bool(who, b);
}

// The declaration behind vc_varExpr and its relatives.
Expr declare(VCImpl* vc, const char* who, const char* name, stp_sort sort)
{
  if (name == nullptr)
  {
    fatal(message(who, ": null name"));
    return nullptr;
  }
  for (const auto& uf : vc->ufs)
    if (uf.second.name == name)
    {
      report(std::string("name '") + name + "' already denotes an uninterpreted function");
      return nullptr;
    }
  stp_term t = stp_declare(vc->tm, name, sort);
  if (t == nullptr)
  {
    stp_error_code code;
    const std::string err = take_error(vc, &code);
    if (code == STP_ERR_SORT_MISMATCH)
      fatal("CInterface: a symbol cannot be redeclared with a different source sort");
    else
      fatal(message(who, (": " + err).c_str()));
    return nullptr;
  }
  return wrap(vc, t, false);
}

// The (eb, sb) of a floating-point Type handle.
bool fp_type_widths(Type type, std::uint32_t& eb, std::uint32_t& sb)
{
  stp_sort s = type_of(type, "vc_fp");
  if (s == nullptr)
    return false;
  if (!is_fp(s))
  {
    fatal("CInterface: expected a floating-point type (from vc_fpType): ");
    return false;
  }
  return fp_format(s, eb, sb);
}

bool check_fp_widths(int eb, int sb)
{
  if (eb >= 2 && sb >= 2)
    return true;
  fatal("CInterface: a floating-point format needs at least 2 exponent and 2 significand bits");
  return false;
}

} // namespace

// ============================================================ types

Type vc_boolType(VC vcp)
{
  VCImpl* vc = vcimpl(vcp, "vc_boolType");
  return vc != nullptr ? wrap_type(vc, stp_mk_bool_sort(vc->tm)) : nullptr;
}

Type vc_bvType(VC vcp, int no_bits)
{
  VCImpl* vc = vcimpl(vcp, "vc_bvType");
  if (vc == nullptr)
    return nullptr;
  if (no_bits <= 0)
  {
    fatal("CInterface: number of bits in a bvtype must be a positive integer:");
    return nullptr;
  }
  stp_sort s = stp_mk_bv_sort(vc->tm, static_cast<std::uint32_t>(no_bits));
  if (s == nullptr)
  {
    fatal("CInterface: vc_bvType: " + take_error(vc));
    return nullptr;
  }
  return wrap_type(vc, s);
}

Type vc_bv32Type(VC vc)
{
  return vc_bvType(vc, 32);
}

Type vc_arrayType(VC vcp, Type typeIndex, Type typeData)
{
  VCImpl* vc = vcimpl(vcp, "vc_arrayType");
  if (vc == nullptr)
    return nullptr;
  stp_sort ti = type_of(typeIndex, "vc_arrayType");
  stp_sort td = type_of(typeData, "vc_arrayType");
  if (ti == nullptr || td == nullptr)
    return nullptr;
  const auto scalar = [](stp_sort s) { return is_bv(s) || is_fp(s) || is_rm(s); };
  if (!scalar(ti))
  {
    fatal("CInterface: vc_arrayType: the index type must be a bitvector, floating-point or "
          "RoundingMode type: ");
    return nullptr;
  }
  if (!scalar(td))
  {
    fatal("CInterface: vc_arrayType: the element type must be a bitvector, floating-point or "
          "RoundingMode type: ");
    return nullptr;
  }
  stp_sort s = stp_mk_array_sort(vc->tm, ti, td);
  if (s == nullptr)
  {
    fatal("CInterface: vc_arrayType: " + take_error(vc));
    return nullptr;
  }
  return wrap_type(vc, s);
}

Type vc_fpType(VC vcp, int exp_bits, int sig_bits)
{
  VCImpl* vc = vcimpl(vcp, "vc_fpType");
  if (vc == nullptr || !check_fp_widths(exp_bits, sig_bits))
    return nullptr;
  stp_sort s = stp_mk_fp_sort(vc->tm, static_cast<std::uint32_t>(exp_bits), static_cast<std::uint32_t>(sig_bits));
  if (s == nullptr)
  {
    fatal("CInterface: vc_fpType: " + take_error(vc));
    return nullptr;
  }
  return wrap_type(vc, s);
}

Type vc_fpRoundingModeType(VC vcp)
{
  VCImpl* vc = vcimpl(vcp, "vc_fpRoundingModeType");
  return vc != nullptr ? wrap_type(vc, stp_mk_rm_sort(vc->tm)) : nullptr;
}

Type vc_realType(VC vcp)
{
  VCImpl* vc = vcimpl(vcp, "vc_realType");
  return vc != nullptr ? wrap_type(vc, stp_mk_real_sort(vc->tm)) : nullptr;
}

// ============================================================ symbols

Expr vc_varExpr(VC vcp, const char* name, Type type)
{
  VCImpl* vc = vcimpl(vcp, "vc_varExpr");
  if (vc == nullptr)
    return nullptr;
  stp_sort s = type_of(type, "vc_varExpr");
  if (s == nullptr)
    return nullptr;
  switch (sort_kind(s))
  {
    case STP_SORT_BOOL:
    case STP_SORT_BV:
    case STP_SORT_FP:
    case STP_SORT_RM:
    case STP_SORT_ARRAY:
    case STP_SORT_REAL:
      break;
    default:
      fatal("CInterface: vc_varExpr: unsupported source sort: ");
      return nullptr;
  }
  // A RoundingMode symbol ranges over the five modes by construction in 3.x;
  // the pin 2.x asserted on declaration is intrinsic to the sort.
  return declare(vc, "vc_varExpr", name, s);
}

Expr vc_varExpr1(VC vcp, const char* name, int indexwidth, int valuewidth)
{
  VCImpl* vc = vcimpl(vcp, "vc_varExpr1");
  if (vc == nullptr)
    return nullptr;
  if (indexwidth > 0 && valuewidth <= 0)
  {
    fatal("CInterface: vc_varExpr1: number of bits in an array's elements must be a positive integer");
    return nullptr;
  }
  stp_sort s;
  if (indexwidth > 0)
    s = stp_mk_array_sort(vc->tm, stp_mk_bv_sort(vc->tm, static_cast<std::uint32_t>(indexwidth)),
                          stp_mk_bv_sort(vc->tm, static_cast<std::uint32_t>(valuewidth)));
  else if (valuewidth > 0)
    s = stp_mk_bv_sort(vc->tm, static_cast<std::uint32_t>(valuewidth));
  else
    s = stp_mk_bool_sort(vc->tm);
  if (s == nullptr)
  {
    fatal("CInterface: vc_varExpr1: " + take_error(vc));
    return nullptr;
  }
  return declare(vc, "vc_varExpr1", name, s);
}

Expr vc_fpRoundingModeVar(VC vcp, const char* name)
{
  VCImpl* vc = vcimpl(vcp, "vc_fpRoundingModeVar");
  return vc != nullptr ? declare(vc, "vc_fpRoundingModeVar", name, stp_mk_rm_sort(vc->tm)) : nullptr;
}

Expr vc_bvCreateMemoryArray(VC vcp, const char* arrayName)
{
  VCImpl* vc = vcimpl(vcp, "vc_bvCreateMemoryArray");
  if (vc == nullptr)
    return nullptr;
  stp_sort s = stp_mk_array_sort(vc->tm, stp_mk_bv_sort(vc->tm, 32), stp_mk_bv_sort(vc->tm, 8));
  return declare(vc, "vc_bvCreateMemoryArray", arrayName, s);
}

Expr vc_paramBoolExpr(VC vcp, Expr boolvar, Expr parameter)
{
  VCImpl* vc = vcimpl(vcp, "vc_paramBoolExpr");
  stp_term c = term_of(boolvar, "vc_paramBoolExpr");
  stp_term t = term_of(parameter, "vc_paramBoolExpr");
  if (vc == nullptr || c == nullptr || t == nullptr)
    return nullptr;
  if (!check_bool("vc_paramBoolExpr", c) || !check_bv("vc_paramBoolExpr", t))
    return nullptr;
  if (!stp_term_is_value(t))
  {
    fatal("vc_paramBoolExpr: the parameter must be a constant bit-vector");
    return nullptr;
  }
  // A Boolean variable named after the application as 2.x printed it, each
  // operand in the presentation language: "p (0b1 )" and "p (0x1 )", a
  // one-bit parameter's and a four-bit one's, are two variables.
  char* var_text = stp_term_to_string(c, STP_FORMAT_CVC, false);
  char* param_text = var_text != nullptr ? stp_term_to_string(t, STP_FORMAT_CVC, false) : nullptr;
  if (param_text == nullptr)
  {
    stp_free(var_text);
    fatal(message("vc_paramBoolExpr", (": " + take_error(vc)).c_str()));
    return nullptr;
  }
  const std::string name = std::string(var_text) + "(" + param_text + ")";
  stp_free(var_text);
  stp_free(param_text);
  return declare(vc, "vc_paramBoolExpr", name.c_str(), stp_mk_bool_sort(vc->tm));
}

// ============================================================ Boolean terms

Expr vc_trueExpr(VC vcp)
{
  VCImpl* vc = vcimpl(vcp, "vc_trueExpr");
  return vc != nullptr ? built(vc, stp_mk_true(vc->tm), "vc_trueExpr") : nullptr;
}

Expr vc_falseExpr(VC vcp)
{
  VCImpl* vc = vcimpl(vcp, "vc_falseExpr");
  return vc != nullptr ? built(vc, stp_mk_false(vc->tm), "vc_falseExpr") : nullptr;
}

Expr vc_notExpr(VC vcp, Expr child)
{
  VCImpl* vc = vcimpl(vcp, "vc_notExpr");
  stp_term a = term_of(child, "vc_notExpr");
  if (vc == nullptr || a == nullptr || !check_bool("vc_notExpr", a))
    return nullptr;
  return built(vc, stp_not(vc->tm, a), "vc_notExpr");
}

namespace
{

Expr connective(VC vcp, const char* who, Expr l, Expr r, stp_term (*make)(stp_tm, stp_term, stp_term))
{
  VCImpl* vc = vcimpl(vcp, who);
  stp_term a, b;
  if (vc == nullptr || !bool_pair("Boolean connective", l, r, a, b))
    return nullptr;
  return built(vc, make(vc->tm, a, b), who);
}

stp_term make_nand(stp_tm tm, stp_term a, stp_term b)
{
  stp_term inner = stp_and2(tm, a, b);
  if (inner == nullptr)
    return nullptr;
  stp_term out = stp_not(tm, inner);
  stp_term_release(inner);
  return out;
}

stp_term make_nor(stp_tm tm, stp_term a, stp_term b)
{
  stp_term inner = stp_or2(tm, a, b);
  if (inner == nullptr)
    return nullptr;
  stp_term out = stp_not(tm, inner);
  stp_term_release(inner);
  return out;
}

} // namespace

Expr vc_andExpr(VC vc, Expr left, Expr right) { return connective(vc, "vc_andExpr", left, right, stp_and2); }
Expr vc_orExpr(VC vc, Expr left, Expr right) { return connective(vc, "vc_orExpr", left, right, stp_or2); }
Expr vc_xorExpr(VC vc, Expr left, Expr right) { return connective(vc, "vc_xorExpr", left, right, stp_xor2); }
Expr vc_nandExpr(VC vc, Expr left, Expr right) { return connective(vc, "vc_nandExpr", left, right, make_nand); }
Expr vc_norExpr(VC vc, Expr left, Expr right) { return connective(vc, "vc_norExpr", left, right, make_nor); }
Expr vc_impliesExpr(VC vc, Expr hyp, Expr conc) { return connective(vc, "vc_impliesExpr", hyp, conc, stp_implies); }
Expr vc_iffExpr(VC vc, Expr left, Expr right) { return connective(vc, "vc_iffExpr", left, right, stp_eq); }

namespace
{

Expr nary(VC vcp, const char* who, Expr* children, int n, stp_term (*make)(stp_tm, size_t, const stp_term*))
{
  VCImpl* vc = vcimpl(vcp, who);
  if (vc == nullptr)
    return nullptr;
  if (n <= 0 || children == nullptr)
  {
    fatal(message(who, ": at least one child is needed"));
    return nullptr;
  }
  std::vector<stp_term> terms;
  terms.reserve(static_cast<std::size_t>(n));
  for (int i = 0; i < n; ++i)
  {
    stp_term t = term_of(children[i], who);
    if (t == nullptr || !check_bool(who, t))
      return nullptr;
    terms.push_back(t);
  }
  if (terms.size() == 1)
    return wrap(vc, stp_term_copy(terms[0]), false);
  return built(vc, make(vc->tm, terms.size(), terms.data()), who);
}

} // namespace

Expr vc_andExprN(VC vc, Expr* children, int numOfChildNodes)
{
  return nary(vc, "vc_andExprN", children, numOfChildNodes, stp_and);
}

Expr vc_orExprN(VC vc, Expr* children, int numOfChildNodes)
{
  return nary(vc, "vc_orExprN", children, numOfChildNodes, stp_or);
}

Expr vc_iteExpr(VC vcp, Expr conditional, Expr thenExpr, Expr elseExpr)
{
  VCImpl* vc = vcimpl(vcp, "vc_iteExpr");
  stp_term c = term_of(conditional, "vc_iteExpr");
  stp_term t = term_of(thenExpr, "vc_iteExpr");
  stp_term e = term_of(elseExpr, "vc_iteExpr");
  if (vc == nullptr || c == nullptr || t == nullptr || e == nullptr)
    return nullptr;
  if (!check_owned(vc, "vc_iteExpr", conditional) || !check_owned(vc, "vc_iteExpr", thenExpr) ||
      !check_owned(vc, "vc_iteExpr", elseExpr))
    return nullptr;
  if (!is_bool(stp_term_sort(c)))
  {
    fatal("CInterface: vc_iteExpr requires a Boolean condition: ");
    return nullptr;
  }
  const stp_sort ts = stp_term_sort(t), es = stp_term_sort(e);
  if (ts != es)
  {
    std::uint32_t eb1 = 0, sb1 = 0, eb2 = 0, sb2 = 0;
    if (is_fp(ts) && is_fp(es) && fp_format(ts, eb1, sb1) && fp_format(es, eb2, sb2))
    {
      fatal("CInterface: vc_iteExpr: the then and else branches differ in floating-point format: ");
      return nullptr;
    }
    // 2.x's Real path refused the branch that is not Real with this wording.
    if (is_real(ts) || is_real(es))
    {
      fatal("CInterface: vc_iteExpr requires Real operands: ");
      return nullptr;
    }
    fatal("CInterface: vc_iteExpr requires operands of the same sort: ");
    return nullptr;
  }
  return built(vc, stp_ite(vc->tm, c, t, e), "vc_iteExpr");
}

Expr vc_boolToBVExpr(VC vcp, Expr form)
{
  VCImpl* vc = vcimpl(vcp, "vc_boolToBVExpr");
  stp_term c = term_of(form, "vc_boolToBVExpr");
  if (vc == nullptr || c == nullptr || !check_bool("vc_boolToBVExpr", c))
    return nullptr;
  return built(vc, stp_bool_to_bv1(vc->tm, c), "vc_boolToBVExpr");
}

Expr vc_eqExpr(VC vcp, Expr child0, Expr child1)
{
  VCImpl* vc = vcimpl(vcp, "vc_eqExpr");
  stp_term a = term_of(child0, "vc_eqExpr");
  stp_term b = term_of(child1, "vc_eqExpr");
  if (vc == nullptr || a == nullptr || b == nullptr)
    return nullptr;
  if (!check_owned(vc, "vc_eqExpr", child0) || !check_owned(vc, "vc_eqExpr", child1) ||
      !check_same("vc_eqExpr", a, b))
    return nullptr;
  // 2.x refuses a whole-array equality at construction unless 'x' is on (the
  // node factory's message, which the acceptance tests expect verbatim); 3.x
  // builds it regardless and decides it when array-equality is on.
  if (is_array(stp_term_sort(a)) && !vc->flag_x)
  {
    fatal("STP cannot decide equality between whole array terms without --array-equality (the C API's "
          "vc_setFlag(vc, 'x'), or Solver(array_equality=True) in Python).");
    return nullptr;
  }
  // Bool: iff; floats: SMT-LIB '='; arrays: extensional equality -- all one
  // constructor in 3.x.
  return built(vc, stp_eq(vc->tm, a, b), "vc_eqExpr");
}

// ============================================================ arrays

namespace
{

bool check_array_index(const char* who, stp_term arr, stp_term index)
{
  const stp_sort as = stp_term_sort(arr);
  if (!is_array(as))
  {
    fatal("CInterface: select/store expects an array: ");
    return false;
  }
  const stp_sort expected = stp_sort_array_index(as);
  if (stp_term_sort(index) == expected)
    return true;
  if (is_fp(expected))
    fatal(message(who, ": the array is indexed by a floating-point sort, but the index is not a float "
                       "of that format: "));
  else if (is_rm(expected))
    fatal(message(who, ": the array is indexed by RoundingMode, but the index is not a rounding mode: "));
  else
    fatal(message(who, ": index sort differs from the array's bitvector index sort: "));
  return false;
}

bool check_array_value(stp_term arr, stp_term value)
{
  const stp_sort as = stp_term_sort(arr);
  if (!is_array(as))
  {
    fatal("CInterface: vc_writeExpr expects an array: ");
    return false;
  }
  const stp_sort expected = stp_sort_array_element(as);
  if (stp_term_sort(value) == expected)
    return true;
  if (is_fp(expected))
    fatal("CInterface: vc_writeExpr: the array's elements are floats, but the stored value is not a "
          "float of that format: ");
  else if (is_rm(expected))
    fatal("CInterface: vc_writeExpr: the array's elements are rounding modes, but the stored value is "
          "not one: ");
  else
    fatal("CInterface: vc_writeExpr: stored value sort differs from the array's bitvector element sort: ");
  return false;
}

} // namespace

Expr vc_readExpr(VC vcp, Expr array, Expr index)
{
  VCImpl* vc = vcimpl(vcp, "vc_readExpr");
  stp_term a = term_of(array, "vc_readExpr");
  stp_term i = term_of(index, "vc_readExpr");
  if (vc == nullptr || a == nullptr || i == nullptr || !check_array_index("vc_readExpr", a, i))
    return nullptr;
  return built(vc, stp_select(vc->tm, a, i), "vc_readExpr");
}

Expr vc_writeExpr(VC vcp, Expr array, Expr index, Expr newValue)
{
  VCImpl* vc = vcimpl(vcp, "vc_writeExpr");
  stp_term a = term_of(array, "vc_writeExpr");
  stp_term i = term_of(index, "vc_writeExpr");
  stp_term v = term_of(newValue, "vc_writeExpr");
  if (vc == nullptr || a == nullptr || i == nullptr || v == nullptr)
    return nullptr;
  if (!check_array_index("vc_writeExpr", a, i) || !check_array_value(a, v))
    return nullptr;
  return built(vc, stp_store(vc->tm, a, i, v), "vc_writeExpr");
}

Expr vc_bvReadMemoryArray(VC vcp, Expr array, Expr byteIndex, int numOfBytes)
{
  VCImpl* vc = vcimpl(vcp, "vc_bvReadMemoryArray");
  if (vc == nullptr)
    return nullptr;
  if (numOfBytes <= 0)
  {
    fatal("numOfBytes must be greater than 0");
    return nullptr;
  }
  Expr a = vc_readExpr(vcp, array, byteIndex);
  for (int count = 1; count < numOfBytes && a != nullptr; ++count)
  {
    Expr offset = vc_bvConstExprFromInt(vcp, 32, static_cast<unsigned>(count));
    Expr at = vc_bvPlusExpr(vcp, 32, byteIndex, offset);
    Expr b = vc_readExpr(vcp, array, at);
    Expr next = vc_bvConcatExpr(vcp, b, a);
    // the intermediate handles are the shim's, not the caller's
    vc_DeleteExpr(at);
    vc_DeleteExpr(b);
    vc_DeleteExpr(a);
    a = next;
  }
  return a;
}

Expr vc_bvWriteToMemoryArray(VC vcp, Expr array, Expr byteIndex, Expr element, int numOfBytes)
{
  VCImpl* vc = vcimpl(vcp, "vc_bvWriteToMemoryArray");
  if (vc == nullptr)
    return nullptr;
  if (numOfBytes <= 0)
  {
    fatal("numOfBytes must be greater than 0");
    return nullptr;
  }
  if (numOfBytes == 1)
    return vc_writeExpr(vcp, array, byteIndex, element);
  Expr c = vc_bvExtract(vcp, element, 7, 0);
  Expr newarray = vc_writeExpr(vcp, array, byteIndex, c);
  vc_DeleteExpr(c);
  for (int count = 1; count < numOfBytes && newarray != nullptr; ++count)
  {
    const int low = 8 * count;
    c = vc_bvExtract(vcp, element, low + 7, low);
    Expr offset = vc_bvConstExprFromInt(vcp, 32, static_cast<unsigned>(count));
    Expr at = vc_bvPlusExpr(vcp, 32, byteIndex, offset);
    Expr next = vc_writeExpr(vcp, newarray, at, c);
    vc_DeleteExpr(c);
    vc_DeleteExpr(at);
    vc_DeleteExpr(newarray);
    newarray = next;
  }
  return newarray;
}

// ============================================================ bit-vector constants

Expr vc_bvConstExprFromDecStr(VC vcp, int width, const char* decimalInput)
{
  VCImpl* vc = vcimpl(vcp, "vc_bvConstExprFromDecStr");
  if (vc == nullptr)
    return nullptr;
  if (decimalInput == nullptr || width <= 0)
  {
    fatal("CInterface: vc_bvConstExprFromDecStr: a positive width and a decimal string are needed");
    return nullptr;
  }
  return built(vc, stp_mk_bv_str(vc->tm, static_cast<std::uint32_t>(width), decimalInput, 10),
               "vc_bvConstExprFromDecStr");
}

Expr vc_bvConstExprFromStr(VC vcp, const char* binaryInput)
{
  VCImpl* vc = vcimpl(vcp, "vc_bvConstExprFromStr");
  if (vc == nullptr)
    return nullptr;
  if (binaryInput == nullptr || *binaryInput == '\0')
  {
    fatal("CInterface: vc_bvConstExprFromStr: a non-empty binary string is needed");
    return nullptr;
  }
  return built(vc, stp_mk_bv_str(vc->tm, static_cast<std::uint32_t>(std::strlen(binaryInput)), binaryInput, 2),
               "vc_bvConstExprFromStr");
}

Expr vc_bvConstExprFromInt(VC vcp, int bitWidth, unsigned int value)
{
  VCImpl* vc = vcimpl(vcp, "vc_bvConstExprFromInt");
  if (vc == nullptr)
    return nullptr;
  if (bitWidth <= 0)
  {
    std::printf("CInterface: vc_bvConstExprFromInt: Bit width must be positive, got %d.\n", bitWidth);
    fatal("FatalError");
    return nullptr;
  }
  const std::uint64_t v = value;
  const std::uint64_t max = bitWidth >= 64 ? UINT64_MAX : ((UINT64_C(1) << bitWidth) - 1);
  if (v > max)
  {
    std::printf("CInterface: vc_bvConstExprFromInt: Cannot construct a constant %" PRIu64
                " in %d bits, the maximum is %" PRIu64 ".\n",
                v, bitWidth, max);
    fatal("FatalError");
    return nullptr;
  }
  return built(vc, stp_mk_bv_uint64(vc->tm, static_cast<std::uint32_t>(bitWidth), v),
               "vc_bvConstExprFromInt", /* checker_owned */ true);
}

Expr vc_bvConstExprFromLL(VC vcp, int bitWidth, uint64_t value)
{
  VCImpl* vc = vcimpl(vcp, "vc_bvConstExprFromLL");
  if (vc == nullptr)
    return nullptr;
  if (bitWidth <= 0)
  {
    fatal("CInterface: vc_bvConstExprFromLL: the bit width must be positive");
    return nullptr;
  }
  // truncates to the width, as 2.x's CreateBVConst did
  return built(vc, stp_mk_bv_wrapped(vc->tm, static_cast<std::uint32_t>(bitWidth), value), "vc_bvConstExprFromLL");
}

Expr vc_bv32ConstExprFromInt(VC vc, unsigned int value)
{
  return vc_bvConstExprFromInt(vc, 32, value);
}

// ============================================================ bit-vector terms

namespace
{

Expr binary_term(VC vcp, const char* who, int n_bits, Expr l, Expr r, stp_term (*make)(stp_tm, stp_term, stp_term))
{
  VCImpl* vc = vcimpl(vcp, who);
  stp_term a, b;
  if (vc == nullptr || !bv_pair("bitvector operation", l, r, a, b))
    return nullptr;
  if (n_bits >= 0 && !check_width(who, n_bits, a))
    return nullptr;
  return built(vc, make(vc->tm, a, b), who);
}

Expr predicate(VC vcp, const char* who, Expr l, Expr r, stp_term (*make)(stp_tm, stp_term, stp_term))
{
  VCImpl* vc = vcimpl(vcp, who);
  stp_term a, b;
  if (vc == nullptr || !bv_pair("bitvector predicate", l, r, a, b))
    return nullptr;
  return built(vc, make(vc->tm, a, b), who);
}

stp_term make_bvnand(stp_tm tm, stp_term a, stp_term b)
{
  stp_term inner = stp_bvand(tm, a, b);
  if (inner == nullptr)
    return nullptr;
  stp_term out = stp_bvnot(tm, inner);
  stp_term_release(inner);
  return out;
}

stp_term make_bvnor(stp_tm tm, stp_term a, stp_term b)
{
  stp_term inner = stp_bvor(tm, a, b);
  if (inner == nullptr)
    return nullptr;
  stp_term out = stp_bvnot(tm, inner);
  stp_term_release(inner);
  return out;
}

stp_term make_bvxnor(stp_tm tm, stp_term a, stp_term b)
{
  stp_term inner = stp_bvxor(tm, a, b);
  if (inner == nullptr)
    return nullptr;
  stp_term out = stp_bvnot(tm, inner);
  stp_term_release(inner);
  return out;
}

} // namespace

Expr vc_bvConcatExpr(VC vc, Expr left, Expr right)
{
  return binary_term(vc, "vc_bvConcatExpr", -1, left, right, stp_concat);
}

Expr vc_bvPlusExpr(VC vc, int bitWidth, Expr left, Expr right)
{
  return binary_term(vc, "vc_bvPlusExpr", bitWidth, left, right, stp_bvadd);
}

Expr vc_bvPlusExprN(VC vcp, int bitWidth, Expr* children, int numOfChildNodes)
{
  VCImpl* vc = vcimpl(vcp, "vc_bvPlusExprN");
  if (vc == nullptr)
    return nullptr;
  if (numOfChildNodes <= 0 || children == nullptr)
  {
    fatal("CInterface: vc_bvPlusExprN: at least one child is needed");
    return nullptr;
  }
  std::vector<stp_term> terms;
  for (int i = 0; i < numOfChildNodes; ++i)
  {
    stp_term t = term_of(children[i], "vc_bvPlusExprN");
    if (t == nullptr || !check_bv("vc_bvPlusExprN", t) || !check_width("vc_bvPlusExprN", bitWidth, t))
      return nullptr;
    terms.push_back(t);
  }
  if (terms.size() == 1)
    return wrap(vc, stp_term_copy(terms[0]), false);
  return built(vc, stp_bvadd_n(vc->tm, terms.size(), terms.data()), "vc_bvPlusExprN");
}

Expr vc_bv32PlusExpr(VC vc, Expr left, Expr right) { return vc_bvPlusExpr(vc, 32, left, right); }
Expr vc_bvMinusExpr(VC vc, int w, Expr l, Expr r) { return binary_term(vc, "vc_bvMinusExpr", w, l, r, stp_bvsub); }
Expr vc_bv32MinusExpr(VC vc, Expr left, Expr right) { return vc_bvMinusExpr(vc, 32, left, right); }
Expr vc_bvMultExpr(VC vc, int w, Expr l, Expr r) { return binary_term(vc, "vc_bvMultExpr", w, l, r, stp_bvmul); }
Expr vc_bv32MultExpr(VC vc, Expr left, Expr right) { return vc_bvMultExpr(vc, 32, left, right); }
Expr vc_bvDivExpr(VC vc, int w, Expr l, Expr r) { return binary_term(vc, "vc_bvDivExpr", w, l, r, stp_bvudiv); }
Expr vc_bvModExpr(VC vc, int w, Expr l, Expr r) { return binary_term(vc, "vc_bvModExpr", w, l, r, stp_bvurem); }
Expr vc_bvRemExpr(VC vc, int w, Expr l, Expr r) { return binary_term(vc, "vc_bvRemExpr", w, l, r, stp_bvurem); }
Expr vc_sbvDivExpr(VC vc, int w, Expr l, Expr r) { return binary_term(vc, "vc_sbvDivExpr", w, l, r, stp_bvsdiv); }
Expr vc_sbvModExpr(VC vc, int w, Expr l, Expr r) { return binary_term(vc, "vc_sbvModExpr", w, l, r, stp_bvsmod); }
Expr vc_sbvRemExpr(VC vc, int w, Expr l, Expr r) { return binary_term(vc, "vc_sbvRemExpr", w, l, r, stp_bvsrem); }

Expr vc_bvLtExpr(VC vc, Expr l, Expr r) { return predicate(vc, "vc_bvLtExpr", l, r, stp_bvult); }
Expr vc_bvLeExpr(VC vc, Expr l, Expr r) { return predicate(vc, "vc_bvLeExpr", l, r, stp_bvule); }
Expr vc_bvGtExpr(VC vc, Expr l, Expr r) { return predicate(vc, "vc_bvGtExpr", l, r, stp_bvugt); }
Expr vc_bvGeExpr(VC vc, Expr l, Expr r) { return predicate(vc, "vc_bvGeExpr", l, r, stp_bvuge); }
Expr vc_sbvLtExpr(VC vc, Expr l, Expr r) { return predicate(vc, "vc_sbvLtExpr", l, r, stp_bvslt); }
Expr vc_sbvLeExpr(VC vc, Expr l, Expr r) { return predicate(vc, "vc_sbvLeExpr", l, r, stp_bvsle); }
Expr vc_sbvGtExpr(VC vc, Expr l, Expr r) { return predicate(vc, "vc_sbvGtExpr", l, r, stp_bvsgt); }
Expr vc_sbvGeExpr(VC vc, Expr l, Expr r) { return predicate(vc, "vc_sbvGeExpr", l, r, stp_bvsge); }

Expr vc_bvUnsignedAddOverflowExpr(VC vc, Expr l, Expr r) { return predicate(vc, "vc_bvUnsignedAddOverflowExpr", l, r, stp_bvuaddo); }
Expr vc_bvSignedAddOverflowExpr(VC vc, Expr l, Expr r) { return predicate(vc, "vc_bvSignedAddOverflowExpr", l, r, stp_bvsaddo); }
Expr vc_bvUnsignedSubOverflowExpr(VC vc, Expr l, Expr r) { return predicate(vc, "vc_bvUnsignedSubOverflowExpr", l, r, stp_bvusubo); }
Expr vc_bvSignedSubOverflowExpr(VC vc, Expr l, Expr r) { return predicate(vc, "vc_bvSignedSubOverflowExpr", l, r, stp_bvssubo); }
Expr vc_bvUnsignedMulOverflowExpr(VC vc, Expr l, Expr r) { return predicate(vc, "vc_bvUnsignedMulOverflowExpr", l, r, stp_bvumulo); }
Expr vc_bvSignedMulOverflowExpr(VC vc, Expr l, Expr r) { return predicate(vc, "vc_bvSignedMulOverflowExpr", l, r, stp_bvsmulo); }

Expr vc_bvUMinusExpr(VC vcp, Expr child)
{
  VCImpl* vc = vcimpl(vcp, "vc_bvUMinusExpr");
  stp_term a = term_of(child, "vc_bvUMinusExpr");
  if (vc == nullptr || a == nullptr || !check_bv("vc_bvUMinusExpr", a))
    return nullptr;
  return built(vc, stp_bvneg(vc->tm, a), "vc_bvUMinusExpr");
}

Expr vc_bvAndExpr(VC vc, Expr l, Expr r) { return binary_term(vc, "vc_bvAndExpr", -1, l, r, stp_bvand); }
Expr vc_bvOrExpr(VC vc, Expr l, Expr r) { return binary_term(vc, "vc_bvOrExpr", -1, l, r, stp_bvor); }
Expr vc_bvXorExpr(VC vc, Expr l, Expr r) { return binary_term(vc, "vc_bvXorExpr", -1, l, r, stp_bvxor); }
Expr vc_bvNandExpr(VC vc, Expr l, Expr r) { return binary_term(vc, "vc_bvNandExpr", -1, l, r, make_bvnand); }
Expr vc_bvNorExpr(VC vc, Expr l, Expr r) { return binary_term(vc, "vc_bvNorExpr", -1, l, r, make_bvnor); }
Expr vc_bvXnorExpr(VC vc, Expr l, Expr r) { return binary_term(vc, "vc_bvXnorExpr", -1, l, r, make_bvxnor); }

Expr vc_bvNotExpr(VC vcp, Expr child)
{
  VCImpl* vc = vcimpl(vcp, "vc_bvNotExpr");
  stp_term a = term_of(child, "vc_bvNotExpr");
  if (vc == nullptr || a == nullptr || !check_bv("vc_bvNotExpr", a))
    return nullptr;
  return built(vc, stp_bvnot(vc->tm, a), "vc_bvNotExpr");
}

Expr vc_bvLeftShiftExprExpr(VC vc, int w, Expr l, Expr r) { return binary_term(vc, "vc_bvLeftShiftExprExpr", w, l, r, stp_bvshl); }
Expr vc_bvRightShiftExprExpr(VC vc, int w, Expr l, Expr r) { return binary_term(vc, "vc_bvRightShiftExprExpr", w, l, r, stp_bvlshr); }
Expr vc_bvSignedRightShiftExprExpr(VC vc, int w, Expr l, Expr r) { return binary_term(vc, "vc_bvSignedRightShiftExprExpr", w, l, r, stp_bvashr); }

// The legacy shifts: a widening left shift (concat with zeroes), a right
// shift by a constant that drops bits, and the 32-bit / variable forms.
Expr vc_bvLeftShiftExpr(VC vcp, int sh_amt, Expr child)
{
  VCImpl* vc = vcimpl(vcp, "vc_bvLeftShiftExpr");
  stp_term a = term_of(child, "vc_bvLeftShiftExpr");
  if (vc == nullptr || a == nullptr || !check_bv("vc_bvLeftShiftExpr", a))
    return nullptr;
  if (sh_amt == 0)
    return wrap(vc, stp_term_copy(a), false);
  if (sh_amt < 0)
  {
    fatal("CInterface: vc_bvLeftShiftExpr: the shift amount must not be negative");
    return nullptr;
  }
  stp_term zeros = stp_mk_bv_zero(vc->tm, static_cast<std::uint32_t>(sh_amt));
  stp_term out = zeros != nullptr ? stp_concat(vc->tm, a, zeros) : nullptr;
  if (zeros != nullptr)
    stp_term_release(zeros);
  return built(vc, out, "vc_bvLeftShiftExpr");
}

Expr vc_bvRightShiftExpr(VC vcp, int sh_amt, Expr child)
{
  VCImpl* vc = vcimpl(vcp, "vc_bvRightShiftExpr");
  stp_term a = term_of(child, "vc_bvRightShiftExpr");
  if (vc == nullptr || a == nullptr || !check_bv("vc_bvRightShiftExpr", a))
    return nullptr;
  const std::uint32_t w = bv_width(stp_term_sort(a));
  if (sh_amt == 0)
    return wrap(vc, stp_term_copy(a), false);
  if (sh_amt > 0 && static_cast<std::uint32_t>(sh_amt) < w)
  {
    stp_term zeros = stp_mk_bv_zero(vc->tm, static_cast<std::uint32_t>(sh_amt));
    stp_term high = stp_extract(vc->tm, w - 1, static_cast<std::uint32_t>(sh_amt), a);
    stp_term out = zeros != nullptr && high != nullptr ? stp_concat(vc->tm, zeros, high) : nullptr;
    if (zeros != nullptr)
      stp_term_release(zeros);
    if (high != nullptr)
      stp_term_release(high);
    return built(vc, out, "vc_bvRightShiftExpr");
  }
  // shifted out entirely (or a negative amount, as 2.x's unsigned compare read it)
  return built(vc, stp_mk_bv_zero(vc->tm, w), "vc_bvRightShiftExpr");
}

Expr vc_bv32LeftShiftExpr(VC vc, int sh_amt, Expr child)
{
  Expr wide = vc_bvLeftShiftExpr(vc, sh_amt, child);
  if (wide == nullptr)
    return nullptr;
  Expr out = vc_bvExtract(vc, wide, 31, 0);
  vc_DeleteExpr(wide);
  return out;
}

Expr vc_bv32RightShiftExpr(VC vc, int sh_amt, Expr child)
{
  Expr shifted = vc_bvRightShiftExpr(vc, sh_amt, child);
  if (shifted == nullptr)
    return nullptr;
  Expr out = vc_bvExtract(vc, shifted, 31, 0);
  vc_DeleteExpr(shifted);
  return out;
}

namespace
{

// The 2.x if-then-else ladders over every shift amount from 32 down to 0.
Expr shift_ladder(VC vcp, Expr sh_amt, Expr child, bool left, bool pow2)
{
  const char* who = left ? "vc_bvVar32LeftShiftExpr" : pow2 ? "vc_bvVar32DivByPowOfTwoExpr" : "vc_bvVar32RightShiftExpr";
  VCImpl* vc = vcimpl(vcp, who);
  stp_term c = term_of(child, who);
  stp_term s = term_of(sh_amt, who);
  if (vc == nullptr || c == nullptr || s == nullptr || !check_bv(who, c) || !check_bv(who, s))
    return nullptr;
  const int child_width = static_cast<int>(bv_width(stp_term_sort(c)));
  const int shift_width = static_cast<int>(bv_width(stp_term_sort(s)));
  Expr elsepart = pow2 ? vc_bvConstExprFromInt(vcp, 32, 0) : vc_bvConstExprFromInt(vcp, child_width, 0);
  for (int count = 31; count >= 0 && elsepart != nullptr; --count)
  {
    Expr ifpart;
    Expr thenpart;
    if (pow2)
    {
      ifpart = vc_eqExpr(vcp, sh_amt, vc_bvConstExprFromInt(vcp, 32, 1u << count));
      thenpart = vc_bvRightShiftExpr(vcp, count, child);
    }
    else
    {
      ifpart = vc_eqExpr(vcp, sh_amt, vc_bvConstExprFromInt(vcp, shift_width, static_cast<unsigned>(count)));
      if (left)
      {
        Expr wide = vc_bvLeftShiftExpr(vcp, count, child);
        thenpart = vc_bvExtract(vcp, wide, child_width - 1, 0);
        vc_DeleteExpr(wide);
      }
      else
        thenpart = vc_bvRightShiftExpr(vcp, count, child);
    }
    Expr ite = vc_iteExpr(vcp, ifpart, thenpart, elsepart);
    vc_DeleteExpr(ifpart);
    vc_DeleteExpr(thenpart);
    vc_DeleteExpr(elsepart);
    elsepart = ite;
  }
  return elsepart;
}

} // namespace

Expr vc_bvVar32LeftShiftExpr(VC vc, Expr sh_amt, Expr child) { return shift_ladder(vc, sh_amt, child, true, false); }
Expr vc_bvVar32RightShiftExpr(VC vc, Expr sh_amt, Expr child) { return shift_ladder(vc, sh_amt, child, false, false); }
Expr vc_bvVar32DivByPowOfTwoExpr(VC vc, Expr child, Expr rhs) { return shift_ladder(vc, rhs, child, false, true); }

Expr vc_bvExtract(VC vcp, Expr child, int high_bit_no, int low_bit_no)
{
  VCImpl* vc = vcimpl(vcp, "vc_bvExtract");
  stp_term a = term_of(child, "vc_bvExtract");
  if (vc == nullptr || a == nullptr || !check_bv("vc_bvExtract", a))
    return nullptr;
  if (low_bit_no < 0 || high_bit_no < low_bit_no)
  {
    fatal("CInterface: vc_bvExtract: the extracted range must satisfy 0 <= low <= high");
    return nullptr;
  }
  return built(vc, stp_extract(vc->tm, static_cast<std::uint32_t>(high_bit_no), static_cast<std::uint32_t>(low_bit_no), a),
               "vc_bvExtract");
}

namespace
{

Expr bool_extract(VC vcp, const char* who, Expr x, int bit_no, bool one)
{
  VCImpl* vc = vcimpl(vcp, who);
  stp_term a = term_of(x, who);
  if (vc == nullptr || a == nullptr || !check_bv(who, a))
    return nullptr;
  if (bit_no < 0)
  {
    fatal(message(who, ": the bit number must not be negative"));
    return nullptr;
  }
  stp_term bit = stp_extract(vc->tm, static_cast<std::uint32_t>(bit_no), static_cast<std::uint32_t>(bit_no), a);
  if (bit == nullptr)
    return built(vc, nullptr, who);
  stp_term value = one ? stp_mk_bv_ones(vc->tm, 1) : stp_mk_bv_zero(vc->tm, 1);
  stp_term out = stp_eq(vc->tm, bit, value);
  stp_term_release(bit);
  stp_term_release(value);
  return built(vc, out, who);
}

Expr extend(VC vcp, const char* who, Expr child, int newWidth, bool sign)
{
  VCImpl* vc = vcimpl(vcp, who);
  stp_term a = term_of(child, who);
  if (vc == nullptr || a == nullptr || !check_bv(who, a))
    return nullptr;
  if (newWidth <= 0)
  {
    fatal(std::string(who) + ": the new width must be positive");
    return nullptr;
  }
  const std::uint32_t have = bv_width(stp_term_sort(a));
  const std::uint32_t want = static_cast<std::uint32_t>(newWidth);
  if (have == want)
    return wrap(vc, stp_term_copy(a), false);
  if (have > want) // 2.x truncated instead of failing
    return built(vc, stp_extract(vc->tm, want - 1, 0, a), who);
  return built(vc, sign ? stp_sign_extend(vc->tm, want - have, a) : stp_zero_extend(vc->tm, want - have, a), who);
}

} // namespace

Expr vc_bvBoolExtract(VC vc, Expr x, int bit_no) { return bool_extract(vc, "vc_bvBoolExtract", x, bit_no, false); }
Expr vc_bvBoolExtract_Zero(VC vc, Expr x, int bit_no) { return bool_extract(vc, "vc_bvBoolExtract_Zero", x, bit_no, false); }
Expr vc_bvBoolExtract_One(VC vc, Expr x, int bit_no) { return bool_extract(vc, "vc_bvBoolExtract_One", x, bit_no, true); }
Expr vc_bvSignExtend(VC vc, Expr child, int newWidth) { return extend(vc, "vc_bvSignExtend", child, newWidth, true); }
Expr vc_bvZeroExtend(VC vc, Expr child, int newWidth) { return extend(vc, "vc_bvZeroExtend", child, newWidth, false); }

// ============================================================ floating point

Expr vc_fpConstFromBits(VC vcp, int exp_bits, int sig_bits, Expr bv)
{
  VCImpl* vc = vcimpl(vcp, "vc_fpConstFromBits");
  stp_term bits = term_of(bv, "vc_fpConstFromBits");
  if (vc == nullptr || bits == nullptr || !check_fp_widths(exp_bits, sig_bits) ||
      !check_bv("vc_fpConstFromBits", bits))
    return nullptr;
  if (!stp_term_is_value(bits))
  {
    fatal("CInterface: vc_fpConstFromBits: the bits argument must be a bitvector constant: ");
    return nullptr;
  }
  if (bv_width(stp_term_sort(bits)) != static_cast<std::uint32_t>(exp_bits + sig_bits))
  {
    fatal("CInterface: vc_fpConstFromBits: the bitvector width must equal exp_bits + sig_bits: ");
    return nullptr;
  }
  stp_sort fp = stp_mk_fp_sort(vc->tm, static_cast<std::uint32_t>(exp_bits), static_cast<std::uint32_t>(sig_bits));
  return built(vc, stp_mk_fp_from_bits(vc->tm, fp, bits), "vc_fpConstFromBits", true);
}

Expr vc_fpEqExpr(VC vcp, Expr a, Expr b)
{
  VCImpl* vc = vcimpl(vcp, "vc_fpEqExpr");
  stp_term l = term_of(a, "vc_fpEqExpr");
  stp_term r = term_of(b, "vc_fpEqExpr");
  if (vc == nullptr || l == nullptr || r == nullptr)
    return nullptr;
  if (!is_fp(stp_term_sort(l)) || !is_fp(stp_term_sort(r)))
  {
    fatal("CInterface: vc_fpEqExpr requires floating-point operands: ");
    return nullptr;
  }
  if (!check_same("vc_fpEqExpr", l, r))
    return nullptr;
  return built(vc, stp_fp_eq(vc->tm, l, r), "vc_fpEqExpr", true);
}

Expr vc_fpRoundingMode(VC vcp, enum VCRoundingMode mode)
{
  VCImpl* vc = vcimpl(vcp, "vc_fpRoundingMode");
  if (vc == nullptr)
    return nullptr;
  stp_rm rm;
  if (!rm_from_onehot(static_cast<unsigned>(mode), rm))
  {
    fatal("CInterface: vc_fpRoundingMode: not one of the five rounding modes");
    return nullptr;
  }
  return built(vc, stp_mk_rm(vc->tm, rm), "vc_fpRoundingMode", true);
}

namespace
{

// A rounded or unrounded floating-point operation over operands that must
// all share one format; the result is checker-owned as in 2.x.
Expr fp_op(VC vcp, const char* who, Expr rm, const Expr* operands, int n,
           stp_term (*make)(stp_tm, const stp_term*))
{
  VCImpl* vc = vcimpl(vcp, who);
  if (vc == nullptr)
    return nullptr;
  stp_term args[5];
  int k = 0;
  if (rm != nullptr)
  {
    stp_term m = term_of(rm, who);
    if (m == nullptr || !check_rm(who, m))
      return nullptr;
    args[k++] = m;
  }
  stp_term first = nullptr;
  for (int i = 0; i < n; ++i)
  {
    stp_term t = term_of(operands[i], who);
    if (t == nullptr)
      return nullptr;
    if (i == 0)
    {
      if (!check_fp(t))
        return nullptr;
      first = t;
    }
    else if (!check_same("floating-point operation", first, t))
      return nullptr;
    args[k++] = t;
  }
  return built(vc, make(vc->tm, args), who, true);
}

Expr fp_pred(VC vcp, const char* who, const Expr* operands, int n, stp_term (*make)(stp_tm, const stp_term*))
{
  VCImpl* vc = vcimpl(vcp, who);
  if (vc == nullptr)
    return nullptr;
  stp_term args[2];
  for (int i = 0; i < n; ++i)
  {
    stp_term t = term_of(operands[i], who);
    if (t == nullptr)
      return nullptr;
    if (i == 0 && !is_fp(stp_term_sort(t)))
    {
      fatal("CInterface: floating-point predicate requires a floating-point operand");
      return nullptr;
    }
    if (i > 0 && !check_same("floating-point predicate", args[0], t))
      return nullptr;
    args[i] = t;
  }
  return built(vc, make(vc->tm, args), who, true);
}

stp_term mk_abs(stp_tm tm, const stp_term* a) { return stp_fp_abs(tm, a[0]); }
stp_term mk_neg(stp_tm tm, const stp_term* a) { return stp_fp_neg(tm, a[0]); }
stp_term mk_add(stp_tm tm, const stp_term* a) { return stp_fp_add(tm, a[0], a[1], a[2]); }
stp_term mk_sub(stp_tm tm, const stp_term* a) { return stp_fp_sub(tm, a[0], a[1], a[2]); }
stp_term mk_mul(stp_tm tm, const stp_term* a) { return stp_fp_mul(tm, a[0], a[1], a[2]); }
stp_term mk_div(stp_tm tm, const stp_term* a) { return stp_fp_div(tm, a[0], a[1], a[2]); }
stp_term mk_fma(stp_tm tm, const stp_term* a) { return stp_fp_fma(tm, a[0], a[1], a[2], a[3]); }
stp_term mk_sqrt(stp_tm tm, const stp_term* a) { return stp_fp_sqrt(tm, a[0], a[1]); }
stp_term mk_rti(stp_tm tm, const stp_term* a) { return stp_fp_rti(tm, a[0], a[1]); }
stp_term mk_min(stp_tm tm, const stp_term* a) { return stp_fp_min(tm, a[0], a[1]); }
stp_term mk_max(stp_tm tm, const stp_term* a) { return stp_fp_max(tm, a[0], a[1]); }
stp_term mk_lt(stp_tm tm, const stp_term* a) { return stp_fp_lt(tm, a[0], a[1]); }
stp_term mk_leq(stp_tm tm, const stp_term* a) { return stp_fp_leq(tm, a[0], a[1]); }
stp_term mk_gt(stp_tm tm, const stp_term* a) { return stp_fp_gt(tm, a[0], a[1]); }
stp_term mk_geq(stp_tm tm, const stp_term* a) { return stp_fp_geq(tm, a[0], a[1]); }
stp_term mk_is_normal(stp_tm tm, const stp_term* a) { return stp_fp_is_normal(tm, a[0]); }
stp_term mk_is_subnormal(stp_tm tm, const stp_term* a) { return stp_fp_is_subnormal(tm, a[0]); }
stp_term mk_is_zero(stp_tm tm, const stp_term* a) { return stp_fp_is_zero(tm, a[0]); }
stp_term mk_is_inf(stp_tm tm, const stp_term* a) { return stp_fp_is_inf(tm, a[0]); }
stp_term mk_is_nan(stp_tm tm, const stp_term* a) { return stp_fp_is_nan(tm, a[0]); }
stp_term mk_is_neg(stp_tm tm, const stp_term* a) { return stp_fp_is_neg(tm, a[0]); }
stp_term mk_is_pos(stp_tm tm, const stp_term* a) { return stp_fp_is_pos(tm, a[0]); }

} // namespace

Expr vc_fpAbsExpr(VC vc, Expr f) { const Expr ops[] = {f}; return fp_op(vc, "vc_fpAbsExpr", nullptr, ops, 1, mk_abs); }
Expr vc_fpNegExpr(VC vc, Expr f) { const Expr ops[] = {f}; return fp_op(vc, "vc_fpNegExpr", nullptr, ops, 1, mk_neg); }
Expr vc_fpAddExpr(VC vc, Expr rm, Expr a, Expr b) { const Expr ops[] = {a, b}; return fp_op(vc, "vc_fpAddExpr", rm, ops, 2, mk_add); }
Expr vc_fpSubExpr(VC vc, Expr rm, Expr a, Expr b) { const Expr ops[] = {a, b}; return fp_op(vc, "vc_fpSubExpr", rm, ops, 2, mk_sub); }
Expr vc_fpMulExpr(VC vc, Expr rm, Expr a, Expr b) { const Expr ops[] = {a, b}; return fp_op(vc, "vc_fpMulExpr", rm, ops, 2, mk_mul); }
Expr vc_fpDivExpr(VC vc, Expr rm, Expr a, Expr b) { const Expr ops[] = {a, b}; return fp_op(vc, "vc_fpDivExpr", rm, ops, 2, mk_div); }
Expr vc_fpFMAExpr(VC vc, Expr rm, Expr a, Expr b, Expr c) { const Expr ops[] = {a, b, c}; return fp_op(vc, "vc_fpFMAExpr", rm, ops, 3, mk_fma); }
Expr vc_fpSqrtExpr(VC vc, Expr rm, Expr f) { const Expr ops[] = {f}; return fp_op(vc, "vc_fpSqrtExpr", rm, ops, 1, mk_sqrt); }
Expr vc_fpRoundToIntegralExpr(VC vc, Expr rm, Expr f) { const Expr ops[] = {f}; return fp_op(vc, "vc_fpRoundToIntegralExpr", rm, ops, 1, mk_rti); }
Expr vc_fpMinExpr(VC vc, Expr a, Expr b) { const Expr ops[] = {a, b}; return fp_op(vc, "vc_fpMinExpr", nullptr, ops, 2, mk_min); }
Expr vc_fpMaxExpr(VC vc, Expr a, Expr b) { const Expr ops[] = {a, b}; return fp_op(vc, "vc_fpMaxExpr", nullptr, ops, 2, mk_max); }

Expr vc_fpRemExpr(VC vcp, Expr a, Expr b)
{
  VCImpl* vc = vcimpl(vcp, "vc_fpRemExpr");
  stp_term x = term_of(a, "vc_fpRemExpr");
  stp_term y = term_of(b, "vc_fpRemExpr");
  if (vc == nullptr || x == nullptr || y == nullptr)
    return nullptr;
  if (!is_fp(stp_term_sort(x)))
  {
    fatal("CInterface: vc_fpRemExpr: fp.rem applied to a non-float operand: ");
    return nullptr;
  }
  if (!check_same("floating-point operation", x, y))
    return nullptr;
  stp_term out = stp_fp_rem(vc->tm, x, y);
  if (out == nullptr)
  {
    stp_error_code code;
    const std::string err = take_error(vc, &code);
    if (code == STP_ERR_UNSUPPORTED)
      fatal("CInterface: vc_fpRemExpr: fp.rem is not supported at this format: its circuit unrolls one "
            "divide step per representable exponent difference, which is exponential in the exponent "
            "width; use a format no larger than binary64");
    else
      fatal("CInterface: vc_fpRemExpr: " + err);
    return nullptr;
  }
  return wrap(vc, out, true);
}

Expr vc_fpLtExpr(VC vc, Expr a, Expr b) { const Expr ops[] = {a, b}; return fp_pred(vc, "vc_fpLtExpr", ops, 2, mk_lt); }
Expr vc_fpLeqExpr(VC vc, Expr a, Expr b) { const Expr ops[] = {a, b}; return fp_pred(vc, "vc_fpLeqExpr", ops, 2, mk_leq); }
Expr vc_fpGtExpr(VC vc, Expr a, Expr b) { const Expr ops[] = {a, b}; return fp_pred(vc, "vc_fpGtExpr", ops, 2, mk_gt); }
Expr vc_fpGeqExpr(VC vc, Expr a, Expr b) { const Expr ops[] = {a, b}; return fp_pred(vc, "vc_fpGeqExpr", ops, 2, mk_geq); }
Expr vc_fpIsNormalExpr(VC vc, Expr f) { const Expr ops[] = {f}; return fp_pred(vc, "vc_fpIsNormalExpr", ops, 1, mk_is_normal); }
Expr vc_fpIsSubnormalExpr(VC vc, Expr f) { const Expr ops[] = {f}; return fp_pred(vc, "vc_fpIsSubnormalExpr", ops, 1, mk_is_subnormal); }
Expr vc_fpIsZeroExpr(VC vc, Expr f) { const Expr ops[] = {f}; return fp_pred(vc, "vc_fpIsZeroExpr", ops, 1, mk_is_zero); }
Expr vc_fpIsInfiniteExpr(VC vc, Expr f) { const Expr ops[] = {f}; return fp_pred(vc, "vc_fpIsInfiniteExpr", ops, 1, mk_is_inf); }
Expr vc_fpIsNaNExpr(VC vc, Expr f) { const Expr ops[] = {f}; return fp_pred(vc, "vc_fpIsNaNExpr", ops, 1, mk_is_nan); }
Expr vc_fpIsNegativeExpr(VC vc, Expr f) { const Expr ops[] = {f}; return fp_pred(vc, "vc_fpIsNegativeExpr", ops, 1, mk_is_neg); }
Expr vc_fpIsPositiveExpr(VC vc, Expr f) { const Expr ops[] = {f}; return fp_pred(vc, "vc_fpIsPositiveExpr", ops, 1, mk_is_pos); }

namespace
{

Expr fp_special(VC vcp, const char* who, Type fpType, stp_term (*make)(stp_tm, stp_sort))
{
  VCImpl* vc = vcimpl(vcp, who);
  if (vc == nullptr)
    return nullptr;
  std::uint32_t eb = 0, sb = 0;
  if (!fp_type_widths(fpType, eb, sb))
    return nullptr;
  return built(vc, make(vc->tm, type_of(fpType, who)), who, true);
}

} // namespace

Expr vc_fpNaN(VC vc, Type fpType) { return fp_special(vc, "vc_fpNaN", fpType, stp_mk_fp_nan); }
Expr vc_fpPlusInfinity(VC vc, Type fpType) { return fp_special(vc, "vc_fpPlusInfinity", fpType, stp_mk_fp_pos_inf); }
Expr vc_fpMinusInfinity(VC vc, Type fpType) { return fp_special(vc, "vc_fpMinusInfinity", fpType, stp_mk_fp_neg_inf); }
Expr vc_fpPlusZero(VC vc, Type fpType) { return fp_special(vc, "vc_fpPlusZero", fpType, stp_mk_fp_pos_zero); }
Expr vc_fpMinusZero(VC vc, Type fpType) { return fp_special(vc, "vc_fpMinusZero", fpType, stp_mk_fp_neg_zero); }

namespace
{

// A native double or float: reinterpret its bits at its own format, then
// reformat under rm when the target differs.
Expr fp_from_native(VC vcp, const char* who, Type target, Expr rm, std::uint64_t bits, std::uint32_t eb,
                    std::uint32_t sb)
{
  VCImpl* vc = vcimpl(vcp, who);
  stp_term m = term_of(rm, who);
  if (vc == nullptr || m == nullptr || !check_rm(who, m))
    return nullptr;
  std::uint32_t teb = 0, tsb = 0;
  if (!fp_type_widths(target, teb, tsb))
    return nullptr;
  stp_sort native = stp_mk_fp_sort(vc->tm, eb, sb);
  stp_term bv = stp_mk_bv_uint64(vc->tm, eb + sb, bits);
  stp_term value = bv != nullptr ? stp_mk_fp_from_bits(vc->tm, native, bv) : nullptr;
  if (bv != nullptr)
    stp_term_release(bv);
  if (value == nullptr)
    return built(vc, nullptr, who);
  if (teb == eb && tsb == sb)
    return wrap(vc, value, true);
  stp_term out = stp_to_fp(vc->tm, type_of(target, who), m, value);
  stp_term_release(value);
  return built(vc, out, who, true);
}

// The to_fp family: the (eb, sb) format, an optional rounding mode, a source
// whose sort the entry point names.
Expr to_fp(VC vcp, const char* who, int eb, int sb, Expr rm, Expr src, int form)
{
  VCImpl* vc = vcimpl(vcp, who);
  stp_term s = term_of(src, who);
  if (vc == nullptr || s == nullptr || !check_fp_widths(eb, sb))
    return nullptr;
  const bool expects_float = form == 1;
  const stp_sort ss = stp_term_sort(s);
  if ((expects_float && !is_fp(ss)) || (!expects_float && !is_bv(ss)))
  {
    fatal(expects_float ? "CInterface: float-to-float conversion requires a floating-point source: "
                        : "CInterface: bitvector-to-float conversion requires a bitvector source: ");
    return nullptr;
  }
  stp_term m = nullptr;
  if (rm != nullptr || form != 0)
  {
    m = term_of(rm, who);
    if (m == nullptr || !check_rm("to_fp", m))
      return nullptr;
  }
  stp_sort fp = stp_mk_fp_sort(vc->tm, static_cast<std::uint32_t>(eb), static_cast<std::uint32_t>(sb));
  stp_term out;
  switch (form)
  {
    case 0: out = stp_to_fp_from_bits(vc->tm, fp, s); break;
    case 1:
    case 2: out = stp_to_fp(vc->tm, fp, m, s); break;
    default: out = stp_to_fp_unsigned(vc->tm, fp, m, s); break;
  }
  return built(vc, out, who, true);
}

Expr fp_to_bv(VC vcp, const char* who, int width, Expr rm, Expr f, bool signed_)
{
  VCImpl* vc = vcimpl(vcp, who);
  stp_term m = term_of(rm, who);
  stp_term x = term_of(f, who);
  if (vc == nullptr || m == nullptr || x == nullptr)
    return nullptr;
  if (width < 1)
  {
    fatal("CInterface: fp.to_ubv/fp.to_sbv need a positive target width");
    return nullptr;
  }
  if (!is_fp(stp_term_sort(x)))
  {
    fatal("CInterface: fp.to_ubv/fp.to_sbv applied to a non-float: ");
    return nullptr;
  }
  if (!check_rm("fp.to_ubv/fp.to_sbv", m))
    return nullptr;
  const std::uint32_t w = static_cast<std::uint32_t>(width);
  return built(vc, signed_ ? stp_fp_to_sbv(vc->tm, w, m, x) : stp_fp_to_ubv(vc->tm, w, m, x), who, true);
}

} // namespace

Expr vc_fpConstFromDouble(VC vc, Type target, Expr rm, double d)
{
  std::uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(bits));
  return fp_from_native(vc, "vc_fpConstFromDouble", target, rm, bits, 11, 53);
}

Expr vc_fpConstFromFloat(VC vc, Type target, Expr rm, float f)
{
  std::uint32_t bits = 0;
  std::memcpy(&bits, &f, sizeof(bits));
  return fp_from_native(vc, "vc_fpConstFromFloat", target, rm, bits, 8, 24);
}

Expr vc_fpToFPFromIEEEBV(VC vc, int eb, int sb, Expr bv) { return to_fp(vc, "vc_fpToFPFromIEEEBV", eb, sb, nullptr, bv, 0); }
Expr vc_fpToFPFromFP(VC vc, int eb, int sb, Expr rm, Expr f) { return to_fp(vc, "vc_fpToFPFromFP", eb, sb, rm, f, 1); }
Expr vc_fpToFPFromSignedBV(VC vc, int eb, int sb, Expr rm, Expr bv) { return to_fp(vc, "vc_fpToFPFromSignedBV", eb, sb, rm, bv, 2); }
Expr vc_fpToFPFromUnsignedBV(VC vc, int eb, int sb, Expr rm, Expr bv) { return to_fp(vc, "vc_fpToFPFromUnsignedBV", eb, sb, rm, bv, 3); }
Expr vc_fpToUBVExpr(VC vc, int width, Expr rm, Expr f) { return fp_to_bv(vc, "vc_fpToUBVExpr", width, rm, f, false); }
Expr vc_fpToSBVExpr(VC vc, int width, Expr rm, Expr f) { return fp_to_bv(vc, "vc_fpToSBVExpr", width, rm, f, true); }

Expr vc_fpToIEEEBV(VC vcp, Expr f)
{
  VCImpl* vc = vcimpl(vcp, "vc_fpToIEEEBV");
  stp_term x = term_of(f, "vc_fpToIEEEBV");
  if (vc == nullptr || x == nullptr)
    return nullptr;
  if (!is_fp(stp_term_sort(x)))
  {
    fatal("CInterface: vc_fpToIEEEBV applied to a non-float: ");
    return nullptr;
  }
  return built(vc, stp_fp_to_ieee_bv(vc->tm, x), "vc_fpToIEEEBV", true);
}

// ============================================================ Real

namespace
{

// A Real constructor's refusal is fatal, as every constructor's is (NULL
// under STP_ON_ERROR_RETURN). 2.x returned a nonfatal NULL for a literal or
// term beyond the exact-arithmetic budget; the 3.x API refuses those as
// UNSUPPORTED, as it does any other operation it cannot represent, so they
// are not told apart here (NOTES.md, item 18).
Expr real_built(VCImpl* vc, stp_term t, const char* who)
{
  if (t != nullptr)
    return wrap(vc, t, false);
  const std::string err = take_error(vc, nullptr);
  fatal(std::string("CInterface: ") + who + " failed: " + err);
  return nullptr;
}

bool real_pair(VCImpl* vc, const char* who, Expr l, Expr r, stp_term& a, stp_term& b)
{
  a = term_of(l, who);
  b = term_of(r, who);
  if (a == nullptr || b == nullptr)
    return false;
  for (stp_term t : {a, b})
  {
    Handle* h = handle(t == a ? l : r);
    if (h->vc != vc)
    {
      fatal(std::string("CInterface: ") + who + " received an Expr owned by a different validity checker");
      return false;
    }
    if (!is_real(stp_term_sort(t)))
    {
      fatal(std::string("CInterface: ") + who + " requires Real operands: ");
      return false;
    }
  }
  return true;
}

Expr real_binary(VC vcp, const char* who, Expr l, Expr r, stp_term (*make)(stp_tm, stp_term, stp_term))
{
  VCImpl* vc = vcimpl(vcp, who);
  stp_term a, b;
  if (vc == nullptr || !real_pair(vc, who, l, r, a, b))
    return nullptr;
  return real_built(vc, make(vc->tm, a, b), who);
}

} // namespace

Expr vc_realConstExprFromStr(VC vcp, const char* exact_text)
{
  VCImpl* vc = vcimpl(vcp, "vc_realConstExprFromStr");
  if (vc == nullptr)
    return nullptr;
  if (exact_text == nullptr)
  {
    fatal("CInterface: vc_realConstExprFromStr received null text");
    return nullptr;
  }
  return real_built(vc, stp_mk_real_str(vc->tm, exact_text), "vc_realConstExprFromStr");
}

Expr vc_realConstExpr(VC vcp, const char* numerator, const char* denominator)
{
  VCImpl* vc = vcimpl(vcp, "vc_realConstExpr");
  if (vc == nullptr)
    return nullptr;
  if (numerator == nullptr || denominator == nullptr)
  {
    fatal("CInterface: vc_realConstExpr received a null component");
    return nullptr;
  }
  const std::string text = std::string(numerator) + "/" + denominator;
  return real_built(vc, stp_mk_real_str(vc->tm, text.c_str()), "vc_realConstExpr");
}

Expr vc_realPlusExpr(VC vc, Expr l, Expr r) { return real_binary(vc, "vc_realPlusExpr", l, r, stp_real_add); }
Expr vc_realMinusExpr(VC vc, Expr l, Expr r) { return real_binary(vc, "vc_realMinusExpr", l, r, stp_real_sub); }
Expr vc_realMultExpr(VC vc, Expr l, Expr r) { return real_binary(vc, "vc_realMultExpr", l, r, stp_real_mul); }
Expr vc_realDivExpr(VC vc, Expr l, Expr r) { return real_binary(vc, "vc_realDivExpr", l, r, stp_real_div); }
Expr vc_realLtExpr(VC vc, Expr l, Expr r) { return real_binary(vc, "vc_realLtExpr", l, r, stp_real_lt); }
Expr vc_realLeExpr(VC vc, Expr l, Expr r) { return real_binary(vc, "vc_realLeExpr", l, r, stp_real_le); }
Expr vc_realGtExpr(VC vc, Expr l, Expr r) { return real_binary(vc, "vc_realGtExpr", l, r, stp_real_gt); }
Expr vc_realGeExpr(VC vc, Expr l, Expr r) { return real_binary(vc, "vc_realGeExpr", l, r, stp_real_ge); }

Expr vc_realUMinusExpr(VC vcp, Expr operand)
{
  VCImpl* vc = vcimpl(vcp, "vc_realUMinusExpr");
  stp_term a = term_of(operand, "vc_realUMinusExpr");
  if (vc == nullptr || a == nullptr)
    return nullptr;
  if (!is_real(stp_term_sort(a)))
  {
    fatal("CInterface: vc_realUMinusExpr requires Real operands: ");
    return nullptr;
  }
  return real_built(vc, stp_real_neg(vc->tm, a), "vc_realUMinusExpr");
}
