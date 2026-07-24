/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: January 2021
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

#include "stp/FloatBlaster/symbolic_fp.h"

#include "stp/FloatBlaster/FloatBlaster.h"
#include "stp/Globals/Globals.h"
#include <cassert>
#include <string>
#include <cmath>

#include "symfpu/core/add.h"
#include "symfpu/core/classify.h"
#include "symfpu/core/compare.h"
#include "symfpu/core/convert.h"
#include "symfpu/core/divide.h"
#include "symfpu/core/fma.h"
#include "symfpu/core/ite.h"
#include "symfpu/core/multiply.h"
#include "symfpu/core/packing.h"
#include "symfpu/core/remainder.h"
#include "symfpu/core/sign.h"
#include "symfpu/core/sqrt.h"
#include "symfpu/utils/numberOfRoundingModes.h"
#include "symfpu/utils/properties.h"

namespace stp
{

FloatBlaster* FloatBlaster::_instance = nullptr;

FloatBlaster* FloatBlaster::instance()
{
  if (_instance == nullptr)
  {
    assert(stp::GlobalParserBM != nullptr);
    _instance = new FloatBlaster();
  }
  return _instance;
}

FloatBlaster::FloatBlaster()
{
  ASTTrue = stp::GlobalParserBM->CreateNode(TRUE);
  ASTFalse = stp::GlobalParserBM->CreateNode(FALSE);
  ASTUndefined = stp::GlobalParserBM->CreateNode(UNDEFINED);
  nf = stp::GlobalParserBM->defaultNodeFactory;

  symbolic_fp::init_vc(stp::GlobalParserBM);
}

ASTNode FloatBlaster::withFormat(STPMgr* bm, const ASTNode& n,
                                 unsigned int exp_width,
                                 unsigned int sig_width)
{
  if (exp_width == 0 && sig_width == 0)
    return n;

  if (n.GetExpWidth() == exp_width && n.GetSigWidth() == sig_width)
    return n;

  // Only a float-shaped value can carry a float's format; a rounding mode or
  // one of to_fp's format arguments must be left alone.
  if (n.GetValueWidth() != exp_width + sig_width)
    return n;

  ASTNode out(n);

  if (out.GetKind() == BVCONST)
  {
    // ASTBVConst cannot hold a format; ASTFPConst can. CreateFPConst makes a
    // fresh node, so this never retypes a shared constant.
    out = bm->CreateFPConst(out);
  }

  out.SetExpWidth(exp_width);
  out.SetSigWidth(sig_width);
  return out;
}

ASTNode FloatBlaster::canonicalBits(const ASTNode& f)
{
  // Point symfpu at the current manager before blasting (see init_vc).
  symbolic_fp::init_vc(stp::GlobalParserBM);
  return symbolic_fp::blast_reinterpret(f, f.GetExpWidth(), f.GetSigWidth());
}

ASTNode FloatBlaster::unspecifiedValue(STPMgr* bm, const char* tag,
                                       const ASTNode& index,
                                       unsigned int value_width)
{
  const unsigned int index_width = index.GetValueWidth();

  std::string name("_stp_fp_unspecified_");
  name += tag;
  name += "_";
  name += std::to_string(index_width);
  name += "_";
  name += std::to_string(value_width);

  const ASTNode array = bm->defaultNodeFactory->CreateSymbol(
      name.c_str(), index_width, value_width);

  return bm->CreateTerm(READ, value_width, array, index);
}

ASTNode FloatBlaster::BlastNode_TopLevel(const ASTNode& b)
{
  // Point symfpu's backend at the manager being blasted now, rather than
  // whichever manager happened to blast first (see symbolic_fp::init_vc).
  symbolic_fp::init_vc(stp::GlobalParserBM);
  ASTNode out = FloatBlaster::instance()->BlastNode(b);
  return out;
}

ASTNode FloatBlaster::BlastNode(const ASTNode& actualInputterm)
{
  ASTNode inputterm(actualInputterm);

  ASTNode output = inputterm;
  // assert(BVTypeCheck(inputterm));

  types t = actualInputterm.GetType();
  // comparisions are Boolean
  // assert(t == FLOATINGPOINT_TYPE || t == BOOLEAN_TYPE);

  Kind k = inputterm.GetKind();

  switch (k)
  {
    // The arithmetic operations all carry their rounding mode as child 0,
    // matching their arity in ASTKind.kinds.
    case FP_ADD:
      output = symbolic_fp::blast_fpadd(/* rm */ inputterm[0], inputterm[1],
                                        inputterm[2]);
      break;
    case FP_SUB:
      output = symbolic_fp::blast_fpsub(/* rm */ inputterm[0], inputterm[1],
                                        inputterm[2]);
      break;
    case FP_MUL:
      output = symbolic_fp::blast_fpmul(/* rm */ inputterm[0], inputterm[1],
                                        inputterm[2]);
      break;
    case FP_DIV:
      output = symbolic_fp::blast_fpdiv(/* rm */ inputterm[0], inputterm[1],
                                        inputterm[2]);
      break;
    case FP_FMA:
      output = symbolic_fp::blast_fpfma(/* rm */ inputterm[0], inputterm[1],
                                        inputterm[2], inputterm[3]);
      break;
    case FP_SQRT:
      output = symbolic_fp::blast_fpsqrt(/* rm */ inputterm[0], inputterm[1]);
      break;
    // fp.rem, fp.min and fp.max take no rounding mode.
    case FP_REM:
      output = symbolic_fp::blast_fprem(inputterm[0], inputterm[1]);
      break;
    // The choice of zero for (+0, -0) arrives as a third child, put there by
    // FpTotalise before solving.
    case FP_MIN:
    case FP_MAX:
    {
      assert(inputterm.Degree() == 3);

      // Child 2 is a 1-bit bitvector; symfpu wants a proposition.
      const ASTNode zero_case = stp::GlobalParserBM->CreateNode(
          EQ, inputterm[2], stp::GlobalParserBM->CreateOneConst(1));

      output = (k == FP_MIN)
                   ? symbolic_fp::blast_fpmin(inputterm[0], inputterm[1],
                                              zero_case)
                   : symbolic_fp::blast_fpmax(inputterm[0], inputterm[1],
                                              zero_case);
      break;
    }
    case FP_ABS:
      output = symbolic_fp::blast_fpabs(inputterm[0]);
      break;
    case FP_NEG:
      output = symbolic_fp::blast_fpneg(inputterm[0]);
      break;
    case FP_ISNORMAL:
      output = symbolic_fp::blast_is_normal(inputterm[0]);
      break;
    case FP_ISSUBNORMAL:
      output = symbolic_fp::blast_is_subnormal(inputterm[0]);
      break;
    case FP_ISZERO:
      output = symbolic_fp::blast_is_zero(inputterm[0]);
      break;
    case FP_ISINFINITE:
      output = symbolic_fp::blast_is_infinite(inputterm[0]);
      break;
    case FP_ISNAN:
      output = symbolic_fp::blast_is_nan(inputterm[0]);
      break;
    case FP_ISNEGATIVE:
      output = symbolic_fp::blast_is_negative(inputterm[0]);
      break;
    case FP_ISPOSITIVE:
      output = symbolic_fp::blast_is_positive(inputterm[0]);
      break;
    // fp.eq is IEEE equality; FP_SMT_EQ is SMT-LIB's `=` on floats.
    case FP_EQ:
      output = symbolic_fp::blast_fpeq(inputterm[0], inputterm[1]);
      break;
    case FP_LT:
      output = symbolic_fp::blast_fplt(inputterm[0], inputterm[1]);
      break;
    case FP_LEQ:
      output = symbolic_fp::blast_fpleq(inputterm[0], inputterm[1]);
      break;
    // fp.gt/fp.geq are the reversed forms; SMT-LIB defines them that way.
    case FP_GT:
      output = symbolic_fp::blast_fplt(inputterm[1], inputterm[0]);
      break;
    case FP_GEQ:
      output = symbolic_fp::blast_fpleq(inputterm[1], inputterm[0]);
      break;
    // ((_ to_fp e s) [rm] f). Children are (e, s, bits) for the bitvector
    // reinterpretation, or (e, s, rm, expr) for a float-to-float conversion.
    //
    // Take the target format from the e/s children rather than from the
    // node's own exponent/significand widths. Those are mutable per-node
    // state that a rebuild can drop, and blasting against a format of
    // (0, 0) underflows a width rather than failing; the children always
    // say what the format is.
    case FP_TOFP:
    {
      const unsigned int to_exp = inputterm[0].GetUnsignedConst();
      const unsigned int to_sig = inputterm[1].GetUnsignedConst();

      if (inputterm.Degree() == 3)
      {
        output = symbolic_fp::blast_reinterpret(/* bits */ inputterm[2],
                                                to_exp, to_sig);
      }
      else
      {
        assert(inputterm.Degree() == 4);

        // With a rounding mode, the source may be another float (reformat) or
        // a bitvector holding a signed integer (convert).
        if (inputterm[3].GetType() == FLOATINGPOINT_TYPE)
          output = symbolic_fp::blast_convert_float_to_float(
              /* rm */ inputterm[2], /* expr */ inputterm[3], to_exp, to_sig);
        else
          output = symbolic_fp::blast_convert_bv_to_float(
              /* rm */ inputterm[2], /* bits */ inputterm[3], to_exp, to_sig,
              /* is_signed */ true);
      }

      // The node may have arrived without its format for the same reason,
      // so hand the derived one back rather than the (possibly zero) stored
      // one that the tail below would otherwise apply.
      return FloatBlaster::withFormat(stp::GlobalParserBM, output, to_exp,
                                      to_sig);
    }
    case FP_CONST_POS_INF:
      output = symbolic_fp::blast_pos_inf(actualInputterm);
      break;
    case FP_CONST_NEG_INF:
      output = symbolic_fp::blast_neg_inf(actualInputterm);
      break;
    case FP_CONST_NAN:
      output = symbolic_fp::blast_nan(actualInputterm);
      break;
    case FP_CONST_POS_ZERO:
      output = symbolic_fp::blast_zero(actualInputterm, false);
      break;
    case FP_CONST_NEG_ZERO:
      output = symbolic_fp::blast_zero(actualInputterm, true);
      break;
    // ((_ to_fp_unsigned e s) rm bv): the source is always an unsigned
    // integer in a bitvector.
    case FP_TOFP_UNSIGNED:
    {
      const unsigned int to_exp = inputterm[0].GetUnsignedConst();
      const unsigned int to_sig = inputterm[1].GetUnsignedConst();
      output = symbolic_fp::blast_convert_bv_to_float(
          /* rm */ inputterm[2], /* bits */ inputterm[3], to_exp, to_sig,
          /* is_signed */ false);
      return FloatBlaster::withFormat(stp::GlobalParserBM, output, to_exp,
                                      to_sig);
    }
    // (m, rm, x, unspecified). The result is a bitvector, not a float, so no
    // floating-point format is stamped on it.
    case FP_TO_UBV:
    case FP_TO_SBV:
      assert(inputterm.Degree() == 4);
      return symbolic_fp::blast_fp_to_bv(
          /* rm */ inputterm[1], /* x */ inputterm[2],
          inputterm[0].GetUnsignedConst(), /* undef */ inputterm[3],
          /* is_signed */ k == FP_TO_SBV);
    // A float reinterpreted as its packed IEEE bits (unpack then pack, which
    // canonicalises NaN). Result is a bitvector, not a float.
    case FP_TO_IEEE_BV:
      output = symbolic_fp::blast_reinterpret(inputterm[0],
                                              inputterm[0].GetExpWidth(),
                                              inputterm[0].GetSigWidth());
      break;
    case FP_SMT_EQ:
      output = symbolic_fp::blast_smt_eq(inputterm[0], inputterm[1]);
      break;
    case FP_ROUNDTOINTEGRAL:
      output = symbolic_fp::blast_round_to_integral(/* rm */ inputterm[0],
                                                    /* expr */ inputterm[1]);
      break;
    default:
      std::cerr << "FloatBlaster::BlastNode: Unhandled kind: " << k
                << std::endl;
      assert(false);
      break;
  };

  // As in the simplifier: only float-producing operations get their result
  // re-made as a floating-point constant. A Boolean or bitvector result must
  // be left exactly as it is.
  if (actualInputterm.GetExpWidth() != 0)
  {
    if (output.GetKind() == BVCONST)
    {
      output = stp::GlobalParserBM->CreateFPConst(output);
    }
    output.SetExpWidth(actualInputterm.GetExpWidth());
    output.SetSigWidth(actualInputterm.GetSigWidth());
  }

  // std::cout << output.GetExpWidth() << " " << output.GetKind() << std::endl;

  return output;
}

} // namespace stp
