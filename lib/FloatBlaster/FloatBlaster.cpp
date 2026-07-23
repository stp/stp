/********************************************************************
 * AUTHORS: Andrew V. Jones
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

ASTNode FloatBlaster::BlastNode_TopLevel(const ASTNode& b)
{
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
    // The target format is already recorded on the node itself.
    case FP_TOFP:
      if (inputterm.Degree() == 3)
      {
        // Reinterpretation: floats are stored packed, so the bit pattern is
        // already the answer.
        output = inputterm[2];
      }
      else
      {
        assert(inputterm.Degree() == 4);
        output = symbolic_fp::blast_convert_float_to_float(
            /* rm */ inputterm[2], /* expr */ inputterm[3],
            actualInputterm.GetExpWidth(), actualInputterm.GetSigWidth());
      }
      break;
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

  if (output.GetKind() == BVCONST)
  {
    output = stp::GlobalParserBM->CreateFPConst(output);
  }
  output.SetExpWidth(actualInputterm.GetExpWidth());
  output.SetSigWidth(actualInputterm.GetSigWidth());

  // std::cout << output.GetExpWidth() << " " << output.GetKind() << std::endl;

  return output;
}

} // namespace stp
