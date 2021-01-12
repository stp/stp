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
  assert(t == FLOATINGPOINT_TYPE || t == BOOLEAN_TYPE);

  Kind k = inputterm.GetKind();

  symbolic_fp::roundingMode default_rm(symbolic_fp::traits::RNE());

  switch (k)
  {
    case FP_EQ:
      output = symbolic_fp::blast_fpeq(inputterm[0], inputterm[1]);
      break;
    case FP_ADD:
      output = symbolic_fp::blast_fpadd(default_rm, inputterm[0], inputterm[1]);
      break;
    default:
      std::cerr << "FloatBlaster::BlastNode: Unhandled kind: " << k
                << std::endl;
      assert(false);
      break;
  };

  return output;
}

} // namespace stp
