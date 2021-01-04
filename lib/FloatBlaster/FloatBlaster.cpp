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

#include "stp/FloatBlaster/FloatBlaster.h"
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

ASTNode FloatBlaster::BlastTerm_TopLevel(const ASTNode& b)
{
  ASTNode out = BlastTerm(b);
  return out;
}

ASTNode FloatBlaster::BlastTerm(const ASTNode& actualInputterm)
{
  ASTNode inputterm(actualInputterm);

  ASTNode output = inputterm;
  assert(BVTypeCheck(inputterm));

  types t = actualInputterm.GetType();
  // comparisions are Boolean
  assert(t == FLOATINGPOINT_TYPE || t == BOOLEAN_TYPE);

  Kind k = inputterm.GetKind();

  switch (k)
  {
    case FP_EQ:
      std::cerr << "FloatBlaster::BlastTerm: Unhandled kind: " << k
                << std::endl;
      break;
    default:
      std::cerr << "FloatBlaster::BlastTerm: Unhandled kind: " << k
                << std::endl;
      break;
  };

  return output;
}

} // namespace stp
