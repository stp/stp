/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: October, 2026
 *
 * LICENSE: Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to permit
 * persons to whom the Software is furnished to do so, subject to the
 * following conditions:
 *
 * The above copyright notice and this permission notice shall be included
 * in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 ********************************************************************/

#include "stp/Simplifier/StrengthReducingNodeFactory.h"
#include "stp/Simplifier/NodeDomainAnalysis.h"
#include "stp/Simplifier/StrengthReduction.h"

namespace stp
{

// A leaf has nothing to reduce; a constant is already its own domain.
ASTNode StrengthReducingNodeFactory::reduce(const ASTNode& n)
{
  if (n.Degree() == 0)
    return n;
  return reduction.reduceNode(n, domains);
}

ASTNode StrengthReducingNodeFactory::CreateNode(Kind kind, ASTChildren children)
{
  return reduce(inner.CreateNode(kind, children));
}

ASTNode StrengthReducingNodeFactory::CreateTerm(Kind kind, unsigned int width,
                                                ASTChildren children)
{
  return reduce(inner.CreateTerm(kind, width, children));
}

ASTNode StrengthReducingNodeFactory::CreateArrayTerm(Kind kind,
                                                     unsigned int index,
                                                     unsigned int width,
                                                     ASTChildren children)
{
  return reduce(inner.CreateArrayTerm(kind, index, width, children));
}
}
