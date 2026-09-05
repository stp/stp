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
********************************************************************/

#include "stp/Simplifier/EmbeddedConstraints.h"
#include "stp/Simplifier/SubstitutionMap.h"

namespace stp
{

ASTNode EmbeddedConstraints::topLevel(const ASTNode& input)
{
  if (input.GetKind() != AND)
    return input;

  NodeFactory* nf = bm->defaultNodeFactory;
  const ASTNode ASTTrue = bm->CreateNode(TRUE);
  const ASTNode ASTFalse = bm->CreateNode(FALSE);

  // What each assertion says. A negated one says its child is false, which
  // is the stronger reading and the one worth having: the child is what
  // recurs inside the others.
  ASTNodeMap says;
  for (const ASTNode& c : input.GetChildren())
  {
    if (c.GetKind() == NOT)
      says[c[0]] = ASTFalse;
    else if (c.GetKind() != TRUE && c.GetKind() != FALSE)
      says[c] = ASTTrue;
  }

  if (says.empty())
    return input;

  ASTVec rebuilt;
  rebuilt.reserve(input.Degree());
  bool anyChange = false;

  for (const ASTNode& c : input.GetChildren())
  {
    // The assertion's own top node is not substituted; only what is under
    // it. For a negated assertion that means going under the NOT as well,
    // since the map sends its child to false and rebuilding from that child
    // would leave `not false`.
    const bool inverted = (c.GetKind() == NOT);
    const ASTNode body = inverted ? c[0] : c;

    if (body.Degree() == 0)
    {
      rebuilt.push_back(c);
      continue;
    }

    ASTVec children;
    children.reserve(body.Degree());
    bool changed = false;
    for (const ASTNode& child : body.GetChildren())
    {
      // A copy per child: replace() is documented to modify the map it is
      // given, and every child has to be asked the same question.
      ASTNodeMap fromTo = says;
      ASTNodeMap cache;
      const ASTNode after =
          SubstitutionMap::replace(child, fromTo, cache, nf);
      changed = changed || (after != child);
      children.push_back(after);
    }

    if (!changed)
    {
      rebuilt.push_back(c);
      continue;
    }

    anyChange = true;
    ASTNode node = nf->CreateNode(body.GetKind(), children);
    if (inverted)
      node = nf->CreateNode(NOT, node);
    rebuilt.push_back(node);
  }

  if (!anyChange)
    return input;

  return nf->CreateNode(AND, rebuilt);
}

} // namespace stp
