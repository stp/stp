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

#include "stp/FloatBlaster/FloatBlast.h"

#include "stp/FloatBlaster/FloatBlaster.h"

namespace stp
{

FloatBlast::FloatBlast(STPMgr* bm_) : bm(bm_), nf(bm_->defaultNodeFactory) {}

ASTNode FloatBlast::topLevel(const ASTNode& n)
{
  traversal_cache.clear();
  const ASTNode out = visit(n);
  traversal_cache.clear();
  return out;
}

ASTNode FloatBlast::rebuild(const ASTNode& n, const ASTVec& children)
{
  if (n.GetType() == BOOLEAN_TYPE)
    return nf->CreateNode(n.GetKind(), children);

  if (n.GetIndexWidth() > 0)
    return nf->CreateArrayTerm(n.GetKind(), n.GetIndexWidth(),
                               n.GetValueWidth(), children);

  return nf->CreateTerm(n.GetKind(), n.GetValueWidth(), children);
}

ASTNode FloatBlast::visit(const ASTNode& n)
{
  // A leaf is already the bits it denotes: a float symbol is a bitvector of
  // exp + sig bits carrying its declared format, and a float constant is an
  // interned ASTFPConst holding its packed bits. Neither is shared with a
  // plain bitvector use -- a declaration names one entity, and float
  // constants intern apart from the plain constant with the same bits -- so
  // the format they carry retypes nothing.
  if (n.Degree() == 0)
    return n;

  const ASTNodeMap::const_iterator persistent = persistent_cache.find(n);
  if (persistent != persistent_cache.end())
    return persistent->second;
  const ASTNodeMap::const_iterator current = traversal_cache.find(n);
  if (current != traversal_cache.end())
    return current->second;

  ASTVec children;
  children.reserve(n.Degree());

  bool changed = false;
  for (size_t i = 0; i < n.Degree(); i++)
  {
    const ASTNode c = visit(n[i]);
    changed = changed || (c != n[i]);
    children.push_back(c);
  }

  const Kind k = n.GetKind();
  ASTNode out;

  if (is_FP_kind(k))
  {
    // The operand format comes from `n`, whose children still say what sort
    // they are; `children` are bits by now and could only be guessed at.
    // This is the whole reason the pass walks the floating-point graph
    // rather than blasting whatever the simplifier happens to hand it.
    const std::pair<unsigned int, unsigned int> fmt =
        FloatBlaster::operandFormat(n);

    out = FloatBlaster::BlastNode_TopLevel(bm, k, children, fmt.first,
                                           fmt.second);
  }
  else if (changed)
  {
    out = rebuild(n, children);
  }
  else
  {
    out = n;
  }

  traversal_cache[n] = out;
  if (out != n &&
      (is_FP_kind(k) ||
       n.GetSourceSort().kind() == SourceSort::Kind::FloatingPoint))
    persistent_cache[n] = out;
  return out;
}

} // namespace stp
