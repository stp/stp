/********************************************************************
 * AUTHORS: Andrew V. Jones
 *
 * BEGIN DATE: July, 2026
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

#include "stp/Extensionality/ExtensionalityContext.h"
#include "stp/STPManager/STPManager.h"

namespace stp
{

namespace
{

bool isArrayType(const ASTNode& n)
{
  return n.GetType() == ARRAY_TYPE;
}

// Postorder DAG collection of every node beneath (and including) n.
void collectDag(const ASTNode& n, ASTNodeSet& visited)
{
  if (!visited.insert(n).second)
    return;
  for (unsigned k = 0; k < n.Degree(); k++)
    collectDag(n[k], visited);
}

} // namespace

ExtensionalityContext::ExtensionalityContext(STPMgr* bm_) : bm(bm_)
{
}

bool ExtensionalityContext::enabled() const
{
  return bm->UserFlags.enable_array_equality;
}

void ExtensionalityContext::collectPossibleConeSymbols(const ASTNode& n)
{
  ASTNodeSet visited;
  collectDag(n, visited);
  for (ASTNodeSet::const_iterator it = visited.begin(); it != visited.end();
       ++it)
    if (it->GetKind() == SYMBOL && isArrayType(*it))
      possibleConeSymbols.insert(*it);
}

// Formula abstraction of an array equality (paper section 5): instead
// of an EQ node, return a fresh Boolean abstraction variable, and
// record the pair. Reflexive requests fold to true. The record's
// constraint bundle -- the paper's preprocessing step 1: a fresh
// witness index lambda, the two virtual reads read(a,lambda) and
// read(b,lambda) (kept alive through named defining equations), and
// the witness clause "proxy OR nameL != nameR" -- is built here over
// the construction operands, with the plain hashing factory so no
// simplifying rewrite can alter the recorded terms.
ASTNode ExtensionalityContext::makeEquality(const ASTNode& a, const ASTNode& b)
{
  if (!isArrayType(a) || !isArrayType(b) ||
      a.GetIndexWidth() != b.GetIndexWidth() ||
      a.GetValueWidth() != b.GetValueWidth())
  {
    FatalError("array-equality: equality between arrays requires "
               "identical index and element widths",
               a);
  }

  if (a == b)
    return bm->ASTTrue;

  // The hashing factory sorts EQ children, so callers may present the
  // operands in either order; canonicalize the registry key the same
  // way.
  const bool ordered = a.GetNodeNum() < b.GetNodeNum();
  const ASTNode& left = ordered ? a : b;
  const ASTNode& right = ordered ? b : a;

  const std::pair<ASTNode, ASTNode> key(left, right);
  std::map<std::pair<ASTNode, ASTNode>, size_t>::const_iterator it =
      keyToRecord.find(key);
  if (it != keyToRecord.end())
    return records[it->second].proxy;

  NodeFactory* hf = bm->hashingNodeFactory;
  const unsigned iw = left.GetIndexWidth();
  const unsigned ew = left.GetValueWidth();

  Record r;
  r.id = records.size();
  r.proxy = bm->CreateFreshVariable(0, 0, "ext_eq");
  r.constructionLeft = left;
  r.constructionRight = right;
  r.lambda = bm->CreateFreshVariable(0, iw, "ext_lam");
  r.nameL = bm->CreateFreshVariable(0, ew, "ext_wit");
  r.nameR = bm->CreateFreshVariable(0, ew, "ext_wit");

  ASTNode readL = hf->CreateTerm(READ, ew, left, r.lambda);
  ASTNode readR = hf->CreateTerm(READ, ew, right, r.lambda);
  r.anchorL = hf->CreateNode(EQ, r.nameL, readL);
  r.anchorR = hf->CreateNode(EQ, r.nameR, readR);
  r.witnessClause = hf->CreateNode(
      OR, r.proxy, hf->CreateNode(NOT, hf->CreateNode(EQ, r.nameL, r.nameR)));

  protectedSymbols.insert(r.proxy);
  protectedSymbols.insert(r.lambda);
  protectedSymbols.insert(r.nameL);
  protectedSymbols.insert(r.nameR);
  collectPossibleConeSymbols(left);
  collectPossibleConeSymbols(right);

  keyToRecord[key] = r.id;
  proxyToRecord[r.proxy] = r.id;
  records.push_back(r);
  return records.back().proxy;
}

} // namespace stp
