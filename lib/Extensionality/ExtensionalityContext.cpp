/********************************************************************
 * AUTHORS: Andrew Teylu
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
#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/ToSat/ToSATBase.h"
#include <algorithm>

namespace stp
{

namespace
{

bool isArrayType(const ASTNode& n)
{
  return n.GetType() == ARRAY_TYPE;
}

bool nodeNumLess(const ASTNode& a, const ASTNode& b)
{
  return a.GetNodeNum() < b.GetNodeNum();
}

// The plain bitvector twin of a constant. A floating-point constant
// interns separately from the bitvector constant with the same bits
// (the format is part of the identity), but this machinery works on
// packed bits and compares model constants by node identity, so every
// constant it keeps -- scalar names, checker model values, lemma
// leaves -- must be the plain flavour: a float-element write value
// held as a float constant would never compare equal to the same bits
// read back from the SAT assignment, and the checker would report the
// same phantom conflict on every refinement iteration.
ASTNode plainConst(STPMgr* bm, const ASTNode& c)
{
  assert(c.isConstant());
  if (c.GetExpWidth() == 0)
    return c;
  return bm->CreateBVConst(CONSTANTBV::BitVector_Clone(c.GetBVConst()),
                           c.GetValueWidth());
}

// Whether the packed floating-point cell x of format (eb, sb) holds a NaN:
// an all-ones exponent with a nonzero significand, the layout being
// [sign | exponent eb | significand sb-1]. Built as a plain bitvector
// circuit because witness clauses can be minted during preparation, after
// the floating-point lowering has already run.
ASTNode isPackedNaN(NodeFactory* hf, const ASTNode& x, unsigned eb,
                    unsigned sb)
{
  const unsigned w = eb + sb;
  const ASTNode exponent =
      hf->CreateTerm(BVEXTRACT, eb, x, hf->CreateBVConst(32, w - 2),
                     hf->CreateBVConst(32, sb - 1));
  const ASTNode significand =
      hf->CreateTerm(BVEXTRACT, sb - 1, x, hf->CreateBVConst(32, sb - 2),
                     hf->CreateBVConst(32, 0));
  return hf->CreateNode(
      AND, hf->CreateNode(EQ, exponent, hf->CreateMaxConst(eb)),
      hf->CreateNode(
          NOT, hf->CreateNode(EQ, significand, hf->CreateZeroConst(sb - 1))));
}

// Postorder DAG collection of every node beneath (and including) n.
void collectDag(const ASTNode& n, ASTNodeSet& visited)
{
  if (!visited.insert(n).second)
    return;
  for (unsigned k = 0; k < n.Degree(); k++)
    collectDag(n[k], visited);
}

// The current form of an equality operand, read back from its witness
// anchor. The anchor was recorded as name = read(operand, lambda), but
// STP's simplifier pushes reads through array if-then-else, so by
// preparation time the right-hand side may instead be an if-then-else
// tree whose leaves are reads at lambda. A read leaf contributes its
// array operand; an if-then-else contributes the array if-then-else
// rebuilt (with the plain hashing factory) over the recovered
// branches -- exactly the operand's current form, which the usual
// elimination then replaces. Every read leaf must still read at this
// record's witness index, and any other shape means the anchor was
// rewritten beyond recognition: refuse loudly rather than guess.
//
// A rebuilt if-then-else that elimination already replaced (this
// solve or an earlier one) recovers as its fresh replacement array.
// That is what lets the elimination fixed point terminate: the pushed
// anchor keeps its if-then-else shape inside the formula, where the
// root substitution over array terms cannot rewrite it, so without
// the cache lookup recovery would resurrect the same if-then-else on
// every iteration.
ASTNode recoverAnchoredOperand(const ASTNode& rhs, const ASTNode& lambda,
                               const ASTNode& proxy, NodeFactory* hf,
                               const std::map<ASTNode, ASTNode>& replacements)
{
  if (rhs.GetKind() == READ)
  {
    if (rhs[1] != lambda)
      FatalError("array-equality: a witness read's index was rewritten "
                 "away, although witness indices are protected from "
                 "substitution",
                 proxy);
    return rhs[0];
  }
  if (rhs.GetKind() == ITE)
  {
    const ASTNode thenPart =
        recoverAnchoredOperand(rhs[1], lambda, proxy, hf, replacements);
    const ASTNode elsePart =
        recoverAnchoredOperand(rhs[2], lambda, proxy, hf, replacements);
    ASTVec children;
    children.push_back(rhs[0]);
    children.push_back(thenPart);
    children.push_back(elsePart);
    const ASTNode rebuilt =
        hf->CreateArrayTerm(ITE, thenPart.GetIndexWidth(),
                            thenPart.GetValueWidth(), children);
    std::map<ASTNode, ASTNode>::const_iterator rep =
        replacements.find(rebuilt);
    return rep == replacements.end() ? rebuilt : rep->second;
  }
  FatalError("array-equality: a witness-read defining equation was "
             "rewritten into a shape operand recovery does not "
             "recognize",
             proxy);
  return rhs; // unreachable; FatalError does not return
}

} // namespace

ExtensionalityContext::ExtensionalityContext(STPMgr* bm_)
    : lemmasEmitted(0), lemmaAtomsFolded(0), bm(bm_), coneIsFrozen(false),
      graphBound(false),
      pendingLemmaValid(false)
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

// An equality between a chain of writes and the chain's own base
// array,
//
//   write(...write(base, i_n, v_n)..., i_1, v_1) = base
//
// (i_1 outermost), holds exactly when every written value is already
// in the base at its index, unless an outer write shadows it:
//
//   AND_k [ i_k = i_1 OR ... OR i_k = i_{k-1}
//           OR read(base, i_k) = v_k ]
//
// This dissolves the common "array unchanged except at a few indices"
// frame-condition shape into plain bitvector-and-read constraints --
// no abstraction variable, no witness, no refinement. The two-sided
// variant, where both operands stack writes on a shared deeper base,
// is deliberately not attempted: its guards grow quadratically, and
// the general lemmas-on-demand procedure already covers that shape.
//
// Built with the plain hashing factory; the result is ordinary formula
// content that STP's later passes simplify as usual. A conjunct whose
// index term is identical to an outer write's index term is certainly
// shadowed and is dropped here, since the hashing factory would not
// fold the reflexive equality itself. The outermost write never has
// outer writes, so the conjunction is never empty.
ASTNode ExtensionalityContext::solveWriteChain(const ASTNode& a,
                                               const ASTNode& b) const
{
  for (int orientation = 0; orientation < 2; orientation++)
  {
    const ASTNode& chain = (orientation == 0) ? a : b;
    const ASTNode& base = (orientation == 0) ? b : a;

    // Peel writes off the chain side, outermost first, until the base
    // side appears; anything else is not this shape.
    ASTVec writesOutermostFirst;
    ASTNode cur = chain;
    bool matched = false;
    while (cur.GetKind() == WRITE)
    {
      writesOutermostFirst.push_back(cur);
      cur = cur[0];
      if (cur == base)
      {
        matched = true;
        break;
      }
    }
    if (!matched)
      continue;

    NodeFactory* hf = bm->hashingNodeFactory;
    const unsigned ew = base.GetValueWidth();
    ASTVec conjuncts;
    for (size_t k = 0; k < writesOutermostFirst.size(); k++)
    {
      const ASTNode& indexK = writesOutermostFirst[k][1];
      const ASTNode& valueK = writesOutermostFirst[k][2];
      ASTVec disjuncts;
      bool certainlyShadowed = false;
      for (size_t m = 0; m < k; m++)
      {
        const ASTNode& indexM = writesOutermostFirst[m][1];
        if (indexK == indexM)
        {
          certainlyShadowed = true;
          break;
        }
        disjuncts.push_back(hf->CreateNode(EQ, indexK, indexM));
      }
      if (certainlyShadowed)
        continue;
      disjuncts.push_back(hf->CreateNode(
          EQ, hf->CreateTerm(READ, ew, base, indexK), valueK));
      conjuncts.push_back(disjuncts.size() == 1
                              ? disjuncts[0]
                              : hf->CreateNode(OR, disjuncts));
    }
    return conjuncts.size() == 1 ? conjuncts[0]
                                 : hf->CreateNode(AND, conjuncts);
  }
  return ASTNode();
}

// The equality arm of the paper's formula abstraction (section 5),
// applied eagerly at construction: instead of an EQ node, return a
// fresh Boolean abstraction variable, and record the pair. Reflexive
// requests fold to true. The record's constraint bundle corresponds
// to the paper's preprocessing step 1 -- a fresh witness index
// lambda, the two virtual reads read(a,lambda) and read(b,lambda)
// (kept alive through named defining equations), and the witness
// clause "proxy OR nameL != nameR". The paper orders that
// preprocessing before abstraction; here the bundle is built
// alongside the variable, over the construction operands, with the
// plain hashing factory so no simplifying rewrite can alter the
// recorded terms, and enters the formula at solve time.
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

  // Same packed width is not the same sort: a floating-point-element
  // array and a bitvector-element array of one packed width (or two
  // floating-point formats splitting one width differently) may not be
  // equated, mirroring the parser's rejection of = between a float and
  // a bitvector.
  if (a.GetExpWidth() != b.GetExpWidth() ||
      a.GetSigWidth() != b.GetSigWidth())
  {
    FatalError("array-equality: equality between arrays requires "
               "identical element sorts",
               a);
  }

  if (a == b)
    return bm->ASTTrue;

  // A chain of writes equated with its own base needs no abstraction
  // at all; solve it by rewriting.
  {
    const ASTNode solved = solveWriteChain(a, b);
    if (!solved.IsNull())
      return solved;
  }

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

  // The witness disequality. Bitvector cells differ exactly when their
  // bits differ. Packed floating-point cells denote the one NaN value
  // under every NaN bit pattern (SMT-LIB = on floats is identity of
  // values, and symfpu carries no payload), so differing bits witness
  // a real difference only when the cells are not both NaN -- without
  // that qualification a false equality between float arrays could be
  // "witnessed" by two NaN payloads of pointwise-equal arrays.
  ASTNode differ =
      hf->CreateNode(NOT, hf->CreateNode(EQ, r.nameL, r.nameR));
  const unsigned eb = left.GetExpWidth();
  if (eb != 0)
  {
    const unsigned sb = left.GetSigWidth();
    differ = hf->CreateNode(
        AND, differ,
        hf->CreateNode(NOT,
                       hf->CreateNode(AND, isPackedNaN(hf, r.nameL, eb, sb),
                                      isPackedNaN(hf, r.nameR, eb, sb))));
  }
  r.witnessClause = hf->CreateNode(OR, r.proxy, differ);

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

void ExtensionalityContext::beginSolve()
{
  coneIsFrozen = false;
  coneArrays.clear();
  coneWrites.clear();
  coneWriteParents.clear();
  eqEdges.clear();
  eqAdjacency.clear();
  witnessObls.clear();
  scalarNames.clear();
  nameToTermMap.clear();
  lemmaOnlySymbols.clear();
  graph = ExtGraph();
  graphBound = false;
  pendingLemmaValid = false;
  eqLitCache.clear();
  lastObserved.clear();
  for (size_t i = 0; i < records.size(); i++)
  {
    records[i].canonicalLeft = ASTNode();
    records[i].canonicalRight = ASTNode();
  }
}

ASTNode ExtensionalityContext::conjoinRecordConstraints(const ASTNode& root)
{
  if (records.empty())
    return root;
  ASTVec conjuncts;
  conjuncts.push_back(root);
  for (size_t i = 0; i < records.size(); i++)
  {
    conjuncts.push_back(records[i].anchorL);
    conjuncts.push_back(records[i].anchorR);
    conjuncts.push_back(records[i].witnessClause);
  }
  return bm->defaultNodeFactory->CreateNode(AND, conjuncts);
}

// Recover each record's canonical operands from its anchor equations
// in the current formula. The anchors were conjoined before STP's
// simplifications ran, so they were rewritten by exactly the passes
// that rewrote the rest of the formula; the array operand under each
// witness read is therefore the current form of the recorded operand.
// Fails loudly when an anchor is missing or malformed -- a protected
// definition was eliminated, which the substitution guards should have
// prevented.
void ExtensionalityContext::locateCanonicalOperands(const ASTNode& root)
{
  // name symbol -> the anchored right-hand side: the witness read, or
  // the if-then-else the simplifier pushed it into.
  std::map<ASTNode, ASTNode> anchorRhs;
  ASTNodeSet visited;
  collectDag(root, visited);
  for (ASTNodeSet::const_iterator it = visited.begin(); it != visited.end();
       ++it)
  {
    const ASTNode& n = *it;
    if (n.GetKind() != EQ || n.Degree() != 2)
      continue;
    for (int side = 0; side < 2; side++)
    {
      const ASTNode& s = n[side];
      const ASTNode& other = n[1 - side];
      if (s.GetKind() == SYMBOL && isProtected(s) &&
          (other.GetKind() == READ || other.GetKind() == ITE))
        anchorRhs[s] = other;
    }
  }

  for (size_t i = 0; i < records.size(); i++)
  {
    Record& r = records[i];
    std::map<ASTNode, ASTNode>::const_iterator lit = anchorRhs.find(r.nameL);
    std::map<ASTNode, ASTNode>::const_iterator rit = anchorRhs.find(r.nameR);
    if (lit == anchorRhs.end() || rit == anchorRhs.end())
      FatalError("array-equality: a witness-read defining equation was "
                 "lost during preprocessing, so the current form of an "
                 "equality operand cannot be recovered",
                 r.proxy);
    r.canonicalLeft =
        recoverAnchoredOperand(lit->second, r.lambda, r.proxy,
                               bm->hashingNodeFactory, iteReplacements);
    r.canonicalRight =
        recoverAnchoredOperand(rit->second, r.lambda, r.proxy,
                               bm->hashingNodeFactory, iteReplacements);
  }
}

// Compute the cone: the set of array terms the abstracted equalities
// can constrain. Seed with every record's canonical operands, close
// downward through write bases and if-then-else branches, and upward
// through the writes and if-then-elses stacked on cone arrays in the
// formula (upward closure is what makes extensional reasoning
// complete; compare rule U in section 7.3 of the paper).
void ExtensionalityContext::computeProvisionalCone(
    const ASTNode& root, std::set<ASTNode>& cone,
    std::map<ASTNode, std::vector<ASTNode>>& parents,
    std::vector<ASTNode>& coneITEs)
{
  cone.clear();
  parents.clear();
  coneITEs.clear();

  ASTNodeSet visited;
  collectDag(root, visited);
  for (size_t i = 0; i < records.size(); i++)
  {
    collectDag(records[i].canonicalLeft, visited);
    collectDag(records[i].canonicalRight, visited);
  }

  // parent adjacency over every array node in sight
  std::map<ASTNode, std::vector<ASTNode>> upEdges; // child array -> parents
  for (ASTNodeSet::const_iterator it = visited.begin(); it != visited.end();
       ++it)
  {
    const ASTNode& n = *it;
    if (n.GetKind() == WRITE)
      upEdges[n[0]].push_back(n);
    else if (n.GetKind() == ITE && isArrayType(n))
    {
      upEdges[n[1]].push_back(n);
      upEdges[n[2]].push_back(n);
    }
  }

  std::vector<ASTNode> todo;
  for (size_t i = 0; i < records.size(); i++)
  {
    todo.push_back(records[i].canonicalLeft);
    todo.push_back(records[i].canonicalRight);
  }

  while (!todo.empty())
  {
    ASTNode n = todo.back();
    todo.pop_back();
    if (!cone.insert(n).second)
      continue;
    // downward
    if (n.GetKind() == WRITE)
      todo.push_back(n[0]);
    else if (n.GetKind() == ITE && isArrayType(n))
    {
      todo.push_back(n[1]);
      todo.push_back(n[2]);
    }
    // upward through parents in the prepared formula
    std::map<ASTNode, std::vector<ASTNode>>::const_iterator pit =
        upEdges.find(n);
    if (pit != upEdges.end())
      for (size_t i = 0; i < pit->second.size(); i++)
        todo.push_back(pit->second[i]);
  }

  for (std::set<ASTNode>::const_iterator it = cone.begin(); it != cone.end();
       ++it)
  {
    if (it->GetKind() == ITE && isArrayType(*it))
      coneITEs.push_back(*it);
    if (it->GetKind() == WRITE)
      parents[(*it)[0]].push_back(*it);
  }
  for (std::map<ASTNode, std::vector<ASTNode>>::iterator it = parents.begin();
       it != parents.end(); ++it)
    std::sort(it->second.begin(), it->second.end(), nodeNumLess);
  std::sort(coneITEs.begin(), coneITEs.end(), nodeNumLess);
}

// Create or reuse a scalar name for a checker-visible term and queue
// its defining constraint name = term. The defining equation is
// conjoined before bit-blasting, so the name has SAT variables and a
// lemma mentioning the term can be encoded over them.
ASTNode ExtensionalityContext::freshName(const ASTNode& term,
                                         ASTVec& namingConstraints)
{
  if (term.isConstant())
    return plainConst(bm, term);
  std::map<ASTNode, ASTNode>::const_iterator it = scalarNames.find(term);
  if (it != scalarNames.end())
    return it->second;
  ASTNode name = bm->CreateFreshVariable(0, term.GetValueWidth(), "ext_name");
  protectedSymbols.insert(name);
  namingConstraints.push_back(
      bm->defaultNodeFactory->CreateNode(EQ, name, term));
  scalarNames[term] = name;
  nameToTermMap[name] = term;
  return name;
}

// Final preparation before STP's main array transformation:
// recover canonical operands, compute the cone, eliminate array-valued
// if-then-else inside it to a fixed point (paper section 4.1), then
// freeze the cone, inventory its writes as accesses (section 11.4),
// and give every compound write index/value a scalar name.
ASTNode ExtensionalityContext::prepare(const ASTNode& root_)
{
  assert(active());
  ASTNode root = root_;
  ASTVec extraConstraints;

  std::set<ASTNode> cone;
  std::map<ASTNode, std::vector<ASTNode>> parents;
  std::vector<ASTNode> coneITEs;

  // Operand recovery and if-then-else elimination interleave to a
  // fixed point: eliminating an ITE creates fresh guarded equalities,
  // whose operands may expose further ITEs.
  while (true)
  {
    locateCanonicalOperands(root);
    computeProvisionalCone(root, cone, parents, coneITEs);
    if (coneITEs.empty())
      break;

    const size_t recordsBefore = records.size();
    ASTNodeMap iteMap;
    ASTVec newConstraints;
    for (size_t i = 0; i < coneITEs.size(); i++)
    {
      const ASTNode& t = coneITEs[i];
      // Nested if-then-elses are in coneITEs too: every one gets its
      // replacement in this same round, and the substitution below
      // rewrites the inner occurrences inside the outer ones' guarded
      // equalities. The enclosing loop iterates only because the
      // fresh guarded records may expose further if-then-elses when
      // their operands are next recovered.
      const ASTNode cond = t[0];
      const ASTNode thn = t[1];
      const ASTNode els = t[2];
      // Reuse the persistent replacement for this ITE node if an
      // earlier solve already created one; the registry key dedup then
      // also reuses its two equality records, so repeated solves add
      // no records and no fresh symbols.
      ASTNode d;
      std::map<ASTNode, ASTNode>::const_iterator cached =
          iteReplacements.find(t);
      if (cached != iteReplacements.end())
      {
        d = cached->second;
      }
      else
      {
        d = bm->CreateFreshVariable(t.GetIndexWidth(), t.GetValueWidth(),
                                    "ext_ite");
        // A replacement for a float-element array is itself a
        // float-element array: the guarded equalities minted below
        // need the element format for their witness clauses.
        if (t.GetExpWidth() != 0)
        {
          d.SetExpWidth(t.GetExpWidth());
          d.SetSigWidth(t.GetSigWidth());
        }
        iteReplacements[t] = d;
        possibleConeSymbols.insert(d);
      }
      // Guarded equality proxies through the same early-minting funnel
      // (section 4.1): c -> d = thn ; not(c) -> d = els. The
      // equalities go through the ordinary abstraction, and the
      // guards are
      // conjoined into every solve's root, cached replacement or not,
      // so a record is never active without its defining implication.
      ASTNode eqThen = bm->defaultNodeFactory->CreateNode(EQ, d, thn);
      ASTNode eqElse = bm->defaultNodeFactory->CreateNode(EQ, d, els);
      newConstraints.push_back(bm->defaultNodeFactory->CreateNode(
          OR, bm->defaultNodeFactory->CreateNode(NOT, cond), eqThen));
      newConstraints.push_back(
          bm->defaultNodeFactory->CreateNode(OR, cond, eqElse));
      iteMap[t] = d;
    }

    // Records minted for the guarded equalities need their witness
    // bundles in the
    // formula too; no further simplification passes run, so conjoining
    // them here is equivalent to the start-of-solve conjunction.
    for (size_t i = recordsBefore; i < records.size(); i++)
    {
      newConstraints.push_back(records[i].anchorL);
      newConstraints.push_back(records[i].anchorR);
      newConstraints.push_back(records[i].witnessClause);
    }

    ASTNodeMap cache;
    root = SubstitutionMap::replace(root, iteMap, cache,
                                    bm->defaultNodeFactory);
    for (size_t i = 0; i < newConstraints.size(); i++)
    {
      ASTNodeMap cache2;
      newConstraints[i] = SubstitutionMap::replace(newConstraints[i], iteMap,
                                                   cache2,
                                                   bm->defaultNodeFactory);
    }
    root = bm->defaultNodeFactory->CreateNode(
        AND, root, ASTVec(newConstraints.begin(), newConstraints.end()));
  }

  // No array-valued if-then-else may remain inside the cone.
  assert(coneITEs.empty());

  // Freeze the cone; it must not change for the rest of the solve.
  coneArrays = cone;
  coneWriteParents = parents;

  // Inventory the cone's writes as accesses (a write is treated as a
  // read of its own index yielding the written value, paper section
  // 11.4), and give their indexes and values scalar names: writes occur
  // only inside equality operands and witness reads, so their scalar
  // children would otherwise never reach the bit-blaster.
  std::vector<ASTNode> writeNodes;
  for (std::set<ASTNode>::const_iterator it = cone.begin(); it != cone.end();
       ++it)
    if (it->GetKind() == WRITE)
      writeNodes.push_back(*it);
  std::sort(writeNodes.begin(), writeNodes.end(), nodeNumLess);

  for (size_t i = 0; i < writeNodes.size(); i++)
  {
    const ASTNode& w = writeNodes[i];
    ExtWriteNode info;
    info.write = w;
    info.base = w[0];
    info.indexTerm = w[1];
    info.indexName = freshName(w[1], extraConstraints);
    coneWrites[w] = info;
    // write value names are needed when the access list is built
    freshName(w[2], extraConstraints);
  }

  // Equality edges over canonical operands + witness obligations.
  for (size_t i = 0; i < records.size(); i++)
  {
    const Record& r = records[i];
    ExtEqEdge e;
    e.record = r.id;
    e.left = r.canonicalLeft;
    e.right = r.canonicalRight;
    e.proxy = r.proxy;
    eqEdges.push_back(e);

    ExtWitness w;
    w.record = r.id;
    w.proxy = r.proxy;
    w.index = r.lambda;
    w.leftValue = r.nameL;
    w.rightValue = r.nameR;
    witnessObls.push_back(w);
  }

  // adjacency, sorted by (record, other endpoint) per source
  {
    std::map<ASTNode, std::vector<std::pair<std::pair<size_t, unsigned>,
                                            size_t>>> adj;
    for (size_t i = 0; i < eqEdges.size(); i++)
    {
      const ExtEqEdge& e = eqEdges[i];
      adj[e.left].push_back(std::make_pair(
          std::make_pair(e.record, e.right.GetNodeNum()), i));
      if (!(e.left == e.right))
        adj[e.right].push_back(std::make_pair(
            std::make_pair(e.record, e.left.GetNodeNum()), i));
    }
    for (std::map<ASTNode,
                  std::vector<std::pair<std::pair<size_t, unsigned>,
                                        size_t>>>::iterator it = adj.begin();
         it != adj.end(); ++it)
    {
      std::sort(it->second.begin(), it->second.end());
      std::vector<size_t>& out = eqAdjacency[it->first];
      for (size_t i = 0; i < it->second.size(); i++)
        out.push_back(it->second[i].second);
    }
  }

  coneIsFrozen = true;

  if (extraConstraints.empty())
    return root;
  return bm->defaultNodeFactory->CreateNode(AND, root, extraConstraints);
}

// After the main ArrayTransformer pass: the read inventory (ordinary
// cone reads plus witness reads) now carries its abstraction and index
// symbols; bind everything into the immutable checker graph.
void ExtensionalityContext::bindAfterTransform(ArrayTransformer* at)
{
  assert(coneIsFrozen);

  graph = ExtGraph();

  // reads, deterministically ordered by (array, index) node numbers
  struct ReadRow
  {
    ASTNode array;
    ASTNode index;
    ASTNode symbol;
    ASTNode indexSymbol;
    bool operator<(const ReadRow& o) const
    {
      if (array.GetNodeNum() != o.array.GetNodeNum())
        return array.GetNodeNum() < o.array.GetNodeNum();
      return index.GetNodeNum() < o.index.GetNodeNum();
    }
  };
  std::vector<ReadRow> reads;
  for (ArrayTransformer::ArrType::const_iterator it =
           at->arrayToIndexToRead.begin();
       it != at->arrayToIndexToRead.end(); ++it)
  {
    if (!inCone(it->first))
      continue;
    for (std::map<ASTNode, ArrayTransformer::ArrayRead>::const_iterator it2 =
             it->second.begin();
         it2 != it->second.end(); ++it2)
    {
      ReadRow row;
      row.array = it->first;
      row.index = it2->first;
      row.symbol = it2->second.symbol;
      row.indexSymbol = it2->second.index_symbol;
      reads.push_back(row);
    }
  }
  std::sort(reads.begin(), reads.end());

  for (size_t i = 0; i < reads.size(); i++)
  {
    const ReadRow& row = reads[i];
    ExtAccess a;
    a.id = graph.accesses.size();
    a.isWrite = false;
    a.site = row.array;
    a.indexTerm = row.index;
    NodeFactory* hf = bm->hashingNodeFactory;
    a.valueTerm = hf->CreateTerm(READ, row.array.GetValueWidth(), row.array,
                                 row.index);
    a.indexName = row.indexSymbol.IsNull() ? row.index : row.indexSymbol;
    a.valueName = row.symbol;
    if (!(a.indexName.GetKind() == SYMBOL || a.indexName.isConstant()))
      FatalError("array-equality: a read index inside the cone has no "
                 "bit-blasted scalar name to encode lemmas over",
                 row.index);
    // A cone read's semantics live entirely in refinement lemmas, so
    // its abstraction variable and index may legally never reach the
    // bit-blasted formula (the read's only occurrence can sit inside
    // another abstracted term); the translator allocates fresh SAT
    // variables for whichever of these it never saw.
    lemmaOnlySymbols.insert(a.valueName);
    if (a.indexName.GetKind() == SYMBOL)
      lemmaOnlySymbols.insert(a.indexName);
    graph.accesses.push_back(a);
  }

  // writes, deterministically ordered by node number
  std::vector<ASTNode> writeNodes;
  for (std::map<ASTNode, ExtWriteNode>::const_iterator it = coneWrites.begin();
       it != coneWrites.end(); ++it)
    writeNodes.push_back(it->first);
  std::sort(writeNodes.begin(), writeNodes.end(), nodeNumLess);
  for (size_t i = 0; i < writeNodes.size(); i++)
  {
    const ExtWriteNode& info = coneWrites[writeNodes[i]];
    ExtAccess a;
    a.id = graph.accesses.size();
    a.isWrite = true;
    a.site = info.write;
    a.indexTerm = info.indexTerm;
    a.valueTerm = info.write[2];
    a.indexName = info.indexName;
    std::map<ASTNode, ASTNode>::const_iterator nit =
        scalarNames.find(info.write[2]);
    a.valueName = info.write[2].isConstant()
                      ? info.write[2]
                      : (nit != scalarNames.end() ? nit->second : ASTNode());
    if (a.valueName.IsNull())
      FatalError("array-equality: a write value inside the cone has no "
                 "bit-blasted scalar name to encode lemmas over",
                 info.write);
    graph.accesses.push_back(a);
  }

  graph.writes = coneWrites;
  graph.writeParents = coneWriteParents;
  graph.eqEdges = eqEdges;
  graph.eqAdjacency = eqAdjacency;
  graph.witnesses = witnessObls;
  graphBound = true;
}

namespace
{
// The candidate assignment sigma, read out of STP's materialized
// counterexample.
class CEModelView : public ExtModelView
{
  AbsRefine_CounterExample* ce;
  STPMgr* bm;

public:
  CEModelView(AbsRefine_CounterExample* ce_, STPMgr* bm_)
      : ce(ce_), bm(bm_)
  {
  }

  virtual ASTNode bvValue(const ASTNode& term)
  {
    ASTNode v = ce->ModelValueOfTerm(term);
    if (v.IsNull() || !v.isConstant())
      FatalError("array-equality: the candidate assignment has no "
                 "concrete value for a term the consistency checker "
                 "needs",
                 term);
    // Substitution entries can hand a float-element symbol back as a
    // float constant; the checker compares constants by node identity,
    // so give it the plain twin.
    return plainConst(bm, v);
  }

  virtual bool boolValue(const ASTNode& term)
  {
    ASTNode v = ce->ModelValueOfFormula(term);
    if (v.IsNull() || !(v.GetKind() == TRUE || v.GetKind() == FALSE))
      FatalError("array-equality: the candidate assignment has no "
                 "Boolean value for a term the consistency checker "
                 "needs",
                 term);
    return v.GetKind() == TRUE;
  }
};
} // namespace

ExtensionalityContext::CertificationAction
ExtensionalityContext::decideCertification(bool ordinaryResult,
                                           bool registryNonempty,
                                           CandidateOutcome ext)
{
  if (!registryNonempty)
  {
    if (!(ext == EXT_SKIPPED || ext == EXT_CONSISTENT))
      return INTERNAL_ERROR;
    return ordinaryResult ? RETURN_SAT : RUN_HOST_REFINEMENT;
  }
  if (ext == EXT_CONFLICT)
    return ADD_EXT_LEMMA;
  if (ext == EXT_WITNESS_ERROR)
    return INTERNAL_ERROR;
  if (ext != EXT_CONSISTENT)
    return INTERNAL_ERROR;
  return ordinaryResult ? RETURN_SAT : RUN_HOST_REFINEMENT;
}

ExtensionalityContext::CandidateOutcome
ExtensionalityContext::checkCandidate(AbsRefine_CounterExample* ce)
{
  assert(graphBound);
  pendingLemmaValid = false;
  CEModelView view(ce, bm);
  ExtCheckResult res = ExtChecker::check(graph, view, false);
  switch (res.status)
  {
    case ExtCheckResult::CONSISTENT:
      lastObserved = res.observed;
      return EXT_CONSISTENT;
    case ExtCheckResult::CONFLICT:
      pendingLemma = res.conflict;
      pendingLemmaValid = true;
      return EXT_CONFLICT;
    case ExtCheckResult::WITNESS_VIOLATION:
    default:
      return EXT_WITNESS_ERROR;
  }
}

// Encode the pending lemma into the persistent incremental SAT solver
// as the clause
//   NOT p1 OR ... OR NOT pk OR conclusion
// over reified equality literals of already-encoded scalar symbols.
// This is the abstraction alpha of the theory lemma (paper section 8);
// adding it as clauses over the existing CNF is what makes each
// refinement iteration incremental -- no new word-level formula is
// ever handed back to the bit-blaster.
// A lemma leaf is legal only as a constant or as a SYMBOL with a
// stable, completely encoded SAT-variable vector. Anything else is an
// internal error, never a reason to allocate fresh SAT variables in
// the middle of refinement: a freshly invented variable would carry no
// connection to the term the candidate assignment was checked against,
// so the resulting clause could fail to rule the candidate out.
const char*
ExtensionalityContext::checkPreencodedBV(const ASTNode& n,
                                         const ToSATBase::ASTNodeToSATVar& satVar)
{
  if (n.isConstant())
    return NULL;
  if (n.GetKind() != SYMBOL)
    return "array-equality: lemma leaf is neither a constant nor a "
           "variable";
  ToSATBase::ASTNodeToSATVar::const_iterator it = satVar.find(n);
  if (it == satVar.end())
    return "array-equality: lemma leaf was never bit-blasted (it has no "
           "SAT-variable vector)";
  if (it->second.size() != n.GetValueWidth())
    return "array-equality: lemma leaf's SAT-variable vector has the "
           "wrong width";
  for (size_t i = 0; i < it->second.size(); i++)
    if (it->second[i] == ~((unsigned)0))
      return "array-equality: lemma leaf has an unencoded SAT-variable "
             "bit";
  return NULL;
}

void ExtensionalityContext::encodePendingLemma(SATSolver& solver,
                                               ToSATBase* tosat)
{
  assert(pendingLemmaValid);
  ToSATBase::ASTNodeToSATVar& satVar = tosat->SATVar_to_SymbolIndexMap();

  // Validate every bit-vector leaf of the lemma before any SAT
  // mutation, so a violation is a localized internal error and
  // getEquals below can never fall into its fresh-variable fallback.
  {
    std::vector<ASTNode> leaves;
    for (size_t i = 0; i < pendingLemma.abstractPremise.size(); i++)
    {
      const ExtLemmaAtom& atom = pendingLemma.abstractPremise[i];
      if (atom.op == ExtLemmaAtom::BV_EQ || atom.op == ExtLemmaAtom::BV_NE)
      {
        leaves.push_back(atom.a);
        leaves.push_back(atom.b);
      }
    }
    leaves.push_back(pendingLemma.abstractConclusionA);
    leaves.push_back(pendingLemma.abstractConclusionB);
    for (size_t i = 0; i < leaves.size(); i++)
    {
      const char* reason = checkPreencodedBV(leaves[i], satVar);
      if (reason != NULL)
        FatalError(reason, leaves[i]);
    }
  }

  SATSolver::vec_literals clause;

  // Returns -1 for an atom decided by constants (the caller drops the
  // literal; the lemma self-check already fixed its polarity), else the
  // reified equality variable q with q <-> (a = b), full equivalence in
  // both directions.
  struct EqLit
  {
    ExtensionalityContext* self;
    SATSolver& solver;
    ToSATBase::ASTNodeToSATVar& satVar;
    EqLit(ExtensionalityContext* s, SATSolver& sol,
          ToSATBase::ASTNodeToSATVar& sv)
        : self(s), solver(sol), satVar(sv)
    {
    }
    int operator()(const ASTNode& a, const ASTNode& b)
    {
      if (a.isConstant() && b.isConstant())
        return -1;
      const unsigned na = a.GetNodeNum(), nb = b.GetNodeNum();
      const std::pair<unsigned, unsigned> key(std::min(na, nb),
                                              std::max(na, nb));
      std::map<std::pair<unsigned, unsigned>, int>::const_iterator it =
          self->eqLitCache.find(key);
      if (it != self->eqLitCache.end())
        return it->second;

      // An atom the simplifier can decide from the defining terms
      // needs no circuit: each name equals its term through the
      // anchoring equations, and the lemma self-check verified the
      // atom's polarity in the candidate, so a structurally decided
      // atom sits on its satisfied side and its literal is redundant
      // -- the same argument as the constant/constant case above.
      // Write indices that are offsets from a shared pointer are the
      // common win: the simplifying factory cancels the shared operand
      // and decides the equality, sparing the SAT solver a 32-bit
      // arithmetic case split per lemma.
      {
        const std::map<ASTNode, ASTNode>& n2t = self->nameToTermMap;
        std::map<ASTNode, ASTNode>::const_iterator ta = n2t.find(a);
        std::map<ASTNode, ASTNode>::const_iterator tb = n2t.find(b);
        const ASTNode& termA = (ta == n2t.end()) ? a : ta->second;
        const ASTNode& termB = (tb == n2t.end()) ? b : tb->second;
        const ASTNode folded =
            self->bm->defaultNodeFactory->CreateNode(EQ, termA, termB);
        if (folded.GetKind() == TRUE || folded.GetKind() == FALSE)
        {
          self->lemmaAtomsFolded++;
          self->eqLitCache[key] = -1;
          return -1;
        }
      }

      const int q = getEquals(solver, a, b, satVar, BOTH);
      self->eqLitCache[key] = q;
      return q;
    }
  } eqLit(this, solver, satVar);

  for (size_t i = 0; i < pendingLemma.abstractPremise.size(); i++)
  {
    const ExtLemmaAtom& atom = pendingLemma.abstractPremise[i];
    if (atom.op == ExtLemmaAtom::BV_EQ || atom.op == ExtLemmaAtom::BV_NE)
    {
      const int q = eqLit(atom.a, atom.b);
      if (q < 0)
        continue; // constant-decided premise, necessarily true; drop
      // premise literal appears negated in the final clause
      clause.push(SATSolver::mkLit(q, atom.op == ExtLemmaAtom::BV_EQ));
    }
    else
    {
      assert(atom.op == ExtLemmaAtom::BOOL_LIT);
      ToSATBase::ASTNodeToSATVar::const_iterator vit =
          satVar.find(atom.boolTerm);
      if (vit == satVar.end() || vit->second.size() != 1 ||
          vit->second[0] == ~((unsigned)0))
        FatalError("array-equality: an equality abstraction variable "
                   "was never bit-blasted, so the lemma cannot be "
                   "encoded",
                   atom.boolTerm);
      clause.push(SATSolver::mkLit(vit->second[0], true));
    }
  }

  {
    const int q =
        eqLit(pendingLemma.abstractConclusionA, pendingLemma.abstractConclusionB);
    if (q >= 0)
      clause.push(SATSolver::mkLit(q, false));
    // A constant-decided conclusion is necessarily false (the lemma
    // self-check verified it); the clause then consists of the negated
    // premises alone.
  }

  if (clause.size() == 0)
    FatalError("array-equality: refinement produced an empty clause "
               "(the candidate should have been unsatisfiable already)");

  solver.addClause(clause);
  lemmasEmitted++;
  pendingLemmaValid = false;
}

// Publish the conflict-free observed values of every cone array
// (symbols, writes, and the fresh arrays standing for if-then-else
// alike) into the counterexample map, so model evaluation, the model
// APIs, and the printers see the array contents certified by the
// consistency check. Indices with no observation default to zero at
// lookup/print time.
void ExtensionalityContext::publishObservations(AbsRefine_CounterExample* ce)
{
  for (std::map<ASTNode,
                std::vector<std::pair<ASTNode, ASTNode>>>::const_iterator it =
           lastObserved.begin();
       it != lastObserved.end(); ++it)
  {
    const ASTNode& array = it->first;
    NodeFactory* hf = bm->hashingNodeFactory;
    for (size_t i = 0; i < it->second.size(); i++)
    {
      const ASTNode key = hf->CreateTerm(READ, array.GetValueWidth(), array,
                                         it->second[i].first);
      ce->InsertIntoCounterExampleMap(key, it->second[i].second);
    }
  }
}

} // namespace stp
