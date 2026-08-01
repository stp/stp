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
#include <cstdio>
#include <cstdlib>
#include <functional>

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

// Postorder DAG collection of every node beneath (and including) n.
void collectDag(const ASTNode& n, ASTNodeSet& visited)
{
  if (!visited.insert(n).second)
    return;
  for (unsigned k = 0; k < n.Degree(); k++)
    collectDag(n[k], visited);
}

// The current form of an equality operand, read back from its witness
// anchor. The anchor was recorded as name = read(operand, lambda), and
// stays that shape: the only rewrite that could break it is the
// simplifier distributing the read over an array if-then-else, which it
// does not do while the procedure is active -- the checker reasons
// about those directly and needs the read left where it stands.
// Anything else means an anchor was rewritten beyond recognition:
// refuse loudly rather than guess.
ASTNode recoverAnchoredOperand(const ASTNode& rhs, const ASTNode& lambda,
                               const ASTNode& proxy)
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
    FatalError("array-equality: a witness read was distributed over an "
               "array if-then-else, although that is suppressed while the "
               "procedure is active",
               proxy);
  FatalError("array-equality: a witness-read defining equation was "
             "rewritten into a shape operand recovery does not "
             "recognize",
             proxy);
  return rhs; // unreachable; FatalError does not return
}

} // namespace

ExtensionalityContext::ExtensionalityContext(STPMgr* bm_)
    : lemmasEmitted(0), lemmaAtomsFolded(0), bm(bm_), registrySealed(false),
      arrayGraphIsFrozen(false), graphBound(false), pendingLemmaValid(false)
{
}

bool ExtensionalityContext::enabled() const
{
  return bm->UserFlags.enable_array_equality;
}

void ExtensionalityContext::collectAnticipatedArraySymbols(const ASTNode& n)
{
  ASTNodeSet visited;
  collectDag(n, visited);
  for (ASTNodeSet::const_iterator it = visited.begin(); it != visited.end();
       ++it)
    if (it->GetKind() == SYMBOL && isArrayType(*it))
      anticipatedArraySymbols.insert(*it);
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

// The equality arm of the paper's formula abstraction (section 5), applied by
// solve-boundary lowering: return a fresh Boolean abstraction variable and
// cache the pair's witness bundle. Reflexive
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

  if (registrySealed)
    FatalError("array-equality: an array equality was built during a "
               "solve, after the registry's constraints were taken; its "
               "witness bundle could not reach the formula",
               left);

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
  keyToRecord[key] = r.id;
  proxyToRecord[r.proxy] = r.id;
  records.push_back(r);
  return records.back().proxy;
}

ASTNode ExtensionalityContext::lowerArrayEqualities(const ASTNode& root)
{
  if (!enabled())
    FatalError("array-equality: opaque equality reached lowering while the "
               "decision procedure is disabled");

  ASTNodeMap cache;
  NodeFactory* hf = bm->hashingNodeFactory;
  std::function<ASTNode(const ASTNode&)> lower = [&](const ASTNode& n) {
    ASTNodeMap::const_iterator found = cache.find(n);
    if (found != cache.end())
      return found->second;

    const ASTChildren children = n.GetChildren();
    ASTVec loweredChildren;
    bool changed = false;
    loweredChildren.reserve(children.size());
    for (const ASTNode& originalChild : children)
    {
      const ASTNode child = lower(originalChild);
      loweredChildren.push_back(child);
      changed = changed || child != originalChild;
    }

    ASTNode result;
    if (n.GetKind() == ARRAY_EQ)
    {
      assert(loweredChildren.size() == 2);
      result = makeEquality(loweredChildren[0], loweredChildren[1]);
      currentLowerings[n] = result;
    }
    else if (!changed)
    {
      result = n;
    }
    else if (n.GetValueWidth() == 0)
    {
      result = hf->CreateNode(n.GetKind(), loweredChildren);
    }
    else if (n.GetIndexWidth() > 0)
    {
      result = hf->CreateArrayTerm(n.GetKind(), n.GetIndexWidth(),
                                   n.GetValueWidth(), loweredChildren);
    }
    else
    {
      result = hf->CreateTerm(n.GetKind(), n.GetValueWidth(), loweredChildren);
    }

    cache.insert(std::make_pair(n, result));
    return result;
  };

  const ASTNode lowered = lower(root);

  // ARRAY_EQ is legal only in the user-facing AST. Ordinary simplification,
  // array transformation and bit-blasting intentionally have no case for it.
  ASTNodeSet nodes;
  collectDag(lowered, nodes);
  for (ASTNodeSet::const_iterator it = nodes.begin(); it != nodes.end(); ++it)
    if (it->GetKind() == ARRAY_EQ)
      FatalError("array-equality: query lowering left an opaque equality", *it);

  activateReachableRecords(lowered);

  return lowered;
}

bool ExtensionalityContext::getCurrentLowering(const ASTNode& opaque,
                                               ASTNode& lowered) const
{
  const ASTNodeMap::const_iterator it = currentLowerings.find(opaque);
  if (it == currentLowerings.end())
    return false;
  lowered = it->second;
  return true;
}

void ExtensionalityContext::activateReachableRecords(
    const ASTNode& loweredRoot)
{
  std::set<size_t> activeIds;
  ASTNodeSet visited;
  ASTVec pending(1, loweredRoot);
  while (!pending.empty())
  {
    const ASTNode node = pending.back();
    pending.pop_back();
    if (!visited.insert(node).second)
      continue;

    const std::map<ASTNode, size_t>::const_iterator proxy =
        proxyToRecord.find(node);
    if (proxy != proxyToRecord.end() && activeIds.insert(proxy->second).second)
    {
      const Record& r = records[proxy->second];
      // An outer equality can hide an inner equality proxy in an array-ITE
      // condition or another operand subterm. Follow cached operands so that
      // activation is the transitive closure, not merely the proxies still
      // visible at the Boolean root.
      pending.push_back(r.constructionLeft);
      pending.push_back(r.constructionRight);
    }

    for (unsigned i = 0; i < node.Degree(); ++i)
      pending.push_back(node[i]);
  }

  activeRecordIds.assign(activeIds.begin(), activeIds.end());
  anticipatedArraySymbols.clear();
  for (size_t i = 0; i < activeRecordIds.size(); ++i)
  {
    const Record& r = records[activeRecordIds[i]];
    collectAnticipatedArraySymbols(r.constructionLeft);
    collectAnticipatedArraySymbols(r.constructionRight);
  }
}

void ExtensionalityContext::beginSolve()
{
  registrySealed = false;
  records.clear();
  keyToRecord.clear();
  proxyToRecord.clear();
  activeRecordIds.clear();
  currentLowerings.clear();
  protectedSymbols.clear();
  anticipatedArraySymbols.clear();
  arrayGraphIsFrozen = false;
  ownedArrays.clear();
  ownedWrites.clear();
  ownedWriteParents.clear();
  ownedItes.clear();
  ownedIteParents.clear();
  eqEdges.clear();
  eqAdjacency.clear();
  witnessObls.clear();
  // Scalar and condition names are rebuilt for each preprocessed formula.
  scalarNames.clear();
  nameToTermMap.clear();
  lemmaOnlySymbols.clear();
  graph = ExtGraph();
  graphBound = false;
  pendingLemmaValid = false;
  pendingLemmas.clear();
  eqLitCache.clear();
  lastObserved.clear();
}

ASTNode ExtensionalityContext::conjoinRecordConstraints(const ASTNode& root)
{
  if (activeRecordIds.empty())
    return root;
  ASTVec conjuncts;
  conjuncts.push_back(root);
  for (size_t i = 0; i < activeRecordIds.size(); i++)
  {
    const Record& r = records[activeRecordIds[i]];
    conjuncts.push_back(r.anchorL);
    conjuncts.push_back(r.anchorR);
    conjuncts.push_back(r.witnessClause);
  }
  ASTNode out = bm->defaultNodeFactory->CreateNode(AND, conjuncts);

  // Anticipate the complete owned graph before any pass can act on the
  // answer. Once an equality is active, the checker owns every array
  // read in the solve: congruence connects otherwise unrelated arrays
  // through shared scalar index expressions, so an equality-seeded
  // subgraph is not a closed theory boundary.
  //
  // anticipatedArraySymbols decides which reads are protected from the
  // read-equals-constant substitution. It must come from the whole root,
  // not just equality operands: an unrelated array or an array-ITE branch
  // is owned too.
  // This is the one point where the whole expanded formula and the
  // active registry are known and no simplification has run, so it is
  // also the point at which read-deleting substitutions can still be
  // prevented.
  collectAnticipatedArraySymbols(out);

  // Everything the decision procedure needs is now in this solve's
  // formula; anything minted after this point could not be.
  registrySealed = true;
  return out;
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
  // Only the witness names are ever looked up below, so only they are
  // collected: a protected lambda or proxy turning up in an equation of
  // the same shape is none of this function's business.
  std::set<ASTNode> witnessNames;
  for (size_t i = 0; i < activeRecordIds.size(); i++)
  {
    const Record& r = records[activeRecordIds[i]];
    witnessNames.insert(r.nameL);
    witnessNames.insert(r.nameR);
  }

  // name symbol -> the anchored right-hand side: the witness read, or
  // the if-then-else the simplifier pushed it into.
  //
  // Exactly one equation of this shape may exist per name. The names
  // are fresh, so no user term mentions them; they occur only in their
  // own anchor and in the witness clause, whose equality has the other
  // NAME on its far side and so does not match here; substitution
  // cannot move them (SubstitutionMap::extensionalityProtected refuses
  // any pair with a protected symbol on either side) and unconstrained
  // removal cannot delete them (MutableASTNode's untouchable set); and
  // because nodes are immutable and hash-consed, a rewritten anchor's
  // predecessor is no longer reachable from the root, so the walk
  // cannot see both.
  //
  // That is a property of every pass that runs in between, not
  // something this function can arrange, and the walk visits the whole
  // DAG rather than the top-level conjuncts -- so a second equation of
  // this shape would be believed even nested under a disjunction. The
  // container is hash-ordered, so silently keeping the last one found
  // would pick a different operand from run to run and certify the
  // candidate against the wrong arrays. Refuse instead.
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
      if (s.GetKind() != SYMBOL ||
          witnessNames.find(s) == witnessNames.end() ||
          !(other.GetKind() == READ || other.GetKind() == ITE))
        continue;
      const std::map<ASTNode, ASTNode>::const_iterator prev = anchorRhs.find(s);
      if (prev != anchorRhs.end() && !(prev->second == other))
        FatalError("array-equality: a witness read's defining equation "
                   "occurs twice with different right-hand sides, so which "
                   "one gives the equality operand's current form is not "
                   "determined",
                   s);
      anchorRhs[s] = other;
    }
  }

  for (size_t i = 0; i < activeRecordIds.size(); i++)
  {
    Record& r = records[activeRecordIds[i]];
    std::map<ASTNode, ASTNode>::const_iterator lit = anchorRhs.find(r.nameL);
    std::map<ASTNode, ASTNode>::const_iterator rit = anchorRhs.find(r.nameR);
    if (lit == anchorRhs.end() || rit == anchorRhs.end())
      FatalError("array-equality: a witness-read defining equation was "
                 "lost during preprocessing, so the current form of an "
                 "equality operand cannot be recovered",
                 r.proxy);
    r.canonicalLeft = recoverAnchoredOperand(lit->second, r.lambda, r.proxy);
    r.canonicalRight = recoverAnchoredOperand(rit->second, r.lambda, r.proxy);
  }
}

// Compute the owned array-term graph directly from every array-valued
// node reachable in the prepared root. Record write parenthood at the
// same time; array-if-then-else parenthood is populated with its reified
// condition below, after scalar naming.
void ExtensionalityContext::computeArrayGraph(
    const ASTNode& root, std::set<ASTNode>& arrays,
    std::map<ASTNode, std::vector<ASTNode>>& parents)
{
  arrays.clear();
  parents.clear();

  ASTNodeSet visited;
  collectDag(root, visited);
  for (ASTNodeSet::const_iterator it = visited.begin(); it != visited.end();
       ++it)
  {
    const ASTNode& n = *it;
    if (isArrayType(n))
      arrays.insert(n);
    if (n.GetKind() == WRITE)
      parents[n[0]].push_back(n);
  }
  for (std::map<ASTNode, std::vector<ASTNode>>::iterator it = parents.begin();
       it != parents.end(); ++it)
    std::sort(it->second.begin(), it->second.end(), nodeNumLess);
}

// Create or reuse a scalar name for a checker-visible term and queue
// its defining constraint name = term. The defining equation is
// conjoined before bit-blasting, so the name has SAT variables and a
// lemma mentioning the term can be encoded over them.
ASTNode ExtensionalityContext::freshName(const ASTNode& term,
                                         ASTVec& namingConstraints)
{
  if (term.isConstant())
    return term;
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

// See the header. The Boolean analogue of freshName.
ASTNode ExtensionalityContext::conditionName(const ASTNode& cond,
                                             ASTVec& namingConstraints)
{
  std::map<ASTNode, ASTNode>::const_iterator it = scalarNames.find(cond);
  if (it != scalarNames.end())
    return it->second;
  ASTNode name = bm->CreateFreshVariable(0, 0, "ext_cond");
  protectedSymbols.insert(name);
  namingConstraints.push_back(
      bm->defaultNodeFactory->CreateNode(IFF, name, cond));
  scalarNames[cond] = name;
  nameToTermMap[name] = cond;
  return name;
}

// Final preparation before STP's main array transformation: recover
// canonical operands, collect and freeze the complete array graph,
// inventory its writes as accesses (section 11.4), and give every
// compound write index/value a scalar name.
//
// Array-valued if-then-elses remain structural and are inventoried here;
// the consistency checker's T-up/T-down rules reason about the selected
// branch directly.
ASTNode ExtensionalityContext::prepare(const ASTNode& root_)
{
  if (!active())
    FatalError("array-equality: preparation ran without an active equality");
  if (arrayGraphIsFrozen || graphBound)
    FatalError("array-equality: the complete array graph was prepared twice");
  ASTNode root = root_;
  ASTVec extraConstraints;

  std::set<ASTNode> arrays;
  std::map<ASTNode, std::vector<ASTNode>> parents;

  locateCanonicalOperands(root);
  computeArrayGraph(root, arrays, parents);

  for (size_t i = 0; i < activeRecordIds.size(); ++i)
  {
    const Record& r = records[activeRecordIds[i]];
    if (arrays.find(r.canonicalLeft) == arrays.end() ||
        arrays.find(r.canonicalRight) == arrays.end())
      FatalError("array-equality: a canonical equality operand is absent "
                 "from the complete prepared array graph",
                 r.proxy);
  }

  // anticipatedArraySymbols recorded which reads had to be protected
  // from read-equals-constant substitution, and this graph contains all
  // arrays as they are NOW, after simplification. What makes the first
  // a superset of the second is that conjoinRecordConstraints walked
  // the whole formula before any pass touched it.
  // What is left to assume is only that no pass in between introduces an
  // array symbol that was not reachable then --
  // a claim about every pass that runs, not something this code can
  // arrange. Losing it is silent: an unanticipated array symbol's reads
  // were never protected, so the substitution may have deleted an
  // observation the consistency check needs, and the check then
  // certifies a candidate against contents it never saw. Cheap to
  // verify, so verify it.
  for (std::set<ASTNode>::const_iterator it = arrays.begin();
       it != arrays.end(); ++it)
  {
    if (it->GetKind() == SYMBOL && !wasArrayAnticipated(*it))
      FatalError("array-equality: an array symbol entered the prepared graph "
                 "without appearing at the pre-preprocessing ownership "
                 "boundary, so its reads were never protected from "
                 "substitution",
                 *it);
  }

  // Freeze the complete graph; it must not change for the rest of the solve.
  ownedArrays = arrays;
  ownedWriteParents = parents;

  // Inventory the owned graph's writes as accesses (a write is treated as a
  // read of its own index yielding the written value, paper section
  // 11.4), and give their indexes and values scalar names: writes occur
  // inside array terms, so their scalar children can otherwise disappear
  // when every read of the array is directly abstracted.
  std::vector<ASTNode> writeNodes;
  for (std::set<ASTNode>::const_iterator it = arrays.begin();
       it != arrays.end(); ++it)
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
    ownedWrites[w] = info;
    // write value names are needed when the access list is built
    freshName(w[2], extraConstraints);
  }

  // Inventory the owned graph's array-valued if-then-elses. Unlike section
  // 4.1's elimination, these stay as terms: the checker reasons about
  // them directly with rules T-down/T-up, which fire on whichever
  // branch sigma selects. That costs one Boolean literal per
  // if-then-else instead of two array equalities, two witness indices
  // and four virtual reads -- and, because exactly one branch is live
  // per candidate, it leaves no unconstrained proxy for the solver to
  // guess and the checker to refute.
  //
  // The condition is reified as a Boolean symbol here. The checker must
  // branch on the value the bit-blasted circuit took; re-deriving it
  // from the counterexample is the failure class that let a scalar name
  // disagree with its term, and here it would make the wrong branch
  // live and certify a model that does not satisfy the if-then-else
  // axiom. The same symbol is what a lemma premise names.
  std::vector<ASTNode> iteNodes;
  for (std::set<ASTNode>::const_iterator it = arrays.begin();
       it != arrays.end(); ++it)
    if (it->GetKind() == ITE && isArrayType(*it))
      iteNodes.push_back(*it);
  std::sort(iteNodes.begin(), iteNodes.end(), nodeNumLess);

  for (size_t i = 0; i < iteNodes.size(); i++)
  {
    const ASTNode& t = iteNodes[i];
    ExtIteNode info;
    info.ite = t;
    info.condTerm = t[0];
    info.condName = conditionName(t[0], extraConstraints);
    info.thn = t[1];
    info.els = t[2];
    ownedItes[t] = info;
    ownedIteParents[t[1]].push_back(t);
    if (t[2] != t[1])
      ownedIteParents[t[2]].push_back(t);
  }
  for (std::map<ASTNode, std::vector<ASTNode>>::iterator it =
           ownedIteParents.begin();
       it != ownedIteParents.end(); ++it)
    std::sort(it->second.begin(), it->second.end(), nodeNumLess);

  // Equality edges over canonical operands + witness obligations.
  for (size_t i = 0; i < activeRecordIds.size(); i++)
  {
    const Record& r = records[activeRecordIds[i]];
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

  arrayGraphIsFrozen = true;

  if (extraConstraints.empty())
    return root;
  return bm->defaultNodeFactory->CreateNode(AND, root, extraConstraints);
}

// After the main ArrayTransformer pass: the complete read inventory
// (ordinary reads plus witness reads) now carries its abstraction and index
// symbols; bind everything into the immutable checker graph.
void ExtensionalityContext::bindAfterTransform(ArrayTransformer* at)
{
  if (!arrayGraphIsFrozen)
    FatalError("array-equality: binding began before the complete array "
               "graph was frozen");
  if (graphBound)
    FatalError("array-equality: the complete array graph was bound twice");

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
  // The transformer must have put every read into the complete graph.
  // There is deliberately no complementary host-refinement partition:
  // sharing scalar indexes across such a partition was the source of
  // candidates that neither subsystem could prove or refute.
  for (ArrayTransformer::ArrType::const_iterator it =
           at->arrayToIndexToRead.begin();
       it != at->arrayToIndexToRead.end(); ++it)
  {
    if (!ownsArray(it->first))
      FatalError("array-equality: the transformer registered a read outside "
                 "the complete owned array graph",
                 it->first);
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
      FatalError("array-equality: an owned read index has no "
                 "bit-blasted scalar name to encode lemmas over",
                 row.index);
    // An owned read's semantics live entirely in refinement lemmas, so
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
  for (std::map<ASTNode, ExtWriteNode>::const_iterator it = ownedWrites.begin();
       it != ownedWrites.end(); ++it)
    writeNodes.push_back(it->first);
  std::sort(writeNodes.begin(), writeNodes.end(), nodeNumLess);
  for (size_t i = 0; i < writeNodes.size(); i++)
  {
    const ExtWriteNode& info = ownedWrites[writeNodes[i]];
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
      FatalError("array-equality: an owned write value has no "
                 "bit-blasted scalar name to encode lemmas over",
                 info.write);
    graph.accesses.push_back(a);
  }

  // The property that lets namesAgreeWithCandidate skip the witness
  // names: every witness read reached the inventory. It holds by
  // construction -- the anchor is protected from substitution, and
  // locateCanonicalOperands fails loudly if one is lost, so the read is
  // in the transformed formula; the transformer registers it; and the
  // operand it reads is in the owned graph, so bindAfterTransform harvests
  // it.
  // Defend it at runtime so release builds cannot silently certify an
  // incomplete graph.
  for (size_t i = 0; i < activeRecordIds.size(); i++)
  {
    const Record& r = records[activeRecordIds[i]];
    bool haveL = false, haveR = false;
    for (size_t z = 0; z < graph.accesses.size(); z++)
    {
      const ExtAccess& acc = graph.accesses[z];
      if (acc.isWrite || !(acc.indexTerm == r.lambda))
        continue;
      haveL = haveL || acc.site == r.canonicalLeft;
      haveR = haveR || acc.site == r.canonicalRight;
    }
    if (!haveL || !haveR)
      FatalError("array-equality: a witness read is absent from the complete "
                 "owned access graph",
                 r.proxy);
  }

  graph.writes = ownedWrites;
  graph.writeParents = ownedWriteParents;
  graph.ites = ownedItes;
  graph.iteParents = ownedIteParents;
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

public:
  explicit CEModelView(AbsRefine_CounterExample* ce_) : ce(ce_) {}

  virtual ASTNode bvValue(const ASTNode& term)
  {
    if (term.GetKind() == BVCONST)
      return term;
    if (term.GetKind() != SYMBOL)
      FatalError("array-equality: the checker requested a bit-vector term "
                 "instead of its scalar SAT name",
                 term);
    ASTNode v = ce->LookupAssignedValue(term);
    if (v.IsNull() || v.GetKind() != BVCONST ||
        v.GetValueWidth() != term.GetValueWidth())
      FatalError("array-equality: the materialized SAT assignment has no "
                 "concrete value for a scalar name the consistency checker "
                 "depends on",
                 term);
    return v;
  }

  virtual bool boolValue(const ASTNode& term)
  {
    if (term.GetKind() == TRUE || term.GetKind() == FALSE)
      return term.GetKind() == TRUE;
    if (term.GetKind() != SYMBOL)
      FatalError("array-equality: the checker requested a Boolean term "
                 "instead of its scalar SAT name",
                 term);
    ASTNode v = ce->LookupAssignedValue(term);
    if (v.IsNull() || !(v.GetKind() == TRUE || v.GetKind() == FALSE))
      FatalError("array-equality: the materialized SAT assignment has no "
                 "Boolean value for a scalar name the consistency checker "
                 "depends on",
                 term);
    return v.GetKind() == TRUE;
  }
};
} // namespace

ExtensionalityContext::CertificationAction
ExtensionalityContext::decideCertification(bool ordinaryResult,
                                           bool checkerActive,
                                           CandidateOutcome ext)
{
  if (!checkerActive)
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
  // With the complete array graph owned here, a conflict-free fixed
  // point must make the semantic input true on the same scalar
  // assignment. There is no second array-refinement subsystem to hand
  // a disagreement to.
  return ordinaryResult ? RETURN_SAT : INTERNAL_ERROR;
}

ExtensionalityContext::CandidateOutcome
ExtensionalityContext::checkCandidate(AbsRefine_CounterExample* ce)
{
  if (!graphBound)
    FatalError("array-equality: candidate checking began before the complete "
               "array graph was bound");
  if (pendingLemmaValid || !pendingLemmas.empty())
    FatalError("array-equality: a new candidate was checked before the prior "
               "conflict certificates were encoded");
  lastObserved.clear();
  CEModelView view(ce);
  ExtCheckResult res = ExtChecker::check(graph, view, false);
  switch (res.status)
  {
    case ExtCheckResult::CONSISTENT:
      lastObserved = res.observed;
      // Publishing first makes the certified array contents visible
      // to term evaluation; only then can an owned read's term be
      // compared against its name.
      publishObservations(ce);
      if (!namesAgreeWithCandidate(view, ce))
        FatalError("array-equality: a scalar name disagrees with its term "
                   "after the complete array graph reached a conflict-free "
                   "fixed point");
      return EXT_CONSISTENT;
    case ExtCheckResult::CONFLICT:
      if (res.conflicts.empty())
        FatalError("array-equality: the checker reported a conflict without "
                   "a refinement certificate");
      pendingLemmas = res.conflicts;
      pendingLemmaValid = true;
      return EXT_CONFLICT;
    case ExtCheckResult::WITNESS_VIOLATION:
    default:
      return EXT_WITNESS_ERROR;
  }
}

// The checker reads the candidate through scalar names whose defining
// equations were part of the initial bit-blast. Verify, with certified
// observations published, that every name still evaluates exactly like
// its term. Since every read abstraction is in this graph, a mismatch
// is an ownership/encoding invariant violation rather than a third
// refinement outcome; equal concrete indexes with different values
// must already have produced a rule-C conflict.
bool ExtensionalityContext::namesAgreeWithCandidate(
    ExtModelView& view, AbsRefine_CounterExample* ce) const
{
  for (size_t i = 0; i < graph.accesses.size(); i++)
  {
    const ExtAccess& a = graph.accesses[i];
    if (!(a.indexName == a.indexTerm))
    {
      const ASTNode termValue = ce->ModelValueOfTerm(a.indexTerm);
      if (termValue.IsNull() || termValue.GetKind() != BVCONST ||
          termValue.GetValueWidth() != a.indexTerm.GetValueWidth())
        FatalError("array-equality: an access index has no concrete value in "
                   "the certified model",
                   a.indexTerm);
      if (view.bvValue(a.indexName) != termValue)
        return false;
    }
    if (!(a.valueName == a.valueTerm))
    {
      const ASTNode termValue = ce->ModelValueOfTerm(a.valueTerm);
      if (termValue.IsNull() || termValue.GetKind() != BVCONST ||
          termValue.GetValueWidth() != a.valueTerm.GetValueWidth())
        FatalError("array-equality: an access value has no concrete value in "
                   "the certified model",
                   a.valueTerm);
      if (view.bvValue(a.valueName) != termValue)
        return false;
    }
  }

  // Each reified if-then-else condition against the condition it names.
  // The checker branches on these to decide which branch is live, so a
  // name that disagrees with its term selects the wrong one and can
  // certify a model that does not satisfy the if-then-else axiom. This
  // is the same guard the access names get, for the same reason, and it
  // is the failure class the direct integration reopened.
  for (std::map<ASTNode, ExtIteNode>::const_iterator it = ownedItes.begin();
       it != ownedItes.end(); ++it)
  {
    const ASTNode termValue = ce->ModelValueOfFormula(it->second.condTerm);
    if (termValue.IsNull() ||
        !(termValue.GetKind() == TRUE || termValue.GetKind() == FALSE))
      FatalError("array-equality: an array-if-then-else condition has no "
                 "concrete value in the certified model",
                 it->second.condTerm);
    if (view.boolValue(it->second.condName) != (termValue.GetKind() == TRUE))
      return false;
  }

  // The witness names -- the records' nameL and nameR, which the
  // checker's witness loop reads directly -- need no comparison of
  // their own. Each is anchored by nameL = read(left, lambda) in the
  // bit-blasted formula, so the candidate gives it the value of that
  // read's abstraction variable; that read is always in the inventory
  // (bindAfterTransform asserts it), so the loop above has already
  // checked its variable against its term. Transitivity does the rest.
  return true;
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

void ExtensionalityContext::encodePendingLemmas(SATSolver& solver,
                                                ToSATBase* tosat)
{
  if (!pendingLemmaValid || pendingLemmas.empty())
    FatalError("array-equality: lemma encoding began without a pending "
               "certificate");
  for (size_t i = 0; i < pendingLemmas.size(); i++)
    encodeOneLemma(pendingLemmas[i], solver, tosat);
  pendingLemmas.clear();
  pendingLemmaValid = false;
}

void ExtensionalityContext::encodeOneLemma(const ExtConflict& pendingLemma,
                                           SATSolver& solver,
                                           ToSATBase* tosat)
{
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

      const int q = getEquals(solver, a, b, satVar, Polarity::BOTH);
      // Unlike the host's read axioms, which build their reified
      // variables fresh for each clause, these are cached and reused by
      // later refinement rounds -- with the solver's own simplification
      // running in between. A backend that eliminates variables would
      // be handed a dead one, so keep them.
      solver.setFrozen(q);
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
      assert(atom.op == ExtLemmaAtom::BOOL_LIT ||
             atom.op == ExtLemmaAtom::BOOL_LIT_NEG);
      ToSATBase::ASTNodeToSATVar::const_iterator vit =
          satVar.find(atom.boolTerm);
      if (vit == satVar.end() || vit->second.size() != 1 ||
          vit->second[0] == ~((unsigned)0))
        FatalError("array-equality: an equality abstraction variable "
                   "was never bit-blasted, so the lemma cannot be "
                   "encoded",
                   atom.boolTerm);
      // A premise literal appears negated in the clause, so a
      // negatively-taken condition appears positively.
      clause.push(SATSolver::mkLit(vit->second[0],
                                   atom.op == ExtLemmaAtom::BOOL_LIT));
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
}

// Publish the conflict-free observed values of every owned array
// (symbols, writes, and array-if-then-else terms alike) into the
// counterexample map, so model evaluation, the model
// APIs, and the printers see the array contents certified by the
// consistency check. Indices with no observation default to zero at
// lookup/print time.
void ExtensionalityContext::publishObservations(AbsRefine_CounterExample* ce)
{
  ASTNodeMap batch;
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
      ASTNodeMap::const_iterator prior = batch.find(key);
      if (prior != batch.end() && !(prior->second == it->second[i].second))
        FatalError("array-equality: a conflict-free checker result assigns "
                   "two values to one concrete array cell",
                   key);
      batch[key] = it->second[i].second;
    }
  }

  // Validate the entire batch before mutating the public model. Active
  // candidates normally have no READ entries yet; this check also makes
  // that ownership boundary fail closed if a future preprocessing path
  // introduces one.
  for (ASTNodeMap::const_iterator it = batch.begin(); it != batch.end(); ++it)
  {
    const ASTNode prior = ce->LookupAssignedValue(it->first);
    if (!prior.IsNull() && !(prior == it->second))
      FatalError("array-equality: certified array observation conflicts with "
                 "an existing counterexample entry",
                 it->first);
  }
  for (ASTNodeMap::const_iterator it = batch.begin(); it != batch.end(); ++it)
    ce->InsertIntoCounterExampleMap(it->first, it->second);

  // No model evaluation should precede certification, but clearing the
  // cache here makes publication an explicit phase boundary.
  ce->ClearComputeFormulaMap();
}

} // namespace stp
