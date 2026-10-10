/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: February, 2011
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

/*
 * Identifies unconstrained variables and remove them from the input.
 * Robert Bruttomesso's & Robert Brummayer's dissertations describe this.
 *
 * Kinds without a per-kind rule (bvsx, bvzx, bvurem/bvudiv by a
 * constant, masks, ...) can still be eliminated when the variable's
 * whole use is a predicate over it and constants: see
 * tryGroundPathCollapse.
 *
 * The array rules (READ, WRITE and array-sorted ITE) are the ones
 * Brummayer's dissertation states for the extensional theory of
 * arrays. One condition is less obvious than it looks: a write is
 * unconstrained only when its *value* is unconstrained as well as its
 * base array. write(a, i, e) with a free but e fixed is pinned to e at
 * i, so it does not range over every array, and treating it as free
 * would decide equalities that are in fact unsatisfiable. The same holds
 * when e is the index itself: write(a, e, e) holds e at e, whatever a
 * is, although e passes for unconstrained -- the write is its only
 * parent, and parents are counted once however many times they name it.
 *
 * The corresponding rule for array equality -- one unconstrained side
 * is enough to make the equality a free boolean -- is deliberately
 * absent. It was implemented and measured over QF_ABV: it won nothing
 * that the other three do not already win, and it cost the
 * brummayerbiere fifo family up to 4x, because replacing a settled
 * equality with a free boolean leaves the abstraction refinement loop
 * to rediscover it -- 22 rounds rather than 2.
 * RemoveUnconstrained_Collapse.array_equality pins the absence.
 *
 * Float- and RoundingMode-sorted arrays are excluded throughout, for
 * the reason PropagateEqualities excludes them from the equivalent
 * substitution: the model machinery that reconstructs a substituted
 * symbol's cells reads them as plain bits, which is wrong under NaN's
 * many packings and float index canonicalisation.
 */

#include "stp/Simplifier/RemoveUnconstrained.h"
#include <cstdlib>
#include "stp/Extensionality/ExtensionalityContext.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/FloatBlaster/FloatBlaster.h"
#include "stp/FloatBlaster/FpAbstraction.h"
#include "stp/FloatBlaster/rounding_modes.h"
#include "stp/Simplifier/AchievableImage.h"
#include "stp/Simplifier/constantBitP/Dependencies.h"
#include <cstdint>

namespace stp
{
using simplifier::constantBitP::Dependencies;

RemoveUnconstrained::RemoveUnconstrained(STPMgr& _bm) : bm(_bm), checkGraph(getenv("STP_RU_CHECK_GRAPH") != NULL)
{
  nf = _bm.defaultNodeFactory;
  simplifier = NULL;
}

ASTNode RemoveUnconstrained::topLevel(const ASTNode& n, Simplifier* simplifier,
                                      const std::set<ASTNode>* alsoUntouchable)
{
  ASTNode result(n);

  // Symbols the array-equality procedure depends on must not be
  // treated as unconstrained. Every rule below decides what to rewrite
  // from isUnconstrained(), and each one mutates the graph before
  // recording the variable's replacement -- so a substitution the map
  // refuses (see SubstitutionMap::extensionalityProtected) cannot undo
  // the rewrite that was made on its promise. Excluding the symbols
  // from the predicate is what makes the protection a precondition
  // instead of a return code nobody can act on. The caller's own
  // untouchable set -- symbols constrained outside this formula -- is
  // honoured the same way, merged when both apply.
  ExtensionalityContext* ext = bm.getExtensionalityIfAny();
  arrayRules = (ext == NULL || !ext->activeInSolve());
  const std::set<ASTNode>* extSet =
      (ext != NULL && ext->activeInSolve()) ? &ext->getFrozenSymbols() : NULL;
  UFContext* uf = bm.getUFContextIfAny();
  const ASTNodeSet* ufSet =
      (uf != NULL && uf->activeInSolve()) ? &uf->getProtectedSymbols() : NULL;
  // The floating-point abstraction's surrogates and proxies, for the same
  // reason as the array-equality symbols above: the one constraint such a
  // symbol occurs in must stay, because the refinement's lemmas over it
  // splice onto the variables that constraint gives it.
  FpAbstraction* fp = bm.getFpAbstractionIfAny();
  const std::set<ASTNode>* fpSet =
      (fp != NULL && fp->active()) ? &fp->protectedSymbols() : NULL;

  // A declared sort may be given as few elements as the formula's terms
  // name (see ExtDeclaredElement), and an equality between arrays over it
  // can make use of that: a store chain equated with a constant array can
  // say every element is one of a few terms. A variable of such a sort is
  // then not free to differ from another term, which is what replacing an
  // equality over it by a fresh Boolean assumes -- the assumption that the
  // sort has a second element. So where a sort indexes both a constant
  // array and an array equality, its symbols, and the arrays whose reads
  // are values of it, keep their constraints. Without the equality nothing
  // compares whole arrays over the sort, and nothing can bound it.
  std::set<ASTNode> boundableSymbols;
  if (bm.hasConstArrays())
  {
    std::set<unsigned> constIndexed, equated;
    const auto declaredIndex = [](const ASTNode& array, std::set<unsigned>& to) {
      const SourceSort sort = array.GetSourceSort();
      if (sort.kind() == SourceSort::Kind::Array &&
          sort.index().kind() == SourceSort::Kind::Uninterpreted)
        to.insert(sort.index().uninterpretedId());
    };
    ASTNodeSet visited;
    std::vector<ASTNode> pending(1, result);
    std::vector<ASTNode> symbols;
    while (!pending.empty())
    {
      const ASTNode node = pending.back();
      pending.pop_back();
      if (!visited.insert(node).second)
        continue;
      if (node.GetKind() == CONST_ARRAY)
        declaredIndex(node, constIndexed);
      if ((node.GetKind() == ARRAY_EQ || node.GetKind() == DISTINCT) &&
          node.Degree() > 0 && node[0].GetType() == ARRAY_TYPE)
        declaredIndex(node[0], equated);
      if (node.GetKind() == SYMBOL)
        symbols.push_back(node);
      for (const ASTNode& child : node.GetChildren())
        pending.push_back(child);
    }
    for (const ASTNode& symbol : symbols)
    {
      SourceSort sort = symbol.GetSourceSort();
      if (sort.kind() == SourceSort::Kind::Array)
        sort = sort.element();
      if (sort.kind() == SourceSort::Kind::Uninterpreted &&
          constIndexed.count(sort.uninterpretedId()) != 0 &&
          equated.count(sort.uninterpretedId()) != 0)
        boundableSymbols.insert(symbol);
    }
  }

  // An earlier pass may already have assigned a symbol a reconstruction
  // definition. Replacing it again would overwrite that definition (and
  // violates UpdateSubstitutionMapFewChecks' contract). This matters when
  // a protected symbolic default keeps the source symbol reachable across
  // repeated preprocessing rounds.
  std::set<ASTNode> alreadyDefined;
  for (const auto& binding : *simplifier->Return_SolverMap())
    if (binding.first.GetKind() == SYMBOL)
      alreadyDefined.insert(binding.first);
  // The image-constrained fresh variables join this set as they are
  // made (tryImageConstrainShared), so the set is always materialised
  // when that rewrite is enabled.
  std::set<ASTNode> mergedUntouchable;
  const std::set<ASTNode>* effective = NULL;
  if (extSet != NULL || ufSet != NULL || fpSet != NULL ||
      alsoUntouchable != NULL || !alreadyDefined.empty() ||
      !boundableSymbols.empty() || bm.UserFlags.unconstrained_image_vars)
  {
    if (extSet != NULL)
      mergedUntouchable.insert(extSet->begin(), extSet->end());
    mergedUntouchable.insert(boundableSymbols.begin(), boundableSymbols.end());
    mergedUntouchable.insert(alreadyDefined.begin(), alreadyDefined.end());
    if (ufSet != NULL)
      mergedUntouchable.insert(ufSet->begin(), ufSet->end());
    if (fpSet != NULL)
      mergedUntouchable.insert(fpSet->begin(), fpSet->end());
    if (alsoUntouchable != NULL)
      mergedUntouchable.insert(alsoUntouchable->begin(),
                               alsoUntouchable->end());
    effective = &mergedUntouchable;
  }
  untouchable = effective;
  passUntouchable = effective == NULL ? NULL : &mergedUntouchable;

  bm.GetRunTimes()->start(RunTimes::RemoveUnconstrained);

  if (simplifier->hasUnappliedSubstitutions())
    result = simplifier->applySubstitutionMap(result);

  // In some rare cases, the simplifier might not have removed a term
  // that can be substituted away. e.g. read(A,0), if read(A,0) == 1,
  // in the substitution map.
  result = topLevel_other(result, simplifier);

  // Any definition the substitution map refused goes back as a
  // conjunct, so the variable it defines is not left free.
  if (!refusedDefinitions.empty())
  {
    refusedDefinitions.push_back(result);
    result = nf->CreateNode(AND, refusedDefinitions);
    refusedDefinitions.clear();
  }

  bm.GetRunTimes()->stop(RunTimes::RemoveUnconstrained);
  passUntouchable = NULL;
  untouchable = NULL;
  return result;
}

// Whether an array-sorted node may take part in the array rules. A
// float- or RoundingMode-sorted array is left alone: see the header
// comment.
static bool eligibleArray(const ASTNode& n)
{
  return n.GetIndexWidth() > 0 && n.GetType() == ARRAY_TYPE &&
         !n.GetSourceSort().usesFloatingPointTheory();
}


static bool isRNEConstant(const ASTNode& n)
{
  return n.GetKind() == BVCONST && n.GetValueWidth() == 5 &&
         n.GetUnsignedConst() ==
             symbolic_fp::rounding_modes::ROUND_NEAREST_TIES_TO_EVEN;
}

// Whether narrowing a source-format quotient into the target format absorbs
// the error of steering that quotient with a source-format divisor. Two
// requirements, from the witness construction in the FP_DIV rule below: the
// witness divisor and the division it feeds each contribute one part in
// 2^(ss-1) of relative error, while the target's round-to-nearest interval
// around any representable value is at least 2^-(ts+2) wide relative (the
// tight case sits just above a power of two), so five extra significand
// bits cover it with margin; and the witness quotient x/t -- |x| at most
// the target's largest finite, |t| at least its smallest subnormal -- must
// stay inside the source format's normal range, which spans 2^±emax_s.
static bool narrowingAbsorbsDivisorGrid(unsigned se, unsigned ss,
                                        unsigned te, unsigned ts)
{
  if (se < 2 || te < 2 || se > 62 || te > 62)
    return false;
  if (ss < ts + 5)
    return false;
  const uint64_t emax_t = (uint64_t(1) << (te - 1)) - 1;
  const uint64_t emax_s = (uint64_t(1) << (se - 1)) - 1;
  return emax_s >= 2 * emax_t + ts + 1;
}

// A fresh symbol that can stand in for `like`. Widths alone name a
// bit-vector sort; a declared sort, or an array over one, has to be
// carried explicitly or a later array equality between the stand-in and
// a source term sees two different sorts.
ASTNode RemoveUnconstrained::freshLike(const ASTNode& like,
                                       const std::string& prefix)
{
  const SourceSort sort = like.GetSourceSort();
  if (sort.kind() == SourceSort::Kind::Uninterpreted ||
      sort.kind() == SourceSort::Kind::Array)
    return bm.CreateFreshSourceVariable(sort, prefix);
  return bm.CreateFreshVariable(like.GetIndexWidth(), like.GetValueWidth(),
                                prefix);
}

bool RemoveUnconstrained::singleParent(const ASTNode& n, ASTNode& parent)
{
  std::vector<ASTNode> ps;
  g->parents(n, ps);
  if (ps.empty())
    return false;
  // One distinct parent: a node used twice by the same parent, as in
  // (bvmul t t), still has one place that reads it.
  for (size_t i = 1; i < ps.size(); i++)
    if (ps[i] != ps[0])
      return false;
  parent = ps[0];
  return true;
}

bool RemoveUnconstrained::unconstrained(const ASTNode& n)
{
  if (n.GetKind() != SYMBOL)
    return false;
  // A protected symbol is never free to be given a value here, however
  // it occurs.
  if (untouchable != NULL && untouchable->find(n) != untouchable->end())
    return false;
  ASTNode parent;
  return singleParent(n, parent);
}

// As the graph sees them now: a replaced child is its replacement, and a
// child standing above a replacement is converted, so that what the
// rules read below it is current structure.
void RemoveUnconstrained::kidsOf(const ASTNode& n, ASTVec& out)
{
  out.clear();
  for (const ASTNode& c : n)
    out.push_back(g->normalise(c));
}

void RemoveUnconstrained::variablesIn(const ASTNode& n,
                                      std::vector<ASTNode>& out)
{
  ASTNodeSet seen;
  std::vector<ASTNode> stack;
  stack.push_back(g->current(n));
  while (!stack.empty())
  {
    const ASTNode cur = stack.back();
    stack.pop_back();
    if (!seen.insert(cur).second)
      continue;
    if (cur.GetKind() == SYMBOL)
      out.push_back(cur);
    for (const ASTNode& c : cur)
      stack.push_back(g->current(c));
  }
}

// Symbols whose parent count changed are candidates again: the fresh
// symbol a rule put in, and the symbols under whatever it took out.
void RemoveUnconstrained::drain()
{
  auto requeue = [this](std::unordered_map<uint64_t, std::vector<ASTNode>>& m,
                        uint64_t key) {
    const auto d = m.find(key);
    if (d == m.end())
      return;
    worklist.insert(worklist.end(), d->second.begin(), d->second.end());
    m.erase(d);
  };
  for (const MutableGraph::Change& c : g->changes())
  {
    if (c.what != MutableGraph::Change::CountChanged)
      continue;
    // The event names the handle whose count changed; a record may have
    // been keyed by what stands for it now.
    requeue(blockedOn, c.node.GetNodeNum());
    requeue(blockedOn, g->current(c.node).GetNodeNum());
    if (c.node.GetKind() != SYMBOL)
      continue;
    worklist.push_back(c.node);
    requeue(deferredOn, c.node.GetNodeNum());
  }
  g->clearChanges();
}

void RemoveUnconstrained::splice(const ASTNode& node, const ASTNode& by)
{
  // The nodes that held `node` now hold `by`: their other children, if
  // symbols, may qualify for a rule with the new sibling that they did
  // not with the old one. Bounded as the wide-conjunction check is.
  std::vector<ASTNode> holders;
  g->parents(node, holders);
  if (checkGraph)
    std::cerr << "  [ru] splice " << node.GetNodeNum() << " kind " << node.GetKind()
              << " -> " << by.GetNodeNum() << " kind " << by.GetKind()
              << " (" << holders.size() << " holders)" << std::endl;

  g->replace(node, by);
  if (checkGraph)
  {
    std::string why;
    if (!g->checkInvariant(&why))
      FatalError(("RemoveUnconstrained: graph invariant broken: " + why).c_str());
  }
  drain();

  for (const ASTNode& h : holders)
  {
    const ASTNode q = g->current(h);
    if (q.Degree() > 200)
      continue;
    for (const ASTNode& c : q)
      if (c.GetKind() == SYMBOL)
        worklist.push_back(c);
  }
  // The symbols inside `by` sit under new structure (a comparison
  // rewritten as a predicate over the sibling, say) and may qualify for
  // a rule there that they did not where they were. A symbol itself has
  // no inside; a replacement over a handful of nodes is the usual case.
  if (by.GetKind() != SYMBOL && !by.isConstant())
  {
    std::vector<ASTNode> inside;
    variablesIn(by, inside);
    for (const ASTNode& v : inside)
      worklist.push_back(v);
  }
}

ASTNode RemoveUnconstrained::replaceWithFresh(const ASTNode& node)
{
  // An array-sorted node (a write, or an if-then-else over arrays)
  // needs an array-sorted stand-in; the index width is zero for
  // everything else, so this is the ordinary case too.
  ASTNode v = freshLike(node, "unconstrained");
  // A float-valued node's stand-in must carry the format too, or the
  // blaster later meets a formatless bitvector where a float belongs.
  v.SetExpWidth(node.GetExpWidth());
  v.SetSigWidth(node.GetSigWidth());
  splice(node, v);
  return v;
}

//  nb. This avoids the expensive checks that usually updating the substitution
//  map entails.
void RemoveUnconstrained::replace(const ASTNode& from, const ASTNode to)
{
  assert(from.GetKind() == SYMBOL);
  assert(from.GetValueWidth() == to.GetValueWidth());
  if (checkGraph)
    std::cerr << "  [ru] define " << from.GetNodeNum() << " (count "
              << (g != NULL ? g->parentCount(from) : 0) << ")" << std::endl;
  if (simplifier->UpdateSubstitutionMapFewChecks(from, to))
    return;

  // Refused (by SubstitutionMap::theoryProtected or erasesSourceSort).
  // The caller has already rewritten the graph to remove whatever
  // constrained "from", so dropping the definition here would leave it
  // free. Keep it as an ordinary conjunct instead; topLevel() attaches
  // these to the result.
  refusedDefinitions.push_back(
      from.GetType() == BOOLEAN_TYPE ? nf->CreateNode(IFF, from, to)
                                     : nf->CreateNode(EQ, from, to));
}

// Rebuild one collected step as an ASTNode around `in`. Used when a
// distributed ITE's other branch gets the suffix steps re-applied.
static ASTNode applyStepToNode(NodeFactory* nf, STPMgr& bm,
                               const GroundStep& s, const ASTNode& in)
{
  if (s.kind == BVSX || s.kind == BVZX)
    return nf->CreateTerm(s.kind, s.outWidth, in,
                          bm.CreateBVConst(32, s.outWidth));
  if (s.kind == BVEXTRACT)
    return nf->CreateTerm(BVEXTRACT, s.outWidth, in, s.constants[0],
                          s.constants[1]);
  if (s.samePathAllOperands)
    return nf->CreateTerm(s.kind, s.outWidth, in, in);
  if (s.pathIndex == 0)
    return nf->CreateTerm(s.kind, s.outWidth, in, s.constants[0]);
  return nf->CreateTerm(s.kind, s.outWidth, s.constants[0], in);
}

// Forward-evaluate the whole chain at a concrete x. Returns an owned CBV
// at the chain's output width.
static CBV evalChain(const std::vector<GroundStep>& steps, const CBV x)
{
  CBV v = CONSTANTBV::BitVector_Clone(x);
  for (const GroundStep& s : steps)
  {
    CBV nv = AchievableImage::evalStep(s, v);
    CONSTANTBV::BitVector_Destroy(v);
    v = nv;
  }
  return v;
}

static ASTNode mkExtract(NodeFactory* nf, STPMgr& bm, const ASTNode& u,
                         unsigned high, unsigned low)
{
  return nf->CreateTerm(BVEXTRACT, high - low + 1, u,
                        bm.CreateBVConst(32, high), bm.CreateBVConst(32, low));
}

/* One step of the pseudo-inverse walk for an equality against a symbolic
 * term t. `u` holds the term this step's OUTPUT must equal; on success it
 * is replaced by the term the step's INPUT must equal, and the membership
 * condition on the old `u` (the invertibility condition) is appended to
 * `conds`.
 *
 * The conditions must characterise the COMPOSED chain's image exactly, so
 * a step whose preimage is not unique (its condition describes the image
 * of a FREE input, and its inverse picks one preimage of several) is only
 * admitted at the bottom of the chain, where its input really is the free
 * variable. Anywhere else the picked preimage could fall outside the
 * lower chain's image while another preimage lies inside it, and the
 * collected conditions would under-approximate membership -- losing
 * satisfying assignments. Bijective steps and injective-under-condition
 * steps (concat with a constant, sign/zero extension) compose exactly.
 *
 * Returns false when the step has no usable inverse here, or when it
 * collapses the image to a single value (such chains are constants and
 * belong to the factory, not to this rule).
 */
static bool invertStepSymbolic(NodeFactory* nf, STPMgr& bm, Simplifier* simp,
                               const GroundStep& s, bool isBottom, ASTNode& u,
                               ASTVec& conds)
{
  if (s.samePathAllOperands)
    return false;
  const unsigned w = s.outWidth;
  switch (s.kind)
  {
    case BVMULT:
    {
      // c = odd * 2^k. The odd factor is a bijection (invert with the
      // modular inverse, anywhere on the chain); the 2^k factor makes
      // the image exactly the multiples of 2^k, with the k low bits of
      // the preimage free -- so like the shifts it is bottom-only, with
      // the condition that u's k low bits are zero.
      const ASTNode& c = s.constants[0];
      const CBV cv = c.GetBVConst();
      if (CONSTANTBV::BitVector_is_empty(cv))
        return false; // image is {0}.
      unsigned k = 0;
      while (!CONSTANTBV::BitVector_bit_test(cv, k))
        k++;
      ASTNode oddPart = c;
      if (k > 0)
      {
        if (!isBottom)
          return false;
        CBV shifted = CONSTANTBV::BitVector_Create(w, true);
        CONSTANTBV::BitVector_Interval_Copy(shifted, cv, 0, k, w - k);
        oddPart = bm.CreateBVConst(shifted, w);
        conds.push_back(nf->CreateNode(EQ, mkExtract(nf, bm, u, k - 1, 0),
                                       bm.CreateZeroConst(k)));
        u = nf->CreateTerm(BVCONCAT, w, bm.CreateZeroConst(k),
                           mkExtract(nf, bm, u, w - 1, k));
      }
      u = nf->CreateTerm(BVMULT, w, simp->MultiplicativeInverse(oddPart), u);
      return true;
    }

    // Bijective: exact everywhere, no condition.
    case BVXOR:
      u = nf->CreateTerm(BVXOR, w, u, s.constants[0]);
      return true;
    case BVPLUS:
    {
      std::vector<CBV> a = {s.constants[0].GetBVConst()};
      CBV negC = NonMemberBVConstEvaluator(BVUMINUS, a, w);
      u = nf->CreateTerm(BVPLUS, w, u, bm.CreateBVConst(negC, w));
      return true;
    }
    case BVSUB:
      u = (s.pathIndex == 0)
              ? nf->CreateTerm(BVPLUS, w, u, s.constants[0])
              : nf->CreateTerm(BVSUB, w, s.constants[0], u);
      return true;
    case BVUMINUS:
    case BVNOT:
      u = nf->CreateTerm(s.kind, w, u);
      return true;

    // Injective under the condition: exact everywhere.
    case BVCONCAT:
    {
      const ASTNode& c = s.constants[0];
      const unsigned cW = c.GetValueWidth();
      if (s.pathIndex == 0) // x is the high slice, c the low.
      {
        conds.push_back(nf->CreateNode(EQ, mkExtract(nf, bm, u, cW - 1, 0), c));
        u = mkExtract(nf, bm, u, w - 1, cW);
      }
      else
      {
        conds.push_back(
            nf->CreateNode(EQ, mkExtract(nf, bm, u, w - 1, w - cW), c));
        u = mkExtract(nf, bm, u, w - cW - 1, 0);
      }
      return true;
    }
    case BVSX:
    {
      const ASTNode low = mkExtract(nf, bm, u, s.inWidth - 1, 0);
      conds.push_back(nf->CreateNode(
          EQ, u, nf->CreateTerm(BVSX, w, low, bm.CreateBVConst(32, w))));
      u = low;
      return true;
    }
    case BVZX:
    {
      conds.push_back(nf->CreateNode(
          EQ, mkExtract(nf, bm, u, w - 1, s.inWidth),
          bm.CreateZeroConst(w - s.inWidth)));
      u = mkExtract(nf, bm, u, s.inWidth - 1, 0);
      return true;
    }

    // Preimage not unique: bottom of the chain only.
    case BVAND:
    {
      const ASTNode& c = s.constants[0];
      if (!isBottom || CONSTANTBV::BitVector_is_empty(c.GetBVConst()))
        return false; // shared bits chosen below, or image is {0}.
      std::vector<CBV> a = {c.GetBVConst()};
      CBV notC = NonMemberBVConstEvaluator(BVNOT, a, w);
      conds.push_back(nf->CreateNode(
          EQ, nf->CreateTerm(BVAND, w, u, bm.CreateBVConst(notC, w)),
          bm.CreateZeroConst(w)));
      return true; // x := u reproduces u under the condition.
    }
    case BVOR:
    {
      const ASTNode& c = s.constants[0];
      if (!isBottom || CONSTANTBV::BitVector_is_full(c.GetBVConst()))
        return false;
      conds.push_back(
          nf->CreateNode(EQ, nf->CreateTerm(BVAND, w, u, c), c));
      return true; // x := u reproduces u under the condition.
    }
    case BVEXTRACT:
    {
      if (!isBottom)
        return false;
      const unsigned high = s.constants[0].GetUnsignedConst();
      const unsigned low = s.constants[1].GetUnsignedConst();
      if (low > 0)
        u = nf->CreateTerm(BVCONCAT, low + s.outWidth, u,
                           bm.CreateZeroConst(low));
      if (high + 1 < s.inWidth)
        u = nf->CreateTerm(BVCONCAT, s.inWidth,
                           bm.CreateZeroConst(s.inWidth - 1 - high), u);
      return true;
    }
    case BVMOD:
    {
      const ASTNode& c = s.constants[0];
      if (!isBottom || s.pathIndex != 0 ||
          CONSTANTBV::BitVector_is_empty(c.GetBVConst()) ||
          c == bm.CreateOneConst(w))
        return false; // x mod 0 / mod 1: leave to the factory.
      conds.push_back(nf->CreateNode(BVLT, u, c));
      return true; // x := u.
    }
    case BVDIV:
    {
      const ASTNode& c = s.constants[0];
      if (!isBottom || s.pathIndex != 0 ||
          CONSTANTBV::BitVector_is_empty(c.GetBVConst()))
        return false;
      // Bind the CreateMaxConst node: it is a temporary, and GetBVConst()
      // returns a pointer into it, so it must outlive the evaluator call
      // below -- otherwise a[0] dangles (a use-after-free).
      const ASTNode maxC = bm.CreateMaxConst(w);
      std::vector<CBV> a = {maxC.GetBVConst(), c.GetBVConst()};
      CBV maxQ = NonMemberBVConstEvaluator(BVDIV, a, w);
      const ASTNode maxQn = bm.CreateBVConst(maxQ, w);
      if (maxQn == bm.CreateZeroConst(w))
        return false; // image is {0}.
      conds.push_back(nf->CreateNode(BVLE, u, maxQn));
      u = nf->CreateTerm(BVMULT, w, u, c);
      return true;
    }
    case BVRIGHTSHIFT:
    case BVLEFTSHIFT:
    {
      const ASTNode& c = s.constants[0];
      if (s.pathIndex != 0 || c.GetValueWidth() > 32)
        return false;
      const unsigned k = c.GetUnsignedConst();
      if (k == 0)
        return true; // identity, bijective.
      if (!isBottom || k >= w)
        return false; // low/high bits chosen below, or image is {0}.
      if (s.kind == BVRIGHTSHIFT)
      {
        conds.push_back(nf->CreateNode(EQ, mkExtract(nf, bm, u, w - 1, w - k),
                                       bm.CreateZeroConst(k)));
        u = nf->CreateTerm(BVCONCAT, w, mkExtract(nf, bm, u, w - k - 1, 0),
                           bm.CreateZeroConst(k));
      }
      else
      {
        conds.push_back(nf->CreateNode(EQ, mkExtract(nf, bm, u, k - 1, 0),
                                       bm.CreateZeroConst(k)));
        u = nf->CreateTerm(BVCONCAT, w, bm.CreateZeroConst(k),
                           mkExtract(nf, bm, u, w - 1, k));
      }
      return true;
    }

    default:
      return false;
  }
}

// Two distinct chain outputs with the x values that achieve them, for the
// false branch of an equality collapse. Tries 0, each single bit, and all
// ones; returns false if every candidate evaluates alike.
static bool findTwoChainValues(const std::vector<GroundStep>& steps,
                               unsigned varWidth, STPMgr& bm, ASTNode& v1,
                               ASTNode& x1, ASTNode& v2, ASTNode& x2)
{
  const unsigned outW = steps.empty() ? varWidth : steps.back().outWidth;
  std::vector<CBV> xs;
  xs.push_back(CONSTANTBV::BitVector_Create(varWidth, true));
  for (unsigned i = 0; i < varWidth && i < 24; i++)
  {
    CBV c = CONSTANTBV::BitVector_Create(varWidth, true);
    CONSTANTBV::BitVector_Bit_On(c, i);
    xs.push_back(c);
  }
  CBV ones = CONSTANTBV::BitVector_Create(varWidth, false);
  CONSTANTBV::BitVector_Fill(ones);
  xs.push_back(ones);

  CBV firstV = evalChain(steps, xs[0]);
  bool found = false;
  for (size_t i = 1; i < xs.size() && !found; i++)
  {
    CBV v = evalChain(steps, xs[i]);
    if (CONSTANTBV::BitVector_Lexicompare(v, firstV) != 0)
    {
      v1 = bm.CreateBVConst(firstV, outW);
      x1 = bm.CreateBVConst(CONSTANTBV::BitVector_Clone(xs[0]), varWidth);
      v2 = bm.CreateBVConst(v, outW);
      x2 = bm.CreateBVConst(CONSTANTBV::BitVector_Clone(xs[i]), varWidth);
      found = true;
    }
    else
      CONSTANTBV::BitVector_Destroy(v);
  }
  if (!found)
    CONSTANTBV::BitVector_Destroy(firstV);
  for (CBV c : xs)
    CONSTANTBV::BitVector_Destroy(c);
  return found;
}

// Compare two chain outputs in the requested order.
static int cmpChainValue(const CBV a, const CBV b, bool isSigned, unsigned w)
{
  if (isSigned)
  {
    const bool sa = CONSTANTBV::BitVector_bit_test(a, w - 1);
    const bool sb = CONSTANTBV::BitVector_bit_test(b, w - 1);
    if (sa != sb)
      return sa ? -1 : 1;
  }
  return CONSTANTBV::BitVector_Lexicompare(a, b);
}

// The exact smallest and largest chain outputs in the requested order,
// with x values achieving them, by enumerating every value of a narrow
// free variable. Exactness matters: an under-approximated extreme would
// force the rewritten predicate below a value the original could reach,
// losing satisfying assignments.
static void enumerateChainExtremes(const std::vector<GroundStep>& steps,
                                   unsigned varWidth, bool isSigned, STPMgr& bm,
                                   ASTNode& mn, ASTNode& xmn, ASTNode& mx,
                                   ASTNode& xmx)
{
  const unsigned outW = steps.empty() ? varWidth : steps.back().outWidth;
  CBV x = CONSTANTBV::BitVector_Create(varWidth, true);
  CBV bestLo = NULL, bestHi = NULL, xLo = NULL, xHi = NULL;
  const uint64_t count = 1ULL << varWidth;
  for (uint64_t i = 0; i < count; i++)
  {
    CBV v = evalChain(steps, x);
    if (bestLo == NULL || cmpChainValue(v, bestLo, isSigned, outW) < 0)
    {
      if (bestLo != NULL)
      {
        CONSTANTBV::BitVector_Destroy(bestLo);
        CONSTANTBV::BitVector_Destroy(xLo);
      }
      bestLo = CONSTANTBV::BitVector_Clone(v);
      xLo = CONSTANTBV::BitVector_Clone(x);
    }
    if (bestHi == NULL || cmpChainValue(v, bestHi, isSigned, outW) > 0)
    {
      if (bestHi != NULL)
      {
        CONSTANTBV::BitVector_Destroy(bestHi);
        CONSTANTBV::BitVector_Destroy(xHi);
      }
      bestHi = CONSTANTBV::BitVector_Clone(v);
      xHi = CONSTANTBV::BitVector_Clone(x);
    }
    CONSTANTBV::BitVector_Destroy(v);
    CONSTANTBV::BitVector_increment(x);
  }
  CONSTANTBV::BitVector_Destroy(x);
  mn = bm.CreateBVConst(bestLo, outW);
  xmn = bm.CreateBVConst(xLo, varWidth);
  mx = bm.CreateBVConst(bestHi, outW);
  xmx = bm.CreateBVConst(xHi, varWidth);
}

/* A shared non-surjective single-step chain: t = op(x, c) has several
 * parents, so no predicate-level collapse is possible -- pinning x for
 * one consumer would change the others. But t's image is exactly and
 * cheaply expressible, so replace t ITSELF with a fresh variable v,
 * conjoin "v is in the image" onto the formula, and define x as a
 * projection of v:
 *
 *    exists x. phi(t(x))   <=>   exists v. v in Image(t)  /\  phi(v)
 *
 * e.g. shared (concat 0 x) becomes v with high bits pinned to zero and
 * x := extract(v). Consumers then see a variable, which the
 * symbol-keyed passes (equality propagation, the bit-vector solver, the
 * disjoint-extract splitter, later runs of this pass) can work with.
 *
 * Within this run, v is untouchable. The membership constraint is held
 * aside until the mutable tree is materialised, so the tree counts one
 * parent too few for v: once another rule replaces one of t's old
 * consumers, v looks single-use, and a per-kind rule would then give it
 * a witness value that the constraint excludes -- a wrong unsat.
 *
 * Note this rewrite satisfies equisatisfiability with model mapping (a
 * model of the result maps back through x := projection(v)), not the
 * stronger pointwise identity the constant-witness rules satisfy: off
 * the image, t(projection(v)) differs from v, which is exactly what the
 * conjoined constraint excludes.
 */
bool RemoveUnconstrained::tryImageConstrainShared(const ASTNode& var,
                                                  const ASTNode& sharedNode,
                                                  const GroundStep& step)
{
  if (step.samePathAllOperands)
    return false; // squares: image genuinely scattered

  const unsigned w = step.inWidth;
  const unsigned W = step.outWidth;

  const auto extractOf = [&](const ASTNode& n, unsigned high, unsigned low) {
    return nf->CreateTerm(BVEXTRACT, high - low + 1, n,
                          bm.CreateBVConst(32, high),
                          bm.CreateBVConst(32, low));
  };
  // A constant's value when it fits a machine word.
  const auto constToU64 = [](const ASTNode& n, uint64_t& out) {
    const CBV c = n.GetBVConst();
    if (CONSTANTBV::Set_Max(c) >= 32)
      return false;
    out = ((unsigned*)c)[0];
    return true;
  };

  ASTNode v = bm.CreateFreshVariable(0, W, "unconstrained_image");
  ASTNode constraint, projection;

  switch (step.kind)
  {
    case BVCONCAT:
    {
      const ASTNode c = step.constants[0];
      const unsigned cw = c.GetValueWidth();
      if (step.pathIndex == 1) // c ++ x: the high bits equal c
      {
        constraint = nf->CreateNode(EQ, extractOf(v, W - 1, w), c);
        projection = extractOf(v, w - 1, 0);
      }
      else // x ++ c: the low bits equal c
      {
        constraint = nf->CreateNode(EQ, extractOf(v, cw - 1, 0), c);
        projection = extractOf(v, W - 1, cw);
      }
      break;
    }

    case BVZX:
    {
      if (W == w)
        return false;
      constraint =
          nf->CreateNode(EQ, extractOf(v, W - 1, w), bm.CreateZeroConst(W - w));
      projection = extractOf(v, w - 1, 0);
      break;
    }

    case BVSX:
    {
      if (W == w)
        return false;
      // The image is the fixed points of re-extension.
      projection = extractOf(v, w - 1, 0);
      constraint = nf->CreateNode(
          EQ, v,
          nf->CreateTerm(BVSX, W, projection, bm.CreateBVConst(32, W)));
      break;
    }

    case BVMULT:
    {
      // c = 2^s * o with o odd and s > 0 (odd constants are bijective
      // and consumed by the per-kind rule): the image is the multiples
      // of 2^s, and x = (v >> s) * o^-1 inverts it.
      const CBV c = step.constants[0].GetBVConst();
      if (CONSTANTBV::BitVector_is_empty(c))
        return false;
      const unsigned s = (unsigned)CONSTANTBV::Set_Min(c);
      if (s == 0)
        return false;
      CBV oc = CONSTANTBV::BitVector_Create(W, true);
      CONSTANTBV::BitVector_Interval_Copy(oc, c, 0, s, W - s);
      const ASTNode oInv =
          simplifier->MultiplicativeInverse(bm.CreateBVConst(oc, W));
      constraint = nf->CreateNode(EQ, extractOf(v, s - 1, 0),
                                  bm.CreateZeroConst(s));
      projection = nf->CreateTerm(
          BVMULT, W, oInv,
          nf->CreateTerm(BVRIGHTSHIFT, W, v, bm.CreateBVConst(W, s)));
      break;
    }

    case BVLEFTSHIFT:
    {
      uint64_t k;
      if (step.pathIndex != 0 || !constToU64(step.constants[0], k) || k == 0 ||
          k >= W)
        return false;
      constraint = nf->CreateNode(EQ, extractOf(v, (unsigned)k - 1, 0),
                                  bm.CreateZeroConst((unsigned)k));
      projection = nf->CreateTerm(BVRIGHTSHIFT, W, v, step.constants[0]);
      break;
    }

    case BVRIGHTSHIFT:
    {
      uint64_t k;
      if (step.pathIndex != 0 || !constToU64(step.constants[0], k) || k == 0 ||
          k >= W)
        return false;
      constraint = nf->CreateNode(EQ, extractOf(v, W - 1, W - (unsigned)k),
                                  bm.CreateZeroConst((unsigned)k));
      projection = nf->CreateTerm(BVLEFTSHIFT, W, v, step.constants[0]);
      break;
    }

    case BVAND:
    {
      // A low mask behaves as mod 2^kb: high bits zero, x := v.
      const CBV c = step.constants[0].GetBVConst();
      if (CONSTANTBV::BitVector_is_empty(c) ||
          CONSTANTBV::BitVector_is_full(c))
        return false;
      const unsigned kb = (unsigned)CONSTANTBV::Set_Max(c) + 1;
      CBV lowMask = CONSTANTBV::BitVector_Create(W, true);
      CONSTANTBV::BitVector_Interval_Fill(lowMask, 0, kb - 1);
      const bool isLowMask = CONSTANTBV::BitVector_equal(c, lowMask);
      CONSTANTBV::BitVector_Destroy(lowMask);
      if (!isLowMask || kb >= W)
        return false;
      constraint = nf->CreateNode(EQ, extractOf(v, W - 1, kb),
                                  bm.CreateZeroConst(W - kb));
      projection = v;
      break;
    }

    case BVMOD:
    {
      const ASTNode c = step.constants[0];
      if (step.pathIndex != 0 ||
          CONSTANTBV::BitVector_is_empty(c.GetBVConst()))
        return false;
      constraint = nf->CreateNode(BVLT, v, c);
      projection = v;
      break;
    }

    case BVDIV:
    {
      const ASTNode c = step.constants[0];
      if (step.pathIndex != 0 ||
          CONSTANTBV::BitVector_is_empty(c.GetBVConst()))
        return false;
      // Image is [0, allones / c]; x = v * c re-divides to v within it.
      std::vector<CBV> args = {nullptr, nullptr};
      CBV ones = CONSTANTBV::BitVector_Create(W, true);
      CONSTANTBV::BitVector_Fill(ones);
      args[0] = ones;
      args[1] = c.GetBVConst();
      CBV q = NonMemberBVConstEvaluator(BVDIV, args, W);
      CONSTANTBV::BitVector_Destroy(ones);
      constraint = nf->CreateNode(BVLE, v, bm.CreateBVConst(q, W));
      projection = nf->CreateTerm(BVMULT, W, v, c);
      break;
    }

    default:
      return false;
  }

  assert(projection.GetValueWidth() == var.GetValueWidth());
  assert(passUntouchable != NULL);
  passUntouchable->insert(v);
  splice(sharedNode, v);
  replace(var, projection);
  imageConstraints.push_back(constraint);
  imageConstraintsMade++;
  return true;
}

/* When none of the per-kind rules fired for `var` (each detaches the
 * variable when it does), generalise: climb from the variable towards the
 * root while every node on the way is single-use and every sibling is a
 * constant. The first boolean-valued node reached is then a predicate over
 * a function of the variable alone -- e.g. ((x mod 100) + 7 >u 50) -- even
 * though no individual operation on the path has (or could have) a rule of
 * its own. AchievableImage tracks which values the chain can produce; if
 * the predicate can be made both true and false, it is replaced by a fresh
 * boolean v with var := ITE(v, w_true, w_false) recorded, exactly like the
 * direct EQ rule.
 *
 * Term-level ITEs may sit on the path with non-ground conditions and
 * other branches: the predicate distributes over each,
 *   P(g(ite(c, f(x), t)))  ==>  ite(c, v, P(g(t))),
 * applied per frame from the innermost out, so a stack of selects
 * becomes a nest of boolean ITEs with one rebuilt predicate per frame
 * (linear growth, capped). x's definition is sound regardless of the
 * conditions, since x only influences the formula when every frame
 * selects its branch.
 *
 * The interior nodes must be single-use: a second use of any node on the
 * path would survive the rewrite and be forced to the witness values,
 * changing its meaning. The predicate node itself may be shared, since
 * under the recorded definition every occurrence of it evaluates to v
 * (or to the distributed ITE, which is a pure equivalence).
 */
bool RemoveUnconstrained::tryGroundPathCollapse(const ASTNode& var)
{
  if (var.GetValueWidth() == 0 || var.GetIndexWidth() != 0)
    return false;

  // Phase 1: collect the path structurally, up to the predicate. Knowing
  // the predicate's constant before the image is built lets it be used as
  // a seed hint when the image degrades to samples.
  std::vector<GroundStep> steps;
  ASTNode predicate;
  Kind predKind = UNDEFINED;
  bool pathFirst = false;
  ASTNode predConst;
  ASTNode predOther; // set instead when the side is symbolic.

  // ITE frames on the path, innermost first. Each frame costs one
  // rebuilt predicate around its other branch, so growth is linear in
  // the frame count; the cap bounds it.
  struct IteFrame
  {
    ASTNode cond;
    ASTNode other;
    bool pathThen;
    size_t stepsBelow;
  };
  const size_t MAX_ITE_FRAMES = 4;
  std::vector<IteFrame> frames;

  ASTNode cur = var;
  ASTVec kids;
  for (unsigned depth = 0; depth < AchievableImage::MAX_PATH; depth++)
  {
    ASTNode p;
    if (!singleParent(cur, p))
      return false;
    // Normalised, so that the grandparent's (normalised) children name
    // it by the same handle when the walk compares them.
    p = g->normalise(p);
    kidsOf(p, kids);

    if (p.GetValueWidth() == 0)
    {
      // Boolean level: a predicate between the chain and either a
      // constant or -- for the invertibility-condition collapse -- any
      // term (the single-use x cannot occur inside the other side).
      if (!AchievableImage::predicateKind(p.GetKind()) || kids.size() != 2)
        return false;
      pathFirst = (kids[0] == cur);
      if (kids[0] == kids[1] || (!pathFirst && kids[1] != cur))
        return false;
      const ASTNode otherN = pathFirst ? kids[1] : kids[0];
      if (otherN.GetValueWidth() != cur.GetValueWidth())
        return false;
      predicate = p;
      predKind = p.GetKind();
      if (otherN.isConstant())
        predConst = otherN;
      else
        predOther = otherN;
      break;
    }

    // Term level: one path child, constants everywhere else.
    const Kind kind = p.GetKind();

    if (kind == ITE && p.GetValueWidth() > 0)
    {
      // Capture a distribution frame and keep climbing; the ITE
      // contributes no image step (on x's branch it is the identity).
      if (frames.size() >= MAX_ITE_FRAMES || p.GetIndexWidth() != 0 ||
          kids.size() != 3)
        return false;
      const bool inThen = (kids[1] == cur);
      if ((!inThen && kids[2] != cur) || kids[1] == kids[2] || kids[0] == cur)
        return false;
      frames.push_back(
          {kids[0], inThen ? kids[2] : kids[1], inThen, steps.size()});
      ASTNode pp;
      if (!singleParent(p, pp))
      {
        blockedOn[p.GetNodeNum()].push_back(var);
        return false;
      }
      cur = p;
      continue;
    }

    if (!AchievableImage::handledKind(kind))
      return false;

    size_t pathCount = 0, pathIdx = 0;
    bool nonConstSibling = false;
    for (size_t i = 0; i < kids.size(); i++)
    {
      if (kids[i] == cur)
      {
        pathCount++;
        pathIdx = i;
      }
      else if (!kids[i].isConstant())
        nonConstSibling = true;
    }
    if (nonConstSibling)
      return false;
    // Both operands being the path -- (bvmul t t), squaring -- is still
    // a unary function of the path value; anything else duplicated is
    // not a chain.
    const bool samePathAllOperands = (pathCount == 2 && kids.size() == 2);
    if (pathCount != 1 && !samePathAllOperands)
      return false;

    GroundStep step;
    step.kind = kind;
    step.outWidth = p.GetValueWidth();
    step.inWidth = cur.GetValueWidth();

    if (samePathAllOperands)
    {
      step.samePathAllOperands = true;
      step.pathIndex = 0;
    }
    else if (kind == BVSX || kind == BVZX)
    {
      // The second child is the width constant; the evaluator takes the
      // width from outWidth instead.
      if (pathIdx != 0)
        return false;
      step.pathIndex = 0;
    }
    else if (kind == BVEXTRACT)
    {
      if (pathIdx != 0)
        return false;
      step.pathIndex = 0;
      step.constants.push_back(kids[1]);
      step.constants.push_back(kids[2]);
    }
    else if (kind == BVPLUS || kind == BVMULT || kind == BVAND ||
             kind == BVOR || kind == BVXOR)
    {
      // n-ary and commutative: fold the constant siblings into one.
      // (Don't assume an earlier factory folded them; inputs can come
      // through the hashing factory.)
      if (kids.size() == 2)
      {
        step.pathIndex = pathIdx;
        step.constants.push_back(kids[1 - pathIdx]);
      }
      else
      {
        std::vector<CBV> consts;
        for (size_t i = 0; i < kids.size(); i++)
          if (i != pathIdx)
            consts.push_back(kids[i].GetBVConst());
        CBV folded = NonMemberBVConstEvaluator(kind, consts, step.outWidth);
        step.pathIndex = 0;
        step.constants.push_back(bm.CreateBVConst(folded, step.outWidth));
      }
    }
    else
    {
      // Binary, position matters.
      if (kids.size() != 2)
        return false;
      step.pathIndex = pathIdx;
      step.constants.push_back(kids[1 - pathIdx]);
    }

    steps.push_back(step);

    // Interior nodes must be single-use to step past them. A shared
    // single-step chain may still be eliminated by constraining a fresh
    // variable to its image.
    ASTNode pp;
    if (!singleParent(p, pp))
    {
      if (bm.UserFlags.unconstrained_image_vars && steps.size() == 1 &&
          frames.empty())
        return tryImageConstrainShared(var, p, steps[0]);
      blockedOn[p.GetNodeNum()].push_back(var);
      return false;
    }
    cur = p;
  }
  if (predicate.IsNull())
    return false; // too deep

  if (!predOther.IsNull())
  {
    /* The other side is symbolic, so achievability cannot be decided
     * statically; instead the predicate is rewritten into its
     * invertibility condition -- a predicate over t alone -- joined with
     * a fresh boolean, and x is defined to realise whichever truth value
     * the rewritten predicate takes:
     *
     *   (= (bvand x c) t)   ==>  (and (= (bvand t (bvnot c)) 0) b)
     *   (bvugt (f x) t)     ==>  (and (bvugt M t) (or b (bvugt m t)))
     *
     * with x := ITE(newP, x_true, x_false). For an equality the true
     * witness is the chain's pseudo-inverse applied to t (the collected
     * conditions state exactly that t is in the chain's image); for a
     * comparison the witnesses are the x values reaching the chain's
     * smallest and largest output m/M in the predicate's order, found by
     * exhaustive enumeration of a narrow x. The rewrite is a pointwise
     * function equality -- P(f(x_def), t) == newP for every valuation of
     * t's variables and b -- so it holds in any polarity and under
     * shared predicates, exactly like the fresh-boolean EQ rule.
     */
    const unsigned varW = var.GetValueWidth();
    const unsigned MAX_ENUM_WIDTH = 12;

    // If the other side holds an unconstrained variable of its own, an
    // elimination from that side (e.g. the EQ rule) collapses the whole
    // predicate to a bare boolean -- strictly better than this rewrite,
    // which copies t into the invertibility condition and by that extra
    // use would destroy the other side's unconstrainedness. Defer.
    {
      std::vector<ASTNode> otherVars;
      variablesIn(predOther, otherVars);
      bool deferred = false;
      for (const ASTNode& ov : otherVars)
        if (unconstrained(ov))
        {
          deferredOn[ov.GetNodeNum()].push_back(var);
          deferred = true;
        }
      if (deferred)
        return false;
    }

    // t as a graph handle, for what goes back into the formula.
    const ASTNode t = predOther;
    ASTNode newP, xDef;

    if (predKind == EQ)
    {
      ASTVec conds;
      ASTNode u = t;
      bool ok = true;
      for (size_t i = steps.size(); i-- > 0 && ok;)
        ok = invertStepSymbolic(gf, bm, simplifier, steps[i],
                                /*isBottom=*/i == 0, u, conds);
      ASTNode v1, x1, v2, x2;
      if (ok)
        ok = findTwoChainValues(steps, varW, bm, v1, x1, v2, x2);
      if (!ok)
        return false;

      const ASTNode b = bm.CreateFreshVariable(0, 0, "unconstrained_ic");
      conds.push_back(b);
      newP = (conds.size() == 1) ? b : gf->CreateNode(AND, conds);
      // The definition is recorded over hash-consed terms.
      const ASTNode tExp = exported(t);
      const ASTNode xAlt =
          nf->CreateTerm(ITE, varW, nf->CreateNode(EQ, tExp, v1), x2, x1);
      xDef = nf->CreateTerm(ITE, varW, exported(newP), exported(u), xAlt);
    }
    else
    {
      if (varW > MAX_ENUM_WIDTH)
        return false;
      const bool isSigned = (predKind == BVSGT || predKind == BVSGE ||
                             predKind == BVSLT || predKind == BVSLE);
      ASTNode m, xm, M, xM;
      enumerateChainExtremes(steps, varW, isSigned, bm, m, xm, M, xM);

      const auto mkP = [&](const ASTNode& v) {
        return pathFirst ? gf->CreateNode(predKind, v, t)
                         : gf->CreateNode(predKind, t, v);
      };
      // As a function of the chain's value, the predicate is monotone;
      // vTop maximises it and vBot minimises it, so P(vTop) is the
      // invertibility condition and P(vBot) forces truth when even the
      // minimising witness satisfies the predicate.
      const bool greater = (predKind == BVGT || predKind == BVGE ||
                            predKind == BVSGT || predKind == BVSGE);
      const bool increasing = (greater == pathFirst);
      const ASTNode& vTop = increasing ? M : m;
      const ASTNode& vBot = increasing ? m : M;
      const ASTNode& xTop = increasing ? xM : xm;
      const ASTNode& xBot = increasing ? xm : xM;

      const ASTNode b = bm.CreateFreshVariable(0, 0, "unconstrained_ic");
      newP =
          gf->CreateNode(AND, mkP(vTop), gf->CreateNode(OR, b, mkP(vBot)));
      xDef = nf->CreateTerm(ITE, varW, exported(newP), xTop, xBot);
    }

    // Distribute over any captured ITE frames with the rewritten
    // predicate as the innermost leaf, then splice it in. The frames'
    // conditions and other branches are graph handles, so the splice
    // reuses them as they are.
    ASTNode inner = newP;
    for (const IteFrame& fr : frames)
    {
      ASTNode gt = fr.other;
      for (size_t i = fr.stepsBelow; i < steps.size(); i++)
        gt = applyStepToNode(gf, bm, steps[i], gt);
      const ASTNode elseP = pathFirst ? gf->CreateNode(predKind, gt, t)
                                      : gf->CreateNode(predKind, t, gt);
      inner = gf->CreateNode(ITE, fr.cond, fr.pathThen ? inner : elseP,
                             fr.pathThen ? elseP : inner);
    }

    splice(predicate, inner);
    replace(var, xDef);
    if (bm.UserFlags.stats_flag)
    {
      std::cerr << "{RemoveUnconstrained} symbolic-side collapse: " << predKind
                << " over";
      for (const GroundStep& s : steps)
        std::cerr << " " << s.kind;
      std::cerr << (steps.empty() ? " the bare variable" : "") << std::endl;
    }
    return true;
  }

  // Phase 2: flow the achievable image up the collected path and decide.
  AchievableImage image(bm, var.GetValueWidth());
  image.addHintChain(steps, predConst);
  for (const GroundStep& step : steps)
    if (!image.apply(step))
      return false;

  AchievableImage::Decision d = image.decide(predKind, pathFirst, predConst);
  if (!d.collapse)
    return false;

  if (frames.empty())
  {
    // The predicate has width 0, so this creates a fresh boolean and
    // prunes the whole path out of the formula.
    ASTNode v = replaceWithFresh(predicate);
    replace(var, nf->CreateTerm(ITE, var.GetValueWidth(), v, d.witnessTrue,
                                d.witnessFalse));
    return true;
  }

  // Distribute the predicate over the captured frames, innermost out:
  //   P(...ite(c_i, path_i, t_i)...)
  //     ==>  ite(c_k, ... ite(c_1, v, P(above_1(t_1))) ..., P(above_k(t_k)))
  // where above_i re-applies every ground step recorded above frame i.
  ASTNode v = bm.CreateFreshVariable(0, 0, "unconstrained_ite");
  ASTNode inner = v;
  for (const IteFrame& fr : frames)
  {
    ASTNode gt = fr.other;
    for (size_t i = fr.stepsBelow; i < steps.size(); i++)
      gt = applyStepToNode(gf, bm, steps[i], gt);
    ASTNode elseP = pathFirst ? gf->CreateNode(predKind, gt, predConst)
                              : gf->CreateNode(predKind, predConst, gt);
    inner = gf->CreateNode(ITE, fr.cond, fr.pathThen ? inner : elseP,
                           fr.pathThen ? elseP : inner);
  }

  splice(predicate, inner);
  replace(var, nf->CreateTerm(ITE, var.GetValueWidth(), v, d.witnessTrue,
                              d.witnessFalse));
  return true;
}

ASTNode RemoveUnconstrained::topLevel_other(const ASTNode& n,
                                            Simplifier* simplifier)
{
  if (n.GetKind() == SYMBOL)
    return n; // top level is an unconstrained symbol/.

  this->simplifier = simplifier;

  imageConstraints.clear();
  imageConstraintsMade = 0;

  MutableGraph graph(bm);
  graph.import(n);
  if (checkGraph)
    std::cerr << "  [ru] start, root " << n.GetNodeNum() << std::endl;
  g = &graph;
  gf = &graph.factory();

  // Every symbol, parents before children (the reverse of a post-order
  // walk), so that given (F(x_1,... x_10000) = v) with v unconstrained the
  // whole of F is chopped out before its variables are examined.
  worklist.clear();
  deferredOn.clear();
  blockedOn.clear();
  {
    std::vector<ASTNode> post;
    ASTNodeSet seen;
    struct Frame
    {
      ASTNode node;
      size_t next = 0;
    };
    std::vector<Frame> stack;
    stack.push_back({n});
    seen.insert(n);
    while (!stack.empty())
    {
      Frame& f = stack.back();
      if (f.next < f.node.Degree())
      {
        const ASTNode c = f.node[f.next++];
        if (seen.insert(c).second)
          stack.push_back({c});
        continue;
      }
      if (f.node.GetKind() == SYMBOL)
        post.push_back(f.node);
      stack.pop_back();
    }
    worklist.assign(post.rbegin(), post.rend());
  }
  graph.clearChanges();

  // We don't want to check some expensive nodes over and over again.
  ASTNodeSet noCheck;

  // Candidates are appended while the loop runs; each is examined once
  // per time it was put on the list, in the order it was put there.
  for (size_t i = 0; i < worklist.size(); i++)
  {
    const ASTNode var = worklist[i];
    assert(var.GetKind() == SYMBOL);

    if (!unconstrained(var))
      continue;

    ASTNode parent;
    singleParent(var, parent);
    // As the graph sees it: a parent standing above an earlier
    // replacement is converted, so its children, and every comparison of
    // handles below, are current.
    parent = g->normalise(parent);
    if (checkGraph)
      std::cerr << "  [ru] examine " << var.GetNodeNum() << " under "
                << parent.GetNodeNum() << " kind " << parent.GetKind()
                << std::endl;

    if (noCheck.find(parent) != noCheck.end())
      continue;

    ASTVec children;
    kidsOf(parent, children);

    const size_t numberOfChildren = children.size();
    const Kind kind = parent.GetKind();
    unsigned width = parent.GetValueWidth();
    unsigned indexWidth = parent.GetIndexWidth();

    ASTNode other;

    if (numberOfChildren == 2)
    {
      if (children[0] != var)
        other = children[0];
      else
        other = children[1];

      if (kind != AND && kind != OR && kind != BVOR && kind != BVAND &&
          other == var)
      {
        continue; // Most rules don't like duplicate variables.
      }
    }
    else
    {
      if (kind != AND && kind != OR && kind != BVOR && kind != BVAND)
      {
        size_t found = 0;
        for (size_t j = 0; j < numberOfChildren; j++)
        {
          if (children[j] == var)
            found++;
        }

        if (found != 1)
          continue; // Most rules don't like duplicate variables.
      }
    }

    switch (kind)
    {
      case BVCONCAT:
      {
        assert(numberOfChildren == 2);
        if (unconstrained(children[0]) && unconstrained(children[1]))
        {
          ASTNode v = replaceWithFresh(parent);

          ASTNode top_lhs = bm.CreateBVConst(32, width - 1);
          ASTNode bottom_lhs =
              bm.CreateBVConst(32, children[1].GetValueWidth());

          ASTNode top_rhs =
              bm.CreateBVConst(32, children[1].GetValueWidth() - 1);
          ASTNode bottom_rhs = bm.CreateBVConst(32, 0);

          ASTNode lhs = nf->CreateTerm(BVEXTRACT, children[0].GetValueWidth(),
                                       v, top_lhs, bottom_lhs);
          ASTNode rhs = nf->CreateTerm(BVEXTRACT, children[1].GetValueWidth(),
                                       v, top_rhs, bottom_rhs);

          replace(children[0], lhs);
          replace(children[1], rhs);
        }
      }
      break;

      case NOT:
      {
        ASTNode v = replaceWithFresh(parent);
        replace(children[0], nf->CreateNode(NOT, v));
      }
      break;

      case BVUMINUS:
      case BVNOT:
      {
        assert(numberOfChildren == 1);
        ASTNode v = replaceWithFresh(parent);
        replace(var, nf->CreateTerm(kind, width, v));
      }
      break;

      case BVSGT:
      case BVSGE:
      case BVGT:
      case BVGE:
      {
        width = var.GetValueWidth();
        if (width == 1)
          break; // Hard to get right here; the ground-path collapse
                 // below handles the width-1 case.

        ASTNode biggestNumber, smallestNumber;

        if (kind == BVSGT || kind == BVSGE)
        {
          // 011111111 (most positive number.)
          CBV max = CONSTANTBV::BitVector_Create(width, false);
          CONSTANTBV::BitVector_Fill(max);
          CONSTANTBV::BitVector_Bit_Off(max, width - 1);
          biggestNumber = bm.CreateBVConst(max, width);

          // 1000000000 (most negative number.)
          max = CONSTANTBV::BitVector_Create(width, true);
          CONSTANTBV::BitVector_Bit_On(max, width - 1);
          smallestNumber = bm.CreateBVConst(max, width);
        }
        else
        {
          assert(kind == BVGT || kind == BVGE);
          biggestNumber = bm.CreateMaxConst(width);
          smallestNumber = bm.CreateZeroConst(width);
        }

        ASTNode c1, c2;
        if (kind == BVSGT || kind == BVGT)
        {
          c1 = biggestNumber;
          c2 = smallestNumber;
        }
        else
        {
          assert(kind == BVSGE || kind == BVGE);
          c1 = smallestNumber;
          c2 = biggestNumber;
        }

        if (unconstrained(children[0]) && unconstrained(children[1]))
        {
          ASTNode v = replaceWithFresh(parent);

          ASTNode lhs = nf->CreateTerm(ITE, width, v, bm.CreateOneConst(width),
                                       bm.CreateZeroConst(width));
          ASTNode rhs = nf->CreateTerm(ITE, width, v, bm.CreateZeroConst(width),
                                       bm.CreateOneConst(width));
          replace(children[0], lhs);
          replace(children[1], rhs);
        }
        else if (children[0] == var && children[1].isConstant())
        {
          if (children[1] == c1)
            continue; // always false. Or always false.

          ASTNode v = replaceWithFresh(parent);

          ASTNode rhs =
              nf->CreateTerm(ITE, width, v, biggestNumber, smallestNumber);
          replace(var, rhs);
        }
        else if (children[1] == var && children[0].isConstant())
        {
          if (children[0] == c2)
            continue; // always false. Or always false.

          ASTNode v = replaceWithFresh(parent);

          ASTNode rhs =
              nf->CreateTerm(ITE, width, v, smallestNumber, biggestNumber);
          replace(var, rhs);
        }
        else // One side is a variable. The other is anything.
        {
          bool varOnLHS = (var == children[0]);

          ASTNode v = bm.CreateFreshVariable(0, 0, "STP_INTERNAL_comparison");

          // The definition, over hash-consed terms; and the predicate that
          // replaces the comparison, over the sibling as it is in the graph.
          ASTNode rhs;
          ASTNode pred;
          if (varOnLHS)
          {
            rhs = nf->CreateTerm(ITE, width, v, biggestNumber, smallestNumber);

            if (kind == BVSGE || kind == BVGE)
              pred = gf->CreateNode(OR, v, gf->CreateNode(EQ, children[1], c1));
            else
              pred = gf->CreateNode(
                  AND, v,
                  gf->CreateNode(NOT, gf->CreateNode(EQ, children[1], c1)));
          }
          else
          {
            rhs = nf->CreateTerm(ITE, width, v, smallestNumber, biggestNumber);

            if (kind == BVSGE || kind == BVGE)
              pred = gf->CreateNode(OR, v, gf->CreateNode(EQ, children[0], c2));
            else
              pred = gf->CreateNode(
                  AND, v,
                  gf->CreateNode(NOT, gf->CreateNode(EQ, children[0], c2)));
          }
          replace(var, rhs);
          splice(parent, pred);
        }
      }
      break;

      case FP_GT:
      {
        // fp.gt over an unconstrained float, handled here while the
        // comparison is still one source node and the variable one use --
        // after FloatBlast the variable feeds its unpack circuit many times
        // over and stops looking unconstrained. The witnesses are IEEE's
        // extremes: NaN makes any ordered comparison false, and an infinity
        // of the right sign makes fp.gt true whenever any value can.
        if (numberOfChildren != 2)
          break;

        const SourceSort sort = var.GetSourceSort();
        if (sort.kind() != SourceSort::Kind::FloatingPoint)
          break;

        const unsigned exp_width = sort.exponentWidth();
        const unsigned sig_width = sort.significandWidth();

        width = var.GetValueWidth();

        // NaN and the infinities intern canonically (CreateFPConst funnels
        // every NaN payload to the one quiet NaN), so recognising them in a
        // constant operand is node identity.
        const ASTNode nan =
            bm.CreateFPSpecialConst(FPSpecial::NaN, exp_width, sig_width);

        if (unconstrained(children[0]) && unconstrained(children[1]) &&
            children[0].GetSourceSort() == children[1].GetSourceSort())
        {
          // x > y: true via (+oo, +0), false via (NaN, NaN).
          ASTNode v = replaceWithFresh(parent);
          replace(children[0],
                  nf->CreateTerm(ITE, width, v,
                                 bm.CreateFPSpecialConst(
                                     FPSpecial::PlusInfinity, exp_width,
                                     sig_width),
                                 nan));
          replace(children[1],
                  nf->CreateTerm(ITE, width, v,
                                 bm.CreateFPSpecialConst(FPSpecial::PlusZero,
                                                         exp_width, sig_width),
                                 nan));
        }
        else if (other.GetSourceSort() == sort)
        {
          // FP constant folding is deferred solver-wide, so a literal
          // usually arrives as to_fp's three-child reinterpret form over
          // constant bits, not as an interned constant. Resolve it locally,
          // through the canonicalising funnel (CreateFPConst), so NaN
          // payloads compare by node identity below. `other` itself is not
          // rewritten; it leaves the formula along with the predicate.
          ASTNode constant = other;
          if (constant.GetKind() == FP_TOFP && constant.Degree() == 3 &&
              g->current(constant[2]).GetKind() == BVCONST)
            constant =
                bm.CreateFPConst(g->current(constant[2]), exp_width, sig_width);

          if (!constant.isConstant())
            break;

          const bool varOnLHS = (children[0] == var);

          // The constant the variable's side cannot beat: nothing exceeds
          // +oo (variable on the left), nothing lies below -oo (variable on
          // the right) -- and nothing compares to NaN.
          const ASTNode unbeatable = bm.CreateFPSpecialConst(
              varOnLHS ? FPSpecial::PlusInfinity : FPSpecial::MinusInfinity,
              exp_width, sig_width);

          if (constant == nan || constant == unbeatable)
            continue; // Always false; the blasted circuit collapses it.

          // Both outcomes achievable: the variable's own extreme wins,
          // NaN loses.
          ASTNode v = replaceWithFresh(parent);
          replace(var, nf->CreateTerm(ITE, width, v, unbeatable, nan));
        }
      }
      break;

      case FP_DIV:
      {
        // A division whose divisor is unconstrained, rounded down into a
        // narrower format:
        //
        //   to_fp[te,ts](RNE, fp.div(RNE, to_fp[se,ss](rm, x), u))
        //
        // takes every value of the narrow format as u ranges, provided the
        // source format out-resolves the target one
        // (narrowingAbsorbsDivisorGrid). For finite non-zero x the witness
        // u0 = fl_src(x/t) reaches any finite target t: u0 is off from x/t
        // by one part in 2^(ss-1), dividing by it costs one more, and the
        // narrowing rounds an error that small back onto t. IEEE's special
        // quotients (x/±0, x/±oo, x/NaN) supply the extremes. When x itself
        // is NaN, zero or infinite the quotient is pinned to NaN, {±0, NaN}
        // or {±oo, NaN} -- the free divisor sign still picks the sign, but
        // the magnitude cannot leave the class -- so the stand-in is a
        // fresh variable filtered through x's classification.
        //
        // The narrowing is essential, not decoration: at the division's own
        // format the reachable quotient grid has holes no divisor fills, so
        // this arm keys on the divisor and then insists on the conversion
        // above it. Like FP_GT this must run while the division is one
        // source node and the divisor one use -- after lowering the divisor
        // feeds its unpack circuit many times over and stops looking
        // unconstrained.
        //
        // Only round-to-nearest-even instances have been verified
        // (exhaustively at small formats, and by re-evaluating witnesses at
        // binary32/binary64), so both rounding modes must be that constant;
        // directed modes would need their own verification first.

        if (numberOfChildren != 3 || children[2] != var)
          break;

        const ASTNode rm = children[0];
        if (!isRNEConstant(rm))
          break;

        ASTNode narrow;
        if (!singleParent(parent, narrow))
          break;
        narrow = g->normalise(narrow);
        ASTVec narrowKids;
        kidsOf(narrow, narrowKids);
        if (narrow.GetKind() != FP_TOFP || narrowKids.size() != 4 ||
            narrowKids[3] != parent || !isRNEConstant(narrowKids[2]))
          break;

        const ASTNode widen = children[1];
        ASTVec widenKids;
        kidsOf(widen, widenKids);
        if (widen.GetKind() != FP_TOFP || widenKids.size() != 4)
          break;

        const unsigned te = narrowKids[0].GetUnsignedConst();
        const unsigned ts = narrowKids[1].GetUnsignedConst();
        const unsigned se = widenKids[0].GetUnsignedConst();
        const unsigned ss = widenKids[1].GetUnsignedConst();

        // The numerator must be a widening from exactly the result's
        // format: that is what keeps the witness quotient x/t inside the
        // source format's normal range.
        const ASTNode x = widenKids[3];
        if (x.GetExpWidth() != te || x.GetSigWidth() != ts)
          break;

        const SourceSort usort = var.GetSourceSort();
        if (usort.kind() != SourceSort::Kind::FloatingPoint ||
            usort.exponentWidth() != se || usort.significandWidth() != ss)
          break;

        if (!narrowingAbsorbsDivisorGrid(se, ss, te, ts))
          break;

        const unsigned tw = te + ts;
        const unsigned sw = se + ss;

        ASTNode v = bm.CreateFreshVariable(0, tw, "unconstrained");
        v.SetExpWidth(te);
        v.SetSigWidth(ts);

        const ASTNode nanT = bm.CreateFPSpecialConst(FPSpecial::NaN, te, ts);

        // The stand-in, over x as it is in the graph: v, confined to the
        // class a special numerator pins.
        {
          const ASTNode isZeroX = gf->CreateNode(FP_ISZERO, x);
          const ASTNode isInfX = gf->CreateNode(FP_ISINFINITE, x);
          const ASTNode vIfZero = gf->CreateTerm(
              ITE, tw,
              gf->CreateNode(OR, gf->CreateNode(FP_ISZERO, v),
                             gf->CreateNode(FP_ISNAN, v)),
              v, nanT);
          const ASTNode vIfInf = gf->CreateTerm(
              ITE, tw,
              gf->CreateNode(OR, gf->CreateNode(FP_ISINFINITE, v),
                             gf->CreateNode(FP_ISNAN, v)),
              v, nanT);
          const ASTNode replacement = gf->CreateTerm(
              ITE, tw, gf->CreateNode(FP_ISNAN, x), nanT,
              gf->CreateTerm(ITE, tw, isZeroX, vIfZero,
                             gf->CreateTerm(ITE, tw, isInfX, vIfInf, v)));
          splice(narrow, replacement);
        }

        // The divisor that makes the original quotient come out at v,
        // recorded for model construction, over hash-consed terms.
        // sign(quotient) = sign(x) XOR sign(u), so a zero or infinite
        // quotient's sign picks the sign of the infinite (resp. zero)
        // divisor, and NaN needs 0/0 (resp. oo/oo). Everywhere else
        // fl_src(x/v) is the proof's witness, and IEEE's special quotients
        // make the same expression cover v being NaN, a zero or an
        // infinity.
        const ASTNode xExp = exported(x);
        const ASTNode widenExp = exported(widen);
        const ASTNode isZeroX = nf->CreateNode(FP_ISZERO, xExp);
        const ASTNode isInfX = nf->CreateNode(FP_ISINFINITE, xExp);
        const ASTNode isNegX = nf->CreateNode(FP_ISNEGATIVE, xExp);
        const ASTNode isNegV = nf->CreateNode(FP_ISNEGATIVE, v);
        const ASTNode signsDiffer = nf->CreateNode(XOR, isNegX, isNegV);
        const ASTNode pInfS =
            bm.CreateFPSpecialConst(FPSpecial::PlusInfinity, se, ss);
        const ASTNode mInfS =
            bm.CreateFPSpecialConst(FPSpecial::MinusInfinity, se, ss);
        const ASTNode pZeroS =
            bm.CreateFPSpecialConst(FPSpecial::PlusZero, se, ss);
        const ASTNode mZeroS =
            bm.CreateFPSpecialConst(FPSpecial::MinusZero, se, ss);

        const ASTNode uWhenZero = nf->CreateTerm(
            ITE, sw, nf->CreateNode(FP_ISZERO, v),
            nf->CreateTerm(ITE, sw, signsDiffer, mInfS, pInfS), pZeroS);
        const ASTNode uWhenInf = nf->CreateTerm(
            ITE, sw, nf->CreateNode(FP_ISINFINITE, v),
            nf->CreateTerm(ITE, sw, signsDiffer, mZeroS, pZeroS), pInfS);
        const ASTNode uOtherwise = nf->CreateTerm(
            FP_DIV, sw, rm, widenExp,
            nf->CreateTerm(FP_TOFP, sw, {widenKids[0], widenKids[1], rm, v}));
        const ASTNode witness = nf->CreateTerm(
            ITE, sw, isZeroX, uWhenZero,
            nf->CreateTerm(ITE, sw, isInfX, uWhenInf, uOtherwise));

        replace(var, witness);
      }
      break;

      case AND:
      case OR:
      case BVOR:
      case BVAND:
      {
        bool allUnconstrained = true;
        for (size_t j = 0; j < numberOfChildren && allUnconstrained; j++)
          allUnconstrained = unconstrained(children[j]);

        if (allUnconstrained)
        {
          ASTNodeSet already;
          ASTNode v = replaceWithFresh(parent);
          for (size_t j = 0; j < numberOfChildren; j++)
          {
            /* to avoid problems with:
            734:(AND
            732:unconstrained_4
            716:unconstrained_2
            732:unconstrained_4)
            */
            if (already.find(children[j]) == already.end())
            {
              replace(children[j], v);
              already.insert(children[j]);
            }
          }
        }
        else
        {
          // Hack. ff.stp has a 325k node conjunction
          // So we check if all the children are unconstrained each time
          // we find a new unconstrained conjunct. This means that if
          // eventually all the nodes become unconstrained we will miss it
          // and not rewrite the AND to a fresh unconstrained variable.

          if (numberOfChildren > 200)
            noCheck.insert(parent);
        }
      }
      break;

      case XOR:
      case BVXOR:
      {
        ASTNode v = replaceWithFresh(parent);

        ASTVec others;
        for (size_t j = 0; j < numberOfChildren; j++)
        {
          if (children[j] != var)
            others.push_back(exported(children[j]));
        }
        assert(others.size() + 1 == numberOfChildren);
        assert(others.size() >= 1);

        if (kind == XOR)
        {
          ASTNode xorNode = nf->CreateNode(XOR, others);
          replace(var, nf->CreateNode(XOR, v, xorNode));
        }
        else
        {
          ASTNode xorNode;
          if (others.size() > 1)
            xorNode = nf->CreateTerm(BVXOR, width, others);
          else
            xorNode = others[0];

          replace(var, nf->CreateTerm(BVXOR, width, v, xorNode));
        }
      }
      break;

      case ITE:
      {
        if (indexWidth > 0 && (!arrayRules || !eligibleArray(parent)))
          continue;

        if (unconstrained(children[0]) && unconstrained(children[1]) &&
            children[0] != children[1])
        {
          ASTNode v = replaceWithFresh(parent);
          replace(children[0], bm.ASTTrue);
          replace(children[1], v);
        }
        else if (unconstrained(children[0]) && unconstrained(children[2]) &&
                 children[0] != children[2])
        {
          ASTNode v = replaceWithFresh(parent);
          replace(children[0], bm.ASTFalse);
          replace(children[2], v);
        }
        else if (unconstrained(children[1]) && unconstrained(children[2]))
        {
          ASTNode v = replaceWithFresh(parent);
          replace(children[1], v);
          if (children[1] != children[2])
            replace(children[2], v);
        }
      }
      break;
      case BVLEFTSHIFT:
      case BVRIGHTSHIFT:
      case BVSRSHIFT:
      {
        assert(numberOfChildren == 2);
        if (unconstrained(children[0]) && unconstrained(children[1]))
        {
          assert(children[0] != children[1]);
          ASTNode v = replaceWithFresh(parent);
          replace(children[1], bm.CreateZeroConst(width));
          replace(children[0], v);
        }
      }
      break;

      case BVMOD:
      case SBVREM:
      case SBVMOD:
      {
        assert(numberOfChildren == 2);
        if (unconstrained(children[0]) && unconstrained(children[1]))
        {
          assert(children[0] != children[1]);
          // STP defines remainder-by-zero as the dividend: bvurem, bvsrem and
          // bvsmod all return x when the divisor is 0 (see consteval.cpp). So
          // (v rem 0) == v, and a fresh dividend with divisor 0 reproduces
          // every value.
          ASTNode v = replaceWithFresh(parent);
          replace(children[1], bm.CreateZeroConst(width));
          replace(children[0], v);
        }
      }
      break;

      case BVDIV:
      case SBVDIV:
      {
        assert(numberOfChildren == 2);
        if (unconstrained(children[0]) && unconstrained(children[1]))
        {
          assert(children[0] != children[1]);
          // (v / 1) == v for both signed and unsigned division (and 1 avoids
          // the divide-by-zero result), so a fresh dividend with divisor 1
          // reproduces every value.
          ASTNode v = replaceWithFresh(parent);
          replace(children[1], bm.CreateOneConst(width));
          replace(children[0], v);
        }
      }
      break;
      case BVMULT:
      {
        if (numberOfChildren == 2)
        {
          if (unconstrained(children[1]) &&
              unconstrained(children[0])) // both are unconstrained
          {
            ASTNode v = replaceWithFresh(parent);
            replace(children[0], bm.CreateOneConst(width));
            replace(children[1], v);
          }

          if (other.isConstant() && simplifier->BVConstIsOdd(other))
          {
            ASTNode v = replaceWithFresh(parent);
            ASTNode inverse = simplifier->MultiplicativeInverse(other);
            ASTNode rhs = nf->CreateTerm(BVMULT, width, inverse, v);
            replace(var, rhs);
          }
          break;
        }

        // A wide product whose every operand is unconstrained takes any
        // value: `var` carries a fresh variable and the other operands
        // become one. A single odd constant among the operands keeps that
        // true -- it is invertible, so its inverse folds into the carried
        // value. (An even constant pins low bits, so it disqualifies.)
        ASTNode oddConstant;
        bool eligible = true;
        for (size_t j = 0; j < numberOfChildren && eligible; j++)
        {
          if (children[j] == var || unconstrained(children[j]))
            continue;
          if (children[j].isConstant() && oddConstant.IsNull() &&
              simplifier->BVConstIsOdd(children[j]))
            oddConstant = children[j];
          else
            eligible = false;
        }

        if (eligible)
        {
          ASTNode v = replaceWithFresh(parent);
          if (!oddConstant.IsNull())
            v = nf->CreateTerm(
                BVMULT, width,
                simplifier->MultiplicativeInverse(oddConstant), v);
          // The same unconstrained operand can appear in several positions
          // (e.g. bvmul(a, b, b)); each occurrence resolves to one symbol.
          // Substitute it only once -- a second replace() would re-enter the
          // substitution map for an already-substituted variable. (cf. the
          // AND/OR/BVAND/BVOR case above, which dedups for the same reason.)
          ASTNodeSet already;
          for (size_t j = 0; j < numberOfChildren; j++)
          {
            if (children[j] == var || children[j].isConstant())
              continue;
            if (already.find(children[j]) != already.end())
              continue;
            replace(children[j], bm.CreateOneConst(width));
            already.insert(children[j]);
          }
          replace(var, v);
        }
      }
      break;

      case READ:
      {
        assert(numberOfChildren == 2);
        // Only the array side is interesting. An unconstrained *index*
        // says nothing: the cell it selects is still whatever the array
        // holds there.
        if (!arrayRules || children[0] != var || !eligibleArray(var))
          break;

        // read(a, i) with a free ranges over every value, so the read
        // becomes a fresh scalar. Recovering a from it needs an array
        // agreeing with v at i and free elsewhere, which is exactly a
        // write of v into a second fresh array.
        const ASTNode index = exported(children[1]);
        ASTNode v = replaceWithFresh(parent);
        ASTNode rest = freshLike(var, "unconstrained_array");
        replace(var, nf->CreateArrayTerm(WRITE, var.GetIndexWidth(),
                                         var.GetValueWidth(), rest, index, v));
      }
      break;

      case WRITE:
      {
        assert(numberOfChildren == 3);
        if (!arrayRules || !eligibleArray(parent))
          break;

        // Both the base array and the written value have to be free.
        // With the value fixed the result is pinned at the write index
        // and is not an arbitrary array; see the header comment. A value
        // that is also the index is fixed in the same way, and the
        // definition below would make it its own read index: e := v[e].
        if (unconstrained(children[0]) && unconstrained(children[2]) &&
            children[1] != children[2])
        {
          const ASTNode index = exported(children[1]);
          ASTNode v = replaceWithFresh(parent);
          // write(a, i, e) == v is met by a := v and e := v[i], for any
          // i: writing a cell's own value back changes nothing.
          replace(children[0], v);
          replace(children[2], nf->CreateTerm(READ, parent.GetValueWidth(), v,
                                              index));
        }
      }
      break;

      case IFF:
      {
        // Normally unreachable: the SimplifyingNodeFactory rewrites IFF(a,b)
        // to NOT(XOR(a,b)) on creation, so the standard pipeline never feeds
        // an IFF node to this pass (it's handled by the NOT and XOR cases
        // instead). Kept as a defensive fallback for non-simplifying factories.
        const ASTNode otherExp = exported(other);
        ASTNode v = replaceWithFresh(parent);

        ASTNode rhs =
            nf->CreateNode(ITE, v, otherExp, nf->CreateNode(NOT, otherExp));
        replace(var, rhs);
      }
      break;

      case EQ:
      {
        const ASTNode otherExp = exported(other);
        ASTNode v = replaceWithFresh(parent);

        width = var.GetValueWidth();
        ASTNode rhs = nf->CreateTerm(
            ITE, width, v, otherExp,
            nf->CreateTerm(BVPLUS, width, otherExp,
                           bm.CreateOneConst(width)));

        replace(var, rhs);
      }
      break;

      case BVSUB:
      {
        assert(numberOfChildren == 2);

        const ASTNode otherExp = exported(other);
        ASTNode v = replaceWithFresh(parent);

        ASTNode rhs;

        if (children[0] == var)
          rhs = nf->CreateTerm(BVPLUS, width, v, otherExp);
        if (children[1] == var)
          rhs = nf->CreateTerm(BVSUB, width, otherExp, v);

        replace(var, rhs);
      }
      break;

      case BVPLUS:
      {
        ASTVec otherOps;
        for (size_t j = 0; j < children.size(); j++)
          if (children[j] != var)
            otherOps.push_back(exported(children[j]));

        assert(otherOps.size() == children.size() - 1);
        assert(otherOps.size() >= 1);

        ASTNode v = replaceWithFresh(parent);

        ASTNode rhs;
        if (otherOps.size() > 1)
          rhs = nf->CreateTerm(BVSUB, width, v,
                               nf->CreateTerm(BVPLUS, width, otherOps));
        else
          rhs = nf->CreateTerm(BVSUB, width, v, otherOps[0]);

        replace(var, rhs);
      }
      break;

      case BVEXTRACT:
      {
        ASTNode v = replaceWithFresh(parent);

        const unsigned operandWidth = var.GetValueWidth();
        assert(children[0] == var); // It can't be anywhere else.

        // Create Fresh variables to pad the LHS and RHS.
        const unsigned high = children[1].GetUnsignedConst();
        const unsigned low = children[2].GetUnsignedConst();
        assert(high >= low);

        const int rhsSize = low;
        const int lhsSize = operandWidth - high - 1;

        ASTNode current = v;
        int newWidth = v.GetValueWidth();

        if (lhsSize > 0)
        {
          ASTNode lhsFresh = bm.CreateFreshVariable(0, lhsSize, "lhs_padding");
          current =
              nf->CreateTerm(BVCONCAT, newWidth + lhsSize, lhsFresh, current);
          newWidth += lhsSize;
        }

        if (rhsSize > 0)
        {
          ASTNode rhsFresh = bm.CreateFreshVariable(0, rhsSize, "rhs_padding");
          current =
              nf->CreateTerm(BVCONCAT, newWidth + rhsSize, current, rhsFresh);
          newWidth += rhsSize;
        }

        assert(newWidth == (int)operandWidth);
        replace(var, current);
      }
      break;

      default:
      {
        // cerr << "!!!!" << kind << endl;
      }
    }

    // None of the per-kind rules fired (each detaches `var` from its
    // parent when it does). Try the generalised ground-path collapse.
    if (unconstrained(var))
      tryGroundPathCollapse(var);
  }

  ASTNode result = graph.exportRoot();
  if (checkGraph)
    std::cerr << "  [ru] end, export " << result << std::endl;
  g = NULL;
  gf = NULL;
  worklist.clear();

  // Membership constraints for image-constrained fresh variables join
  // the formula here, once the tree is materialised.
  if (!imageConstraints.empty())
  {
    ASTVec conj;
    conj.push_back(result);
    conj.insert(conj.end(), imageConstraints.begin(), imageConstraints.end());
    result = nf->CreateNode(AND, conj);
    imageConstraints.clear();
  }
  // cout << result;
  if (result.GetKind() == SYMBOL)
  {
    replace(result, bm.ASTTrue);
    result = bm.ASTTrue;
  }

  return result;
}
}
