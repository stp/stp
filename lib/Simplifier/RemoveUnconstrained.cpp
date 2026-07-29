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
 * Nb. this isn't finished. It doesn't do reads / writes.
 *
 * Kinds without a per-kind rule (bvsx, bvzx, bvurem/bvudiv by a
 * constant, masks, ...) can still be eliminated when the variable's
 * whole use is a predicate over it and constants: see
 * tryGroundPathCollapse.
 */

#include "stp/Simplifier/RemoveUnconstrained.h"
#include "stp/AST/MutableASTNode.h"
#include "stp/Simplifier/AchievableImage.h"
#include "stp/Simplifier/constantBitP/Dependencies.h"

namespace stp
{
using simplifier::constantBitP::Dependencies;

RemoveUnconstrained::RemoveUnconstrained(STPMgr& _bm) : bm(_bm)
{
  nf = _bm.defaultNodeFactory;
  simplifier = NULL;
}

ASTNode RemoveUnconstrained::topLevel(const ASTNode& n, Simplifier* simplifier)
{
  ASTNode result(n);

  bm.GetRunTimes()->start(RunTimes::RemoveUnconstrained);

  if (simplifier->hasUnappliedSubstitutions())
    result = simplifier->applySubstitutionMap(result);

  // In some rare cases, the simplifier might not have removed a term
  // that can be substituted away. e.g. read(A,0), if read(A,0) == 1,
  // in the substitution map.
  result = topLevel_other(result, simplifier);

// It is idempotent if there are no big ANDS (we have a special hack), and,
// if we don't introduced any new "disjoint extracts."

#if 0
  ASTNode result2 = topLevel_other(result, simplifier);
  if (result2 != result)
  {
      cerr << n;
      cerr << result;
      cerr << result2;
      assert(result2 == result);
  }
#endif
  bm.GetRunTimes()->stop(RunTimes::RemoveUnconstrained);
  return result;
}

bool allChildrenAreUnconstrained(vector<MutableASTNode*> children)
{
  for (size_t i = 0; i < children.size(); i++)
    if (!children[i]->isUnconstrained())
      return false;

  return true;
}

ASTNode
RemoveUnconstrained::replaceParentWithFresh(MutableASTNode& mute,
                                            vector<MutableASTNode*>& variables)
{
  const ASTNode& parent = mute.n;
  ASTNode v =
      bm.CreateFreshVariable(0, parent.GetValueWidth(), "unconstrained");
  mute.replaceWithVar(v, variables);
  return v;
}

//  nb. This avoids the expensive checks that usually updating the substitution
//  map entails.
void RemoveUnconstrained::replace(const ASTNode& from, const ASTNode to)
{
  assert(from.GetKind() == SYMBOL);
  assert(from.GetValueWidth() == to.GetValueWidth());
  simplifier->UpdateSubstitutionMapFewChecks(from, to);
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

// Constant-evaluate one collected step on a known input value.
static ASTNode evalStepOnConstant(STPMgr& bm, const GroundStep& s,
                                  const ASTNode& in)
{
  std::vector<CBV> args;
  if (s.samePathAllOperands)
  {
    args.push_back(in.GetBVConst());
    args.push_back(in.GetBVConst());
  }
  else if (s.kind == BVSX || s.kind == BVZX)
  {
    // The evaluator takes the new width from outWidth.
    args.push_back(in.GetBVConst());
  }
  else
  {
    const size_t arity = s.constants.size() + 1;
    size_t ci = 0;
    for (size_t i = 0; i < arity; i++)
    {
      if (i == s.pathIndex)
        args.push_back(in.GetBVConst());
      else
        args.push_back(s.constants[ci++].GetBVConst());
    }
  }
  return bm.CreateBVConst(NonMemberBVConstEvaluator(s.kind, args, s.outWidth),
                          s.outWidth);
}

/* Global polarity of a boolean node within the live mutable tree: the
 * union, over every occurrence and every path to the root, of the
 * negation parity along it. POL_POS alone means the formula is monotone
 * non-decreasing in the node (making it true can only help), POL_NEG
 * the dual. ITE conditions, XOR/IFF operands and anything unrecognised
 * get both. Only pure single-polarity predicates admit the one-sided
 * collapse. */
static const unsigned POL_POS = 1;
static const unsigned POL_NEG = 2;

static unsigned flipPolarity(unsigned p)
{
  return ((p & POL_POS) ? POL_NEG : 0u) | ((p & POL_NEG) ? POL_POS : 0u);
}

static unsigned
polarityOf(MutableASTNode* node,
           std::unordered_map<MutableASTNode*, unsigned>& memo)
{
  const auto it = memo.find(node);
  if (it != memo.end())
    return it->second;

  // A parentless node is the root. (Pruned nodes are unlinked from
  // their children's parent sets, so every parent seen here is live.)
  unsigned pol = node->parents.empty() ? POL_POS : 0;
  for (MutableASTNode* p : node->parents)
  {
    if (p->n.GetValueWidth() != 0 || p->n.GetIndexWidth() != 0)
    {
      pol |= POL_POS | POL_NEG; // a term-level ITE's condition
      continue;
    }
    const unsigned pp = polarityOf(p, memo);
    const vector<MutableASTNode*>& kids = p->children;
    for (size_t i = 0; i < kids.size(); i++)
    {
      if (kids[i] != node)
        continue;
      switch (p->n.GetKind())
      {
        case AND:
        case OR:
          pol |= pp;
          break;
        case NOT:
        case NAND:
        case NOR:
          pol |= flipPolarity(pp);
          break;
        case IMPLIES:
          pol |= (i == 0) ? flipPolarity(pp) : pp;
          break;
        case ITE: // boolean-valued: branches follow it, the condition both.
          pol |= (i == 0) ? (POL_POS | POL_NEG) : pp;
          break;
        default: // XOR, IFF, PARAMBOOL, ...: no monotonicity.
          pol |= POL_POS | POL_NEG;
          break;
      }
    }
    if (pol == (POL_POS | POL_NEG))
      break;
  }
  memo.insert(std::make_pair(node, pol));
  return pol;
}

static unsigned polarityOf(MutableASTNode* node)
{
  std::unordered_map<MutableASTNode*, unsigned> memo;
  return polarityOf(node, memo);
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
 *
 * A non-constant sibling makes the image unknowable, but one value can
 * survive it: forcing the path to an absorbing element (0 through
 * bvand/bvmul, ones through bvor) fixes the chain regardless of the
 * sibling -- e.g. (= (bvand x t) 0) is forced true by x := 0. A single
 * known outcome can only collapse the predicate one way, which is
 * sound exactly when the predicate's global polarity is pure and
 * prefers that outcome: any model of the original formula can flip the
 * predicate to the preferred value without falsifying it (monotonicity),
 * and any model of the rewrite extends with x := witness, which
 * realises the value. The same one-sided rule also rescues all-constant
 * chains where only one polarity is achievable.
 */
bool RemoveUnconstrained::tryGroundPathCollapse(
    MutableASTNode& muteNode, vector<MutableASTNode*>& variables)
{
  const ASTNode var = muteNode.n;
  if (var.GetValueWidth() == 0 || var.GetIndexWidth() != 0)
    return false;

  // Phase 1: collect the path structurally, up to the predicate. Knowing
  // the predicate's constant before the image is built lets it be used as
  // a seed hint when the image degrades to samples.
  std::vector<GroundStep> steps;
  MutableASTNode* predicate = NULL;
  Kind predKind = UNDEFINED;
  bool pathFirst = false;
  ASTNode predConst;

  // ITE frames on the path, innermost first. Each frame costs one
  // rebuilt predicate around its other branch, so growth is linear in
  // the frame count; the cap bounds it.
  struct IteFrame
  {
    MutableASTNode* cond;
    MutableASTNode* other;
    bool pathThen;
    size_t stepsBelow;
  };
  const size_t MAX_ITE_FRAMES = 4;
  std::vector<IteFrame> frames;

  // Concat frames: BVCONCAT nodes with a possibly-symbolic sibling.
  // Equality distributes over concatenation slice by slice, so these
  // need no image -- but only pure concatenation may then sit between
  // the variable and the predicate, and the predicate must be EQ.
  struct ConcatFrame
  {
    MutableASTNode* sibling;
    bool pathHigh; // the path is child 0 (the high part)
  };
  std::vector<ConcatFrame> cframes;

  // Singleton mode: a symbolic sibling at an absorbing operator ends
  // image tracking, but one value survives it -- forcing the path to
  // the operator's absorbing element fixes the output regardless of
  // the sibling, e.g. x := 0 makes (bvand x t) zero for every t. From
  // there only that single value (and x's witness for it) is known, so
  // only the one-sided, polarity-gated collapse can fire.
  bool singleton = false;
  ASTNode knownVal;         // constant at the chain's current width
  ASTNode singletonWitness; // constant at var's width

  MutableASTNode* cur = &muteNode;
  for (unsigned depth = 0; depth < AchievableImage::MAX_PATH; depth++)
  {
    MutableASTNode& parent = cur->getParent();
    const ASTNode& p = parent.n;
    const vector<MutableASTNode*>& kids = parent.children;

    if (p.GetValueWidth() == 0)
    {
      if (!cframes.empty())
      {
        // Slicing mode: an equality against ANY term splits by bit
        // range. x is defined as its slice of the other side (falsity
        // survives through the sibling slices' residual equalities, so
        // no fresh boolean is needed).
        if (p.GetKind() != EQ || kids.size() != 2)
          return false;
        const bool eqPathFirst = (kids[0] == cur);
        if (kids[0] == kids[1] || (!eqPathFirst && kids[1] != cur))
          return false;
        MutableASTNode* otherM = eqPathFirst ? kids[1] : kids[0];
        if (otherM->n.GetValueWidth() != cur->n.GetValueWidth())
          return false;

        // Unwrap the frames innermost-out into a high-to-low slice
        // list; a NULL node marks the variable's own slice.
        struct Slice
        {
          MutableASTNode* node;
          unsigned width;
        };
        std::vector<Slice> slices;
        slices.push_back({NULL, var.GetValueWidth()});
        for (const ConcatFrame& cf : cframes)
        {
          const Slice s = {cf.sibling, cf.sibling->n.GetValueWidth()};
          if (cf.pathHigh)
            slices.push_back(s);
          else
            slices.insert(slices.begin(), s);
        }

        const ASTNode t = otherM->toASTNode(&bm);
        ASTNode varDef;
        ASTVec residuals;
        vector<MutableASTNode*> vars;
        std::unordered_set<MutableASTNode*> visited;
        otherM->getAllVariablesRecursively(vars, visited);
        long hiBit = (long)t.GetValueWidth() - 1;
        for (const Slice& s : slices)
        {
          const long loBit = hiBit + 1 - (long)s.width;
          ASTNode piece =
              nf->CreateTerm(BVEXTRACT, s.width, t,
                             bm.CreateBVConst(32, (unsigned long long)hiBit),
                             bm.CreateBVConst(32, (unsigned long long)loBit));
          if (s.node == NULL)
            varDef = piece;
          else
          {
            residuals.push_back(
                nf->CreateNode(EQ, s.node->toASTNode(&bm), piece));
            s.node->getAllVariablesRecursively(vars, visited);
          }
          hiBit = loBit - 1;
        }
        assert(hiBit == -1);
        visited.clear();

        ASTNode newP = (residuals.size() == 1)
                           ? residuals[0]
                           : nf->CreateNode(AND, residuals);

        std::unordered_map<uint64_t, MutableASTNode*> create;
        for (MutableASTNode* m : vars)
          create.insert(std::make_pair(m->n.GetNodeNum(), m));
        vars.clear();

        parent.replaceWithAnotherNode(MutableASTNode::build(newP, create));
        replace(var, varDef);
        return true;
      }

      // Boolean level: a predicate between the chain and a constant.
      if (!AchievableImage::predicateKind(p.GetKind()) || kids.size() != 2)
        return false;
      pathFirst = (kids[0] == cur);
      if (kids[0] == kids[1] || (!pathFirst && kids[1] != cur))
        return false;
      const ASTNode other = pathFirst ? kids[1]->n : kids[0]->n;
      if (!other.isConstant() ||
          other.GetValueWidth() != cur->n.GetValueWidth())
        return false;
      predicate = &parent;
      predKind = p.GetKind();
      predConst = other;
      break;
    }

    // Term level: one path child, constants everywhere else.
    const Kind kind = p.GetKind();

    // Once slicing has begun, only further concatenation can follow.
    if (!cframes.empty() && kind != BVCONCAT)
      return false;

    if (kind == BVCONCAT && kids.size() == 2 &&
        ((kids[0] == cur) != (kids[1] == cur)))
    {
      const bool pathHigh = (kids[0] == cur);
      MutableASTNode* sib = pathHigh ? kids[1] : kids[0];
      // Enter slicing mode at the first symbolic sibling, but only from
      // the bare variable (no image steps, ITE frames or absorbing
      // steps below); once in it, constant siblings become frames too.
      if (!cframes.empty() ||
          (!sib->n.isConstant() && steps.empty() && frames.empty() &&
           !singleton))
      {
        cframes.push_back({sib, pathHigh});
        if (parent.parents.size() != 1)
          return false;
        cur = &parent;
        continue;
      }
      // Constant sibling outside slicing mode: the ordinary image step
      // below handles it.
    }

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
      if (parent.parents.size() != 1)
        return false;
      cur = &parent;
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
      else if (!kids[i]->n.isConstant())
        nonConstSibling = true;
    }
    if (nonConstSibling)
    {
      // Enter (or stay in) singleton mode if the path can be forced to
      // this operator's absorbing element.
      ASTNode absorbIn, absorbOut;
      const unsigned inW = cur->n.GetValueWidth();
      if ((kind == BVAND || kind == BVMULT) && pathCount == 1)
      {
        absorbIn = bm.CreateZeroConst(inW);
        absorbOut = bm.CreateZeroConst(p.GetValueWidth());
      }
      else if (kind == BVOR && pathCount == 1)
      {
        absorbIn = bm.CreateMaxConst(inW);
        absorbOut = bm.CreateMaxConst(p.GetValueWidth());
      }
      else if ((kind == BVLEFTSHIFT || kind == BVRIGHTSHIFT ||
                kind == BVSRSHIFT || kind == BVMOD || kind == SBVREM ||
                kind == SBVMOD) &&
               pathCount == 1 && pathIdx == 0)
      {
        // Zero shifted by anything is zero; STP defines remainder-by-
        // zero as the dividend, so a zero dividend gives zero for
        // every divisor, including zero.
        absorbIn = bm.CreateZeroConst(inW);
        absorbOut = bm.CreateZeroConst(p.GetValueWidth());
      }
      else
        return false;

      // A frame's other branch gets the suffix steps re-applied as
      // nodes, which a symbolic sibling can't be -- so no frame may
      // sit below a symbolic step. (Frames captured above one are
      // fine: their suffixes only hold the steps recorded after them.)
      if (!frames.empty())
        return false;

      if (singleton)
      {
        if (knownVal != absorbIn)
          return false;
      }
      else
      {
        // Ask the image of the steps so far for a witness reaching the
        // absorbing element (trivially x itself when the variable
        // feeds the operator directly).
        AchievableImage prefix(bm, var.GetValueWidth());
        prefix.addHint(absorbIn);
        for (const GroundStep& s : steps)
          if (!prefix.apply(s))
            return false;
        if (!prefix.decideOneSided(EQ, true, absorbIn, true,
                                   singletonWitness))
          return false;
        singleton = true;
      }
      knownVal = absorbOut;

      // The symbolic step is NOT recorded in `steps`: it never reaches
      // an image, and later frames' suffixes must exclude it.
      if (parent.parents.size() != 1)
        return false;
      cur = &parent;
      continue;
    }
    // Both operands being the path -- (bvmul t t), squaring -- is still
    // a unary function of the path value; anything else duplicated is
    // not a chain.
    const bool samePathAllOperands = (pathCount == 2 && kids.size() == 2);
    if (pathCount != 1 && !samePathAllOperands)
      return false;

    GroundStep step;
    step.kind = kind;
    step.outWidth = p.GetValueWidth();
    step.inWidth = cur->n.GetValueWidth();

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
      step.constants.push_back(kids[1]->n);
      step.constants.push_back(kids[2]->n);
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
        step.constants.push_back(kids[1 - pathIdx]->n);
      }
      else
      {
        std::vector<CBV> consts;
        for (size_t i = 0; i < kids.size(); i++)
          if (i != pathIdx)
            consts.push_back(kids[i]->n.GetBVConst());
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
      step.constants.push_back(kids[1 - pathIdx]->n);
    }

    steps.push_back(step);

    // In singleton mode the known value flows through by evaluation.
    if (singleton)
      knownVal = evalStepOnConstant(bm, step, knownVal);

    // Interior nodes must be single-use to step past them.
    if (parent.parents.size() != 1)
      return false;
    cur = &parent;
  }
  if (predicate == NULL)
    return false; // too deep

  // Phase 2: decide. Two-sided when both polarities of the predicate
  // are achievable: it becomes a fresh boolean. Otherwise one-sided:
  // when one forced outcome is achievable and the predicate's global
  // polarity is pure and points the same way, fixing that outcome only
  // helps, so the predicate becomes a constant and var its witness.
  ASTNode inner;  // what the predicate becomes on the path branch
  ASTNode varDef; // the recorded definition of var
  bool twoSided = false;
  AchievableImage::Decision d;

  if (!singleton)
  {
    // Flow the achievable image up the collected path.
    AchievableImage image(bm, var.GetValueWidth());
    image.addHintChain(steps, predConst);
    for (const GroundStep& step : steps)
      if (!image.apply(step))
        return false;

    d = image.decide(predKind, pathFirst, predConst);
    if (d.collapse)
      twoSided = true;
    else
    {
      const unsigned pol = polarityOf(predicate);
      if (pol == POL_POS &&
          image.decideOneSided(predKind, pathFirst, predConst, true, varDef))
        inner = bm.ASTTrue;
      else if (pol == POL_NEG && image.decideOneSided(predKind, pathFirst,
                                                      predConst, false,
                                                      varDef))
        inner = bm.ASTFalse;
      else
        return false;
    }
  }
  else
  {
    // Singleton mode: exactly one outcome of the predicate is known.
    const bool outcome =
        pathFirst ? NonMemberBVConstPredicateEvaluator(
                        predKind, knownVal.GetBVConst(), predConst.GetBVConst())
                  : NonMemberBVConstPredicateEvaluator(
                        predKind, predConst.GetBVConst(), knownVal.GetBVConst());
    const unsigned pol = polarityOf(predicate);
    if (outcome ? (pol != POL_POS) : (pol != POL_NEG))
      return false;
    inner = outcome ? bm.ASTTrue : bm.ASTFalse;
    varDef = singletonWitness;
  }

  if (twoSided)
  {
    if (frames.empty())
    {
      // The predicate has width 0, so this creates a fresh boolean and
      // prunes the whole path out of the mutable tree.
      ASTNode v = replaceParentWithFresh(*predicate, variables);
      replace(var, nf->CreateTerm(ITE, var.GetValueWidth(), v, d.witnessTrue,
                                  d.witnessFalse));
      return true;
    }
    inner = bm.CreateFreshVariable(0, 0, "unconstrained_ite");
    varDef = nf->CreateTerm(ITE, var.GetValueWidth(), inner, d.witnessTrue,
                            d.witnessFalse);
  }
  else if (frames.empty())
  {
    // One-sided, no frames: the predicate is simply the constant.
    predicate->replaceWithAnotherNode(MutableASTNode::build(inner));
    replace(var, varDef);
    return true;
  }

  // Distribute the predicate over the captured frames, innermost out:
  //   P(...ite(c_i, path_i, t_i)...)
  //     ==>  ite(c_k, ... ite(c_1, v, P(above_1(t_1))) ..., P(above_k(t_k)))
  // where above_i re-applies every ground step recorded above frame i,
  // and v is the fresh boolean (or, one-sided, the forced constant).
  vector<MutableASTNode*> vars;
  std::unordered_set<MutableASTNode*> visited;
  for (const IteFrame& fr : frames)
  {
    ASTNode gt = fr.other->toASTNode(&bm);
    for (size_t i = fr.stepsBelow; i < steps.size(); i++)
      gt = applyStepToNode(nf, bm, steps[i], gt);
    ASTNode elseP = pathFirst ? nf->CreateNode(predKind, gt, predConst)
                              : nf->CreateNode(predKind, predConst, gt);
    inner = nf->CreateNode(ITE, fr.cond->toASTNode(&bm),
                           fr.pathThen ? inner : elseP,
                           fr.pathThen ? elseP : inner);
    fr.cond->getAllVariablesRecursively(vars, visited);
    fr.other->getAllVariablesRecursively(vars, visited);
  }
  visited.clear();

  // Splice the new formula in, reusing the existing mutable nodes for the
  // variables it mentions (same mechanics as the comparison rule).
  std::unordered_map<uint64_t, MutableASTNode*> create;
  for (MutableASTNode* m : vars)
    create.insert(std::make_pair(m->n.GetNodeNum(), m));
  vars.clear();

  MutableASTNode* newN = MutableASTNode::build(inner, create);
  predicate->replaceWithAnotherNode(newN);

  replace(var, varDef);
  return true;
}

ASTNode RemoveUnconstrained::topLevel_other(const ASTNode& n,
                                            Simplifier* simplifier)
{
  if (n.GetKind() == SYMBOL)
    return n; // top level is an unconstrained symbol/.

  this->simplifier = simplifier;

  MutableASTNode* topMutable = MutableASTNode::build(n);

  vector<MutableASTNode*> variable_array;
  topMutable->getAllUnconstrainedVariables(variable_array);

  // We don't want to check some expensive nodes over and over again.
  ASTNodeSet noCheck;

  for (size_t i = 0; i < variable_array.size(); i++)
  {
    // Don't make this is a reference. If the vector gets resized, it will point
    // to memory that no longer contains the object.
    MutableASTNode& muteNode = *variable_array[i];

    const ASTNode var = muteNode.n;
    assert(var.GetKind() == SYMBOL);

    if (!muteNode.isUnconstrained())
      continue;

    MutableASTNode& muteParent = muteNode.getParent();

    if (noCheck.find(muteParent.n) != noCheck.end())
      continue;

    vector<MutableASTNode*> mutable_children = muteParent.children;

    // nb. The children might be dirty. i.e. not have substitutions written
    // through them yet.
    ASTVec children;
    children.reserve(mutable_children.size());
    for (size_t j = 0; j < mutable_children.size(); j++)
      children.push_back(mutable_children[j]->n);

    const size_t numberOfChildren = children.size();
    const Kind kind = muteNode.getParent().n.GetKind();
    unsigned width = muteNode.getParent().n.GetValueWidth();
    unsigned indexWidth = muteNode.getParent().n.GetIndexWidth();

    ASTNode other;
    MutableASTNode* muteOther = NULL;

    if (numberOfChildren == 2)
    {
      if (children[0] != var)
      {
        other = children[0];
        muteOther = mutable_children[0];
      }
      else
      {
        other = children[1];
        muteOther = mutable_children[1];
      }

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
        for (size_t i = 0; i < numberOfChildren; i++)
        {
          if (children[i] == var)
            found++;
        }

        if (found != 1)
          continue; // Most rules don't like duplicate variables.
      }
    }

    /*
    cout << i << " " << kind << " " << variable_array.size() <<  " " <<
    mutable_children.size() << endl;
    cout << "children[0]" << children[0] << endl;
    cout << "children[1]" << children[1] << endl;
    cout << muteParent.n << endl;

     */

    switch (kind)
    {
      case BVCONCAT:
      {
        assert(numberOfChildren == 2);
        if (mutable_children[0]->isUnconstrained() &&
            (mutable_children[1]->isUnconstrained()))
        {
          ASTNode v = replaceParentWithFresh(muteParent, variable_array);

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
        ASTNode v = replaceParentWithFresh(muteParent, variable_array);
        replace(children[0], nf->CreateNode(NOT, v));
      }
      break;

      case BVUMINUS:
      case BVNOT:
      {
        assert(numberOfChildren == 1);
        ASTNode v = replaceParentWithFresh(muteParent, variable_array);
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

        if (mutable_children[0]->isUnconstrained() &&
            mutable_children[1]->isUnconstrained())
        {
          ASTNode v = replaceParentWithFresh(muteParent, variable_array);

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

          ASTNode v = replaceParentWithFresh(muteParent, variable_array);

          ASTNode rhs =
              nf->CreateTerm(ITE, width, v, biggestNumber, smallestNumber);
          replace(var, rhs);
        }
        else if (children[1] == var && children[0].isConstant())
        {
          if (children[0] == c2)
            continue; // always false. Or always false.

          ASTNode v = replaceParentWithFresh(muteParent, variable_array);

          ASTNode rhs =
              nf->CreateTerm(ITE, width, v, smallestNumber, biggestNumber);
          replace(var, rhs);
        }
        else // One side is a variable. The other is anything.
        {
          bool varOnLHS = (var == children[0]);

          // All the ASTNode vars need to map to their existing MutableASTNodes.
          // So we collect all the variables
          vector<MutableASTNode*> vars;
          std::unordered_set<MutableASTNode*> visited;
          muteOther->getAllVariablesRecursively(vars, visited);
          visited.clear();

          std::unordered_map<uint64_t, MutableASTNode*> create;
          for (vector<MutableASTNode*>::iterator it = vars.begin();
               it != vars.end(); it++)
            create.insert(std::make_pair((*it)->n.GetNodeNum(), *it));
          vars.clear();

          ASTNode v = bm.CreateFreshVariable(0, 0, "STP_INTERNAL_comparison");

          ASTNode rhs;
          ASTNode n;
          if (varOnLHS)
          {
            rhs = nf->CreateTerm(ITE, width, v, biggestNumber, smallestNumber);

            if (kind == BVSGE || kind == BVGE)
              n = nf->CreateNode(
                  OR, v,
                  nf->CreateNode(EQ, mutable_children[1]->toASTNode(&bm), c1));
            else
              n = nf->CreateNode(
                  AND, v,
                  nf->CreateNode(
                      NOT,
                      nf->CreateNode(EQ, mutable_children[1]->toASTNode(&bm),
                                     c1)));
          }
          else
          {
            rhs = nf->CreateTerm(ITE, width, v, smallestNumber, biggestNumber);

            if (kind == BVSGE || kind == BVGE)
              n = nf->CreateNode(
                  OR, v,
                  nf->CreateNode(EQ, mutable_children[0]->toASTNode(&bm), c2));
            else
              n = nf->CreateNode(
                  AND, v,
                  nf->CreateNode(
                      NOT,
                      nf->CreateNode(EQ, mutable_children[0]->toASTNode(&bm),
                                     c2)));
          }
          replace(var, rhs);
          MutableASTNode* newN = MutableASTNode::build(n, create);
          muteParent.replaceWithAnotherNode(newN);
          // assert(muteParent.checkInvariant());
        }
      }
      break;

      case AND:
      case OR:
      case BVOR:
      case BVAND:
      {
        if (allChildrenAreUnconstrained(mutable_children))
        {
          ASTNodeSet already;
          ASTNode v = replaceParentWithFresh(muteParent, variable_array);
          for (size_t i = 0; i < numberOfChildren; i++)
          {
            /* to avoid problems with:
            734:(AND
            732:unconstrained_4
            716:unconstrained_2
            732:unconstrained_4)
            */
            if (already.find(children[i]) == already.end())
            {
              replace(children[i], v);
              already.insert(children[i]);
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

          if (mutable_children.size() > 200)
            noCheck.insert(muteParent.n);
        }
      }
      break;

      case XOR:
      case BVXOR:
      {
        ASTNode v = replaceParentWithFresh(muteParent, variable_array);

        ASTVec others;
        for (size_t i = 0; i < numberOfChildren; i++)
        {
          if (children[i] != var)
            others.push_back(mutable_children[i]->toASTNode(&bm));
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
        if (indexWidth > 0)
          continue; // don't do arrays.

        if (mutable_children[0]->isUnconstrained() &&
            mutable_children[1]->isUnconstrained() &&
            children[0] != children[1])
        {
          ASTNode v = replaceParentWithFresh(muteParent, variable_array);
          replace(children[0], bm.ASTTrue);
          replace(children[1], v);
        }
        else if (mutable_children[0]->isUnconstrained() &&
                 mutable_children[2]->isUnconstrained() &&
                 children[0] != children[2])
        {
          ASTNode v = replaceParentWithFresh(muteParent, variable_array);
          replace(children[0], bm.ASTFalse);
          replace(children[2], v);
        }
        else if (mutable_children[1]->isUnconstrained() &&
                 mutable_children[2]->isUnconstrained())
        {
          ASTNode v = replaceParentWithFresh(muteParent, variable_array);
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
        if (mutable_children[0]->isUnconstrained() &&
            mutable_children[1]->isUnconstrained())
        {
          assert(children[0] != children[1]);
          ASTNode v = replaceParentWithFresh(muteParent, variable_array);
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
        if (mutable_children[0]->isUnconstrained() &&
            mutable_children[1]->isUnconstrained())
        {
          assert(children[0] != children[1]);
          // STP defines remainder-by-zero as the dividend: bvurem, bvsrem and
          // bvsmod all return x when the divisor is 0 (see consteval.cpp). So
          // (v rem 0) == v, and a fresh dividend with divisor 0 reproduces
          // every value.
          ASTNode v = replaceParentWithFresh(muteParent, variable_array);
          replace(children[1], bm.CreateZeroConst(width));
          replace(children[0], v);
        }
      }
      break;

      case BVDIV:
      case SBVDIV:
      {
        assert(numberOfChildren == 2);
        if (mutable_children[0]->isUnconstrained() &&
            mutable_children[1]->isUnconstrained())
        {
          assert(children[0] != children[1]);
          // (v / 1) == v for both signed and unsigned division (and 1 avoids
          // the divide-by-zero result), so a fresh dividend with divisor 1
          // reproduces every value.
          ASTNode v = replaceParentWithFresh(muteParent, variable_array);
          replace(children[1], bm.CreateOneConst(width));
          replace(children[0], v);
        }
      }
      break;
      case BVMULT:
      {
        assert(numberOfChildren == 2);

        if (mutable_children[1]->isUnconstrained() &&
            mutable_children[0]->isUnconstrained()) // both are unconstrained
        {
          ASTNode v = replaceParentWithFresh(muteParent, variable_array);
          replace(children[0], bm.CreateOneConst(width));
          replace(children[1], v);
        }

        if (other.isConstant() && simplifier->BVConstIsOdd(other))
        {
          ASTNode v = replaceParentWithFresh(muteParent, variable_array);
          ASTNode inverse = simplifier->MultiplicativeInverse(other);
          ASTNode rhs = nf->CreateTerm(BVMULT, width, inverse, v);
          replace(var, rhs);
        }
      }
      break;

      case IFF:
      {
        // Normally unreachable: the SimplifyingNodeFactory rewrites IFF(a,b)
        // to NOT(XOR(a,b)) on creation, so the standard pipeline never feeds
        // an IFF node to this pass (it's handled by the NOT and XOR cases
        // instead). Kept as a defensive fallback for non-simplifying factories.
        ASTNode v = replaceParentWithFresh(muteParent, variable_array);

        ASTNode rhs =
            nf->CreateNode(ITE, v, muteOther->toASTNode(&bm),
                           nf->CreateNode(NOT, muteOther->toASTNode(&bm)));
        replace(var, rhs);
      }
      break;

      case EQ:
      {
        ASTNode v = replaceParentWithFresh(muteParent, variable_array);

        width = var.GetValueWidth();
        ASTNode rhs = nf->CreateTerm(
            ITE, width, v, muteOther->toASTNode(&bm),
            nf->CreateTerm(BVPLUS, width, muteOther->toASTNode(&bm),
                           bm.CreateOneConst(width)));

        replace(var, rhs);
      }
      break;

      case BVSUB:
      {
        assert(numberOfChildren == 2);

        ASTNode v = replaceParentWithFresh(muteParent, variable_array);

        ASTNode rhs;

        if (children[0] == var)
          rhs = nf->CreateTerm(BVPLUS, width, v, muteOther->toASTNode(&bm));
        if (children[1] == var)
          rhs = nf->CreateTerm(BVSUB, width, muteOther->toASTNode(&bm), v);

        replace(var, rhs);
      }
      break;

      case BVPLUS:
      {
        ASTVec other;
        for (size_t i = 0; i < children.size(); i++)
          if (children[i] != var)
            other.push_back(mutable_children[i]->toASTNode(&bm));

        assert(other.size() == children.size() - 1);
        assert(other.size() >= 1);

        ASTNode v = replaceParentWithFresh(muteParent, variable_array);

        ASTNode rhs;
        if (other.size() > 1)
          rhs = nf->CreateTerm(BVSUB, width, v,
                               nf->CreateTerm(BVPLUS, width, other));
        else
          rhs = nf->CreateTerm(BVSUB, width, v, other[0]);

        replace(var, rhs);
      }
      break;

      case BVEXTRACT:
      {
        ASTNode v = replaceParentWithFresh(muteParent, variable_array);

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

        assert(newWidth == (long int)operandWidth);
        replace(var, current);
      }
      break;

      default:
      {
        // cerr << "!!!!" << kind << endl;
      }

        //        cerr << var;
        //      cerr << parent;
    }

    // None of the per-kind rules fired (each detaches `var` from its
    // parent when it does). Try the generalised ground-path collapse.
    if (muteNode.isUnconstrained())
      tryGroundPathCollapse(muteNode, variable_array);
  }

  ASTNode result = topMutable->toASTNode(&bm);
  topMutable->cleanup();
  // cout << result;
  if (result.GetKind() == SYMBOL)
  {
    replace(result, bm.ASTTrue);
    result = bm.ASTTrue;
  }

  return result;
}
}
