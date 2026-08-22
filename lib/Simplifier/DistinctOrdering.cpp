/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: August, 2026
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

#include "stp/Simplifier/DistinctOrdering.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Util/DagWalk.h"
#include <set>

namespace stp
{

namespace
{

const unsigned POSITIVE = 1;
const unsigned NEGATIVE = 2;

unsigned flipped(const unsigned polarity)
{
  unsigned result = 0;
  if ((polarity & POSITIVE) != 0)
    result |= NEGATIVE;
  if ((polarity & NEGATIVE) != 0)
    result |= POSITIVE;
  return result;
}

// A node under XOR, boolean EQ, an ITE, or an uninterpreted application is
// used both ways at once, and so is everything beneath it. An arbitrary
// function need not be monotone in a Boolean actual: g(false) may be true
// while g(true) is false, so strengthening a distinct inside that actual can
// change satisfiability.
//
// IMPLIES is here for safety rather than because it is reached: the node
// factory rewrites (=> x y) to (or (not x) y) before this pass sees the
// formula, so a distinct in either position arrives with its polarity already
// spelled out. The entry costs nothing and keeps the list honest about which
// kinds mix polarity, so a factory that stopped rewriting implications would
// not silently make this walk wrong.
bool usedBothWays(const Kind kind)
{
  return kind == XOR || kind == IFF || kind == EQ || kind == ITE ||
         kind == IMPLIES || kind == DISTINCT || kind == UF_APPLY;
}

// How a distinct's operands can be interchangeable.
enum class Form
{
  None,
  // (distinct x1 ... xn) over variables. Permuting them maps the formula to
  // itself, so the chain may stand in place of the whole clique: it implies
  // it.
  Variables,
  // (distinct (f x1) ... (f xn)) over one unary declaration. Here the chain
  // orders the *arguments*, and permuting those leaves the operand multiset
  // alone, so the formula is again invariant. The clique has to stay: an
  // order on the arguments says nothing about the results unless f is
  // injective, which is the very thing the query is asking about.
  Arguments
};

// The symbols a group would order, and how. Both forms need the same guard
// afterwards -- that those symbols occur nowhere but the interchangeable
// positions of this one distinct -- so the guard is written once, over
// `ordered`, and neither form gets to state its own version of it.
struct Candidate
{
  ASTNode distinct;
  Form form;
  ASTVec ordered;
};

bool orderableSymbols(const ASTVec& symbols)
{
  std::set<ASTNode> seen;
  SourceSort sort;
  for (const ASTNode& symbol : symbols)
  {
    if (symbol.GetKind() != SYMBOL || symbol.GetType() != BITVECTOR_TYPE ||
        symbol.GetIndexWidth() != 0)
      return false;
    // Bit-vectors and sorts declared by declare-sort, because for both of them
    // bit equality on the carrier is the sort's own equality and an unsigned
    // order over the carrier is therefore a total order on the elements. A
    // float would make the order mean something else -- FP_SMT_EQ is not bit
    // equality -- and a rounding mode has five elements and no reason to be
    // ordered.
    const SourceSort::Kind kind = symbol.GetSourceSort().kind();
    if (kind != SourceSort::Kind::BitVector &&
        kind != SourceSort::Kind::Uninterpreted)
      return false;
    // The whole sort, not the carrier width. Two sorts declared by
    // declare-sort share a carrier width by default, and ordering their union
    // as one group would be a claim about a permutation that maps neither sort
    // to itself.
    if (!sort.isKnown())
      sort = symbol.GetSourceSort();
    else if (symbol.GetSourceSort() != sort)
      return false;
    if (!seen.insert(symbol).second)
      return false; // a repeat makes the distinct false, not symmetric
  }
  if (!sort.isKnown())
    return false;
  // More symbols than the sort can tell apart, which cannot be ordered because
  // no strictly increasing assignment of them exists.
  //
  // The bit-vector arm is the reachable one, which is worth stating because
  // the obvious reading is the opposite. The parser's cardinality fold tests
  // the *distinct's operand* sort; this tests the sort of the symbols being
  // ordered, and on the application form those are the operands' ARGUMENTS.
  // The two differ, so the fold cannot have already handled it: seventeen
  // applications of (_ BitVec 4) -> (_ BitVec 16) have seventeen operands in
  // a sort of 65536, which the fold passes, and seventeen arguments in a sort
  // of 16, which this refuses. Measured, with no declared sort in the file:
  // argument width 4 does not answer in 45 s, width 5 is ordered and sat in
  // 0.08 s. Deleting this arm changes pure bit-vector behaviour.
  //
  // The declared-sort arm is now the unreachable one: an over-capacity query
  // of that shape is refused before any simplifier runs -- see
  // Cpp_interface::sortCarrierExhausted -- so this never sees one. It stays
  // because the two tests answer different questions and nothing makes that
  // ordering permanent.
  const unsigned width = sort.packedWidth();
  if (width < 64 &&
      (uint64_t)symbols.size() > ((uint64_t)1 << width))
    return false;
  return true;
}

// Which form a group has, if any. Fewer than three operands is left alone:
// two are a single disequality, so there is nothing to order and the guard
// would only be risk without reward.
Form classify(const ASTNode& distinct, ASTVec& ordered)
{
  if (distinct.GetKind() != DISTINCT || distinct.Degree() < 3)
    return Form::None;

  const ASTVec operands(distinct.begin(), distinct.end());

  if (orderableSymbols(operands))
  {
    ordered = operands;
    return Form::Variables;
  }

  // One declaration, arity one, a bare variable in the argument. Arity is
  // not incidental: with two arguments the interchangeable thing is the
  // pair, ordering the first components alone would discard assignments
  // where two of them coincide, and those are reachable -- f(a,b1) and
  // f(a,b2) differ perfectly well.
  ASTVec arguments;
  arguments.reserve(operands.size());
  ASTNode declaration;
  for (const ASTNode& operand : operands)
  {
    if (operand.GetKind() != UF_APPLY || operand.Degree() != 2)
      return Form::None;
    if (declaration.IsNull())
      declaration = operand[0];
    else if (operand[0] != declaration)
      return Form::None;
    arguments.push_back(operand[1]);
  }
  if (!orderableSymbols(arguments))
    return Form::None;
  ordered = arguments;
  return Form::Arguments;
}

// One walk answering two of the guard's three questions. It records the
// polarity each candidate's node is reached at, and -- descending through
// everything except those nodes -- the SYMBOLs that occur outside them. A
// node reached at both polarities is expanded once per polarity, which is
// what makes the record exact rather than merely conservative.
void surveyOutside(const ASTNode& root, const ASTNodeSet& opaque,
                   ASTNodeSet& symbols, ASTNodeCountMap& opaquePolarity)
{
  ASTNodeCountMap seen;
  std::vector<std::pair<ASTNode, unsigned>> pending;
  pending.push_back(std::make_pair(root, POSITIVE));
  while (!pending.empty())
  {
    const ASTNode current = pending.back().first;
    const unsigned polarity = pending.back().second;
    pending.pop_back();

    int32_t& already = seen[current];
    if ((already & (int32_t)polarity) == (int32_t)polarity)
      continue;
    already |= (int32_t)polarity;

    if (opaque.count(current) != 0)
    {
      opaquePolarity[current] |= (int32_t)polarity;
      continue;
    }
    if (current.GetKind() == SYMBOL)
    {
      symbols.insert(current);
      continue;
    }

    const Kind kind = current.GetKind();
    const unsigned childPolarity =
        usedBothWays(kind) ? (POSITIVE | NEGATIVE)
                           : (kind == NOT ? flipped(polarity) : polarity);
    for (size_t i = 0; i < current.Degree(); ++i)
      pending.push_back(std::make_pair(current[i], childPolarity));
  }
}

// The third question: what a candidate's node hides from that walk. Asked
// of the node itself rather than reasoned from its shape, because the two
// forms hide different things -- the operands in one, the arguments and the
// declaration's own name in the other -- and a guard that assumed which
// would be wrong the moment a third form appeared.
void collectInside(const ASTNode& node, ASTNodeSet& symbols)
{
  ASTNodeSet visited;
  std::vector<ASTNode> pending(1, node);
  while (!pending.empty())
  {
    const ASTNode current = pending.back();
    pending.pop_back();
    if (!visited.insert(current).second)
      continue;
    if (current.GetKind() == SYMBOL)
    {
      symbols.insert(current);
      continue;
    }
    for (size_t i = 0; i < current.Degree(); ++i)
      pending.push_back(current[i]);
  }
}

ASTNode chainFor(STPMgr* manager, const ASTVec& ordered)
{
  ASTVec conjuncts;
  conjuncts.reserve(ordered.size() - 1);
  for (size_t i = 0; i + 1 < ordered.size(); ++i)
    conjuncts.push_back(
        manager->defaultNodeFactory->CreateNode(BVLT, ordered[i],
                                                ordered[i + 1]));
  return conjuncts.size() == 1
             ? conjuncts[0]
             : manager->defaultNodeFactory->CreateNode(AND, conjuncts);
}

ASTNode rebuildWithChildren(STPMgr* manager, const ASTNode& node,
                            const ASTVec& children)
{
  bool changed = false;
  for (size_t i = 0; i < children.size() && !changed; ++i)
    changed = children[i] != node[i];
  if (!changed)
    return node;
  if (node.GetType() == BOOLEAN_TYPE)
    return manager->defaultNodeFactory->CreateNode(node.GetKind(), children);
  return manager->defaultNodeFactory->CreateArrayTerm(
      node.GetKind(), node.GetIndexWidth(), node.GetValueWidth(), children);
}

} // namespace

ASTNode lowerDistinct(STPMgr* manager, const ASTNode& root)
{
  if (root.IsNull())
    return root;

  DenseNodeMap lowered;
  return postOrderRebuild(
      root, lowered,
      [&](const ASTNode& node, const ASTVec& children) -> ASTNode
      {
        if (node.GetKind() != DISTINCT)
          return rebuildWithChildren(manager, node, children);

        if (children.size() < 2)
          FatalError("distinct lowering: expected at least two operands", node);

        Kind equality = EQ;
        const SourceSort::Kind sort = children[0].GetSourceSort().kind();
        if (sort == SourceSort::Kind::Bool)
          equality = IFF;
        else if (sort == SourceSort::Kind::FloatingPoint)
          equality = FP_SMT_EQ;

        ASTVec disequalities;
        disequalities.reserve(children.size() * (children.size() - 1) / 2);
        for (size_t i = 0; i < children.size(); ++i)
          for (size_t j = i + 1; j < children.size(); ++j)
            disequalities.push_back(manager->defaultNodeFactory->CreateNode(
                NOT, manager->defaultNodeFactory->CreateNode(
                         equality, children[i], children[j])));

        assert(!disequalities.empty());
        return disequalities.size() == 1
                   ? disequalities[0]
                   : manager->defaultNodeFactory->CreateNode(AND,
                                                             disequalities);
      });
}

ASTNode applyDistinctOrdering(STPMgr* manager, const ASTNode& root,
                              size_t* ordered)
{
  if (ordered != NULL)
    *ordered = 0;
  if (root.IsNull() || root.GetType() != BOOLEAN_TYPE)
    return root;

  std::vector<Candidate> candidates;
  ASTNodeSet opaque;
  ASTNodeSet visited;
  ASTVec pending(1, root);
  while (!pending.empty())
  {
    const ASTNode node = pending.back();
    pending.pop_back();
    if (!visited.insert(node).second)
      continue;

    for (const ASTNode& child : node)
      pending.push_back(child);
    if (node.GetKind() != DISTINCT)
      continue;

    Candidate candidate;
    candidate.distinct = node;
    candidate.form = classify(node, candidate.ordered);
    if (candidate.form == Form::None)
      continue;
    candidates.push_back(candidate);
    opaque.insert(node);
  }
  if (candidates.empty())
    return root;

  ASTNodeSet outside;
  ASTNodeCountMap polarity;
  surveyOutside(root, opaque, outside, polarity);

  // A candidate concealed inside another candidate is not reached by the
  // polarity walk (the outer node is intentionally opaque), so retain the
  // reached filter even though the native-node collection itself is local to
  // this root.
  std::vector<const Candidate*> reached;
  std::vector<ASTNodeSet> concealed;
  for (const Candidate& candidate : candidates)
  {
    if (polarity.find(candidate.distinct) == polarity.end())
      continue;
    reached.push_back(&candidate);
    concealed.push_back(ASTNodeSet());
    collectInside(candidate.distinct, concealed.back());
  }

  ASTNodeMap replacements;
  for (size_t i = 0; i < reached.size(); ++i)
  {
    const Candidate& candidate = *reached[i];
    const ASTNode& distinct = candidate.distinct;
    // Positive occurrences only. The chain is the stronger claim, so under a
    // negation it becomes the weaker one, and while that stays
    // equisatisfiable under this same guard it stops the reported model from
    // being a model of the input -- a price this pass is not entitled to
    // charge.
    if (polarity.find(distinct)->second != (int32_t)POSITIVE)
      continue;
    // Each ordered symbol must occur nowhere but the positions this group
    // treats as interchangeable: not outside any candidate's node, and not
    // inside anyone else's.
    bool escapes = false;
    for (size_t s = 0; s < candidate.ordered.size() && !escapes; ++s)
    {
      const ASTNode& symbol = candidate.ordered[s];
      if (outside.count(symbol) != 0)
      {
        escapes = true;
        break;
      }
      for (size_t j = 0; j < reached.size() && !escapes; ++j)
        if (j != i && concealed[j].count(symbol) != 0)
          escapes = true;
    }
    if (escapes)
      continue;

    const ASTNode chain = chainFor(manager, candidate.ordered);
    // The clique goes only when the chain implies it.
    replacements.insert(std::make_pair(
        distinct,
        candidate.form == Form::Variables
            ? chain
            : manager->defaultNodeFactory->CreateNode(AND, distinct, chain)));
  }
  if (ordered != NULL)
    *ordered = replacements.size();
  if (replacements.empty())
    return root;

  DenseNodeMap rewritten;
  return postOrderRebuild(
      root, rewritten,
      [&](const ASTNode& node, const ASTVec& children) -> ASTNode
      {
        const ASTNodeMap::const_iterator found = replacements.find(node);
        if (found != replacements.end())
          return found->second;
        return rebuildWithChildren(manager, node, children);
      });
}

} // namespace stp
