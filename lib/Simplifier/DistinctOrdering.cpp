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

// A node under XOR, boolean EQ, or an ITE condition is used both ways at
// once, and so is everything beneath it.
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
         kind == IMPLIES;
}

// One walk answering both questions the guard asks. It records the polarity
// each candidate group's emitted node is reached at, and -- descending
// through everything *except* those nodes -- the SYMBOLs that occur outside
// them. A node reached at both polarities is expanded once per polarity,
// which is what makes the record exact rather than merely conservative.
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

// Whether a group is even the shape this pass orders: at least three operands
// (two are already one disequality, so there is nothing to gain and the guard
// would only add risk), every operand a distinct bit-vector SYMBOL of the same
// width.
//
// This runs before the occurrence walk, and decides what that walk treats as
// opaque, which is why it has to be exactly this test. Descent stops at a
// candidate's node, so the only symbols that node can conceal are its own
// operands -- and those are compared name by name afterwards. A group with a
// compound operand would conceal symbols that no later comparison names, so it
// is not made opaque at all and the walk goes straight through it.
bool candidate(const DistinctGroup& group)
{
  if (group.operands.size() < 3 || group.emitted.IsNull())
    return false;
  std::set<ASTNode> seen;
  unsigned width = 0;
  for (const ASTNode& operand : group.operands)
  {
    if (operand.GetKind() != SYMBOL || operand.GetType() != BITVECTOR_TYPE ||
        operand.GetIndexWidth() != 0)
      return false;
    // A sort whose equality is not bit equality would make the order mean
    // something else; only plain bit-vectors are ordered here.
    if (operand.GetSourceSort().kind() != SourceSort::Kind::BitVector)
      return false;
    if (width == 0)
      width = operand.GetValueWidth();
    else if (operand.GetValueWidth() != width)
      return false;
    if (!seen.insert(operand).second)
      return false; // a repeated operand makes the distinct false, not
                    // symmetric; leave it to the ordinary path
  }
  return width != 0;
}

ASTNode chainFor(STPMgr* manager, const ASTVec& operands)
{
  ASTVec conjuncts;
  conjuncts.reserve(operands.size() - 1);
  for (size_t i = 0; i + 1 < operands.size(); ++i)
    conjuncts.push_back(manager->defaultNodeFactory->CreateNode(
        BVLT, operands[i], operands[i + 1]));
  return conjuncts.size() == 1
             ? conjuncts[0]
             : manager->defaultNodeFactory->CreateNode(AND, conjuncts);
}

} // namespace

ASTNode applyDistinctOrdering(STPMgr* manager, const ASTNode& root,
                              const std::vector<DistinctGroup>& groups,
                              size_t* ordered)
{
  if (groups.empty() || root.IsNull() || root.GetType() != BOOLEAN_TYPE)
    return root;

  // Each group is judged against the root with every candidate group held
  // opaque, not just its own. Two groups sharing an operand would otherwise
  // each conclude the operand is theirs alone, and ordering both would be
  // two symmetry claims that are only valid one at a time.
  std::vector<const DistinctGroup*> candidates;
  ASTNodeSet opaque;
  for (const DistinctGroup& group : groups)
    if (candidate(group))
    {
      candidates.push_back(&group);
      opaque.insert(group.emitted);
    }
  if (candidates.empty())
    return root;

  ASTNodeSet outside;
  ASTNodeCountMap polarity;
  surveyOutside(root, opaque, outside, polarity);

  // The registry spans a whole session, so most of it is usually about some
  // other query. A group whose node the walk never reached is not part of
  // this formula and must not constrain what this formula may do -- in
  // particular it must not be counted as an overlap. Duplicate registrations
  // of one node -- the same distinct parsed twice -- are one group, or every
  // operand would look shared with itself.
  std::vector<const DistinctGroup*> reached;
  ASTNodeCountMap owners;
  ASTNodeSet counted;
  for (const DistinctGroup* candidatePtr : candidates)
  {
    if (polarity.find(candidatePtr->emitted) == polarity.end())
      continue;
    if (!counted.insert(candidatePtr->emitted).second)
      continue;
    reached.push_back(candidatePtr);
    for (const ASTNode& operand : candidatePtr->operands)
      owners[operand] += 1;
  }

  ASTNodeMap replacements;
  for (const DistinctGroup* groupPtr : reached)
  {
    const DistinctGroup& group = *groupPtr;
    // Positive occurrences only. The chain is strictly stronger than the
    // clique, so under a negation it would be strictly weaker, and while
    // that stays equisatisfiable under this same occurrence guard it stops
    // the reported model from being a model of the input -- which is a
    // price this pass is not entitled to charge.
    if (polarity.find(group.emitted)->second != (int32_t)POSITIVE)
      continue;
    // An operand this group's own node conceals must still be its own: if it
    // occurs anywhere outside, the walk saw it; if it occurs inside another
    // candidate's node, only this count can see it.
    bool escapes = false;
    for (const ASTNode& operand : group.operands)
      escapes = escapes || outside.count(operand) != 0 || owners[operand] > 1;
    if (escapes)
      continue;
    replacements.insert(
        std::make_pair(group.emitted, chainFor(manager, group.operands)));
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
        bool changed = false;
        for (size_t i = 0; i < children.size() && !changed; ++i)
          changed = children[i] != node[i];
        if (!changed)
          return node;
        if (node.GetType() == BOOLEAN_TYPE)
          return manager->defaultNodeFactory->CreateNode(node.GetKind(),
                                                         children);
        // A replacement is a formula, and the one place a formula sits under
        // a term is an if-then-else condition -- which this pass reads as
        // both polarities and therefore never rewrites. So no term should
        // reach here; rebuilding it correctly costs a line and means the
        // rebuild does not quietly depend on that argument staying true.
        return manager->defaultNodeFactory->CreateArrayTerm(
            node.GetKind(), node.GetIndexWidth(), node.GetValueWidth(),
            children);
      });
}

} // namespace stp
