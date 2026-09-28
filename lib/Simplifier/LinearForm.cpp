/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: September, 2026
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

#include "stp/Simplifier/LinearForm.h"
#include "stp/Simplifier/Simplifier.h"

#include <deque>
#include <vector>

namespace stp
{

bool LinearForm::isConstant(const ASTNode& n)
{
  return n.GetKind() == BVCONST;
}

bool LinearForm::isZeroConstant(const ASTNode& n)
{
  return isConstant(n) && CONSTANTBV::BitVector_is_empty(n.GetBVConst());
}

ASTNode LinearForm::constPlus(const ASTNode& a, const ASTNode& b,
                              unsigned width) const
{
  const ASTVec children{a, b};
  return NonMemberBVConstEvaluator(bm, BVPLUS, children, width);
}

ASTNode LinearForm::constTimes(const ASTNode& a, const ASTNode& b,
                               unsigned width) const
{
  const ASTVec children{a, b};
  return NonMemberBVConstEvaluator(bm, BVMULT, children, width);
}

ASTNode LinearForm::constNegate(const ASTNode& a, unsigned width) const
{
  const ASTVec children{a};
  return NonMemberBVConstEvaluator(bm, BVUMINUS, children, width);
}

ASTNode LinearForm::powerOfTwo(unsigned bit, unsigned width) const
{
  assert(bit < width);
  CBV value = CONSTANTBV::BitVector_Create(width, true);
  CONSTANTBV::BitVector_Bit_On(value, bit);
  return bm->CreateBVConst(value, width);
}

// The exponent when `c` is 2^k for some k above zero, and -1 otherwise. A
// coefficient of that shape is written back as the shift it came from
// rather than as a multiply: the shift is wiring, where a product is a
// circuit, and the rest of the simplifier recognises shifts.
int LinearForm::powerOfTwoExponent(const ASTNode& c, unsigned width) const
{
  if (!isConstant(c) || c.GetValueWidth() != width)
    return -1;

  int found = -1;
  const CBV bits = c.GetBVConst();
  for (unsigned i = 0; i < width; i++)
    if (CONSTANTBV::BitVector_bit_test(bits, i))
    {
      if (found >= 0)
        return -1; // more than one bit: not a power of two
      found = static_cast<int>(i);
    }

  return found > 0 ? found : -1;
}

// concat(extract(X, w-1-k, 0), 0_k), which is X * 2^k at width w. Both the
// shape the front ends produce for a shift by a constant and the shape this
// pass writes a power-of-two coefficient back as, so that reading a
// canonical form gives back the combination that produced it.
bool LinearForm::shiftShape(const ASTNode& n, unsigned width, ASTNode& source,
                            unsigned& shift) const
{
  if (n.GetKind() != BVCONCAT || n.Degree() != 2)
    return false;
  if (!isZeroConstant(n[1]))
    return false;

  const unsigned zeros = n[1].GetValueWidth();
  if (zeros == 0 || zeros >= width)
    return false;

  const ASTNode& high = n[0];
  if (high.GetKind() != BVEXTRACT || high.Degree() != 3)
    return false;
  if (!isZeroConstant(high[2]))
    return false;
  if (high[0].GetValueWidth() != width)
    return false;
  if (high[1].GetUnsignedConst() + 1 + zeros != width)
    return false;

  source = high[0];
  shift = zeros;
  return true;
}

ASTNode LinearForm::shiftBy(const ASTNode& term, unsigned shift,
                            unsigned width)
{
  assert(shift > 0 && shift < width);
  const ASTNode high =
      nf->CreateTerm(BVEXTRACT, width - shift, term,
                     nf->CreateBVConst(32, width - shift - 1),
                     nf->CreateBVConst(32, 0));
  return nf->CreateTerm(BVCONCAT, width, high, bm->CreateZeroConst(shift));
}

void LinearForm::addTerm(Combination& c, const ASTNode& atom,
                         const ASTNode& coeff)
{
  if (isZeroConstant(coeff))
    return;

  const auto found = c.terms.find(atom.GetNodeNum());
  if (found == c.terms.end())
  {
    c.terms.insert({atom.GetNodeNum(), {atom, coeff}});
    return;
  }

  found->second.second = constPlus(found->second.second, coeff, c.width);
  if (isZeroConstant(found->second.second))
    c.terms.erase(found);
}

// Reads a combination back out of an already-canonical node. Everything the
// factory may have done to the spelling emit() chose -- a coefficient of
// minus one written as BVUMINUS, a sum written as BVSUB -- is understood
// here, so that the canonical form of a canonical form is itself.
//
// The pending list is on the heap because a sum spliced into a sum is what
// this is for: the input decides how far it descends.
void LinearForm::addScaled(Combination& c, const ASTNode& node,
                           const ASTNode& coeff)
{
  std::vector<std::pair<ASTNode, ASTNode>> pending;
  pending.emplace_back(node, coeff);

  while (!pending.empty())
  {
    const ASTNode current = pending.back().first;
    const ASTNode scale = pending.back().second;
    pending.pop_back();

    if (isZeroConstant(scale))
      continue;

    if (isConstant(current))
    {
      c.constant = constPlus(c.constant, constTimes(scale, current, c.width),
                             c.width);
      continue;
    }

    const Kind k = current.GetKind();

    if (k == BVPLUS)
    {
      for (const ASTNode& child : current.GetChildren())
        pending.emplace_back(child, scale);
      continue;
    }

    if (k == BVSUB && current.Degree() == 2)
    {
      pending.emplace_back(current[0], scale);
      pending.emplace_back(current[1], constNegate(scale, c.width));
      continue;
    }

    if (k == BVUMINUS)
    {
      pending.emplace_back(current[0], constNegate(scale, c.width));
      continue;
    }

    {
      ASTNode source;
      unsigned shift = 0;
      if (shiftShape(current, c.width, source, shift))
      {
        pending.emplace_back(
            source, constTimes(scale, powerOfTwo(shift, c.width), c.width));
        continue;
      }
    }

    if (k == BVMULT)
    {
      ASTNode folded = scale;
      const ASTNode* symbolic = NULL;
      bool simple = true;

      for (const ASTNode& child : current.GetChildren())
      {
        if (isConstant(child))
          folded = constTimes(folded, child, c.width);
        else if (symbolic == NULL)
          symbolic = &child;
        else
        {
          simple = false;
          break;
        }
      }

      if (simple)
      {
        if (symbolic == NULL)
          c.constant = constPlus(c.constant, folded, c.width);
        else
          pending.emplace_back(*symbolic, folded);
        continue;
      }
    }

    addTerm(c, current, scale);
  }
}

bool LinearForm::combinationOf(const ASTNode& n, const ASTVec& children,
                               unsigned width, Combination& out)
{
  const ASTNode one = bm->CreateOneConst(width);

  switch (n.GetKind())
  {
    case BVPLUS:
      for (const ASTNode& child : children)
        addScaled(out, child, one);
      return true;

    case BVUMINUS:
      addScaled(out, children[0], constNegate(one, width));
      return true;

    case BVSUB:
      addScaled(out, children[0], one);
      addScaled(out, children[1], constNegate(one, width));
      return true;

    case BVMULT:
    {
      ASTNode folded = one;
      const ASTNode* symbolic = NULL;

      for (const ASTNode& child : children)
      {
        if (isConstant(child))
          folded = constTimes(folded, child, width);
        else if (symbolic == NULL)
          symbolic = &child;
        else
          return false; // two symbolic operands: not a linear combination
      }

      if (symbolic == NULL)
        out.constant = folded;
      else
        addScaled(out, *symbolic, folded);
      return true;
    }

    case BVCONCAT:
    {
      // A shift left by a constant, which the front ends and the node
      // factory both spell this way. Anything else -- a non-zero low part,
      // an extract that does not start at bit zero, a source term of
      // another width -- is an atom.
      const ASTNode rebuilt =
          nf->CreateArrayTerm(BVCONCAT, 0, width, children);

      ASTNode source;
      unsigned shift = 0;
      if (!shiftShape(rebuilt, width, source, shift))
        return false;

      addScaled(out, source, powerOfTwo(shift, width));
      return true;
    }

    default:
      return false;
  }
}

ASTNode LinearForm::emit(const Combination& c)
{
  ASTVec addends;
  addends.reserve(c.terms.size() + 1);

  for (const auto& entry : c.terms)
  {
    const ASTNode& atom = entry.second.first;
    const ASTNode& coeff = entry.second.second;

    const int exponent = powerOfTwoExponent(coeff, c.width);

    if (coeff == bm->CreateOneConst(c.width))
      addends.push_back(atom);
    else if (exponent > 0)
      addends.push_back(shiftBy(atom, static_cast<unsigned>(exponent), c.width));
    else
      addends.push_back(nf->CreateTerm(BVMULT, c.width, coeff, atom));
  }

  if (addends.empty() || !isZeroConstant(c.constant))
    addends.push_back(c.constant);

  if (addends.size() == 1)
    return addends[0];

  return nf->CreateTerm(BVPLUS, c.width, addends);
}

ASTNode LinearForm::rebuild(const ASTNode& n, const ASTVec& children)
{
  bool changed = false;
  for (size_t i = 0; i < children.size(); i++)
    if (children[i] != n[i])
    {
      changed = true;
      break;
    }

  if (!changed)
    return n;

  if (n.GetType() == BOOLEAN_TYPE)
    return nf->CreateNode(n.GetKind(), children);

  return nf->CreateArrayTerm(n.GetKind(), n.GetIndexWidth(),
                             n.GetValueWidth(), children);
}

ASTNode LinearForm::canonicalise(const ASTNode& n, const ASTVec& children)
{
  if (n.GetType() != BITVECTOR_TYPE || n.GetIndexWidth() != 0)
    return rebuild(n, children);

  const unsigned width = n.GetValueWidth();
  if (width == 0)
    return rebuild(n, children);

  Combination combination;
  combination.width = width;
  combination.constant = bm->CreateZeroConst(width);

  if (!combinationOf(n, children, width, combination))
    return rebuild(n, children);

  // Distributing a constant over a sum writes one multiply per addend. A
  // combination wider than this keeps the spelling it arrived with, which
  // is a decision about the combination and not about the term, so two
  // equal terms are still treated alike.
  if (combination.terms.size() > addendLimit)
    return rebuild(n, children);

  const ASTNode result = emit(combination);
  if (result != n)
    rewritten++;
  return result;
}

// The walk one node is part-way through. On the heap, because the input
// decides how many are live at once: a call per level of the DAG exhausts
// the stack on the formulas that exist. See DeepDag_Test.cpp.
struct LinearForm::Frame
{
  ASTNode n;
  ASTVec children;
  unsigned next = 0;
  bool waiting = false;

  explicit Frame(const ASTNode& n_) : n(n_) { children.reserve(n_.Degree()); }
};

ASTNode LinearForm::topLevel(const ASTNode& n)
{
  bm->GetRunTimes()->start(RunTimes::LinearForm);

  rewritten = 0;

  ASTNode result = n;

  if (n.Degree() > 0)
  {
    // A deque, so that descending into a child never moves the frames above
    // it: `current` stays valid across a push.
    std::deque<Frame> stack;
    stack.emplace_back(n);

    while (true)
    {
      Frame& current = stack.back();

      if (current.waiting)
      {
        current.children.push_back(result);
        current.waiting = false;
      }

      bool descended = false;

      while (current.next < current.n.Degree())
      {
        const ASTNode& child = current.n[current.next++];

        if (child.Degree() == 0)
        {
          current.children.push_back(child);
          continue;
        }

        const auto known = fromTo.find(child.GetNodeNum());
        if (known != fromTo.end())
        {
          current.children.push_back(known->second);
          continue;
        }

        // Where the recursive version called itself. Nothing above may be
        // read after the push.
        current.waiting = true;
        stack.emplace_back(child);
        descended = true;
        break;
      }

      if (descended)
        continue;

      Frame& done = stack.back();
      result = canonicalise(done.n, done.children);
      fromTo.insert({done.n.GetNodeNum(), result});

      stack.pop_back();
      if (stack.empty())
        break;
    }
  }

  if (bm->UserFlags.stats_flag)
    std::cerr << "{LinearForm} Terms given a canonical form:" << rewritten
              << std::endl;

  fromTo.clear();

  bm->GetRunTimes()->stop(RunTimes::LinearForm);
  return result;
}
}
