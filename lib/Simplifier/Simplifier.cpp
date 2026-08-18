/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen, David L. Dill
 *
 * BEGIN DATE: November, 2005
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

#include "stp/Simplifier/Simplifier.h"
#include "stp/Extensionality/ExtensionalityContext.h"
#include "stp/FloatBlaster/FloatBlaster.h"
#include <cassert>
#include <cmath>
#include <cstdint>
#include <deque>

namespace stp
{
using std::cerr;
using std::endl;


// If enabled, simplifyTerm will simplify all the arguments to a function before
// attempting
// the simplification of that function. Without this option the case will be
// selected for
// each kind, and that case needs to simplify the arguments.

// Longer term, this means that each function doesn't need to worry about
// calling simplify
// on it's arguments (I suspect some paths don't call simplify on their
// arguments). But it
// does mean that we can't short cut, for example, if the first argument to a
// BVOR is all trues,
// then all the other arguments have already been simplified, so won't be
// short-cutted.

// is it ITE(p,bv0[1], bv1[1])  OR  ITE(p,bv0[0], bv1[0])
bool isPropositionToTerm(const ASTNode& n)
{
  if (n.GetType() != BITVECTOR_TYPE)
    return false;
  if (n.GetValueWidth() != 1)
    return false;
  if (n.GetKind() != ITE)
    return false;
  if (!n[1].isConstant())
    return false;
  if (!n[2].isConstant())
    return false;
  if (n[1] == n[0])
    return false;
  return true;
}

bool Simplifier::CheckSimplifyMap(const ASTNode& key, ASTNode& output,
                                  bool pushNeg)
{
  if (!pushNeg && key.isSimplfied())
  {
    output = key;
    return true;
  }

  DenseNodeMap::iterator it, itend;
  it = pushNeg ? SimplifyNegMap->find(key) : SimplifyMap->find(key);
  itend = pushNeg ? SimplifyNegMap->end() : SimplifyMap->end();

  if (it != itend)
  {
    output = it->second;
    CountersAndStats("Successful_CheckSimplifyMap", _bm);
    return true;
  }

  if (pushNeg && (it = SimplifyMap->find(key)) != SimplifyMap->end())
  {
    output = (ASTFalse == it->second)
                 ? ASTTrue
                 : (ASTTrue == it->second) ? ASTFalse
                                           : nf->CreateNode(NOT, it->second);
    CountersAndStats("2nd_Successful_CheckSimplifyMap", _bm);
    return true;
  }

  return false;
}

void Simplifier::UpdateSimplifyMap(const ASTNode& key, const ASTNode& value,
                                   bool pushNeg)
{
  assert(!value.IsNull());

  // Don't add leaves. Leaves are easy to recalculate, no need
  // to cache.
  if (0 == key.Degree())
    return;

  if (pushNeg)
    (*SimplifyNegMap)[key] = value;
  else
    (*SimplifyMap)[key] = value;

  if (!pushNeg && key == value)
  {
    key.hasBeenSimplfied();
  }
}

// Substitution Map methods....

bool Simplifier::UpdateSolverMap(const ASTNode& key, const ASTNode& value)
{
  return substitutionMap.UpdateSolverMap(key, value);
}

bool Simplifier::InsideSubstitutionMap(const ASTNode& key, ASTNode& output)
{
  return substitutionMap.InsideSubstitutionMap(key, output);
}

ASTNode Simplifier::applySubstitutionMap(const ASTNode& n)
{
  return substitutionMap.applySubstitutionMap(n);
}

ASTNode Simplifier::applySubstitutionMapAtTopLevel(const ASTNode& topLevel)
{
  return substitutionMap.applySubstitutionMapAtTopLevel(topLevel);
}

ASTNode Simplifier::applySubstitutionMapUntilArrays(const ASTNode& n)
{
  return substitutionMap.applySubstitutionMapUntilArrays(n);
}

ASTNode Simplifier::applySubstitutionMapUntilArrays(const ASTNode& n, DenseNodeMap& cache)
{
  return substitutionMap.applySubstitutionMapUntilArrays(n,cache);
}

bool Simplifier::InsideSubstitutionMap(const ASTNode& key)
{
  return substitutionMap.InsideSubstitutionMap(key);
}
bool Simplifier::UpdateSubstitutionMapFewChecks(const ASTNode& e0,
                                                const ASTNode& e1)
{
  return substitutionMap.UpdateSubstitutionMapFewChecks(e0, e1);
}

bool Simplifier::UpdateSubstitutionMap(const ASTNode& e0, const ASTNode& e1)
{
  return substitutionMap.UpdateSubstitutionMap(e0, e1);
}
// --- Substitution Map methods....

bool Simplifier::CheckMultInverseMap(const ASTNode& key, ASTNode& output)
{
  const auto it = MultInverseMap.find(key);
  if (it != MultInverseMap.end())
  {
    output = it->second;
    return true;
  }
  return false;
}

void Simplifier::UpdateMultInverseMap(const ASTNode& key, const ASTNode& value)
{
  MultInverseMap[key] = value;
}

ASTNode Simplifier::SimplifyFormula_NoRemoveWrites(const ASTNode& b,
                                                   bool pushNeg)
{
  ASTNode out = SimplifyFormula(b, pushNeg);
  return out;
}

// I like simplify to have been run on all the nodes.
void Simplifier::checkIfInSimplifyMap(const ASTNode& n, ASTNodeSet visited)
{
  if (n.isConstant() || (n.GetKind() == SYMBOL))
    return;

  if (visited.find(n) != visited.end())
    return;

  if (SimplifyMap->find(n) == SimplifyMap->end())
  {
    cerr << "not found";
    cerr << n;
    assert(false);
  }

  for (size_t i = 0; i < n.Degree(); i++)
  {
    checkIfInSimplifyMap(n[i], visited);
  }

  visited.insert(n);
}

ASTNodeMap Simplifier::FindConsts_TopLevel(const ASTNode& b, bool pushNeg)
{
  assert(_bm->UserFlags.optimize_flag);
  _bm->GetRunTimes()->start(RunTimes::SimplifyTopLevel);
  ASTNode out = SimplifyFormula(b, pushNeg);

  ASTNodeMap constants;
  
  for (const auto& e: *SimplifyMap)
  {
    if (e.second.isConstant())
    {
      constants.insert(e);
    }
  }
    
  ResetSimplifyMaps();
  _bm->GetRunTimes()->stop(RunTimes::SimplifyTopLevel);
  return constants;
}


// The SimplifyMaps on entry to the topLevel functions may contain
// useful entries.  E.g. The BVSolver may call SimplifyTerm()
ASTNode Simplifier::simplifyAlone(STPMgr* bm, const ASTNode& n)
{
  SubstitutionMap localSm(bm);
  Simplifier localSimp(bm, &localSm);
  return localSimp.SimplifyFormula_TopLevel(n, false);
}

ASTNode Simplifier::SimplifyFormula_TopLevel(const ASTNode& b, bool pushNeg)
{
  assert(_bm->UserFlags.optimize_flag);
  _bm->GetRunTimes()->start(RunTimes::SimplifyTopLevel);
  ASTNode out = SimplifyFormula(b, pushNeg);
  ASTNodeSet visited;
  // checkIfInSimplifyMap(out,visited);
  ResetSimplifyMaps();
  _bm->GetRunTimes()->stop(RunTimes::SimplifyTopLevel);
  return out;
}

ASTNode Simplifier::SimplifyTerm_TopLevel(const ASTNode& b)
{
  assert(_bm->UserFlags.optimize_flag);
  _bm->GetRunTimes()->start(RunTimes::SimplifyTopLevel);
  ASTNode out = SimplifyTerm(b);
  ResetSimplifyMaps();
  _bm->GetRunTimes()->stop(RunTimes::SimplifyTopLevel);
  return out;
}

bool Simplifier::formulaShortcut(const ASTNode& b, bool pushNeg, ASTNode& a,
                                 ASTNode& out)
{
  assert(_bm->UserFlags.optimize_flag);
  assert(BOOLEAN_TYPE == b.GetType());

  if (b.isConstant())
  {
    out = pushNeg ? nf->CreateNode(NOT, b) : b;
    return true;
  }

  if (CheckSimplifyMap(b, out, pushNeg))
    return true;

  // pullUpITE can change the Kind of the node.
  a = PullUpITE(b);
  return false;
}

// A concat's leading constant, if it has one. Keep the answer itself rather
// than only its width: callers inspect several bits, and chasing the first
// child from the root again for every bit makes that quadratic in a deep
// concat's depth and its constant prefix width.
const ASTNode* mostSignificantConstant(const ASTNode& n)
{
  const ASTNode* current = &n;
  while (current->GetKind() == BVCONCAT)
    current = &(*current)[0];
  return current->isConstant() ? current : NULL;
}

unsigned getConstantBit(const ASTNode& constant, const unsigned i)
{
  assert(constant.GetKind() == BVCONST && i < constant.GetValueWidth());
  return CONSTANTBV::BitVector_bit_test(
             constant.GetBVConst(), constant.GetValueWidth() - 1 - i)
             ? 1
             : 0;
}

unsigned numberOfLeadingZeroes(const ASTNode& n)
{
  const ASTNode* constant = mostSignificantConstant(n);
  if (constant == NULL)
    return 0;

  const unsigned c = constant->GetValueWidth();
  for (unsigned i = 0; i < c; i++)
    if (getConstantBit(*constant, i) != 0)
      return i;
  return c;
}

ASTNode Simplifier::CreateSimplifiedINEQ(const Kind k_i, const ASTNode& left_i,
                                         const ASTNode& right_i, bool pushNeg)
{

  // We reduce down to four possible inequalities.
  // NB. If the simplifying node factory is enabled, it will have done this
  // already.
  bool swap = false;
  if (k_i == BVLT || k_i == BVLE || k_i == BVSLT || k_i == BVSLE)
    swap = true;

  const ASTNode& left = (swap) ? right_i : left_i;
  const ASTNode& right = (swap) ? left_i : right_i;

  Kind k = k_i;
  if (k == BVLT)
    k = BVGT;
  else if (k == BVLE)
    k = BVGE;
  else if (k == BVSLT)
    k = BVSGT;
  else if (k == BVSLE)
    k = BVSGE;

  assert(k == BVGT || k == BVGE || k == BVSGT || k == BVSGE);

  ASTNode output;
  if (BVCONST == left.GetKind() && BVCONST == right.GetKind())
  {
    output = BVConstEvaluator(nf->CreateNode(k, left, right));
    output = pushNeg ? (ASTFalse == output) ? ASTTrue : ASTFalse : output;
    return output;
  }

  if (k == BVLT || k == BVGT || k == BVSLT || k == BVSGT)
  {
    if (left == right)
      return pushNeg ? ASTTrue : ASTFalse;
  }

  if (k == BVLE || k == BVGE || k == BVSLE || k == BVSGE)
  {
    if (left == right)
      return pushNeg ? ASTFalse : ASTTrue;
  }

  // NB. Comparisons that differing leading constant bits decide are
  // resolved by strength reduction: the fixed-bit transfer functions for
  // concat and the comparisons subsume that reasoning.

  const unsigned len = left.GetValueWidth();

  const ASTNode unsigned_min = nf->CreateZeroConst(len);
  const ASTNode one = nf->CreateOneConst(len);
  const ASTNode unsigned_max = nf->CreateMaxConst(len);

  switch (k)
  {
    case BVGT:
      if (left == unsigned_min)
      {
        output = pushNeg ? ASTTrue : ASTFalse;
      }
      else if (one == left)
      {
        output = CreateSimplifiedEQ(right, unsigned_min);
        output = pushNeg ? nf->CreateNode(NOT, output) : output;
      }
      else if (right == unsigned_max)
      {
        output = pushNeg ? ASTTrue : ASTFalse;
      }
      else
      {
        output = pushNeg ? nf->CreateNode(BVLE, left, right)
                         : nf->CreateNode(BVLT, right, left);
      }
      break;
    case BVGE:
      if (right == unsigned_min)
      {
        output = pushNeg ? ASTFalse : ASTTrue;
      }
      else if (unsigned_max == left)
      {
        output = pushNeg ? ASTFalse : ASTTrue;
      }
      else if (unsigned_min == left)
      {
        output = CreateSimplifiedEQ(right, unsigned_min);
        output = pushNeg ? nf->CreateNode(NOT, output) : output;
      }
      else
      {
        output = pushNeg ? nf->CreateNode(BVLT, left, right)
                         : nf->CreateNode(BVLE, right, left);
      }
      break;
    case BVSGE:
    {
      output = nf->CreateNode(k, left, right);
      output = pushNeg ? nf->CreateNode(NOT, output) : output;
    }

    break;
    case BVSGT:
      output = nf->CreateNode(k, left, right);
      output = pushNeg ? nf->CreateNode(NOT, output) : output;
      break;
    default:
      FatalError("Wrong Kind");
      break;
  }

  assert(!output.IsNull());
  return output;
}

// turns say (bvslt (ite a b c) (ite a d e)) INTO (ite a (bvslt b d)
// (bvslt c e)) Expensive. But makes some other simplifications
// possible.
ASTNode Simplifier::PullUpITE(const ASTNode& in)
{
  if (2 != in.GetChildren().size())
    return in;
  if (ITE != in[0].GetKind())
    return in;
  if (ITE != in[1].GetKind())
    return in;
  if (in[0][0] != in[1][0]) // if the conditional is not equal.
    return in;

  // Consider equals. It takes bitvectors and returns a boolean.
  // Consider add. It takes bitvectors and returns bitvectors.
  // Consider concat. The bitwidth of each side could vary.

  ASTNode l1;
  ASTNode l2;
  ASTNode result;

  if (in.GetType() == BOOLEAN_TYPE)
  {
    l1 = nf->CreateNode(in.GetKind(), in[0][1], in[1][1]);
    l2 = nf->CreateNode(in.GetKind(), in[0][2], in[1][2]);
    result = nf->CreateNode(ITE, in[0][0], l1, l2);
  }
  else
  {
    l1 = nf->CreateTerm(in.GetKind(), in.GetValueWidth(), in[0][1], in[1][1]);
    l2 = nf->CreateTerm(in.GetKind(), in.GetValueWidth(), in[0][2], in[1][2]);
    result = nf->CreateTerm(ITE, in.GetValueWidth(), in[0][0], l1, l2);
  }

  // A rebuilt node cannot lose the input's floating-point format. The
  // interesting case is not a float operation (those derive their format
  // from their children) but a plain bitvector node carrying a format
  // *stamp*: the canonicalised index of a float-indexed array is a
  // bitvector circuit stamped with the index's format (see FpTotalise),
  // and pulling an if-then-else out of, say, its concatenation must
  // keep the stamp or the node changes type. No-op for everything else.
  result = FloatBlaster::withFormat(_bm, result, in.GetExpWidth(),
                                    in.GetSigWidth());

  assert(result.GetType() == in.GetType());
  assert(result.GetValueWidth() == in.GetValueWidth());
  assert(result.GetIndexWidth() == in.GetIndexWidth());
  assert(BVTypeCheck(result));

  return result;
}

// takes care of some simple ITE Optimizations in the context of equations
ASTNode Simplifier::ITEOpt_InEqs(const ASTNode& in, ASTNode& conditionToNegate)
{
  CountersAndStats("ITEOpts_InEqs", _bm);

  if (!(EQ == in.GetKind()))
  {
    return in;
  }

  ASTNode output;
  if (CheckSimplifyMap(in, output, false))
  {
    return output;
  }

  const ASTNode& in1 = in[0];
  const ASTNode& in2 = in[1];
  const Kind k1 = in1.GetKind();
  const Kind k2 = in2.GetKind();
  if (in1 == in2)
  {
    // terms are syntactically the same
    output = ASTTrue;
  }
  else if (BVCONST == k1 && BVCONST == k2)
  {
    // Distinct constant nodes may still spell one value (a float
    // constant interns apart from the plain constant with its bits).
    output = constantsSameBits(in1, in2) ? ASTTrue : ASTFalse;
  }
  else if (ITE == k1 && BVCONST == in1[1].GetKind() &&
           BVCONST == in1[2].GetKind() && BVCONST == k2)
  {
    // if one side is a BVCONST and the other side is an ITE over
    // BVCONST then we can do the following optimization:
    //
    // c = ITE(cond,c,d) <=> cond
    //
    // similarly ITE(cond,c,d) = c <=> cond
    //
    // c = ITE(cond,d,c) <=> NOT(cond)
    //
    // similarly ITE(cond,d,c) = d <=> NOT(cond)
    // The "other branch differs" side conditions compare values, not
    // nodes: with both branches spelling one value the equality holds
    // whatever the condition, and folding to the condition would be
    // wrong.
    ASTNode cond = in1[0];
    if (in1[1] == in2 && constantsDenoteDifferentValues(in2, in1[2]))
    {
      // ITE(cond, c, d) = c <=> cond
      output = cond;
    }
    else if (in1[2] == in2 && constantsDenoteDifferentValues(in2, in1[1]))
    {
      conditionToNegate = cond;
      return ASTUndefined;
    }
    else
    {
      // last resort is to nf->CreateNode
      output = nf->CreateNode(EQ, in1, in2);
    }
  }
  else if (ITE == k2 && BVCONST == in2[1].GetKind() &&
           BVCONST == in2[2].GetKind() && BVCONST == k1)
  {
    ASTNode cond = in2[0];
    if (in2[1] == in1 && constantsDenoteDifferentValues(in1, in2[2]))
    {
      // ITE(cond, c, d) = c <=> cond
      output = cond;
    }
    else if (in2[2] == in1 && constantsDenoteDifferentValues(in1, in2[1]))
    {
      conditionToNegate = cond;
      return ASTUndefined;
    }
    else
    {
      // last resort is to CreateNode
      output = nf->CreateNode(EQ, in1, in2);
    }
  }
  else
  {
    // last resort is to CreateNode
    output = nf->CreateNode(EQ, in1, in2);
  }

  UpdateSimplifyMap(in, output, false);
  return output;
}

// Tries to simplify the input to TRUE/FALSE. if it fails, then
// return the constructed equality
ASTNode Simplifier::CreateSimplifiedEQ(const ASTNode& in1, const ASTNode& in2)
{
  CountersAndStats("CreateSimplifiedEQ", _bm);
  const Kind k1 = in1.GetKind();
  const Kind k2 = in2.GetKind();

  if (in1 == in2)
    // terms are syntactically the same
    return ASTTrue;

  // Two constant nodes still may be semantically equal: a float constant
  // interns apart from the plain constant with its bits, so compare the
  // bits, not the identities.
  if (BVCONST == k1 && BVCONST == k2)
    return constantsSameBits(in1, in2) ? ASTTrue : ASTFalse;

  // Check if some of the leading constant bits are different. Fancier code
  // would check
  // each bit, not just the leading bits.
  const ASTNode* leading1 = mostSignificantConstant(in1);
  const ASTNode* leading2 = mostSignificantConstant(in2);
  const unsigned constStart =
      leading1 == NULL || leading2 == NULL
          ? 0
          : std::min(leading1->GetValueWidth(), leading2->GetValueWidth());

  for (unsigned i = 0; i < constStart; i++)
  {
    const unsigned a = getConstantBit(*leading1, i);
    const unsigned b = getConstantBit(*leading2, i);
    assert(a == 1 || a == 0);
    assert(b == 1 || b == 0);

    if (a != b)
      return ASTFalse;
  }

  // The above loop has determined that the leading bits are the same.
  if (constStart > 0)
  {
    const unsigned newWidth = in1.GetValueWidth() - constStart;
    ASTNode zero = nf->CreateZeroConst(32);

    ASTNode lhs = nf->CreateTerm(BVEXTRACT, newWidth, in1,
                                 nf->CreateBVConst(32, newWidth - 1), zero);
    ASTNode rhs = nf->CreateTerm(BVEXTRACT, newWidth, in2,
                                 nf->CreateBVConst(32, newWidth - 1), zero);
    ASTNode r = nf->CreateNode(EQ, lhs, rhs);
    assert(BVTypeCheck(r));
    return r;
  }

  // If both the children are concats split them apart.
  // nb. This doesn't cover the case when the children are organised
  // differently:
  // (concat (concat A B) C) == (concat A (concat B C))
  if (k1 == BVCONCAT && k2 == BVCONCAT &&
      in1[0].GetValueWidth() == in2[0].GetValueWidth())
  {
    // Named variables, so that the nodes aren't built in whatever order the
    // compiler picks to evaluate the arguments in.
    const ASTNode topEq = nf->CreateNode(EQ, in1[0], in2[0]);
    const ASTNode bottomEq = nf->CreateNode(EQ, in1[1], in2[1]);
    return nf->CreateNode(AND, topEq, bottomEq);
  }

  // If the rhs is a concat, and the lhs is a constant. Split.
  if (k1 == BVCONST && k2 == BVCONCAT)
  {
    int width = in1.GetValueWidth();
    int bottomW = in2[1].GetValueWidth();
    ASTNode zero = nf->CreateZeroConst(32);

    // split the constant.
    ASTNode top = nf->CreateTerm(BVEXTRACT, width - bottomW, in1,
                                 nf->CreateBVConst(32, width - 1),
                                 nf->CreateBVConst(32, bottomW));
    ASTNode bottom = nf->CreateTerm(BVEXTRACT, bottomW, in1,
                                    nf->CreateBVConst(32, bottomW - 1), zero);
    assert(BVTypeCheck(top));
    assert(BVTypeCheck(bottom));

    const ASTNode topEq = nf->CreateNode(EQ, top, in2[0]);
    const ASTNode bottomEq = nf->CreateNode(EQ, bottom, in2[1]);
    ASTNode r = nf->CreateNode(AND, topEq, bottomEq);

    return r;
  }

  if (k2 == ITE && (in2[1] == in1) && in1.GetType() == BITVECTOR_TYPE)
  {
    ASTNode eq = nf->CreateNode(EQ, in1, in2[2]);
    return nf->CreateNode(OR, in2[0], eq);
  }

  if (k2 == ITE && (in2[2] == in1) && in1.GetType() == BITVECTOR_TYPE)
  {
    ASTNode eq = nf->CreateNode(EQ, in1, in2[1]);
    return nf->CreateNode(OR, nf->CreateNode(NOT, in2[0]), eq);
  }

  // last resort is to CreateNode
  return nf->CreateNode(EQ, in1, in2);
}

// nb. this is sometimes used to build array terms.
// accepts cond == t1, then part is t2, and else part is t3
ASTNode Simplifier::CreateSimplifiedTermITE(const ASTNode& in0,
                                            const ASTNode& in1,
                                            const ASTNode& in2)
{
  const ASTNode& t0 = in0;
  const ASTNode& t1 = in1;
  const ASTNode& t2 = in2;
  CountersAndStats("CreateSimplifiedITE", _bm);
  if (!_bm->UserFlags.optimize_flag)
  {
    if (t1.GetValueWidth() != t2.GetValueWidth())
    {
      cerr << "t2 is : = " << t2;
      FatalError("CreateSimplifiedTermITE: "
                 "the lengths of the two branches don't match",
                 t1);
    }
    if (t1.GetIndexWidth() != t2.GetIndexWidth())
    {
      cerr << "t2 is : = " << t2;
      FatalError("CreateSimplifiedTermITE: "
                 "the lengths of the two branches don't match",
                 t1);
    }
    return nf->CreateArrayTerm(ITE, t1.GetIndexWidth(), t1.GetValueWidth(), t0,
                               t1, t2);
  }

  if (t0 == ASTTrue)
    return t1;
  if (t0 == ASTFalse)
    return t2;
  if (t1 == t2)
    return t1;

  return nf->CreateArrayTerm(ITE, t1.GetIndexWidth(), t1.GetValueWidth(), t0,
                             t1, t2);
}

ASTNode Simplifier::CreateSimplifiedFormulaITE(const ASTNode& in0,
                                               const ASTNode& in1,
                                               const ASTNode& in2)
{
  const ASTNode& t0 = in0;
  const ASTNode& t1 = in1;
  const ASTNode& t2 = in2;
  CountersAndStats("CreateSimplifiedFormulaITE", _bm);

  if (_bm->UserFlags.optimize_flag)
  {
    if (t0 == ASTTrue)
      return t1;
    if (t0 == ASTFalse)
      return t2;
    if (t1 == t2)
      return t1;
  }
  ASTNode result = nf->CreateNode(ITE, t0, t1, t2);
  assert(BVTypeCheck(result));
  return result;
}

// Every connective is where a formula nests: each operand is simplified by
// coming back through here, so a formula nested as deeply as the input runs
// the stack out. The frames live on the heap instead.
//
// The AND/OR spine was walked this way already, on the argument that the
// other kinds "nest through each other rather than through a spine, and
// nothing has been seen to reach a depth that matters". Something has: a
// query built from 8,000 nested fp.add operations lowers to NOT and
// if-then-else nested that deeply, and it died in exactly those two arms --
// below the ~9,300 of the deepest input we have. So all of them are one walk
// now. See DeepDag_Test.cpp.
ASTNode Simplifier::SimplifyFormula(const ASTNode& b, bool pushNeg)
{
  return simplifyNode(b, pushNeg, SimplifyJob::Formula);
}

class Simplifier::SimplifyDriver
{
  Simplifier& owner;
  NodeFactory* const nf;
  STPMgr* const _bm;
  ASTNode& ASTTrue;
  ASTNode& ASTFalse;
  ASTNode& ASTUndefined;

  bool formulaShortcut(const ASTNode& b, const bool pushNeg, ASTNode& a,
                       ASTNode& out)
  {
    return owner.formulaShortcut(b, pushNeg, a, out);
  }

  bool CheckSimplifyMap(const ASTNode& key, ASTNode& output, const bool pushNeg)
  {
    return owner.CheckSimplifyMap(key, output, pushNeg);
  }

  void UpdateSimplifyMap(const ASTNode& key, const ASTNode& value,
                         const bool pushNeg)
  {
    owner.UpdateSimplifyMap(key, value, pushNeg);
  }

  bool InsideSubstitutionMap(const ASTNode& key, ASTNode& output)
  {
    return owner.InsideSubstitutionMap(key, output);
  }

  ASTNode ITEOpt_InEqs(const ASTNode& input, ASTNode& conditionToNegate)
  {
    return owner.ITEOpt_InEqs(input, conditionToNegate);
  }

  ASTNode LhsMinusRhsTerm(const ASTNode& equality,
                          const ASTNode& simplifiedNegatedRhs)
  {
    return owner.LhsMinusRhsTerm(equality, simplifiedNegatedRhs);
  }

  ASTNode CreateSimplifiedEQ(const ASTNode& left, const ASTNode& right)
  {
    return owner.CreateSimplifiedEQ(left, right);
  }

  ASTNode CreateSimplifiedINEQ(const Kind kind, const ASTNode& left,
                               const ASTNode& right, const bool pushNeg)
  {
    return owner.CreateSimplifiedINEQ(kind, left, right, pushNeg);
  }

  ASTNode CreateSimplifiedTermITE(const ASTNode& condition,
                                  const ASTNode& thenValue,
                                  const ASTNode& elseValue)
  {
    return owner.CreateSimplifiedTermITE(condition, thenValue, elseValue);
  }

  ASTNode BVConstEvaluator(const ASTNode& node)
  {
    return owner.BVConstEvaluator(node);
  }

  ASTNode PullUpITE(const ASTNode& node) { return owner.PullUpITE(node); }

  bool hasBeenSimplified(const ASTNode& node)
  {
    return owner.hasBeenSimplified(node);
  }

  ASTNode simplify_term_switch(const ASTNode& actualInput, ASTNode& input,
                               ASTNode& output, const Kind kind,
                               const unsigned valueWidth)
  {
    return owner.simplify_term_switch(actualInput, input, output, kind,
                                      valueWidth);
  }

  // What one node is part-way through. `b` is the node as it arrived and `a`
  // as PullUpITE left it; both are recorded against the answer, as
  // SimplifyFormula and simplifyNonAndOr each did.
  //
  // `pushNeg` is per frame, where the AND/OR-only driver took one for the
  // whole walk. That arm does hand its own negation to every operand, but the
  // others choose per operand: NAND and NOR push it into both, IMPLIES and
  // IFF into one, and a NOT counts the run of NOTs above it and starts again
  // from the parity of that count.
  //
  // Each arm of the switch below is one of the functions this replaced, and
  // each phase is a point where that function called SimplifyFormula and has
  // to be able to stop:
  //
  //     AND, OR              SimplifyAndOrFormula
  //     NOT                  SimplifyNotFormula
  //     XOR                  SimplifyXorFormula
  //     NAND, NOR, IMPLIES   SimplifyNandFormula, SimplifyNorFormula,
  //                          SimplifyImpliesFormula
  //     IFF                  SimplifyIffFormula
  //     ITE                  SimplifyIteFormula
  //     default              SimplifyAtomicFormula
  //
  // An arm reads the same way as the function did if `finish` is read as its
  // `return`, and `requestFormula` as the call it made just above one. Nothing
  // else of those functions moved: the head each shared is formulaShortcut
  // plus the map test before a frame is pushed, and the tail each shared is
  // `finish`.
  struct Frame
  {
    enum Job : uint8_t
    {
      FormulaJob,
      AtomicJob,
      TermJob,
      ArrayJob
    };

    // A resume point belongs to exactly one job. Keeping these as distinct
    // types makes it impossible to suspend (say) a term frame at a formula
    // continuation by mistake.
    enum class FormulaPhase : uint8_t
    {
      Start,
      AfterAndOrOperand,
      AfterNotBody,
      AfterXorOperand,
      AfterBinaryLeft,
      AfterBinaryRight,
      AfterIffRight,
      AfterIffLeft,
      AfterIffFold,
      AfterIteCondition,
      AfterIteThen,
      AfterIteElse,
      AfterIteFold,
      AfterAtomic
    };

    enum class AtomicPhase : uint8_t
    {
      Prepared,
      AfterLeftOperand,
      AfterRightOperand,
      AfterBoolExtract,
      AfterFpOperand,
      AfterNegatedEqualityRhs,
      AfterCombinedEquality,
      AfterIteCondition
    };

    enum class TermPhase : uint8_t
    {
      Prepared,
      PreparedSubstitution,
      AfterSubstitution,
      AfterOperand,
      AfterPullUpIte,
      AfterRetry,
      AfterOutput,
      AfterReadArray
    };

    enum class ArrayPhase : uint8_t
    {
      Prepared,
      AfterCondition,
      AfterThen,
      AfterElse,
      AfterBase,
      AfterIndex,
      AfterValue
    };

    // Put the reference-counted and aligned state first. The scalar state is
    // packed at the tail so a frame does not acquire padding between every
    // phase discriminator and node.
    ASTNode b;
    ASTNode a;

    // AND, OR and XOR collect their operands.
    ASTVec outvec;

    // The operands an arm has to keep across a suspension: what a NOT has
    // under it, the two sides of a binary connective, the three of an
    // if-then-else.
    ASTNode t0, t1, t2;

    // Term jobs simplify their selected operands in `outvec` itself. `output`
    // is also scratch storage for atomic jobs and for the AND/OR annihilator;
    // those jobs are mutually exclusive, so carrying another ASTNode in every
    // frame would only make the explicit stack larger.
    ASTNode output;
    size_t i = 0;

    // Formula jobs use the kind while term jobs use the width. A frame can
    // never be both, so keeping separate words only enlarged every frame.
    union
    {
      Kind outKind;
      unsigned valueWidth;
    };

    Job job = FormulaJob;
    union
    {
      FormulaPhase formulaPhase;
      AtomicPhase atomicPhase;
      TermPhase termPhase;
      ArrayPhase arrayPhase;
    };
    bool pushNeg = false;

    Frame() : outKind(UNDEFINED), formulaPhase(FormulaPhase::Start) {}

    Frame(ASTNode input, ASTNode dispatch, const bool neg,
          const FormulaPhase phase)
        : b(std::move(input)), a(std::move(dispatch)), outKind(UNDEFINED),
          job(FormulaJob), formulaPhase(phase), pushNeg(neg)
    {
    }

    Frame(ASTNode input, const bool neg, const AtomicPhase phase)
        : b(std::move(input)), outKind(UNDEFINED), job(AtomicJob),
          atomicPhase(phase), pushNeg(neg)
    {
    }

    Frame(ASTNode input, const TermPhase phase)
        : b(std::move(input)), outKind(UNDEFINED), job(TermJob),
          termPhase(phase)
    {
    }

    Frame(ASTNode input, const ArrayPhase phase)
        : b(std::move(input)), outKind(UNDEFINED), job(ArrayJob),
          arrayPhase(phase)
    {
    }

    void resumeAt(const FormulaPhase phase)
    {
      assert(job == FormulaJob);
      formulaPhase = phase;
    }
    void resumeAt(const AtomicPhase phase)
    {
      assert(job == AtomicJob);
      atomicPhase = phase;
    }
    void resumeAt(const TermPhase phase)
    {
      assert(job == TermJob);
      termPhase = phase;
    }
    void resumeAt(const ArrayPhase phase)
    {
      assert(job == ArrayJob);
      arrayPhase = phase;
    }
  };

  static_assert(sizeof(Frame) <= 88,
                "simplifier continuation frame unexpectedly grew");

  ASTNode result;
  std::vector<Frame> stack;

  enum class StepResult
  {
    Finished,
    Pushed,
    Redispatch,
    Yield
  };

  // The head of SimplifyFormula: the answers it gives before dispatching to
  // an arm at all. `a` is left holding the node PullUpITE produced, which is
  // what the arm runs on. True when `result` is the answer.
  bool prepareFormula(const ASTNode& n, const bool neg, ASTNode& a)
  {
    ASTNode out;
    if (formulaShortcut(n, neg, a, out))
    {
      result = out;
      return true;
    }

    // Every arm began by asking the map about the node PullUpITE produced.
    // formulaShortcut already asked when PullUpITE left the node unchanged.
    ASTNode cached;
    if (a != n && CheckSimplifyMap(a, cached, neg))
    {
      // `a` is the key that answered, so only the node as it arrived still
      // needs recording.
      UpdateSimplifyMap(n, cached, neg);
      result = cached;
      return true;
    }
    return false;
  }

  // Ask for the simplification of `n` under `neg`, and set this frame's
  // continuation to `resume`.
  //
  // The head runs here rather than in the frame below because most of the
  // time it answers: the operands of a DAG are mostly nodes the walk has
  // already simplified, and a memo hit does not need a frame to return
  // through. Return Pushed only when a child frame was added. An immediate
  // answer stays in `result` and returns Redispatch, which the job-local loop
  // consumes without a control-flow jump or an outer worklist dispatch.
  // `n` can name storage in the current frame (for example f.output or
  // f.t0). Construct the child before growing the vector so it owns those
  // references before a reallocation can move the parent.
  // Keep the four child heads separate. Their job is known at every request
  // site; making it a run-time argument forced this hot path through a
  // four-way discriminator even though only one arm could ever apply.
  template <typename ResumePhase>
  StepResult requestFormula(Frame& f, const ResumePhase resume,
                            const ASTNode& n, const bool neg)
  {
    f.resumeAt(resume);
    ASTNode a;
    if (prepareFormula(n, neg, a))
      return StepResult::Redispatch;
    stack.emplace_back(n, std::move(a), neg, Frame::FormulaPhase::Start);
    return StepResult::Pushed;
  }

  template <typename ResumePhase>
  StepResult requestTerm(Frame& f, const ResumePhase resume, const ASTNode& n)
  {
    f.resumeAt(resume);
    if (n.isConstant())
    {
      result = n;
      return StepResult::Redispatch;
    }

    ASTNode substitutionImage;
    Frame::TermPhase start;
    if (InsideSubstitutionMap(n, substitutionImage))
      start = Frame::TermPhase::PreparedSubstitution;
    else if (CheckSimplifyMap(n, result, false))
      return StepResult::Redispatch;
    else
      start = Frame::TermPhase::Prepared;

    stack.emplace_back(n, start);
    if (start == Frame::TermPhase::PreparedSubstitution)
      stack.back().output = std::move(substitutionImage);
    return StepResult::Pushed;
  }

  template <typename ResumePhase>
  StepResult requestArray(Frame& f, const ResumePhase resume, const ASTNode& n)
  {
    f.resumeAt(resume);
    if (n.GetKind() == SYMBOL)
    {
      result = n;
      return StepResult::Redispatch;
    }
    if (CheckSimplifyMap(n, result, false))
      return StepResult::Redispatch;
    stack.emplace_back(n, Frame::ArrayPhase::Prepared);
    return StepResult::Pushed;
  }

  template <typename ResumePhase>
  StepResult requestAtomic(Frame& f, const ResumePhase resume, const ASTNode& n,
                           const bool neg)
  {
    f.resumeAt(resume);
    stack.emplace_back(n, neg, Frame::AtomicPhase::Prepared);
    return StepResult::Pushed;
  }

  // Keep each job's phase dispatcher in its own function. Formula and term
  // jobs dominate ordinary simplification; folding the atomic and array
  // state machines into the same large body evicts their hot code even when
  // those jobs are not running.
  StepResult stepAtomic(Frame& f)
  {
    assert(f.job == Frame::AtomicJob);
    // The one request site, requestAtomic, always starts an atomic frame
    // prechecked: the formula head that scheduled it has already probed the
    // map for this node under this polarity.
    {
      auto finishAtomic = [&](const ASTNode& output)
      {
        UpdateSimplifyMap(f.b, output, f.pushNeg);
        result = output;
        return StepResult::Finished;
      };

      auto finishEquality = [&](ASTNode output)
      {
        if (output == ASTTrue)
          output = f.pushNeg ? ASTFalse : ASTTrue;
        else if (output == ASTFalse)
          output = f.pushNeg ? ASTTrue : ASTFalse;
        else if (f.pushNeg)
          output = nf->CreateNode(NOT, output);
        return finishAtomic(output);
      };

      auto optimizeAndFinishEquality = [&](ASTNode output)
      {
        const ASTNode input = output;
        ASTNode conditionToNegate;
        output = ITEOpt_InEqs(output, conditionToNegate);
        if (!conditionToNegate.IsNull())
        {
          // ITEOpt_InEqs used to call SimplifyFormula before recording this
          // intermediate equality. Keep the key across that suspension so
          // the resumed job preserves the same memoisation edge.
          f.output = input;
          // This rare helper is itself a continuation boundary. Preserve its
          // historical outer-loop resume for both an immediate answer and a
          // pushed child; the common request sites below fuse their immediate
          // answers directly.
          const StepResult requested =
              requestFormula(f, Frame::AtomicPhase::AfterIteCondition,
                             conditionToNegate, true);
          return requested == StepResult::Redispatch ? StepResult::Yield
                                                     : requested;
        }
        return finishEquality(output);
      };

      if (f.atomicPhase == Frame::AtomicPhase::Prepared)
      {
        // Keep the original atomic-formula order: every binary predicate
        // simplifies both operands before dispatch, including BOOLEXTRACT.
        if (f.b.Degree() == 2)
          return requestTerm(f, Frame::AtomicPhase::AfterLeftOperand, f.b[0]);
      }
      else if (f.atomicPhase == Frame::AtomicPhase::AfterLeftOperand)
      {
        f.t0 = result;
        return requestTerm(f, Frame::AtomicPhase::AfterRightOperand, f.b[1]);
      }
      else if (f.atomicPhase == Frame::AtomicPhase::AfterRightOperand)
      {
        f.t1 = result;
      }
      else if (f.atomicPhase == Frame::AtomicPhase::AfterBoolExtract)
      {
        const ASTNode zero = nf->CreateZeroConst(1);
        const ASTNode one = nf->CreateOneConst(1);
        ASTNode output;
        if (result == zero)
          output = f.pushNeg ? ASTTrue : ASTFalse;
        else if (result == one)
          output = f.pushNeg ? ASTFalse : ASTTrue;
        else
        {
          output = nf->CreateNode(BOOLEXTRACT, f.t0, f.b[1]);
          if (f.pushNeg)
            output = nf->CreateNode(NOT, output);
        }
        return finishAtomic(output);
      }
      else if (f.atomicPhase == Frame::AtomicPhase::AfterFpOperand)
      {
        f.outvec.push_back(result);
        ++f.i;
      }

      if (f.atomicPhase == Frame::AtomicPhase::AfterNegatedEqualityRhs)
      {
        const ASTNode combined = LhsMinusRhsTerm(f.output, result);
        return requestTerm(f, Frame::AtomicPhase::AfterCombinedEquality,
                           combined);
      }

      ASTNode output;
      const Kind kind = f.b.GetKind();
      if (f.atomicPhase == Frame::AtomicPhase::AfterIteCondition)
      {
        UpdateSimplifyMap(f.output, result, false);
        return finishEquality(result);
      }
      if (f.atomicPhase == Frame::AtomicPhase::AfterCombinedEquality)
      {
        output = CreateSimplifiedEQ(
            result, nf->CreateZeroConst(result.GetValueWidth()));
        return optimizeAndFinishEquality(output);
      }

      switch (kind)
      {
        case TRUE:
          output = f.pushNeg ? ASTFalse : ASTTrue;
          break;
        case FALSE:
          output = f.pushNeg ? ASTTrue : ASTFalse;
          break;
        case SYMBOL:
          if (!InsideSubstitutionMap(f.b, output))
            output = f.b;
          if (f.pushNeg)
            output = nf->CreateNode(NOT, output);
          break;
        case BOOLEXTRACT:
        {
          const ASTNode getthebit =
              nf->CreateTerm(BVEXTRACT, 1, f.t0, f.b[1], f.b[1]);
          return requestTerm(f, Frame::AtomicPhase::AfterBoolExtract,
                             getthebit);
        }
        case EQ:
        {
          output = CreateSimplifiedEQ(f.t0, f.t1);
          ASTNode cached;
          if (CheckSimplifyMap(output, cached, false))
            output = cached;
          else if (output.GetKind() == EQ)
          {
            const Kind lhsKind = output[0].GetKind();
            const Kind rhsKind = output[1].GetKind();
            if (lhsKind == BVPLUS || rhsKind == BVPLUS ||
                (lhsKind == BVMULT && rhsKind == BVMULT))
            {
              f.output = output;
              const ASTNode rhs = (lhsKind != BVPLUS && rhsKind == BVPLUS)
                                      ? output[0]
                                      : output[1];
              const ASTNode negated =
                  nf->CreateTerm(BVUMINUS, rhs.GetValueWidth(), rhs);
              return requestTerm(f, Frame::AtomicPhase::AfterNegatedEqualityRhs,
                                 negated);
            }
          }
          return optimizeAndFinishEquality(output);
        }
        case BVLT:
        case BVLE:
        case BVGT:
        case BVGE:
        case BVSLT:
        case BVSLE:
        case BVSGT:
        case BVSGE:
          output = CreateSimplifiedINEQ(kind, f.t0, f.t1, f.pushNeg);
          break;
        case BVUADDO:
        case BVSADDO:
        case BVUMULO:
        case BVSMULO:
        case BVUSUBO:
        case BVSSUBO:
          output = nf->CreateNode(kind, f.t0, f.t1);
          if (f.pushNeg)
            output = nf->CreateNode(NOT, output);
          break;
        case FP_LEQ:
        case FP_LT:
        case FP_GEQ:
        case FP_GT:
        case FP_EQ:
        case FP_ISNORMAL:
        case FP_ISSUBNORMAL:
        case FP_ISZERO:
        case FP_ISINFINITE:
        case FP_ISNAN:
        case FP_ISNEGATIVE:
        case FP_ISPOSITIVE:
        case FP_SMT_EQ:
          if (f.outvec.empty())
            f.outvec.reserve(f.b.Degree());
          if (f.outvec.empty() && f.b.Degree() == 2)
          {
            f.outvec.push_back(f.t0);
            f.outvec.push_back(f.t1);
            f.i = 2;
          }
          while (f.i < f.b.Degree())
          {
            const StepResult requested =
                requestTerm(f, Frame::AtomicPhase::AfterFpOperand, f.b[f.i]);
            if (requested == StepResult::Pushed)
              return requested;
            assert(requested == StepResult::Redispatch);
            f.outvec.push_back(result);
            ++f.i;
          }
          output = nf->CreateNode(kind, f.outvec);
          if (f.pushNeg)
            output = nf->CreateNode(NOT, output);
          break;
        default:
          FatalError("SimplifyAtomicFormula: NO atomic formula of the kind: ",
                     ASTUndefined, kind);
      }

      return finishAtomic(output);
    }
  }

  StepResult stepArray(Frame& f)
  {
    assert(f.job == Frame::ArrayJob);
    {
      auto finishArray = [&](const ASTNode& output)
      {
        UpdateSimplifyMap(f.b, output, false);
        assert(f.b.GetIndexWidth() == output.GetIndexWidth());
        assert(BVTypeCheck(output));
        result = output;
        return StepResult::Finished;
      };

      const unsigned iw = f.b.GetIndexWidth();
      assert(iw > 0);

      if (f.arrayPhase == Frame::ArrayPhase::Prepared)
      {
        if (f.b.GetKind() == ITE)
          return requestFormula(f, Frame::ArrayPhase::AfterCondition, f.b[0],
                                false);
        if (f.b.GetKind() == WRITE)
          return requestArray(f, Frame::ArrayPhase::AfterBase, f.b[0]);

        FatalError("SimplifyArrayTerm: unexpected array term", f.b);
      }

      if (f.b.GetKind() == ITE)
      {
        if (f.arrayPhase == Frame::ArrayPhase::AfterCondition)
        {
          f.t0 = result;
          return requestArray(f, Frame::ArrayPhase::AfterThen, f.b[1]);
        }
        if (f.arrayPhase == Frame::ArrayPhase::AfterThen)
        {
          f.t1 = result;
          return requestArray(f, Frame::ArrayPhase::AfterElse, f.b[2]);
        }

        f.t2 = result;
        return finishArray(CreateSimplifiedTermITE(f.t0, f.t1, f.t2));
      }

      if (f.arrayPhase == Frame::ArrayPhase::AfterBase)
      {
        f.t0 = result;
        return requestTerm(f, Frame::ArrayPhase::AfterIndex, f.b[1]);
      }
      if (f.arrayPhase == Frame::ArrayPhase::AfterIndex)
      {
        f.t1 = result;
        return requestTerm(f, Frame::ArrayPhase::AfterValue, f.b[2]);
      }

      f.t2 = result;
      return finishArray(nf->CreateArrayTerm(WRITE, iw, f.b.GetValueWidth(),
                                             f.t0, f.t1, f.t2));
    }
  }

  StepResult stepTerm(Frame& f)
  {
    assert(f.job == Frame::TermJob);
    {
      auto finishTerm = [&](const ASTNode& output)
      {
        result = output;
        return StepResult::Finished;
      };

      auto finishTermTail = [&](const ASTNode& output)
      {
        if (!f.t2.IsNull())
          UpdateSimplifyMap(f.t2, output, false);
        if (f.a != f.t2)
          UpdateSimplifyMap(f.a, output, false);
        if (f.b != f.a && f.b != f.t2)
          UpdateSimplifyMap(f.b, output, false);

        assert(!output.IsNull());
        assert(f.a.GetValueWidth() == output.GetValueWidth());
        assert(f.a.GetIndexWidth() == output.GetIndexWidth());
        assert(hasBeenSimplified(output));
#ifndef NDEBUG
        for (size_t i = 0; i < output.Degree(); ++i)
        {
          if (output[i].GetType() != ARRAY_TYPE &&
              !hasBeenSimplified(output[i]))
          {
            std::cerr << output << i;
            assert(false);
          }
        }
#endif
        result = output;
        return StepResult::Finished;
      };

      if (f.termPhase == Frame::TermPhase::AfterSubstitution)
        return finishTerm(result);
      if (f.termPhase == Frame::TermPhase::AfterPullUpIte ||
          f.termPhase == Frame::TermPhase::AfterRetry)
      {
        UpdateSimplifyMap(f.b, result, false);
        if (f.a != f.b)
          UpdateSimplifyMap(f.a, result, false);
        return finishTerm(result);
      }
      if (f.termPhase == Frame::TermPhase::AfterOutput)
        return finishTermTail(result);

      if (f.termPhase == Frame::TermPhase::Prepared ||
          f.termPhase == Frame::TermPhase::PreparedSubstitution)
      {
        assert(_bm->UserFlags.optimize_flag);

        f.a = f.b;
        const ASTNode substitutionImage = f.output;
        f.output = f.a;
        assert(BVTypeCheck(f.a));

        if (f.termPhase == Frame::TermPhase::PreparedSubstitution)
          return requestTerm(f, Frame::TermPhase::AfterSubstitution,
                             substitutionImage);
        const Kind k = f.a.GetKind();
        if (!is_Term_kind(k))
          FatalError("SimplifyTerm: You have input a Non-term", f.a);

        f.valueWidth = f.a.GetValueWidth();
        if (k != SYMBOL)
        {
          if (k == BVAND || k == BVOR || k == BVPLUS || k == BVMULT)
            f.outvec = FlattenKind(k, f.b.GetChildren(), 15);
          else
            f.outvec = toASTVec(f.b.GetChildren());
        }
      }
      else if (f.termPhase == Frame::TermPhase::AfterOperand)
      {
        f.outvec[f.i] = result;
        ++f.i;
      }

      // Simplify the selected operands left-to-right. Array operands are
      // deliberately carried through here; READ schedules its array as an
      // ArrayJob below, matching the old split between the two functions.
      while (f.a.GetKind() != SYMBOL && f.i < f.outvec.size())
      {
        const ASTNode& operand = f.outvec[f.i];
        if (operand.GetType() == BITVECTOR_TYPE ||
            operand.GetType() == FLOATINGPOINT_TYPE)
        {
          const StepResult requested =
              requestTerm(f, Frame::TermPhase::AfterOperand, operand);
          if (requested == StepResult::Pushed)
            return requested;
          assert(requested == StepResult::Redispatch);
          f.outvec[f.i] = result;
          ++f.i;
          continue;
        }
        if (operand.GetType() == BOOLEAN_TYPE)
        {
          const StepResult requested =
              requestFormula(f, Frame::TermPhase::AfterOperand, operand, false);
          if (requested == StepResult::Pushed)
            return requested;
          assert(requested == StepResult::Redispatch);
          f.outvec[f.i] = result;
          ++f.i;
          continue;
        }
        ++f.i;
      }

      if (f.a.GetKind() != SYMBOL &&
          f.termPhase != Frame::TermPhase::AfterReadArray)
      {
        assert(!f.outvec.empty());
        if (ASTChildren(f.outvec) != f.b.GetChildren())
        {
          f.output = nf->CreateArrayTerm(f.a.GetKind(), f.b.GetIndexWidth(),
                                         f.valueWidth, f.outvec);
          f.output = FloatBlaster::withFormat(_bm, f.output, f.b.GetExpWidth(),
                                              f.b.GetSigWidth());
        }
        else
          f.output = f.b;

        if (f.a != f.output)
        {
          UpdateSimplifyMap(f.a, f.output, false);
          f.a = f.output;
        }

        const ASTChildren children = f.a.GetChildren();
        const Kind k = f.a.GetKind();
        if (k != stp::UNDEFINED && k != stp::SYMBOL)
        {
          bool allConstant = true;
          for (const ASTNode& child : children)
          {
            if (!child.isConstant())
            {
              allConstant = false;
              break;
            }
          }
          if (allConstant)
          {
            const ASTNode c = BVConstEvaluator(f.a);
            assert(c.isConstant());
            UpdateSimplifyMap(f.a, c, false);
            return finishTerm(c);
          }
        }

        const ASTNode pulledUp = PullUpITE(f.a);
        if (pulledUp != f.a)
          return requestTerm(f, Frame::TermPhase::AfterPullUpIte, pulledUp);

        bool notSimplified = false;
        for (size_t i = 0; i < f.a.Degree(); ++i)
        {
          if (f.a[i].GetType() != ARRAY_TYPE && !hasBeenSimplified(f.a[i]))
          {
            notSimplified = true;
            break;
          }
        }
        if (notSimplified)
          return requestTerm(f, Frame::TermPhase::AfterRetry, f.a);
      }

      if (f.a.GetKind() == READ &&
          f.termPhase != Frame::TermPhase::AfterReadArray)
        return requestArray(f, Frame::TermPhase::AfterReadArray, f.a[0]);

      if (f.a.GetKind() == READ &&
          f.termPhase == Frame::TermPhase::AfterReadArray && result != f.a[0])
      {
        // Preserve the pre-rebuild READ as a memo key. The recursive version
        // returned through that invocation after simplifying the array.
        f.t2 = f.a;
        ASTVec children = toASTVec(f.a.GetChildren());
        children[0] = result;
        f.a = nf->CreateArrayTerm(READ, f.a.GetIndexWidth(), f.valueWidth,
                                  children);
        f.output = f.a;
      }

      // The kind switch and its helpers perform one rewrite step. If that
      // manufactures a different term, schedule the candidate as another
      // term job below. This is the common replacement for every former
      // helper-to-SimplifyTerm call, including terms that did not exist in
      // the input DAG.
      ASTNode ret =
          simplify_term_switch(f.b, f.a, f.output, f.a.GetKind(), f.valueWidth);
      if (ret != ASTUndefined)
        return finishTerm(ret);

      assert(!f.output.IsNull());
      if (f.a != f.output)
        return requestTerm(f, Frame::TermPhase::AfterOutput, f.output);
      return finishTermTail(f.output);
    }
  }

  StepResult stepFormula(Frame& f)
  {
    assert(f.job == Frame::FormulaJob);
    // The formula arms implemented in this frame share their memoisation
    // tail: record the PullUpITE result and, when distinct, the input. The
    // separately scheduled AtomicJob owns its own first entry and bypasses
    // this tail when it returns below.
    auto finish = [&](const ASTNode& output)
    {
      UpdateSimplifyMap(f.a, output, f.pushNeg);
      if (f.b != f.a)
        UpdateSimplifyMap(f.b, output, f.pushNeg);
      result = output;
      return StepResult::Finished;
    };

    // `f.a` is set by the head, which ran before this frame was pushed.
    const Kind k = f.a.GetKind();
    switch (k)
    {
      case AND:
      case OR:
      {
        auto takeChild = [&](const ASTNode& child)
        {
          if (child == f.output)
            return false;

          // A child that simplified to the output connective (typically via
          // De Morgan) would otherwise leave a nested same-kind node, which
          // the factory does not flatten. Splice its already-simplified
          // operands in so the result stays flat -- without this
          // SimplifyFormula is not idempotent.
          if (child.GetKind() == f.outKind)
            f.outvec.insert(f.outvec.end(), child.begin(), child.end());
          else
            f.outvec.push_back(child);
          ++f.i;
          return true;
        };

        if (f.formulaPhase == Frame::FormulaPhase::Start)
        {
          const bool isAnd = (k == AND);
          // Under pushNeg we are simplifying NOT(a): De Morgan flips the
          // connective, and a child that simplifies to the annihilator
          // collapses the whole node.
          f.output = isAnd ? (f.pushNeg ? ASTTrue : ASTFalse)
                           : (f.pushNeg ? ASTFalse : ASTTrue);
          f.outKind = (isAnd == !f.pushNeg) ? AND : OR;
          f.outvec.reserve(f.a.Degree());
        }
        else
        {
          if (!takeChild(result))
            return finish(f.output);
        }

        while (f.i < f.a.Degree())
        {
          const StepResult requested = requestFormula(
              f, Frame::FormulaPhase::AfterAndOrOperand, f.a[f.i], f.pushNeg);
          if (requested == StepResult::Pushed)
            return requested;
          assert(requested == StepResult::Redispatch);
          if (!takeChild(result))
            return finish(f.output);
        }

        // Hand the simplified children to the node factory. CreateSimpleAndOr
        // sorts them, drops identities, removes duplicates, detects
        // complements and unwraps singletons -- so none of that is repeated
        // here.
        return finish(nf->CreateNode(f.outKind, f.outvec));
      }

      case NOT:
      {
        if (f.formulaPhase == Frame::FormulaPhase::AfterNotBody)
          return finish(result);

        if (!(f.a.Degree() == 1 && NOT == f.a.GetKind()))
          FatalError("SimplifyNotFormula: input vector with more than 1 node",
                     ASTUndefined);

        // if pushNeg is set then there is NOT on top
        unsigned int NotCount = f.pushNeg ? 1 : 0;
        ASTNode o = f.a;
        // count the number of NOTs in 'a'
        while (NOT == o.GetKind())
        {
          o = o[0];
          NotCount++;
        }

        // pushnegation if there are odd number of NOTs
        const bool pn = (NotCount % 2 == 0) ? false : true;

        // `requestFormula` owns the child shortcut and memo probe. If it schedules a
        // child frame, that frame records `o`; if it answers immediately,
        // the entry either already exists or `o` is a leaf that is never
        // memoised. The returning NOT frame therefore only records itself.
        return requestFormula(f, Frame::FormulaPhase::AfterNotBody, o, pn);
      }

      case XOR:
      {
        assert(f.a.Degree() > 0);

        if (f.a.Degree() == 1)
          return finish(f.a[0]);

        if (f.formulaPhase == Frame::FormulaPhase::Start)
          f.outvec.reserve(f.a.Degree());

        if (f.formulaPhase == Frame::FormulaPhase::AfterXorOperand)
        {
          f.outvec.push_back(result);
          ++f.i;
        }

        while (f.i < f.a.Degree())
        {
          const StepResult requested = requestFormula(
              f, Frame::FormulaPhase::AfterXorOperand, f.a[f.i], false);
          if (requested == StepResult::Pushed)
            return requested;
          assert(requested == StepResult::Redispatch);
          f.outvec.push_back(result);
          ++f.i;
        }

        if (f.pushNeg)
          f.outvec[0] = nf->CreateNode(NOT, f.outvec[0]);

        if (f.a.Degree() == 2)
        {
          ASTNode output = nf->CreateNode(XOR, f.outvec[0], f.outvec[1]);
          if (f.outvec[0] == f.outvec[1])
            output = ASTFalse;
          else if ((f.outvec[0] == ASTTrue && f.outvec[1] == ASTFalse) ||
                   (f.outvec[0] == ASTFalse && f.outvec[1] == ASTTrue))
            output = ASTTrue;
          return finish(output);
        }

        return finish(nf->CreateNode(XOR, f.outvec));
      }

      case NAND:
      case NOR:
      case IMPLIES:
      {
        if (f.formulaPhase == Frame::FormulaPhase::Start)
        {
          if (k == IMPLIES && !(f.a.Degree() == 2))
            FatalError("SimplifyImpliesFormula: vector with wrong num of nodes",
                       ASTUndefined);

          // NAND and NOR are a negated AND/OR, so the negation they carry
          // goes into both operands and cancels with the caller's. IMPLIES
          // negates only its consequent, and only when it is itself negated.
          return requestFormula(f, Frame::FormulaPhase::AfterBinaryLeft, f.a[0],
                                (k == IMPLIES) ? false : !f.pushNeg);
        }

        if (f.formulaPhase == Frame::FormulaPhase::AfterBinaryLeft)
        {
          f.t0 = result;
          return requestFormula(f, Frame::FormulaPhase::AfterBinaryRight,
                                f.a[1],
                                (k == IMPLIES) ? f.pushNeg : !f.pushNeg);
        }

        f.t1 = result;

        if (k == NAND)
          return finish(nf->CreateNode(f.pushNeg ? AND : OR, f.t0, f.t1));
        if (k == NOR)
          return finish(nf->CreateNode(f.pushNeg ? OR : AND, f.t0, f.t1));

        if (f.pushNeg)
          return finish(nf->CreateNode(AND, f.t0, f.t1));
        if (ASTFalse == f.t0)
          return finish(ASTTrue);
        if (ASTTrue == f.t0)
          return finish(f.t1);
        if (f.t0 == f.t1)
          return finish(ASTTrue);
        if (NOT == f.t0.GetKind())
          return finish(nf->CreateNode(OR, f.t0[0], f.t1));
        return finish(nf->CreateNode(OR, nf->CreateNode(NOT, f.t0), f.t1));
      }

      case IFF:
      {
        if (f.formulaPhase == Frame::FormulaPhase::Start)
        {
          if (!(f.a.Degree() == 2))
            FatalError("SimplifyIffFormula: vector with wrong num of nodes",
                       ASTUndefined);

          // The second operand first, as it was.
          return requestFormula(f, Frame::FormulaPhase::AfterIffRight, f.a[1],
                                false);
        }

        if (f.formulaPhase == Frame::FormulaPhase::AfterIffRight)
        {
          f.t1 = result;
          return requestFormula(f, Frame::FormulaPhase::AfterIffLeft, f.a[0],
                                f.pushNeg);
        }

        if (f.formulaPhase == Frame::FormulaPhase::AfterIffLeft)
        {
          f.t0 = result;

          if (ASTTrue == f.t0)
            return finish(f.t1);
          if (ASTFalse == f.t0)
            return requestFormula(f, Frame::FormulaPhase::AfterIffFold, f.t1,
                                  true);
          if (ASTTrue == f.t1)
            return finish(f.t0);
          if (ASTFalse == f.t1)
            return requestFormula(f, Frame::FormulaPhase::AfterIffFold, f.t0,
                                  true);
          if (f.t0 == f.t1)
            return finish(ASTTrue);
          if ((NOT == f.t0.GetKind() && f.t0[0] == f.t1) ||
              (NOT == f.t1.GetKind() && f.t0 == f.t1[0]))
            return finish(ASTFalse);
          return finish(nf->CreateNode(XOR, nf->CreateNode(NOT, f.t0), f.t1));
        }

        return finish(result); // Frame::FormulaPhase::AfterIffFold
      }

      case ITE:
      {
        if (f.formulaPhase == Frame::FormulaPhase::Start)
        {
          if (!(f.a.Degree() == 3))
            FatalError("SimplifyIteFormula: vector with wrong num of nodes",
                       ASTUndefined);

          return requestFormula(f, Frame::FormulaPhase::AfterIteCondition,
                                f.a[0], false);
        }

        if (f.formulaPhase == Frame::FormulaPhase::AfterIteCondition)
        {
          f.t0 = result;
          return requestFormula(f, Frame::FormulaPhase::AfterIteThen, f.a[1],
                                f.pushNeg);
        }

        if (f.formulaPhase == Frame::FormulaPhase::AfterIteThen)
        {
          f.t1 = result;
          return requestFormula(f, Frame::FormulaPhase::AfterIteElse, f.a[2],
                                f.pushNeg);
        }

        if (f.formulaPhase == Frame::FormulaPhase::AfterIteElse)
        {
          f.t2 = result;

          // Every structural fold here -- constant condition, equal branches,
          // a constant branch collapsing to AND/OR -- is done by the
          // simplifying node factory when the ITE node is (re)created, so we
          // just hand it the simplified children. The one exception is
          // ITE(c, false, true): the factory would only give a shallow
          // NOT(c), whereas pushing the negation into c exposes more
          // simplifications.
          if (ASTTrue == f.t0)
            return finish(f.t1);
          if (ASTFalse == f.t0)
            return finish(f.t2);
          if (ASTFalse == f.t1 && ASTTrue == f.t2)
            return requestFormula(f, Frame::FormulaPhase::AfterIteFold, f.t0,
                                  true);
          return finish(nf->CreateNode(ITE, f.t0, f.t1, f.t2));
        }

        return finish(result); // Frame::FormulaPhase::AfterIteFold
      }

      default:
        // Atomic predicates do not stop the walk: their term operands and any
        // terms they manufacture are jobs on this same continuation stack.
        if (f.formulaPhase == Frame::FormulaPhase::AfterAtomic)
        {
          // AtomicJob has already recorded `f.a`. Only the pre-PullUpITE key
          // can remain for this formula frame to record.
          if (f.b != f.a)
            UpdateSimplifyMap(f.b, result, f.pushNeg);
          return StepResult::Finished;
        }
        return requestAtomic(f, Frame::FormulaPhase::AfterAtomic, f.a,
                             f.pushNeg);
    }
  }

public:
  explicit SimplifyDriver(Simplifier& owner)
      : owner(owner), nf(owner.nf), _bm(owner._bm), ASTTrue(owner.ASTTrue),
        ASTFalse(owner.ASTFalse), ASTUndefined(owner.ASTUndefined)
  {
  }

  ASTNode run(const ASTNode& b, const bool pushNeg, const SimplifyJob rootJob)
  {
    result = ASTNode();
    stack.clear();

    // Answer root-level leaves and memo hits before constructing the vector.
    // A vector allocation is unnecessary for the overwhelmingly common leaf
    // and memo-hit cases.
    Frame top;
    top.b = b;
    top.pushNeg = pushNeg;
    if (rootJob == SimplifyJob::Formula)
    {
      top.job = Frame::FormulaJob;
      if (prepareFormula(b, pushNeg, top.a))
        return result;
    }
    else if (rootJob == SimplifyJob::Term)
    {
      assert(_bm->UserFlags.optimize_flag);
      top.job = Frame::TermJob;

      // A substitution frame is transparent: follow its image without
      // memoising the substituted key until a real term frame is needed.
      ASTNode root = b;
      ASTNode substitutionImage;
      while (true)
      {
        if (root.isConstant())
          return root;
        if (InsideSubstitutionMap(root, substitutionImage))
        {
          root = substitutionImage;
          continue;
        }
        if (CheckSimplifyMap(root, result, false))
          return result;
        break;
      }

      top.b = root;
      top.termPhase = Frame::TermPhase::Prepared;
    }
    else
    {
      assert(b.GetIndexWidth() > 0);
      top.job = Frame::ArrayJob;
      if (CheckSimplifyMap(b, result, false))
        return result;
      if (b.GetKind() == SYMBOL)
        return b;
      top.arrayPhase = Frame::ArrayPhase::Prepared;
    }

    // A child request is the only operation that can grow the vector, and
    // every caller returns from its step immediately afterwards, so no Frame
    // reference survives a move.
    stack.push_back(std::move(top));

    while (true)
    {
      Frame& current = stack.back();
      StepResult stepResult = StepResult::Finished;
      switch (current.job)
      {
        case Frame::FormulaJob:
          do
            stepResult = stepFormula(current);
          while (stepResult == StepResult::Redispatch);
          break;
        case Frame::AtomicJob:
          do
            stepResult = stepAtomic(current);
          while (stepResult == StepResult::Redispatch);
          break;
        case Frame::TermJob:
          do
            stepResult = stepTerm(current);
          while (stepResult == StepResult::Redispatch);
          break;
        case Frame::ArrayJob:
          do
            stepResult = stepArray(current);
          while (stepResult == StepResult::Redispatch);
          break;
      }

      if (stepResult == StepResult::Pushed || stepResult == StepResult::Yield)
        continue;
      assert(stepResult == StepResult::Finished);

      stack.pop_back();
      if (stack.empty())
        return result;
    }
  }
};

ASTNode Simplifier::simplifyNode(const ASTNode& b, const bool pushNeg,
                                 const SimplifyJob rootJob)
{
  return SimplifyDriver(*this).run(b, pushNeg, rootJob);
}

ASTNode Simplifier::makeTower(const Kind k, const stp::ASTVec& children)
{
  std::deque<ASTNode> names;

  for (unsigned i = 0; i < children.size(); i++)
    names.push_back(children[i]);

  while (names.size() > 2)
  {
    ASTNode a = names.front();
    names.pop_front();

    ASTNode b = names.front();
    names.pop_front();

    ASTNode n = nf->CreateTerm(k, a.GetValueWidth(), a, b);
    names.push_back(n);
  }

  // last two now.
  assert(names.size() == 2);

  ASTNode a = names.front();
  names.pop_front();

  ASTNode b = names.front();
  names.pop_front();

  return nf->CreateTerm(k, a.GetValueWidth(), a, b);
}

// If a node is not a leaf, it has only been simplified  if it
// maps to itself in the simplifyMap.
bool Simplifier::hasBeenSimplified(const ASTNode& n)
{
  // n has been simplified if, it's a constant:
  if (n.isConstant())
    return true;

  if (n.isSimplfied())
    return true;

  // If it's a symbol that's not in the substitition Map.
  if (n.GetKind() == SYMBOL && InsideSubstitutionMap(n))
    return false;

  if (n.GetKind() == SYMBOL)
    return true;

  // If it's in the simplification map, it has been simplified.
  const auto it = SimplifyMap->find(n);
  if (it == SimplifyMap->end())
    return false;

  return (it->second == n);
}

// If both of the children are sign extended. Makes this node sign extended too.
ASTNode Simplifier::pullUpBVSX(ASTNode output)
{
  assert(output.GetChildren().size() == 2);
  assert(output[0].GetKind() == BVSX);
  assert(output[1].GetKind() == BVSX);
  [[maybe_unused]] const Kind k = output.GetKind();

  assert(BVMULT == k || SBVDIV == k || BVPLUS == k);
  const int inputValueWidth = output.GetValueWidth();

  unsigned lengthA = output.GetChildren()[0][0].GetValueWidth();
  unsigned lengthB = output.GetChildren()[1][0].GetValueWidth();
  unsigned maxLength;
  switch (output.GetKind())
  {
    case BVMULT:
      maxLength = lengthA + lengthB;
      break;

    case BVPLUS:
    case SBVDIV:
      maxLength = std::max(lengthA, lengthB) + 1;
      break;

    default:
      FatalError("Unexpected.");
  }

  if (maxLength < output.GetValueWidth())
  {
    ASTNode newA = nf->CreateTerm(BVEXTRACT, maxLength, output.GetChildren()[0],
                                  nf->CreateBVConst(32, maxLength - 1),
                                  nf->CreateZeroConst(32));
    ASTNode newB = nf->CreateTerm(BVEXTRACT, maxLength, output.GetChildren()[1],
                                  nf->CreateBVConst(32, maxLength - 1),
                                  nf->CreateZeroConst(32));

    ASTNode mult = nf->CreateTerm(output.GetKind(), maxLength, newA, newB);
    output = nf->CreateTerm(BVSX, inputValueWidth, mult,
                            nf->CreateBVConst(32, inputValueWidth));
  }
  return output;
}

ASTNode Simplifier::SimplifyTerm(const ASTNode& inputterm)
{
  return simplifyNode(inputterm, false, SimplifyJob::Term);
}

ASTNode Simplifier::simplify_term_switch(const ASTNode& actualInputterm,
                                         ASTNode& inputterm, ASTNode& output, Kind k,
                                         const unsigned int inputValueWidth)
{
  switch (k)
  {
    case BVCONST:
      output = inputterm;
      break;

    case SYMBOL:
      if (InsideSubstitutionMap(inputterm, output))
        break;
      output = inputterm;
      break;

    case BVMULT:
    // nb. (t * (u << s)) == ((t * u) << s) is done by the simplifying node
    // factory.

    // fall-through
    case BVPLUS:
    {
      if (BVPLUS == k && inputterm.Degree() == 2 && inputterm[1].GetKind() == BVLEFTSHIFT && inputterm[0] == inputterm[1][1])
      {
        output = nf->CreateTerm(BVOR, inputValueWidth, toASTVec(inputterm.GetChildren()));
        break;
      }



      const ASTVec c = FlattenKind(k, inputterm.GetChildren());

      ASTVec constkids, nonconstkids;

      // go through the childnodes, and separate constant and
      // nonconstant nodes. combine the constant nodes using the
      // constevaluator. if the resultant constant is zero and k ==
      // BVPLUS, then ignore it (similarily for 1 and BVMULT).  else,
      // add the computed constant to the nonconst vector, flatten,
      // sort, and create BVPLUS/BVMULT and return
      for (ASTVec::const_iterator it = c.begin(), itend = c.end(); it != itend;
           it++)
      {
        ASTNode aaa = *it;

        assert(hasBeenSimplified(aaa));

        if (BVCONST == aaa.GetKind())
        {
          constkids.push_back(aaa);
        }
        else
        {
          nonconstkids.push_back(aaa);
        }
      }

      const ASTNode one = nf->CreateOneConst(inputValueWidth);
      const ASTNode max = nf->CreateMaxConst(inputValueWidth);
      const ASTNode zero = nf->CreateZeroConst(inputValueWidth);

      // initialize constoutput to zero, in case there are no elements
      // in constkids
      ASTNode constoutput = (k == BVPLUS) ? zero : one;

      if (1 == constkids.size())
      {
        // only one element in constkids
        constoutput = constkids[0];
      }
      else if (1 < constkids.size())
      {
        // many elements in constkids. simplify it
        constoutput = NonMemberBVConstEvaluator(_bm, k ,constkids, inputterm.GetValueWidth());
      }

      if (BVMULT == k && zero == constoutput)
      {
        output = zero;
      }
      else if (BVMULT == k && 1 == nonconstkids.size() && constoutput == max)
      {
        // useful special case opt: when input is BVMULT(max_const,t),
        // then output = BVUMINUS(t). this is easier on the bitblaster
        output = nf->CreateTerm(BVUMINUS, inputValueWidth, nonconstkids);
      }
      else
      {
        if (0 < nonconstkids.size())
        {
          // ignore identities.
          if (BVPLUS == k && constoutput != zero)
          {
            nonconstkids.push_back(constoutput);
          }
          else if (BVMULT == k && constoutput != one)
          {
            nonconstkids.push_back(constoutput);
          }

          if (1 == nonconstkids.size())
          {
            // exactly one element in nonconstkids. output is exactly
            // nonconstkids[0]
            output = nonconstkids[0];
          }
          else if (BVMULT == k)
          {
            SortByArith(nonconstkids);

            // DistributeMultOverPlus only understands two-operand
            // multiplies, so a wide product with a sum inside is still
            // towered down for it. Otherwise the product stays n-ary.
            bool anyPlus = false;
            for (const ASTNode& kid : nonconstkids)
              if (BVPLUS == kid.GetKind())
                anyPlus = true;

            if (nonconstkids.size() > 2 && anyPlus)
              output = makeTower(k, nonconstkids);
            else
              output = nf->CreateTerm(k, inputValueWidth, nonconstkids);
            output = DistributeMultOverPlus(output, true);
          }
          else // pluss.
          {
            assert(BVPLUS == k);
            // SortByArith(nonconstkids);
            // output = nf->CreateTerm(k, inputValueWidth, nonconstkids);
            // output = Flatten(output);
            // output = CombineLikeTerms(output);
            output = CombineLikeTerms(nonconstkids);
          }
        }
        else
        {
          // nonconstkids was empty, all childnodes were constant, hence
          // constoutput is the output.
          output = constoutput;
        }
      }

      // propagate bvuminus upwards through multiplies.
      if (BVMULT == output.GetKind())
      {
        ASTVec d = toASTVec(output.GetChildren());
        int uminus = 0;
        for (unsigned i = 0; i < d.size(); i++)
        {
          if (d[i].GetKind() == BVUMINUS)
          {
            d[i] = d[i][0];
            uminus++;
          }
        }
        if (uminus != 0)
        {
          SortByArith(d);
          output = nf->CreateTerm(BVMULT, output.GetValueWidth(), d);
          if ((uminus & 0x1) != 0) // odd, pull up the uminus.
          {
            output = nf->CreateTerm(BVUMINUS, output.GetValueWidth(), output);
          }
        }
      }

      if ((BVMULT == output.GetKind() || BVPLUS == output.GetKind()) &&
          output.GetChildren().size() == 2 &&
          output.GetChildren()[0].GetKind() == BVSX &&
          output.GetChildren()[1].GetKind() == BVSX)
      {
        output = pullUpBVSX(output);
      }
      else if (BVMULT == output.GetKind() || BVPLUS == output.GetKind())
      {
        ASTVec d = toASTVec(output.GetChildren());
        SortByArith(d);
        output = nf->CreateTerm(output.GetKind(), output.GetValueWidth(), d);
      }
      break;
    }

    case BVSUB:
      // nb. (x - x) == 0, (x - 0) == x, and (x - y) == x + (-y) are done by
      // the simplifying node factory.
      output = inputterm;
      break;

    case BVUMINUS:
    {
      // important to treat BVUMINUS as a special case, because it
      // helps in arithmetic transformations. e.g.  x + BVUMINUS(x) is
      // actually 0. One way to reveal this fact is to strip bvuminus
      // out, and replace with something else so that combineliketerms
      // can catch this fact.

      const ASTNode& a0 = inputterm[0];
      const Kind k1 = a0.GetKind();
      assert(k1 != BVCONST);
      switch (k1)
      {
        // nb. -(-x) == x and -(~x) == x + 1 are done by the simplifying node
        // factory, so those children never reach here.
        case BVMULT:
        {
          if (a0.Degree() != 2)
          {
            // The rewrites below rebuild from the first two operands only.
            output = inputterm;
          }
          else if (BVUMINUS == a0[0].GetKind())
          {
            output = nf->CreateTerm(BVMULT, inputValueWidth, a0[0][0], a0[1]);
          }
          else if (BVUMINUS == a0[1].GetKind())
          {
            output = nf->CreateTerm(BVMULT, inputValueWidth, a0[0], a0[1][0]);
          }
          else
          {
            // If the first argument to the multiply is a
            // constant, push it through.  Without regard for
            // the splitting of nodes (hmm.)  This is
            // necessary because the bitvector solver can
            // process -3*x, but not -(3*x).
            if (BVCONST == a0[0].GetKind())
            {
              ASTNode a00 =nf->CreateTerm(BVUMINUS, inputValueWidth, a0[0]);
              output = nf->CreateTerm(BVMULT, inputValueWidth, a00, a0[1]);
            }
            else
              output = inputterm;
          }
          break;
        }
        case BVPLUS:
        {
          // push BVUMINUS over all the monomials of BVPLUS. Simplify
          // along the way
          //
          // BVUMINUS(a1x1 + a2x2 + ...) <=> BVPLUS(BVUMINUS(a1x1) +
          // BVUMINUS(a2x2) + ...
          const ASTChildren c = a0.GetChildren();
          ASTVec o;
          for (auto it = c.begin(), itend = c.end();
               it != itend; it++)
          {
            // Simplify(BVUMINUS(a1x1))
            ASTNode aaa =
                nf->CreateTerm(BVUMINUS, inputValueWidth, *it);
            o.push_back(aaa);
          }

          output = nf->CreateTerm(BVPLUS, inputValueWidth, o);
          break;
        }
        // nb. BVUMINUS(BVSUB(x,y)) does not occur: BVSUB is lowered to a
        // BVPLUS by the simplifying node factory.
        // nb. -(x & -x) == x | -x is done by the simplifying node factory.
        // (The -(x | -x) case here was dead: BVOR is lowered to ~(~x & ~y) at
        // creation, so no BVOR node ever reaches this switch.)
        case BVLEFTSHIFT:
          if (a0[0].GetKind() == BVCONST)
            output = nf->CreateTerm(
                BVLEFTSHIFT, inputValueWidth,
                nf->CreateTerm(BVUMINUS, inputValueWidth, a0[0]), a0[1]);
          break;
        case ITE:
        {
          // BVUMINUS(ITE(c,t1,t2)) <==> ITE(c,BVUMINUS(t1),BVUMINUS(t2))
          ASTNode c = a0[0];
          ASTNode t1 =
              nf->CreateTerm(BVUMINUS, inputValueWidth, a0[1]);
          ASTNode t2 =
              nf->CreateTerm(BVUMINUS, inputValueWidth, a0[2]);
          output = CreateSimplifiedTermITE(c, t1, t2);
          break;
        }
        default:
        {
          output = inputterm;
          break;
        }
      }
      break;
    }

    case BVEXTRACT:
    {
      // it is important to take care of wordlevel transformation in
      // BVEXTRACT. it exposes oppurtunities for later simplification
      // and solving (variable elimination)
      const ASTNode& a0 = inputterm[0];

      const Kind k1 = a0.GetKind();

      // indices for BVEXTRACT
      ASTNode i = inputterm[1];
      ASTNode j = inputterm[2];
      const ASTNode zero = nf->CreateZeroConst(32);

      // recall that the indices of BVEXTRACT are always 32 bits
      // long. therefore doing a GetBVUnsigned is ok.
      unsigned int i_val = i.GetUnsignedConst();
      unsigned int j_val = j.GetUnsignedConst();

      // a0[i:0] and len(a0)=i+1, then return a0
      if (inputValueWidth == a0.GetValueWidth())
      {
        assert(0 == j_val);
        output = a0;
        break;
      }

      assert(k1 != BVCONST);

      switch (k1)
      {
        // nb. an extract over an extract is merged by the simplifying node
        // factory.
        case BVCONCAT:
        {
          // assumes concatenation is binary
          //
          // input is of the form a0[i:j]
          //
          // a0 is the conatentation t@u, and a0[0] is t, and a0[1] is u
          ASTNode t = a0[0];
          ASTNode u = a0[1];
          const unsigned int len_a0 = a0.GetValueWidth();
          const unsigned int len_u = u.GetValueWidth();

          if (len_u > i_val)
          {
            // Apply the following rule:
            // (t@u)[i:j] <==> u[i:j], if len(u) > i
            //
            output = nf->CreateTerm(BVEXTRACT, inputValueWidth, u, i, j);
          }
          else if (len_a0 > i_val && j_val >= len_u)
          {
            // Apply the rule: (t@u)[i:j] <==>
            // t[i-len_u:j-len_u], if len(t@u) > i >= j >=
            // len(u)
            i = nf->CreateBVConst(32, i_val - len_u);
            j = nf->CreateBVConst(32, j_val - len_u);
            output = nf->CreateTerm(BVEXTRACT, inputValueWidth, t, i, j);
          }
          else
          {
            // Apply the rule:
            // (t@u)[i:j] <==> t[i-len_u:0] @ u[len_u-1:j]
            i = nf->CreateBVConst(32, i_val - len_u);
            ASTNode m = nf->CreateBVConst(32, len_u - 1);
            t =
                nf->CreateTerm(BVEXTRACT, i_val - len_u + 1, t, i, zero);
            u =nf->CreateTerm(BVEXTRACT, len_u - j_val, u, m, j);
            output = nf->CreateTerm(BVCONCAT, inputValueWidth, t, u);
          }
          break;
        }
        case BVPLUS:
        case BVMULT:
        {
          // (BVMULT(n,t,u))[i:j] <==> BVMULT(i+1,t[i:0],u[i:0])[i:j]
          // similar rule for BVPLUS
          const ASTChildren c = a0.GetChildren();
          ASTVec o;
          for (auto jt = c.begin(), jtend = c.end(); jt != jtend;
               jt++)
          {
            ASTNode aaa = *jt;
            aaa =nf->CreateTerm(BVEXTRACT, i_val + 1, aaa, i, zero);
            o.push_back(aaa);
          }
          output = nf->CreateTerm(a0.GetKind(), i_val + 1, o);
          if (j_val != 0)
          {
            // add extraction only if j is not zero
            output = nf->CreateTerm(BVEXTRACT, inputValueWidth, output, i, j);
          }
          break;
        }

// This can increase the number of nodes exponentially.
// If turned on bitrev2048 will blow out main memory, with
// this disabled it takes 12MB.
#if 0

          case BVAND:
          case BVOR:
          case BVXOR:
            {
              assert(a0.Degree() == 2);

              //assumes these operators are binary
              //
              // (t op u)[i:j] <==> t[i:j] op u[i:j]
              ASTNode t = a0[0];
              ASTNode u = a0[1];
              t =
              SimplifyTerm(nf->CreateTerm(BVEXTRACT,
                      a_len, t, i, j));
              u =
              SimplifyTerm(nf->CreateTerm(BVEXTRACT,
                      a_len, u, i, j));
              BVTypeCheck(t);
              BVTypeCheck(u);
              //output = nf->CreateTerm(k1, a_len, t, u);

              output = inputterm;
              break;
            }
#endif
        // nb. (~t)[i:j] == ~(t[i:j]) is done by the simplifying node factory.
        // case BVSX:{ //(BVSX(t,n)[i:j] <==> BVSX(t,i+1), if n
        //        >= i+1 and j=0 ASTNode t = a0[0]; unsigned int
        //        bvsx_len = a0.GetValueWidth(); if(bvsx_len <
        //        a_len) { FatalError("SimplifyTerm: BVEXTRACT
        //        over BVSX:" "the length of BVSX term must be
        //        greater than extract-len",inputterm); } if(j
        //        != zero) { output =
        //        nf->CreateTerm(BVEXTRACT,a_len,a0,i,j); }
        //        else { output =
        //        nf->CreateTerm(BVSX,a_len,t,
        //                        nf->CreateBVConst(32,a_len));
        //        } break; }

        /*
         * On deeply nested ITES, this can cause an exponential number
         * of nodes to be produced. Especially if there are different
         * extracts over the same node.
         *
         case ITE:
         {
         const ASTNode& t0 = a0[0];
         ASTNode t1 =
         SimplifyTerm(nf->CreateTerm(BVEXTRACT,
         a_len, a0[1], i, j));
         ASTNode t2 =
         SimplifyTerm(nf->CreateTerm(BVEXTRACT,
         a_len, a0[2], i, j));
         output = CreateSimplifiedTermITE(t0, t1, t2);
         break;
         }
         */
        default:
        {
          output = inputterm;
          break;
        }
      }
      break;
    }

    case BVNOT:
    {
      const ASTNode& a0 = inputterm[0];

      assert(a0.GetKind() != BVCONST);

      switch (a0.GetKind())
      {
        case BVNOT:
          output = a0[0];
          break;
        case ITE:
          if (a0[1].isConstant() && a0[2].isConstant())
          {
            ASTNode t =nf->CreateTerm(BVNOT, inputValueWidth, a0[1]);
            ASTNode f =nf->CreateTerm(BVNOT, inputValueWidth, a0[2]);
            output = nf->CreateTerm(ITE, inputValueWidth, a0[0],
                                    BVConstEvaluator(t), BVConstEvaluator(f));
            break;
          }
          /* FALLTHROUGH*/
        // follow on
        default:
        {
            const ASTNode max = _bm->CreateMaxConst(inputValueWidth);
            output = nf->CreateTerm(BVPLUS, inputValueWidth, nf->CreateTerm(BVUMINUS, inputValueWidth, a0), max);
          }
        break;
      }
      break;
    }

    case BVSX:
    {
      // a0 is the expr which is being sign extended
      ASTNode a0 = inputterm[0];

      // a1 represents the length of the term BVSX(a0)
      const ASTNode& a1 = inputterm[1];

      if (a0.GetValueWidth() == inputValueWidth)
      {
        // nothing to signextend
        output = a0;
        break;
      }

      // nb. A BVSX whose argument's most significant bit is known is
      // replaced by a concat by strength reduction.

      assert(a0.GetKind() != BVCONST);

      switch (a0.GetKind())
      {
        case BVNOT:
          output =
              nf->CreateTerm(a0.GetKind(), inputValueWidth,
                             nf->CreateTerm(BVSX, inputValueWidth, a0[0], a1));
          break;
        case BVAND:
        case BVOR:
        {
          const ASTChildren c = a0.GetChildren();
          ASTVec newChildren;
          newChildren.reserve(c.size());
          for (auto it = c.begin(), itend = c.end();
               it != itend; it++)
          {
            newChildren.push_back(
                nf->CreateTerm(BVSX, inputValueWidth, *it, a1));
          }
          output = nf->CreateTerm(a0.GetKind(), inputValueWidth, newChildren);
        }
        break;
        case BVPLUS:
        {
          // BVSX(m,BVPLUS(n,BVSX(t1),BVSX(t2))) <==>
          // BVPLUS(m,BVSX(m,t1),BVSX(m,t2))
          const ASTChildren c = a0.GetChildren();
          bool returnflag = false;
          for (auto it = c.begin(), itend = c.end();
               it != itend; it++)
          {
            if (BVSX != it->GetKind())
            {
              returnflag = true;
              break;
            }
          }
          if (!returnflag)
          {
            ASTVec o;
            o.reserve(c.size());
            for (auto it = c.begin(), itend = c.end();
                 it != itend; it++)
            {
              ASTNode aaa =
                  nf->CreateTerm(BVSX, inputValueWidth, *it, a1);
              o.push_back(aaa);
            }
            output = nf->CreateTerm(a0.GetKind(), inputValueWidth, o);
          }
          break;
        }
        // BVSX(m,BVSX(n,a)) is collapsed to BVSX(m,a) by the
        // simplifying node factory.
        case ITE:
        {
          const ASTNode& cond = a0[0];
          ASTNode thenpart =
              nf->CreateTerm(BVSX, inputValueWidth, a0[1], a1);
          ASTNode elsepart =
              nf->CreateTerm(BVSX, inputValueWidth, a0[2], a1);
          output = CreateSimplifiedTermITE(cond, thenpart, elsepart);
          break;
        }
        default:
          output = inputterm;
          break;
      }
      break;
    }

    case BVZX:
      // nb. BVZX is always lowered to a concat with zero (or its child when
      // the widths match) by the simplifying node factory, so it never
      // reaches here.
      output = inputterm;
      break;

    case BVAND:
    case BVOR:
    {
      // turn BVAND(CONCAT CONCAT) into concat(BVAND() BVAND()). i.e. push ops
      // through concat.
      if (inputterm.Degree() == 2 && inputterm[0].GetKind() == BVCONCAT &&
          inputterm[1].GetKind() == BVCONCAT &&
          inputterm[0][0].GetValueWidth() == inputterm[1][0].GetValueWidth())
      {
        const ASTNode top =
            nf->CreateTerm(k, inputterm[0][0].GetValueWidth(),
                           inputterm[0][0], inputterm[1][0]);
        const ASTNode bottom =
            nf->CreateTerm(k, inputterm[0][1].GetValueWidth(),
                           inputterm[0][1], inputterm[1][1]);
        output = nf->CreateTerm(BVCONCAT, inputterm.GetValueWidth(), top,
                                bottom);
        break;
      }

      const ASTNode max = nf->CreateMaxConst(inputValueWidth);
      const ASTNode zero = nf->CreateZeroConst(inputValueWidth);

      const ASTNode identity = (BVAND == k) ? max : zero;
      const ASTNode annihilator = (BVAND == k) ? zero : max;
      ASTVec c = FlattenKind(inputterm.GetKind(), inputterm.GetChildren());
      SortByArith(c);
      ASTVec constants;
      ASTVec o;
      for (ASTVec::iterator it = c.begin(), itend = c.end(); it != itend; it++)
      {
        ASTNode aaa = *it;
        assert(hasBeenSimplified(aaa));

        if (aaa == annihilator)
        {
          output = annihilator;
          // memoize
          UpdateSimplifyMap(inputterm, output, false);
          if (actualInputterm != inputterm)
            UpdateSimplifyMap(actualInputterm, output, false);
          // cerr << "output of SimplifyTerm: " << output << endl;
          return output;
        }

        if (o.size() > 0 && o.back() == aaa)
        {
          continue; // duplicate.
        }

        // nb: There's no guarantee that the bvneg will immediately follow
        // the thing it's negating if the degree > 2.
        if (o.size() > 0 && aaa.GetKind() == BVNOT && o.back() == aaa[0])
        {
          output = annihilator;
          UpdateSimplifyMap(inputterm, output, false);
          if (actualInputterm != inputterm)
            UpdateSimplifyMap(actualInputterm, output, false);
          return output;
        }

        if (BVCONST == aaa.GetKind())
        {
          constants.push_back(aaa);
        }
        else
        {
          o.push_back(aaa);
        }
      }

      while (constants.size() >= 2)
      {
        ASTNode a = constants.back();
        constants.pop_back();
        ASTNode b = constants.back();
        constants.pop_back();

        ASTNode c = BVConstEvaluator(nf->CreateTerm(
            inputterm.GetKind(), inputterm.GetValueWidth(), a, b));

        constants.push_back(c);
      }
      if (constants.size() != 0 && constants.back() != identity)
        o.push_back(constants.back());

      switch (o.size())
      {
        case 0:
          output = identity;
          break;
        case 1:
          output = o[0];
          break;
        default:
          SortByArith(o);
          output =
              nf->CreateTerm(inputterm.GetKind(), inputterm.GetValueWidth(), o);
          break;
      }

      // This don't make it faster, just makes the graphs easier to understand.
      if (output.GetKind() == BVAND)
      {
        assert(output.Degree() != 0);
        bool allconv = true;
        for (auto it = output.begin(), itend = output.end();
             it != itend; it++)
        {
          if (!isPropositionToTerm(*it))
          {
            allconv = false;
            break;
          }
        }
        if (allconv)
        {
          const ASTNode zero = nf->CreateZeroConst(1);
          ASTVec children;
          for (auto it = output.begin(), itend = output.end();
               it != itend; it++)
          {
            const ASTNode& n = *it;

            if (n[1] == zero)
              children.push_back(nf->CreateNode(NOT, n[0]));
            else
              children.push_back(n[0]);
          }
          output = nf->CreateTerm(ITE, 1, nf->CreateNode(AND, children),
                                  nf->CreateOneConst(1), zero);
          assert(BVTypeCheck(output));
        }

        assert(BVTypeCheck(output));

        // If the leading bits are zero. Replace it by a concat with zero.
        unsigned i;
        if (output.GetKind() == BVAND && output.Degree() == 2 &&
            ((i = numberOfLeadingZeroes(output[0])) > 0))
        {
          // i contains the number of leading zeroes.
          if (i < output.GetValueWidth())
          {
            const unsigned rest = output.GetValueWidth() - i;
            const ASTNode lhs =
                nf->CreateTerm(BVEXTRACT, rest, output[0],
                               nf->CreateBVConst(32, rest - 1),
                               nf->CreateBVConst(32, 0));
            const ASTNode rhs =
                nf->CreateTerm(BVEXTRACT, rest, output[1],
                               nf->CreateBVConst(32, rest - 1),
                               nf->CreateBVConst(32, 0));
            output = nf->CreateTerm(BVCONCAT, output.GetValueWidth(),
                                    nf->CreateZeroConst(i),
                                    nf->CreateTerm(BVAND, rest, lhs, rhs));
          }

          assert(BVTypeCheck(output));
        }
      }
      if (output.GetKind() == BVAND)
      {
        unsigned trailingZeroes = 0;
        for (size_t i = 0; i < output.Degree(); i++)
        {
          const ASTNode& n = output[i];
          if (n.GetKind() != BVCONST)
            continue;
          unsigned j;
          for (j = 0; j < n.GetValueWidth(); j++)
            if (CONSTANTBV::BitVector_bit_test(n.GetBVConst(), j))
              break;

          if (j > trailingZeroes)
            trailingZeroes = j;
        }
        if (trailingZeroes > 0)
        {
          if (trailingZeroes == output.GetValueWidth())
            output = nf->CreateZeroConst(trailingZeroes);
          else
          {
            // cerr << "old" << output;
            ASTNode zeroes = nf->CreateZeroConst(trailingZeroes);
            ASTVec newChildren;
            for (size_t i = 0; i < output.Degree(); i++)
              newChildren.push_back(nf->CreateTerm(
                  BVEXTRACT, output.GetValueWidth() - trailingZeroes, output[i],
                  nf->CreateBVConst(32, output.GetValueWidth() - 1),
                  nf->CreateBVConst(32, trailingZeroes)));

            ASTNode newAnd = nf->CreateTerm(
                BVAND, output.GetValueWidth() - trailingZeroes, newChildren);
            output = nf->CreateTerm(BVCONCAT, output.GetValueWidth(), newAnd,
                                    zeroes);
            assert(BVTypeCheck(output));
            // cerr << "new" << output;
          }
        }
      }

      break;
    }
    case BVCONCAT:
    {
      const ASTNode& t = inputterm[0];
      const ASTNode& u = inputterm[1];

      assert(BVCONST != t.GetKind() || BVCONST != u.GetKind());

      // nb. x[m:n]@x[n-1:k] <==> x[m:k] is done by the simplifying node
      // factory.
      if (t.GetKind() == BVCONCAT && t[0].GetKind() != BVCONCAT)
      {

        /// This makes the left hand child of every concat not a concat.
        const ASTNode& left = t[0];
        ASTNode bottom = nf->CreateTerm(
            BVCONCAT, t[1].GetValueWidth() + u.GetValueWidth(), t[1], u);
        output = nf->CreateTerm(BVCONCAT, inputValueWidth, left, bottom);
        assert(BVTypeCheck(output));
      }
      else
      {
        output = nf->CreateTerm(BVCONCAT, inputValueWidth, t, u);
      }
      break;
    }

    case BVLEFTSHIFT:
    case BVRIGHTSHIFT:
      // nb. A known shift amount is lowered to an extract, and a zero shiftee
      // is folded to zero, by the simplifying node factory.
      output = inputterm;
      break;

    case BVXOR:
    {
      // nb. (x ^ x) == 0 and (0 ^ x) == x are done by the simplifying node
      // factory.
      if (inputterm.Degree() == 2 && inputterm[0].GetKind() == BVCONCAT &&
          inputterm[1].GetKind() == BVCONCAT &&
          inputterm[0][0].GetValueWidth() == inputterm[1][0].GetValueWidth())
      {
        const ASTNode top =
            nf->CreateTerm(k, inputterm[0][0].GetValueWidth(),
                           inputterm[0][0], inputterm[1][0]);
        const ASTNode bottom =
            nf->CreateTerm(k, inputterm[0][1].GetValueWidth(),
                           inputterm[0][1], inputterm[1][1]);
        output = nf->CreateTerm(BVCONCAT, inputterm.GetValueWidth(), top,
                                bottom);
        break;
      }
    }

      output = inputterm;
      break;

    case BVXNOR:
    case BVNAND:
    case BVNOR:
    case BVSRSHIFT:
    // nb. Divisions and remainders with leading-zero dividends are
    // narrowed, and those whose dividend is below the divisor are
    // resolved, by strength reduction.
    case BVDIV:
    case BVMOD:
    {
      output = inputterm;
      break;
    }

    case READ:
    {
      ASTNode out1;

      const

      ASTNode array_term =inputterm[0];
      const
      ASTNode read_index =inputterm[1];

      if (SYMBOL == array_term.GetKind())
      {
        out1 = nf->CreateTerm(READ, inputterm.GetValueWidth(), array_term,
                              read_index);
      }
      else if (WRITE == array_term.GetKind())
      {
        ASTNode eq = CreateSimplifiedEQ(read_index, array_term[1]);
        if (eq == ASTTrue)
          out1 = array_term[2];
        else if (eq == ASTFalse)
        {
          out1 = nf->CreateTerm(READ, inputterm.GetValueWidth(), array_term[0],
                                read_index);
        }
        else
        {
          out1 = nf->CreateTerm(READ, inputterm.GetValueWidth(), array_term,
                                read_index);
        }
      }
      else if (ITE == array_term.GetKind() &&
               !(_bm->getExtensionalityIfAny() != NULL &&
                 _bm->getExtensionalityIfAny()->activeInSolve()))
      {
        // Pushes the READ through ITES, which is potentially exponential.
        // At present, because there's no write refinement or similar, the
        // array transformer is going to do this later anyway. So, we do it
        // here. But it's ugggglly.

        ASTNode cond = array_term[0];
        ASTNode read1 =
            nf->CreateTerm(READ, inputValueWidth, array_term[1], read_index);
        ASTNode read2 =
            nf->CreateTerm(READ, inputValueWidth, array_term[2], read_index);
        out1 = CreateSimplifiedTermITE(cond, read1, read2);
      }
      else if (ITE == array_term.GetKind())
      {
        // Array equality is running: leave the read on the if-then-else.
        // Distributing it would put the reads on the branches, where the
        // consistency checker's T rules cannot see them, and would push a
        // witness anchor into a shape operand recovery does not accept.
        out1 = nf->CreateTerm(READ, inputValueWidth, array_term, read_index);
      }
      else
      {
        FatalError("ffff");
      }

      assert(!out1.IsNull());

// process only if not  in the substitution map. simplifymap
// has been checked already
#if 0
        if (!InsideSubstitutionMap(out1, out1) && out1.GetKind() == READ && WRITE == out1[0].GetKind())
          out1 = RemoveWrites_TopLevel(out1);
#endif

      // it is possible that after all the procesing the READ term
      // reduces to READ(Symbol,const) and hence we should check the
      // substitutionmap once again.
      if (!InsideSubstitutionMap(out1, output))
        output = out1;
      break;
    }

    case ITE:
    {
      output =
          CreateSimplifiedTermITE(inputterm[0], inputterm[1], inputterm[2]);
      break;
    }

    case SBVREM:
    case SBVMOD:
    {
      output = inputterm;
      break;
    }

    case SBVDIV:
    {
      output = inputterm;
      if (SBVDIV == output.GetKind() && output.GetChildren().size() == 2 &&
          output.GetChildren()[0].GetKind() == BVSX &&
          output.GetChildren()[1].GetKind() == BVSX)
        output = pullUpBVSX(output);

      break;
    }
    case FP_ABS:
    case FP_NEG:
    case FP_ADD:
    case FP_SUB:
    case FP_MUL:
    case FP_DIV:
    case FP_FMA:
    case FP_SQRT:
    case FP_REM:
    case FP_ROUNDTOINTEGRAL:
    case FP_MIN:
    case FP_MAX:
    case FP_TOFP:
    case FP_TOFP_SIGNED:
    case FP_TOFP_UNSIGNED:
    case FP_TO_UBV:
    case FP_TO_SBV:
    case FP_TO_IEEE_BV:
    {
      // Rebuild with the same kind and arity. Only the float operands are
      // simplified: the other children -- the rounding mode of the arithmetic
      // operations, and to_fp's format arguments -- are constants the blaster
      // reads directly, so simplifying them buys nothing and risks rewriting
      // them into a form it does not recognise.
      //
      // Nothing here lowers anything. A floating-point operation simplifies
      // to a floating-point operation, with its format derived from its kind
      // and children as always; FloatBlast replaces the whole layer with bits
      // in one pass, before the formula ever reaches this code. Blasting from
      // inside simplification meant rebuilding an FP_ADD over bitvector
      // children -- a node that does not type check, and which only passed
      // because a float format was stamped onto it and its blasted children.
      // Nodes are hash-consed, so that stamp landed on whatever else denoted
      // the same bits.
      // The generic operand phase of the job already simplified every float
      // child. Non-float metadata children were carried through unchanged.
      ASTVec simplified = toASTVec(inputterm.GetChildren());

      // The factory may fold the operation as it rebuilds it (abs/neg of a
      // constant, x*1.0, x/1.0), which is the whole point of going back
      // through it; whatever comes back is what this term simplifies to.
      output = nf->CreateTerm(k, inputValueWidth, simplified);
      break;
    }

    case WRITE:
    default:
      FatalError("SimplifyTerm: Control should never reach here:", inputterm,
                 k);
      assert(false);
      exit(-1);
      break;
  }

  return ASTUndefined;
}

// this function assumes that the input is a vector of childnodes of
// a BVPLUS term. it combines like terms and returns a bvplus
// term. e.g. 1.x + 2.x is converted to 3.x
ASTNode Simplifier::CombineLikeTerms(const ASTNode& a)
{
  if (BVPLUS != a.GetKind())
    return a;

  ASTNode output;
  if (CheckSimplifyMap(a, output, false))
  {
    // check memo table
    // cerr << "output of SimplifyTerm Cache: " << output << endl;
    return output;
  }

  return CombineLikeTerms(toASTVec(a.GetChildren()));
}

ASTNode Simplifier::CombineLikeTerms(const ASTVec& c)
{
  ASTNode output;
  // map from variables to vector of constants
  ASTNodeToVecMap vars_to_consts;
  // vector to hold constants
  ASTVec constkids;
  ASTVec outputvec;

  // useful constants
  unsigned int len = c[0].GetValueWidth();
  ASTNode one = nf->CreateOneConst(len);
  ASTNode zero = nf->CreateZeroConst(len);
  ASTNode max = nf->CreateMaxConst(len);

  // go over the childnodes of the input bvplus, and collect like
  // terms in a map. the key of the map are the variables, and the
  // values are stored in a ASTVec
  for (ASTVec::const_iterator it = c.begin(), itend = c.end(); it != itend;
       it++)
  {
    const ASTNode& aaa = *it;
    if (SYMBOL == aaa.GetKind())
    {
      vars_to_consts[aaa].push_back(one);
    }
    else if (BVMULT == aaa.GetKind() && 2 == aaa.Degree() &&
             BVUMINUS == aaa[0].GetKind() && BVCONST == aaa[0][0].GetKind())
    {
      //(BVUMINUS(c))*(y) <==> compute(BVUMINUS(c))*y
      ASTNode compute_const = BVConstEvaluator(aaa[0]);
      vars_to_consts[aaa[1]].push_back(compute_const);
    }
    else if (BVMULT == aaa.GetKind() && 2 == aaa.Degree() &&
             BVUMINUS == aaa[1].GetKind() && BVCONST == aaa[0].GetKind())
    {
      // c*(BVUMINUS(y)) <==> compute(BVUMINUS(c))*y
      ASTNode cccc = BVConstEvaluator(nf->CreateTerm(BVUMINUS, len, aaa[0]));
      vars_to_consts[aaa[1][0]].push_back(cccc);
    }
    else if (BVMULT == aaa.GetKind() && BVCONST == aaa[0].GetKind())
    {
      if (2 == aaa.Degree())
      {
        vars_to_consts[aaa[1]].push_back(aaa[0]);
      }
      else
      {
        // Wider multiply: the constant is the coefficient, the product of
        // the remaining operands is the variable part.
        ASTVec rest(aaa.begin() + 1, aaa.end());
        vars_to_consts[nf->CreateTerm(BVMULT, len, rest)].push_back(aaa[0]);
      }
    }
    else if (BVMULT == aaa.GetKind() && 2 == aaa.Degree() &&
             BVUMINUS == aaa[0].GetKind())
    {
      //(-1*x)*(y) <==> -1*(xy)
      ASTNode cccc = nf->CreateTerm(BVMULT, len, aaa[0][0], aaa[1]);
      ASTVec cNodes = toASTVec(cccc.GetChildren());
      SortByArith(cNodes);
      vars_to_consts[cccc].push_back(max);
    }
    else if (BVMULT == aaa.GetKind() && 2 == aaa.Degree() &&
             BVUMINUS == aaa[1].GetKind())
    {
      // x*(-1*y) <==> -1*(xy)
      ASTNode cccc = nf->CreateTerm(BVMULT, len, aaa[0], aaa[1][0]);
      ASTVec cNodes = toASTVec(cccc.GetChildren());
      SortByArith(cNodes);
      vars_to_consts[cccc].push_back(max);
    }
    else if (BVCONST == aaa.GetKind())
    {
      constkids.push_back(aaa);
    }
    else if (BVUMINUS == aaa.GetKind())
    {
      // helps to convert BVUMINUS into a BVMULT. here the max
      // constant represents -1. this transformation allows us to
      // conclude that x + BVUMINUS(x) is 0.
      vars_to_consts[aaa[0]].push_back(max);
    }
    else
      vars_to_consts[aaa].push_back(one);
  }

  // go over the map from variables to vector of values. combine the
  // vector of values, multiply to the variable, and put the
  // resultant monomial in the output BVPLUS.
  for (ASTNodeToVecMap::iterator it = vars_to_consts.begin(),
                                 itend = vars_to_consts.end();
       it != itend; it++)
  {
    const ASTVec& ccc = it->second;

    ASTNode constant;
    if (1 < ccc.size())
    {

      constant = NonMemberBVConstEvaluator(_bm, BVPLUS,ccc, ccc[0].GetValueWidth());
    }
    else
      constant = ccc[0];

    // constant * var
    ASTNode monom;
    if (zero == constant)
      monom = zero;
    else if (one == constant)
      monom = it->first;
    else
    {
      monom =nf->CreateTerm(BVMULT, constant.GetValueWidth(),
                                          constant, it->first);
    }
    if (zero != monom)
    {
      outputvec.push_back(monom);
    }
  }

  if (constkids.size() > 1)
  {
    ASTNode output = NonMemberBVConstEvaluator(_bm, BVPLUS, constkids,
                                               constkids[0].GetValueWidth());
    if (output != zero)
      outputvec.push_back(output);
  }
  else if (constkids.size() == 1)
  {
    if (constkids[0] != zero)
      outputvec.push_back(constkids[0]);
  }

  if (outputvec.size() > 1)
  {
    output = nf->CreateTerm(BVPLUS, len, outputvec);
  }
  else if (outputvec.size() == 1)
  {
    output = outputvec[0];
  }
  else
  {
    output = zero;
  }

  // memoize
  // UpdateSimplifyMap(a,output,false);
  return output;
}

// accepts lhs and rhs, and returns lhs - rhs = 0. The function
// assumes that lhs and rhs have already been simplified. although
// this assumption is not needed for correctness, it is essential for
// performance. The function also assumes that lhs is a BVPLUS
ASTNode Simplifier::LhsMinusRhsTerm(const ASTNode& eq,
                                    const ASTNode& simplifiedNegatedRhs)
{
  assert ( eq.GetKind() == EQ);

  ASTNode lhs = eq[0];
  const Kind lhsKind = lhs.GetKind();
  const Kind rhsKind = eq[1].GetKind();
  if (lhsKind !=BVPLUS && rhsKind == BVPLUS)
    lhs = eq[1];

  const ASTNode&
    rhs = simplifiedNegatedRhs;
  const

  unsigned len = lhs.GetValueWidth();

  ASTVec lhsChildren = toASTVec(lhs.GetChildren());
  const ASTChildren rhsChildren = rhs.GetChildren();
  ASTNode sum;
  if ( lhs.GetKind() != BVPLUS && rhs.GetKind() != BVPLUS)
    sum = nf->CreateTerm(BVPLUS, len, lhs, rhs);
  else if ( lhs.GetKind() == BVPLUS && rhs.GetKind() == BVPLUS)
  {
    lhsChildren.insert(lhsChildren.end(), rhsChildren.begin(),
                       rhsChildren.end());
    sum = nf->CreateTerm(BVPLUS, len, lhsChildren);
  }
  else if ( lhs.GetKind() == BVPLUS)
  {
    lhsChildren.push_back(rhs);
    sum = nf->CreateTerm(BVPLUS, len, lhsChildren);
  }
  else
    sum = nf->CreateTerm(BVPLUS, len, lhs, rhs);

  return CombineLikeTerms(sum);
}

// THis function accepts a BVMULT(t1,t2) and distributes the mult
// over plus if either or both t1 and t2 are BVPLUSes.
//
// x*(y1 + y2 + ...+ yn) <==> x*y1 + x*y2 + ... + x*yn
//
// (y1 + y2 + ...+ yn)*x <==> x*y1 + x*y2 + ... + x*yn
//
// The function assumes that the BVPLUSes have been flattened
ASTNode Simplifier::DistributeMultOverPlus(const ASTNode& a,
                                           bool startdistribution)
{
  if (!startdistribution)
    return a;
  Kind k = a.GetKind();
  if (BVMULT != k)
    return a;

  if (a.Degree() != 2)
    return a;

  ASTNode left = a[0];
  ASTNode right = a[1];
  Kind left_kind = left.GetKind();
  Kind right_kind = right.GetKind();

  ASTNode output;
  if (CheckSimplifyMap(a, output, false))
  {
    // check memo table
    // cerr << "output of SimplifyTerm Cache: " << output << endl;
    return output;
  }

  // special case optimization: c1*(c2*t1) <==> (c1*c2)*t1
  if (BVCONST == left_kind && BVMULT == right_kind &&
      BVCONST == right[0].GetKind())
  {
    ASTNode c = BVConstEvaluator(
        nf->CreateTerm(BVMULT, a.GetValueWidth(), left, right[0]));
    c = nf->CreateTerm(BVMULT, a.GetValueWidth(), c, right[1]);
    return c;
  }

  // special case optimization: c1*(t1*c2) <==> (c1*c2)*t1
  if (BVCONST == left_kind && BVMULT == right_kind &&
      BVCONST == right[1].GetKind())
  {
    ASTNode c = BVConstEvaluator(
        nf->CreateTerm(BVMULT, a.GetValueWidth(), left, right[1]));
    c = nf->CreateTerm(BVMULT, a.GetValueWidth(), c, right[0]);
    return c;
  }

  // atleast one of left or right have to be BVPLUS
  if (!(BVPLUS == left_kind || BVPLUS == right_kind))
  {
    return a;
  }

  // if left is BVPLUS and right is not, then swap left and right. we
  // can do this since BVMULT is communtative
  ASTNode swap;
  if (BVPLUS == left_kind && BVPLUS != right_kind)
  {
    swap = left;
    left = right;
    right = swap;
  }
  left_kind = left.GetKind();
  right_kind = right.GetKind();

  // by this point we are gauranteed that right is a BVPLUS, but left
  // may not be
  const ASTChildren rightnodes = right.GetChildren();
  ASTVec outputvec;
  unsigned len = a.GetValueWidth();
  ASTNode zero = nf->CreateZeroConst(len);
  ASTNode one = nf->CreateOneConst(len);
  if (BVPLUS != left_kind)
  {
    // if the multiplier is not a BVPLUS then we have a special case
    // x*(y1 + y2 + ...+ yn) <==> x*y1 + x*y2 + ... + x*yn
    if (zero == left)
    {
      outputvec.push_back(zero);
    }
    else if (one == left)
    {
      outputvec.push_back(left);
    }
    else
    {
      for (auto j = rightnodes.begin(), jend = rightnodes.end();
           j != jend; j++)
      {
        ASTNode out =nf->CreateTerm(BVMULT, len, left, *j);
        outputvec.push_back(out);
      }
    }
  }
  else
  {
    const ASTChildren leftnodes = left.GetChildren();
    // (x1 + x2 + ... + xm)*(y1 + y2 + ...+ yn) <==> x1*y1 + x1*y2 +
    // ... + x2*y1 + ... + xm*yn
    for (auto i = leftnodes.begin(), iend = leftnodes.end();
         i != iend; i++)
    {
      ASTNode multiplier = *i;
      for (auto j = rightnodes.begin(), jend = rightnodes.end();
           j != jend; j++)
      {
        ASTNode out =nf->CreateTerm(BVMULT, len, multiplier, *j);
        outputvec.push_back(out);
      }
    }
  }

  // compute output here
  if (outputvec.size() > 1)
  {
    output = CombineLikeTerms(nf->CreateTerm(BVPLUS, len, outputvec));
  }
  else
    output =outputvec[0];

  // memoize
  // UpdateSimplifyMap(a,output,false);
  return output;
}

// recursively simplify things that are of type array.
ASTNode Simplifier::SimplifyArrayTerm(const ASTNode& term)
{
  return simplifyNode(term, false, SimplifyJob::Array);
}

// compute the multiplicative inverse of the input
ASTNode Simplifier::MultiplicativeInverse(const ASTNode& d)
{
  ASTNode c = d;
  if (BVCONST != c.GetKind())
  {
    FatalError("Input must be a constant", c);
  }

  if (!BVConstIsOdd(c))
  {
    FatalError("MultiplicativeInverse: Input must be odd: ", c);
  }

  // cerr << "input to multinverse function is: " << d << endl;
  ASTNode inverse;
  if (CheckMultInverseMap(d, inverse))
  {
    // cerr << "found the inverse of: " << d << "and it is: " <<
    // inverse << endl;
    return inverse;
  }

  inverse = c;
  unsigned inputwidth = c.GetValueWidth();

  // Compute the multiplicative inverse of c using the extended
  // euclidian algorithm
  //
  // create a '0' which is 1 bit long
  ASTNode onebit_zero = nf->CreateZeroConst(1);
  // zero pad t0, i.e. 0 @ t0
  c = BVConstEvaluator(
      nf->CreateTerm(BVCONCAT, inputwidth + 1, onebit_zero, c));

  // construct 2^(inputwidth), i.e. a bitvector of length
  //'inputwidth+1', which is max(inputwidth)+1
  //
  // all 1's
  ASTNode max = nf->CreateMaxConst(inputwidth);
  // zero pad max
  max = BVConstEvaluator(
      nf->CreateTerm(BVCONCAT, inputwidth + 1, onebit_zero, max));
  //nf->Create a '1' which has leading zeros of length 'inputwidth'
  ASTNode inputwidthplusone_one = nf->CreateOneConst(inputwidth + 1);
  // add 1 to max
  max = nf->CreateTerm(BVPLUS, inputwidth + 1, max, inputwidthplusone_one);
  max = BVConstEvaluator(max);
  ASTNode zero = nf->CreateZeroConst(inputwidth + 1);
  ASTNode max_bvgt_0 = nf->CreateNode(BVGT, max, zero);
  ASTNode quotient, remainder;
  ASTNode x, x1, x2;

  // x1 initialized to zero
  x1 = zero;
  // x2 initialized to one
  x2 = nf->CreateOneConst(inputwidth + 1);
  while (ASTTrue == BVConstEvaluator(max_bvgt_0))
  {
    // quotient = (c divided by max)
    quotient = BVConstEvaluator(nf->CreateTerm(BVDIV, inputwidth + 1, c, max));

    // remainder of (c divided by max)
    remainder = BVConstEvaluator(nf->CreateTerm(BVMOD, inputwidth + 1, c, max));

    // x = x2 - q*x1
    x = nf->CreateTerm(BVSUB, inputwidth + 1, x2,
                       nf->CreateTerm(BVMULT, inputwidth + 1, quotient, x1));
    x = BVConstEvaluator(x);

    // fix the inputs to the extended euclidian algo
    c = max;
    max = remainder;
    max_bvgt_0 = nf->CreateNode(BVGT, max, zero);

    x2 = x1;
    x1 = x;
  }

  ASTNode hi = nf->CreateBVConst(32, inputwidth - 1);
  ASTNode low = nf->CreateZeroConst(32);
  inverse = nf->CreateTerm(BVEXTRACT, inputwidth, x2, hi, low);
  inverse = BVConstEvaluator(inverse);

  UpdateMultInverseMap(d, inverse);
  // cerr << "output of multinverse function is: " << inverse << endl;
  return inverse;
}

// returns true if the input is odd
bool Simplifier::BVConstIsOdd(const ASTNode& c)
{
  if (BVCONST != c.GetKind())
  {
    FatalError("Input must be a constant", c);
  }

  ASTNode zero = nf->CreateZeroConst(1);
  ASTNode hi = nf->CreateZeroConst(32);
  ASTNode low = hi;
  ASTNode lowestbit = nf->CreateTerm(BVEXTRACT, 1, c, hi, low);
  lowestbit = BVConstEvaluator(lowestbit);

  if (lowestbit == zero)
  {
    return false;
  }
  else
  {
    return true;
  }
}

// in ext/std::unordered_map, and tr/unordered_map, there is no provision to
// shrink down the number of buckets in a hash map. If the std::unordered_map
// has previously held a lot of data, then it will have a lot of
// buckets. Slowing down iterators and clears() in particular.
void Simplifier::ResetSimplifyMaps()
{
  // clear() is extremely expensive for std::unordered_maps with a lot of
  // buckets, in the EXT_MAP implementation it visits every bucket,
  // checking whether each bucket is empty or not, if non-empty it
  // deletes the contents.  The destructor seems to clear everything
  // anyway.

  // (With the dense maps the delete/new and clear() are both cheap -- one
  // vector teardown -- but the delete also returns the memory.)

  // SimplifyMap->clear();
  delete SimplifyMap;
  SimplifyMap = new DenseNodeMap(INITIAL_TABLE_SIZE);

  // SimplifyNegMap->clear();
  delete SimplifyNegMap;
  SimplifyNegMap = new DenseNodeMap(INITIAL_TABLE_SIZE);
}

void Simplifier::printCacheStatus()
{
  cerr << "SimplifyMap:" << SimplifyMap->size() << ":"
       << SimplifyMap->bucket_count() << endl;
  cerr << "SimplifyNegMap:" << SimplifyNegMap->size() << ":"
       << SimplifyNegMap->bucket_count() << endl;
  cerr << "MultInverseMap" << MultInverseMap.size() << ":"
       << MultInverseMap.bucket_count() << endl;

#if 0
    cerr << "ReadOverWrite_NewName_Map" << ReadOverWrite_NewName_Map->size() << ":"
        << ReadOverWrite_NewName_Map->bucket_count() << endl;
    cerr << "NewName_ReadOverWrite_Map" << NewName_ReadOverWrite_Map.size() << ":"
        << NewName_ReadOverWrite_Map.bucket_count() << endl;
#endif
  cerr << "substn_map" << substitutionMap.Return_SolverMap()->size() << ":"
       << substitutionMap.Return_SolverMap()->bucket_count() << endl;
}

ASTNode Simplifier::BVConstEvaluator(const ASTNode& t)
{
  if (t.isConstant())
    return t;

  ASTNode OutputNode;

  if (InsideSubstitutionMap(t, OutputNode))
    return OutputNode;

  OutputNode = NonMemberBVConstEvaluator(_bm, t);
  UpdateSolverMap(t, OutputNode);
  return OutputNode;
}


} // namespace stp
