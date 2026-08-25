/********************************************************************
 * AUTHORS: David L. Dill, Vijay Ganesh, Trevor Hansen
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
#include "stp/ToSat/BitBlaster.h"
#include "stp/FloatBlaster/DecimalLiteral.h"
#include "stp/FloatBlaster/FloatBlaster.h"
#include "stp/FloatBlaster/rounding_modes.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/constantBitP/ConstantBitPropagation.h"
#include "stp/Simplifier/constantBitP/FixedBits.h"
#include "stp/Simplifier/constantBitP/NodeToFixedBitsMap.h"
#include "stp/ToSat/BBNodeManagerAIG.h"
#include "stp/Util/DagWalk.h"
#include <algorithm>
#include <cassert>
#include <deque>
#include <cmath>
#include <limits>

namespace stp
{

static bool allBBNodesAreCIs(const BBNodeVec& vec)
{
  for (const auto& node : vec)
    if (node.IsNull() || node.symbol_index < 0)
      return false;
  return !vec.empty();
}

// For operands that contain internal AIG nodes (e.g. BVAND results),
// create fresh proxy CIs with biconditional side constraints so that
// downstream abstraction can proceed.
static BBNodeVec ensureProxyCIs(
    BBNodeManagerAIG* nf,
    const ASTNode& node,
    const BBNodeVec& bits,
    std::vector<BBNode>& sideConstraints)
{
  auto it = nf->symbolToBBNode.find(node);
  if (it != nf->symbolToBBNode.end())
    return it->second;

  if (allBBNodesAreCIs(bits))
  {
    nf->symbolToBBNode[node] = bits;
    return bits;
  }

  unsigned width = bits.size();
  BBNodeVec proxies(width);
  for (unsigned i = 0; i < width; i++)
  {
    proxies[i] = BBNodeAIG(Aig_ObjCreateCi(nf->aigMgr));
    proxies[i].symbol_index = nf->aigMgr->vCis->nSize - 1;
    Aig_Obj_t* bicond = Aig_Not(orderedAigExor(
        nf->aigMgr, proxies[i].n, bits[i].n));
    sideConstraints.push_back(BBNodeAIG(bicond));
  }
  nf->symbolToBBNode[node] = proxies;
  return proxies;
}

/********************************************************************
 * BitBlast
 *
 * Convert bitvector terms and formulas to boolean formulas.  A term
 * is something that can represent a multi-bit bitvector, such as
 * BVPLUS or BVXOR (or a BV variable or constant).  A formula (form)
 * represents a boolean value, such as EQ or BVLE.  Bit blasting a
 * term representing an n-bit bitvector with BBTerm yields a vector
 * of n boolean formulas (returning BBNodeVec).  Bit blasting a formula
 * returns a single boolean formula (type BBNode).  A bitblasted
 * term is a vector of BBNodes for formulas.  The 0th element of
 * the vector corresponds to bit 0 -- the low-order bit.
********************************************************************/

using simplifier::constantBitP::FixedBits;
using simplifier::constantBitP::NodeToFixedBitsMap;
using std::make_pair;

// Used by the debug_multiply tracing below. Defined at the end of this file.
std::ostream& operator<<(std::ostream& output, const BBNodeAIG& h);

vector<BBNodeAIG> _empty_BBNodeAIGVec;

// Bit blast a bitvector term.  The term must have a kind for a
// bitvector term.  Result is a ref to a vector of formula nodes
// representing the boolean formula.

// This prints out each constant expression that the bitblaster
// discovers. I use this to check that the expressions that are
// reaching the bitblaster don't have obvious simplifications
// that should have already been applied.
const bool debug_do_check = false;
const bool debug_bitblaster = false;

namespace
{
// BBForm and BBTerm share one recursion budget because they call each other.
// Keeping the counter in a scope guard makes all of their many early returns
// release the budget without putting cleanup code on each path.
class UnprimedDepth
{
  size_t& depth;
  const bool active;

public:
  UnprimedDepth(size_t& depth_, const bool active_)
      : depth(depth_), active(active_)
  {
    if (active)
      ++depth;
  }

  UnprimedDepth(const UnprimedDepth&) = delete;
  UnprimedDepth& operator=(const UnprimedDepth&) = delete;

  ~UnprimedDepth()
  {
    if (active)
      --depth;
  }
};
} // namespace

// Translates signed BVDIV,BVMOD and BVREM into unsigned variety
static ASTNode TranslateSignedDivModRem(const ASTNode& in, NodeFactory* nf)
{
  assert(in.GetChildren().size() == 2);

  const ASTNode& dividend = in[0];
  const ASTNode& divisor = in[1];
  const unsigned len = in.GetValueWidth();

  ASTNode hi1 = nf->CreateBVConst(32, len - 1);
  ASTNode one = nf->CreateOneConst(1);
  // create the condition for the dividend
  ASTNode cond_dividend =
      nf->CreateNode(EQ, one, nf->CreateTerm(BVEXTRACT, 1, dividend, hi1, hi1));
  // create the condition for the divisor
  ASTNode cond_divisor =
      nf->CreateNode(EQ, one, nf->CreateTerm(BVEXTRACT, 1, divisor, hi1, hi1));

  if (SBVREM == in.GetKind())
  {
    // BVMOD is an expensive operation. So have the fewest bvmods
    // possible. Just one.

    // Take absolute value.
    ASTNode pos_dividend =
        nf->CreateTerm(ITE, len, cond_dividend,
                       nf->CreateTerm(BVUMINUS, len, dividend), dividend);
    ASTNode pos_divisor =
        nf->CreateTerm(ITE, len, cond_divisor,
                       nf->CreateTerm(BVUMINUS, len, divisor), divisor);

    // create the modulus term
    ASTNode modnode = nf->CreateTerm(BVMOD, len, pos_dividend, pos_divisor);

    // If the dividend is <0 take the unary minus.
    ASTNode n = nf->CreateTerm(ITE, len, cond_dividend,
                               nf->CreateTerm(BVUMINUS, len, modnode), modnode);
    return n;
  }

  // This is the modulus of dividing rounding to -infinity.
  else if (SBVMOD == in.GetKind())
  {

    /*
    (bvsmod s t) abbreviates
        (let ((?msb_s ((_ extract |m-1| |m-1|) s))
          (?msb_t ((_ extract |m-1| |m-1|) t)))
        (let ((abs_s (ite (= ?msb_s #b0) s (bvneg s)))
            (abs_t (ite (= ?msb_t #b0) t (bvneg t))))
          (let ((u (bvurem abs_s abs_t)))
          (ite (= u (_ bv0 m))
             u
          (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
             u
          (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
             (bvadd (bvneg u) t)
          (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
             (bvadd u t)
             (bvneg u))))))))
     */

    // Take absolute value.
    ASTNode pos_dividend =
        nf->CreateTerm(ITE, len, cond_dividend,
                       nf->CreateTerm(BVUMINUS, len, dividend), dividend);
    ASTNode pos_divisor =
        nf->CreateTerm(ITE, len, cond_divisor,
                       nf->CreateTerm(BVUMINUS, len, divisor), divisor);

    ASTNode urem_node = nf->CreateTerm(BVMOD, len, pos_dividend, pos_divisor);

    // If the dividend is <0, then we negate the whole thing.
    ASTNode rev_node =
        nf->CreateTerm(ITE, len, cond_dividend,
                       nf->CreateTerm(BVUMINUS, len, urem_node), urem_node);

    // if It's XOR <0, and it doesn't perfectly divide, then add t (not its
    // absolute value).
    ASTNode xor_node = nf->CreateNode(XOR, cond_dividend, cond_divisor);
    ASTNode neZ = nf->CreateNode(
        NOT,
        nf->CreateNode(EQ, rev_node,
                       nf->CreateZeroConst(divisor.GetValueWidth())));
    ASTNode cond = nf->CreateNode(AND, xor_node, neZ);
    ASTNode n = nf->CreateTerm(ITE, len, cond,
                               nf->CreateTerm(BVPLUS, len, rev_node, divisor),
                               rev_node);

    return n;
  }
  else if (SBVDIV == in.GetKind())
  {
    // now handle the BVDIV case
    // if topBit(dividend) is 1 and topBit(divisor) is 0
    //
    // then output is -BVDIV(-dividend,divisor)
    //
    // elseif topBit(dividend) is 0 and topBit(divisor) is 1
    //
    // then output is -BVDIV(dividend,-divisor)
    //
    // elseif topBit(dividend) is 1 and topBit(divisor) is 1
    //
    // then output is BVDIV(-dividend,-divisor)
    //
    // else simply output BVDIV(dividend,divisor)

    // Take absolute value.
    ASTNode pos_dividend =
        nf->CreateTerm(ITE, len, cond_dividend,
                       nf->CreateTerm(BVUMINUS, len, dividend), dividend);
    ASTNode pos_divisor =
        nf->CreateTerm(ITE, len, cond_divisor,
                       nf->CreateTerm(BVUMINUS, len, divisor), divisor);

    ASTNode divnode = nf->CreateTerm(BVDIV, len, pos_dividend, pos_divisor);

    // A little confusing. Only negate the result if they are XOR <0.
    ASTNode xor_node = nf->CreateNode(XOR, cond_dividend, cond_divisor);
    ASTNode n = nf->CreateTerm(ITE, len, xor_node,
                               nf->CreateTerm(BVUMINUS, len, divnode), divnode);

    return n;
  }

  FatalError("TranslateSignedDivModRem:"
             "input must be signed DIV/MOD/REM",
             in);
}

//"Hash" (=add) first 5 node IDs together
//TODO pretty bad hash
class BBVecHasher
{
public:
  size_t operator()(const vector<BBNode>& n) const
  {
    size_t hash = 0;
    for (size_t i = 0; i < std::min(n.size(), (size_t)6); i++)
    {
      hash += n[i].GetNodeNum();
    }
    return hash;
  }
};

class BBVecEquals
{
public:
  bool operator()(const vector<BBNode>& n0, const vector<BBNode>& n1) const
  {
    if (n0.size() != n1.size())
      return false;

    for (size_t i = 0; i < n0.size(); i++)
    {
      if (!(n0[i] == n1[i]))
        return false;
    }
    return true;
  }
};

// Look through the maps to see what the bitblaster has discovered (if anything)
// is constant.
// Then look through for AIGS that are mapped to from different ASTNodes.
void BitBlaster::getConsts(const ASTNode& form,
                           ASTNodeMap& fromTo,
                           ASTNodeMap& equivs)
{
  assert(form.GetType() == BOOLEAN_TYPE);

  BBNodeSet support;
  BBForm(form, support);
  assert(support.size() == 0);

  {
    for (auto it = BBFormMemo.begin(); it != BBFormMemo.end(); it++)
    {
      const ASTNode& n = it->first;
      const BBNode& x = it->second;
      if (n.isConstant())
        continue;

      if (x != BBTrue && x != BBFalse)
        continue;

      assert(n.GetType() == BOOLEAN_TYPE);

      ASTNode result;
      if (x == BBTrue)
        result = ASTNF->getTrue();
      else
        result = ASTNF->getFalse();

      if (n.GetKind() != SYMBOL)
        fromTo.insert(std::make_pair(n, result));
      else
        simp->UpdateSubstitutionMap(n, result);
    }
  }

  for (auto it = BBTermMemo.begin(); it != BBTermMemo.end(); it++)
  {
    const ASTNode& n = it->first;
    // FloatBlast removes FP operations but deliberately leaves float symbols
    // and constants as their packed-bit leaves. They are bit-blaster terms at
    // this internal boundary even though their public sort remains
    // FLOATINGPOINT_TYPE for model reconstruction.
    assert(isBitsValued(n));

    if (n.isConstant())
      continue;

    vector<BBNode>& x = it->second;
    assert(x.size() == n.GetValueWidth());

    bool constNode = true;
    for (int i = 0; i < (int)x.size(); i++)
    {
      if (x[i] != BBTrue && x[i] != BBFalse)
      {
        constNode = false;
        break;
      }
    }
    if (!constNode)
      continue;

    // getConstant re-makes a float's packed bits as an ASTFPConst, keeping
    // the substitution type-correct.
    ASTNode r = getConstant(x, n);
    if (n.GetKind() == SYMBOL)
      simp->UpdateSubstitutionMap(n, r);
    else
      fromTo.insert(std::make_pair(n, r));
  }

  if (true) //(uf->isSet("bb-equiv", "1"))
  {
    std::unordered_map<intptr_t, ASTNode> nodeToFn;
    for (auto it = BBFormMemo.begin(); it != BBFormMemo.end(); it++)
    {
      const ASTNode& n = it->first;
      if (n.isConstant())
        continue;

      const BBNode& x = it->second;
      if (x == BBTrue || x == BBFalse)
        continue;

      if (nodeToFn.find(x.GetNodeNum()) == nodeToFn.end())
      {
        nodeToFn.insert(make_pair(x.GetNodeNum(), n));
      }
      else
      {
        const ASTNode other = (nodeToFn.find(x.GetNodeNum()))->second;
        std::pair<ASTNode, ASTNode> p;
        if (other.GetNodeNum() > n.GetNodeNum())
          p = make_pair(other, n);
        else
          p = make_pair(n, other);

        equivs.insert(p);
        // std::cerr << "from" << p.first << " to" << p.second;
        // ASTNode equals =
        // ASTNF->CreateNode(NOT,ASTNF->CreateNode(EQ,p.first,p.second));
        // printer::SMTLIB2_PrintBack(std::cerr,p.second);
      }
    }
  }

  if (true) //(uf->isSet("bb-equiv", "1"))
  {
    typedef std::unordered_map<vector<BBNode>, ASTNode, BBVecHasher, BBVecEquals>
        M;
    M lookup;
    for (auto it = BBTermMemo.begin(); it != BBTermMemo.end(); it++)
    {
      const ASTNode& n = it->first;
      if (n.isConstant())
        continue;

      const vector<BBNode>& x = it->second;

      bool constNode = true;
      for (int i = 0; i < (int)x.size(); i++)
      {
        if (x[i] != BBTrue && x[i] != BBFalse)
        {
          constNode = false;
          break;
        }
      }
      if (!constNode)
        continue;

      if (lookup.find(x) == lookup.end())
      {
        lookup.insert(make_pair(x, n));
      }
      else
      {
        const ASTNode other = (lookup.find(x))->second;
        std::pair<ASTNode, ASTNode> p;
        if (other.GetNodeNum() > n.GetNodeNum())
          p = make_pair(other, n);
        else
          p = make_pair(n, other);

        // cerr << "EQUIV";
        equivs.insert(p);
      }
    }
  }
}

void BitBlaster::commonCheck(const ASTNode& n)
{
  cerr << "Non constant is constant:";
  cerr << n << endl;

  if (cb == NULL)
    return;
  if (cb->fixedMap->map->find(n) != cb->fixedMap->map->end())
  {
    FixedBits* b = cb->fixedMap->map->find(n)->second;
    cerr << "fixed bits are:" << *b << endl;
  }
}

// If x isn't a constant, and the bit-blasted version is. Print out the
// AST nodes and the fixed bits.
void BitBlaster::check(const BBNode& x,
                       const ASTNode& n)
{
  if (n.isConstant())
    return;

  if (x != BBTrue && x != BBFalse)
    return;

  commonCheck(n);
}

void BitBlaster::check(const vector<BBNode>& x,
                       const ASTNode& n)
{
  if (n.isConstant())
    return;

  for (int i = 0; i < (int)x.size(); i++)
  {
    if (x[i] != BBTrue && x[i] != BBFalse)
      return;
  }

  commonCheck(n);
}

bool BitBlaster::update(
    const ASTNode& n, const int i, simplifier::constantBitP::FixedBits* b,
    BBNode& bb, BBNodeSet& support)
{
  if (b->isFixed(i) && (!(bb == BBTrue || bb == BBFalse)))
  {
    // We have a fixed bit, but the bitblasted values aren't constant true or
    // false.
    if (uf->conjoin_to_top && (fixedFromBottom.find(n) == fixedFromBottom.end()))
    {
      if (b->getValue(i))
        support.insert(bb);
      else
        support.insert(nf->CreateNode(NOT, bb));
    }

    bb = b->getValue(i) ? BBTrue : BBFalse;
  }
  else if (!b->isFixed(i) && (bb == BBTrue || bb == BBFalse))
  {
    b->setFixed(i, true);
    b->setValue(i, bb == BBTrue ? true : false);
    return true; // Need to propagate.
  }

  return false;
}

void BitBlaster::updateForm(const ASTNode& n,
                            BBNode& bb,
                            BBNodeSet& support)
{
  if (cb == NULL || n.isConstant())
    return;

  BBNodeVec v(1, bb);
  updateTerm(n, v, support);
  bb = v[0];
}

void BitBlaster::updateTerm(const ASTNode& n,
                            BBNodeVec& bb,
                            BBNodeSet& support)
{

  if (cb == NULL)
    return;

  if (cb->isUnsatisfiable())
    return;

  if (n.isConstant())
  {
    return;
  }

  bool bbFixed = false;
  for (int i = 0; i < (int)bb.size(); i++)
  {
    if (bb[i] == BBTrue || bb[i] == BBFalse)
    {
      bbFixed = true;
      break;
    }
  }

  FixedBits* b = NULL;

  simplifier::constantBitP::NodeToFixedBitsMap::NodeToFixedBitsMapType::
      const_iterator it;
  if ((it = cb->fixedMap->map->find(n)) == cb->fixedMap->map->end())
  {
    if (bbFixed)
    {
      const unsigned int num_bits = n.GetValueWidth();
      b = new FixedBits(n.GetType() == BOOLEAN_TYPE ? 1 : num_bits,
                        n.GetType() == BOOLEAN_TYPE);
      cb->fixedMap->map->insert(std::pair<ASTNode, FixedBits*>(n, b));
      if (debug_bitblaster)
        cerr << "inserting" << n.GetNodeNum() << endl;
    }
    else
      return; // nothing to update.
  }
  else
    b = it->second;

  assert(b != NULL);
  FixedBits old(*b);

  bool changed = false;
  for (int i = 0; i < (int)bb.size(); i++)
    if (update(n, i, b, bb[i], support))
      changed = true; // don't break, we want to run update(..) on each bit.
  if (changed)
  {
    cb->scheduleNode(n);
    cb->scheduleUp(n);
    cb->propagate();
  }

  // If it's changed, the propagation may have caused new bits to be fixed.
  if (changed && !FixedBits::equals(*b, old))
  {
    updateTerm(n, bb, support);
    return;
  }

  // There may be a conflict between the AIGs and the constant bits (if the
  // problem is unsatisfiable).
  // So we can't ensure that if one is fixed to true (say), that the other
  // should be true also.

  if (!cb->isUnsatisfiable())
    for (int i = 0; i < (int)bb.size(); i++)
    {
      if (b->isFixed(i))
        assert(bb[i] == BBTrue || bb[i] == BBFalse);

      if (bb[i] == BBFalse || bb[i] == BBTrue)
        assert(b->isFixed(i));
    }
}

bool BitBlaster::isConstant(const BBNodeVec& v)
{
  for (unsigned i = 0; i < v.size(); i++)
  {
    if (v[i] != nf->getTrue() && v[i] != nf->getFalse())
      return false;
  }

  return true;
}

ASTNode BitBlaster::getConstant(const BBNodeVec& v,
                                const ASTNode& n)
{
  if (n.GetType() == BOOLEAN_TYPE)
  {
    if (v[0] == nf->getTrue())
      return ASTNF->getTrue();
    else
      return ASTNF->getFalse();
  }

  CBV bv = CONSTANTBV::BitVector_Create(v.size(), true);

  for (unsigned i = 0; i < v.size(); i++)
    if (v[i] == nf->getTrue())
      CONSTANTBV::BitVector_Bit_On(bv, i);

  const ASTNode result = ASTNF->CreateConstant(bv, v.size());

  // n may be a float carried as its packed bits (see isBitsValued). A plain
  // BVCONST cannot hold the format, so the constant that stands in for n has
  // to be re-made as an interned ASTFPConst -- otherwise the rebuilt parent
  // carries a bitvector where an fp is required and fails BVTypeCheck.
  const unsigned int exp_width = n.GetExpWidth();
  if (exp_width != 0)
    return FloatBlaster::withFormat(&ASTNF->getStpMgr(), result, exp_width,
                                    n.GetSigWidth());

  return result;
}

// This block checks if the bitblasting/fixed bits have discovered
// any new constants. If they've discovered a new constant, then
// the simplification function is called on a new term with the constant
// value replacing what used to be a variable child. For instance, if
// the term is ite(x,y,z), and we now know that x is true. Then we will
// call SimplifyTerm on ite(true,y,z), which will do the expected
// simplification.
// Then the term that we bitblast will by "y".
std::unordered_map<ASTNode, vector<BBNode>, ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual>::iterator
BitBlaster::simplify_during_bb(ASTNode& term,
                               BBNodeSet& support)
{
  const int numberOfChildren = term.Degree();
  vector<BBNodeVec> ch;
  ch.reserve(numberOfChildren);

  for (int i = 0; i < numberOfChildren; i++)
  {
    // isBitsValued, not GetType() == BITVECTOR_TYPE: a lowered formula still
    // carries float-typed leaves, which are bits here (see isBitsValued).
    // Testing the type directly is what made this function abort on every
    // query with a float symbol or constant left in it.
    if (isBitsValued(term[i]))
    {
      ch.push_back(BBTerm(term[i], support));
    }
    else if (term[i].GetType() == BOOLEAN_TYPE)
    {
      //Single-length bbnodevec to simulate 1-bit bitvector
      BBNodeVec t;
      t.push_back(BBForm(term[i], support));
      ch.push_back(t);
    }
    else
    {
      assert(false);
      exit(-1);
    }
  }

  bool newConst = false;
  for (int i = 0; i < numberOfChildren; i++)
  {
    if (term[i].isConstant())
      continue;

    if (isConstant(ch[i]))
    {
      // it's only interesting if the child isn't a constant,
      // but the bitblasted version is.
      newConst = true;
      break;
    }
  }

  // Something is now constant that didn't use to be.
  if (newConst)
  {
    ASTVec new_ch;
    new_ch.reserve(numberOfChildren);
    for (size_t i = 0; i < (size_t)numberOfChildren; i++)
    {
      if (!term[i].isConstant() && isConstant(ch[i]))
        new_ch.push_back(getConstant(ch[i], term[i]));
      else
        new_ch.push_back(term[i]);
    }

    ASTNode n_term = simp->SimplifyTerm(
        ASTNF->CreateTerm(term.GetKind(), term.GetValueWidth(), new_ch));
    assert(BVTypeCheck(n_term));
    // n_term is the potentially simplified version of term      return it;.

    if (cb != NULL)
    {
      // Add all the nodes to the worklist that have a constant as a child.
      cb->initWorkList(n_term);

      // The FixedBits are held by pointer rather than map iterator:
      // propagate() inserts into the map, which invalidates iterators,
      // while the pointed-to FixedBits are stable.
      auto it = cb->fixedMap->map->find(n_term);
      FixedBits* nBits;
      if (it == cb->fixedMap->map->end())
      {
        nBits = new FixedBits(std::max((unsigned)1, n_term.GetValueWidth()),
                              term.GetType() == BOOLEAN_TYPE);
        cb->fixedMap->map->insert(
            std::pair<ASTNode, FixedBits*>(n_term, nBits));
      }
      else
        nBits = it->second;

      // concreteToAbstract only models bit-vector and boolean constants;
      // a floating-point constant reaches its unhandled default and aborts.
      // Such a node keeps its default (all-unknown) FixedBits, which is sound.
      if (n_term.isConstant() &&
          (n_term.GetType() == BITVECTOR_TYPE ||
           n_term.GetType() == BOOLEAN_TYPE))
      {
        // It's assumed elsewhere that constants map to themselves in the
        // fixed map.
        // That doesn't happen here unless it's added explicitly.
        *nBits = FixedBits::concreteToAbstract(n_term);
      }

      FixedBits* termBits = nullptr;
      {
        const auto term_it = cb->fixedMap->map->find(term);
        if (term_it != cb->fixedMap->map->end())
          termBits = term_it->second;
      }

      if (termBits != nullptr)
      {
        // Copy over to the (potentially) new node. Everything we know about
        // the old node.
        nBits->mergeIn(*termBits);
      }

      cb->scheduleUp(n_term);
      cb->scheduleNode(n_term);
      cb->propagate();

      if (termBits != nullptr)
      {
        // Copy to the old node, all we know about the new node. This means
        // that
        // all the parents of the old node get the (potentially) updated
        // fixings.
        termBits->mergeIn(*nBits);
      }
      // Propagate through all the parents of term.
      cb->scheduleUp(term);
      cb->scheduleNode(term);
      cb->propagate();
      // Now we've propagated.
    }
    term = n_term;

    // check if we've already done the simplified one.
    auto it = BBTermMemo.find(term);
    if (it != BBTermMemo.end())
    {
      // Constant bit propagation may have updated something.
      updateTerm(term, it->second, support);
      return it;
    }
  }

  return BBTermMemo.end();
}

const BBNodeVec BitBlaster::BBTerm(const ASTNode& term, BBNodeSet& support)
{
  return BBTerm(term, support, false);
}

const BBNodeVec BitBlaster::BBTerm(const ASTNode& _term, BBNodeSet& support,
                                   const bool knownMissing)
{
  ASTNode term = _term; // mutable local copy.

  // Debug-only, and the whole of what holds primeMemos to the blaster: every
  // node reached from here is one the walk has to have offered, and every
  // operand the walk primed is one that has to be reached from here.
  PrimeAudit::Running running(memoAudit, term);

  auto it = BBTermMemo.end();
  if (!knownMissing)
  {
    it = BBTermMemo.find(term);
    if (it != BBTermMemo.end())
    {
      // Constant bit propagation may have updated something.
      updateTerm(term, it->second, support);
      return it->second;
    }
  }

  // Prime below this node once the recursion budget is spent -- and, while a
  // priming walk is in progress, on any memo miss that is not one of the
  // walk's own visits. The walk only covers nodes that existed when it ran:
  // simplify_during_bb can replace a term with a freshly simplified one whose
  // subtree nests with the input, and recursing into it mid-priming would put
  // that depth back on the stack with the budget switched off.
  if (!knownMissing && (priming != 0 || unprimedDepth >= unprimedDepthLimit))
  {
    ++priming;
    primeMemos(term, support);
    --priming;

    it = BBTermMemo.find(term);
    if (it != BBTermMemo.end())
    {
      updateTerm(term, it->second, support);
      return it->second;
    }
  }

  UnprimedDepth depth(unprimedDepth, priming == 0);

  if (uf != NULL && uf->optimize_flag && uf->simplify_during_BB_flag)
  {
    auto it = simplify_during_bb(term, support);
    if (it != BBTermMemo.end())
    {
      return it->second;
    }
  }

  BBNodeVec result;

  const Kind k = term.GetKind();
  if (!is_Term_kind(k))
    FatalError("BBTerm: Illegal kind to BBTerm", term);

  const auto kids_end = term.end();
  const unsigned int num_bits = term.GetValueWidth();


  switch (k)
  {
    case UF_APPLY:
      FatalError("BBTerm: UF_APPLY crossed the completed-root lowering "
                 "barrier",
                 term);
      break;

    case BVNOT:
    {
      // bitwise complement
      const BBNodeVec& bbkids = BBTerm(term[0], support);
      result = BBNeg(bbkids);
      break;
    }

    // fp.neg / fp.abs over a packed IEEE-754 operand: sign-bit edits (IEEE
    // 5.5.1 quiet operations -- no rounding, NaN payload kept), so the
    // operand's bits pass through with the top bit negated or cleared.
    // FloatBlast only leaves these under a surviving native predicate,
    // whose operands are packed views (comparisonLeaf).
    case FP_NEG:
    {
      BBNodeVec bits = BBTerm(term[0], support);
      bits[bits.size() - 1] = nf->CreateNode(NOT, bits[bits.size() - 1]);
      result = bits;
      break;
    }

    case FP_ABS:
    {
      BBNodeVec bits = BBTerm(term[0], support);
      bits[bits.size() - 1] = nf->getFalse();
      result = bits;
      break;
    }

    case BVRIGHTSHIFT:
    case BVSRSHIFT:
    case BVLEFTSHIFT:
    {
      // Barrel shifter
      const BBNodeVec& bbarg1 = BBTerm(term[0], support);
      const BBNodeVec& bbarg2 = BBTerm(term[1], support);

      // Signed right shift, need to copy the sign bit.
      BBNode toFill;
      if (BVSRSHIFT == k)
        toFill = bbarg1.back();
      else
        toFill = nf->getFalse();

      BBNodeVec temp_result(bbarg1);
      // if any bit is set in bbarg2 higher than log2Width, then we know that
      // the result is zero.
      // Add one to make allowance for rounding down. For example, given 300
      // bits, the log2 is about
      // 8.2 so round up to 9.

      const unsigned width = bbarg1.size();
      const unsigned log2Width = (unsigned)std::log2(width) + 1;

      if (k == BVSRSHIFT || k == BVRIGHTSHIFT)
        for (unsigned int i = 0; i < log2Width; i++)
        {
          if (bbarg2[i] == nf->getFalse())
            continue; // Not shifting by anything.

          unsigned int shift_amount = 1 << i;

          for (unsigned int j = 0; j < width; j++)
          {
            if (j + shift_amount >= width)
              temp_result[j] =
                  nf->CreateNode(ITE, bbarg2[i], toFill, temp_result[j]);
            else
              temp_result[j] =
                  nf->CreateNode(ITE, bbarg2[i], temp_result[j + shift_amount],
                                 temp_result[j]);
          }
        }
      else
        for (unsigned int i = 0; i < log2Width; i++)
        {
          if (bbarg2[i] == nf->getFalse())
            continue; // Not shifting by anything.

          int shift_amount = 1 << i;

          for (signed int j = width - 1; j >= 0; j--)
          {
            if (j < shift_amount)
              temp_result[j] =
                  nf->CreateNode(ITE, bbarg2[i], toFill, temp_result[j]);
            else
              temp_result[j] =
                  nf->CreateNode(ITE, bbarg2[i], temp_result[j - shift_amount],
                                 temp_result[j]);
          }
        }

      // If any of the remainder are true. Then the whole thing gets the fill
      // value.
      BBNode remainder = nf->getFalse();
      for (unsigned int i = log2Width; i < width; i++)
      {
        remainder = nf->CreateNode(OR, remainder, bbarg2[i]);
      }

      for (unsigned int i = 0; i < width; i++)
      {
        temp_result[i] = nf->CreateNode(ITE, remainder, toFill, temp_result[i]);
      }

      result = temp_result;
    }
    break;

    case ITE:
    {
      const BBNode& cond = BBForm(term[0], support);
      const BBNodeVec& thn = BBTerm(term[1], support);
      const BBNodeVec& els = BBTerm(term[2], support);

      if (num_bits >= uf->bv_abstraction_width)
        uf->coverage.bv_candidates[UserDefinedFlags::ABSTRACT_ITE]++;

      if (uf->bv_term_abstraction && uf->bv_term_abstraction_ite &&
          num_bits >= uf->bv_abstraction_width)
      {
        uf->coverage.bv_abstracted[UserDefinedFlags::ABSTRACT_ITE]++;
        ensureProxyCIs(nf, term[1], thn, sideConstraints_);
        ensureProxyCIs(nf, term[2], els, sideConstraints_);

        BBNodeVec abstracted(num_bits);
        for (unsigned i = 0; i < num_bits; i++)
        {
          abstracted[i] = BBNodeAIG(Aig_ObjCreateCi(nf->aigMgr));
          abstracted[i].symbol_index = nf->aigMgr->vCis->nSize - 1;
        }
        BBNodeAIG condCI(Aig_ObjCreateCi(nf->aigMgr));
        condCI.symbol_index = nf->aigMgr->vCis->nSize - 1;

        Aig_Obj_t* bicond = Aig_Not(orderedAigExor(
            nf->aigMgr, condCI.n, cond.n));
        sideConstraints_.push_back(BBNodeAIG(bicond));

        nf->symbolToBBNode[term] = abstracted;

        RawBVTermAbstraction raw;
        raw.termNode = term;
        raw.opKind = ITE;
        raw.operands[0] = term[0];
        raw.operands[1] = term[1];
        raw.operands[2] = term[2];
        raw.numOperands = 3;
        raw.width = num_bits;
        raw.condCISymbolIndex = condCI.symbol_index;
        abstractedTerms_.push_back(raw);
        result = abstracted;
      }
      else
      {
        result = BBITE(cond, thn, els);
      }
      break;
    }

    case BVSX:
    case BVZX:
    {
      // Replicate high-order bit as many times as necessary.
      // Arg 0 is expression to be sign extended.
      const ASTNode& arg = term[0];
      const unsigned result_width = term.GetValueWidth();
      const unsigned arg_width = arg.GetValueWidth();
      const BBNodeVec& bbarg = BBTerm(arg, support);

      if (result_width == arg_width)
      {
        // nothing to sign extend
        result = bbarg;
        break;
      }
      else
      {
        // we need to sign extend
        const BBNode& msb = (k == BVSX) ? bbarg.back() : BBFalse;

        BBNodeVec tmp_res(result_width);

        BBNodeVec::const_iterator bb_it = bbarg.begin();
        BBNodeVec::iterator res_it = tmp_res.begin();
        BBNodeVec::iterator res_ext =
            res_it + arg_width; // first bit of extended part
        BBNodeVec::iterator res_end = tmp_res.end();

        // copy LSBs directly from bbvec
        for (; res_it < res_ext; (res_it++, bb_it++))
        {
          *res_it = *bb_it;
        }
        // repeat MSB to fill up rest of result.
        for (; res_it < res_end; (res_it++))
        {
          *res_it = msb;
        }

        result = tmp_res;
        break;
      }
    }

    case BVEXTRACT:
    {
      // bitblast the child, then extract the relevant bits.
      // Note: This could be optimized by not bitblasting the bits
      // that aren't fetched.  But that would be tricky, especially
      // with memo-ization.

      const BBNodeVec& bbkids = BBTerm(term[0], support);
      const unsigned int high = term[1].GetUnsignedConst();
      const unsigned int low = term[2].GetUnsignedConst();

      BBNodeVec::const_iterator bbkfit = bbkids.begin();
      // I should have used pointers to BBNodeVec, to avoid this crock

      result = BBNodeVec(bbkfit + low, bbkfit + high + 1);
      break;
    }
    case BVCONCAT:
    {
      const BBNodeVec& vec1 = BBTerm(term[0], support);
      const BBNodeVec& vec2 = BBTerm(term[1], support);

      BBNodeVec tmp_res(vec2);
      tmp_res.insert(tmp_res.end(), vec1.begin(), vec1.end());
      result = tmp_res;
      break;
    }
    case BVPLUS:
    {
      assert(term.Degree() >= 1);

      // The abstraction below takes two operands, and Flatten folds every
      // chain of additions into one n-ary node, so an addition of three or
      // more operands would reach the exact adder however wide it is -- the
      // arity the front end happened to build would decide what gets
      // abstracted, rather than the width floor that is meant to. Lower it to
      // genuine two-operand nodes first, as BVMULT does, and only when the
      // abstraction would take them, so a query that is not being abstracted
      // keeps the n-ary adder it had. Addition is associative and commutative
      // modulo 2^n, so the tree computes the same value; the sort keeps the
      // shape it takes deterministic.
      if (uf->bv_term_abstraction && uf->bv_term_abstraction_plus &&
          uf->bvplus_variant &&
          term.Degree() > 2 && num_bits >= uf->bv_abstraction_width)
      {
        std::deque<ASTNode> names(term.begin(), term.end());
        std::sort(names.begin(), names.end(), stp::ExprLess{});
        while (names.size() > 1)
        {
          ASTNode a = names.front();
          names.pop_front();
          ASTNode b = names.front();
          names.pop_front();
          names.push_back(ASTNF->CreateTerm(BVPLUS, num_bits, a, b));
        }
        result = BBTerm(names.front(), support);
        break;
      }

      if (term.Degree() == 2 && num_bits >= uf->bv_abstraction_width)
        uf->coverage.bv_candidates[UserDefinedFlags::ABSTRACT_PLUS]++;

      // A wide n-ary addition that was not decomposed above -- because the
      // abstraction is off -- still offered it the Degree-1 binary adds the
      // decomposition would have made. Counting them keeps the candidate
      // number comparable between a run with the flag and a run without,
      // which is the whole use of it: a zero has to mean "no wide addition
      // here", not "the flag that lowers them was off".
      if (term.Degree() > 2 && num_bits >= uf->bv_abstraction_width &&
          !(uf->bv_term_abstraction && uf->bvplus_variant))
      {
        uf->coverage.bv_candidates[UserDefinedFlags::ABSTRACT_PLUS] +=
            term.Degree() - 1;
      }

      if (uf->bv_term_abstraction && uf->bv_term_abstraction_plus &&
          uf->bvplus_variant &&
          term.Degree() == 2 &&
          num_bits >= uf->bv_abstraction_width)
      {
        const BBNodeVec& left = BBTerm(term[0], support);
        const BBNodeVec& right = BBTerm(term[1], support);

        ASTNode realOp[2] = {term[0], term[1]};
        bool negated[2] = {false, false};
        const BBNodeVec* opVecs[2] = {&left, &right};

        for (int i = 0; i < 2; i++)
        {
          if (realOp[i].GetKind() == BVUMINUS &&
              realOp[i].Degree() == 1)
          {
            ASTNode inner = realOp[i][0];
            auto memo = BBTermMemo.find(inner);
            if (memo != BBTermMemo.end())
            {
              realOp[i] = inner;
              negated[i] = true;
              opVecs[i] = &memo->second;
            }
          }
        }

        if (!(negated[0] && negated[1]))
        {
          BBNodeVec abstracted(num_bits);
          for (unsigned i = 0; i < num_bits; i++)
          {
            abstracted[i] = BBNodeAIG(Aig_ObjCreateCi(nf->aigMgr));
            abstracted[i].symbol_index = nf->aigMgr->vCis->nSize - 1;
          }
          uf->coverage.bv_abstracted[UserDefinedFlags::ABSTRACT_PLUS]++;
          nf->symbolToBBNode[term] = abstracted;
          for (int i = 0; i < 2; i++)
            if (realOp[i].GetKind() != BVCONST)
              ensureProxyCIs(nf, realOp[i], *opVecs[i], sideConstraints_);
          RawBVTermAbstraction raw;
          raw.termNode = term;
          raw.opKind = BVPLUS;
          raw.operands[0] = realOp[0];
          raw.operands[1] = realOp[1];
          raw.operands[2] = ASTNode();
          raw.numOperands = 2;
          raw.width = num_bits;
          raw.operandNegated[0] = negated[0];
          raw.operandNegated[1] = negated[1];
          abstractedTerms_.push_back(raw);
          result = abstracted;
          break;
        }
      }

      if (uf->bvplus_variant)
      {
        // Add children pairwise and accumulate in BBsum

        auto it = term.begin();
        BBNodeVec tmp_res = BBTerm(*it, support);
        for (++it; it < kids_end; it++)
        {
          const BBNodeVec& tmp = BBTerm(*it, support);
          assert(tmp.size() == num_bits);
          BBPlus2(tmp_res, tmp, nf->getFalse());
        }

        result = tmp_res;
      }
      else
      {
        // Add all the children up using an addition network.
        vector<BBNodeVec> results;
        for (unsigned i = 0; i < term.Degree(); i++)
          results.push_back(BBTerm(term[i], support));

        const int bitWidth = term[0].GetValueWidth();
        vector<list<BBNode>> products(bitWidth + 1);
        for (int i = 0; i < bitWidth; i++)
        {
          for (unsigned j = 0; j < results.size(); j++)
            products[i].push_back(results[j][i]);
        }

        result = buildAdditionNetworkResult(products, support, term);
      }
      break;
    }
    case BVUMINUS:
    {
      const BBNodeVec& bbkid = BBTerm(term[0], support);
      result = BBUminus(bbkid);
      break;
    }
    case BVSUB:
    {
      // complement of subtrahend
      // copy, since BBSub writes into it.

      BBNodeVec tmp_res = BBTerm(term[0], support);

      const BBNodeVec& bbkid1 = BBTerm(term[1], support);
      BBSub(tmp_res, bbkid1, support);
      result = tmp_res;
      break;
    }
    case BVMULT:
    {
      assert(BVTypeCheck(term));

      if (term.Degree() > 2)
      {
        // BBMult and the multiplication variants read their operands' AST
        // nodes (constant detection, propagated-bit stats), so a wider
        // multiply is lowered to a tree of genuine two-operand nodes.
        std::deque<ASTNode> names(term.begin(), term.end());
        std::sort(names.begin(), names.end(), stp::ExprLess{});
        while (names.size() > 1)
        {
          ASTNode a = names.front();
          names.pop_front();
          ASTNode b = names.front();
          names.pop_front();
          names.push_back(ASTNF->CreateTerm(BVMULT, a.GetValueWidth(), a, b));
        }
        result = BBTerm(names.front(), support);
        break;
      }

      BBNodeVec mpcd1 = BBTerm(term[0], support);
      const BBNodeVec& mpcd2 = BBTerm(term[1], support);
      updateTerm(term[0], mpcd1, support);
      assert(mpcd1.size() == mpcd2.size());

      if (num_bits >= uf->bv_abstraction_width)
        uf->coverage.bv_candidates[UserDefinedFlags::ABSTRACT_MULT]++;

      if (uf->bv_term_abstraction && uf->bv_term_abstraction_mult &&
          num_bits >= uf->bv_abstraction_width)
      {
        uf->coverage.bv_abstracted[UserDefinedFlags::ABSTRACT_MULT]++;
        BBNodeVec op0 = ensureProxyCIs(nf, term[0], mpcd1, sideConstraints_);
        BBNodeVec op1 = ensureProxyCIs(nf, term[1], mpcd2, sideConstraints_);

        BBNodeVec abstracted(num_bits);
        for (unsigned i = 0; i < num_bits; i++)
        {
          abstracted[i] = BBNodeAIG(Aig_ObjCreateCi(nf->aigMgr));
          abstracted[i].symbol_index = nf->aigMgr->vCis->nSize - 1;
        }
        nf->symbolToBBNode[term] = abstracted;

        RawBVTermAbstraction raw;
        raw.termNode = term;
        raw.opKind = BVMULT;
        raw.operands[0] = term[0];
        raw.operands[1] = term[1];
        raw.numOperands = 2;
        raw.width = num_bits;
        abstractedTerms_.push_back(raw);
        result = abstracted;
      }
      else
      {
        result = BBExactBinaryOp(term, mpcd1, mpcd2, support);
      }
      break;
    }
    case SBVREM:
    case SBVMOD:
    case SBVDIV:
    {
      ASTNode p = TranslateSignedDivModRem(term, ASTNF);
      result = BBTerm(p, support);
      break;
    }

    case BVDIV:
    case BVMOD:
    {
      const BBNodeVec& dvdd = BBTerm(term[0], support);
      const BBNodeVec& dvsr = BBTerm(term[1], support);
      assert(dvdd.size() == num_bits);
      assert(dvsr.size() == num_bits);

      if (num_bits >= uf->bv_abstraction_width)
        uf->coverage.bv_candidates[UserDefinedFlags::ABSTRACT_DIVMOD]++;

      if (uf->bv_term_abstraction && uf->bv_term_abstraction_mult &&
          num_bits >= uf->bv_abstraction_width)
      {
        uf->coverage.bv_abstracted[UserDefinedFlags::ABSTRACT_DIVMOD]++;
        ensureProxyCIs(nf, term[0], dvdd, sideConstraints_);
        ensureProxyCIs(nf, term[1], dvsr, sideConstraints_);

        BBNodeVec abstracted(num_bits);
        for (unsigned i = 0; i < num_bits; i++)
        {
          abstracted[i] = BBNodeAIG(Aig_ObjCreateCi(nf->aigMgr));
          abstracted[i].symbol_index = nf->aigMgr->vCis->nSize - 1;
        }
        nf->symbolToBBNode[term] = abstracted;

        RawBVTermAbstraction raw;
        raw.termNode = term;
        raw.opKind = k;
        raw.operands[0] = term[0];
        raw.operands[1] = term[1];
        raw.numOperands = 2;
        raw.width = num_bits;
        abstractedTerms_.push_back(raw);
        result = abstracted;
      }
      else
      {
        result = BBExactBinaryOp(term, dvdd, dvsr, support);
      }
      break;
    }
    //  n-ary bitwise operators.
    case BVXOR:
    case BVXNOR:
    case BVAND:
    case BVOR:
    case BVNOR:
    case BVNAND:
    {
      // Add children pairwise and accumulate in BBsum
      auto it = term.begin();
      Kind bk = UNDEFINED; // Kind of individual bit op.
      switch (k)
      {
        case BVXOR:
          bk = XOR;
          break;
        case BVXNOR:
          bk = IFF;
          break;
        case BVAND:
          bk = AND;
          break;
        case BVOR:
          bk = OR;
          break;
        case BVNOR:
          bk = NOR;
          break;
        case BVNAND:
          bk = NAND;
          break;
        default:
          FatalError("BBTerm: Illegal kind to BBTerm", term);
          break;
      }

      // Sum is destructively modified in the loop, so make a copy of value
      // returned by BBTerm.
      BBNodeVec temp = BBTerm(*it, support);
      BBNodeVec sum(temp); // First operand.

      // Iterate over remaining bitvector term operands
      for (++it; it < kids_end; it++)
      {
        // FIXME FIXME FIXME: Why does using a temp. var change the behavior?
        temp = BBTerm(*it, support);
        const BBNodeVec& y = temp;

        assert(y.size() == num_bits);
        for (unsigned i = 0; i < num_bits; i++)
        {
          sum[i] = nf->CreateNode(bk, sum[i], y[i]);
        }
      }
      result = sum;
      break;
    }
    case SYMBOL:
    {
      assert(num_bits > 0);

      BBNodeVec bbvec;
      bbvec.reserve(num_bits);

      for (unsigned int i = 0; i < num_bits; i++)
      {
        BBNode bit_node = nf->CreateSymbol(term, i);
        bbvec.push_back(bit_node);
      }
      result = bbvec;
      break;
    }
    case BVCONST:
    {
      BBNodeVec tmp_res(num_bits);
      CBV bv = term.GetBVConst();
      for (unsigned int i = 0; i < num_bits; i++)
      {
        tmp_res[i] = CONSTANTBV::BitVector_bit_test(bv, i) ? nf->getTrue()
                                                           : nf->getFalse();
      }
      result = tmp_res;
      break;
    }
    // fp.mul and fp.add survive to the bit-blaster under
    // --bb.fp-native-arith, when FloatBlast left them beneath a surviving
    // native predicate over packed views (comparisonLeaf).
    case FP_MUL:
    {
      result = BBfpMul(term, support);
      break;
    }

    case FP_ADD:
    {
      result = BBfpAdd(term, support);
      break;
    }

    // Only the four-child float-to-float form survives (comparisonLeaf);
    // the reinterpret form resolves to the operand's own bits there.
    case FP_TOFP:
    {
      result = BBfpToFp(term, support);
      break;
    }

    case FP_SUB:
    case FP_DIV:
    case FP_FMA:
    case FP_SQRT:
    case FP_REM:
    case FP_ROUNDTOINTEGRAL:
    case FP_MIN:
    case FP_MAX:
    case FP_TOFP_SIGNED:
    case FP_TOFP_UNSIGNED:
    case FP_TO_UBV:
    case FP_TO_SBV:
    case FP_TO_IEEE_BV:
    {
      FatalError("BBForm: FP terms should not reach the bit-blaster: ", term);
      break;
    }
    default:
      FatalError("BBTerm: Illegal kind to BBTerm", term);
  }

  assert(result.size() == num_bits);

  if (debug_do_check)
    check(result, term);

  if (!uf->conjoin_to_top)
  {
    assert(support.size() == 0);
  }

  updateTerm(term, result, support);
  return (BBTermMemo[term] = result);
}

const BBNode BitBlaster::BBForm(const ASTNode& form)
{
  fpNativeAddIsZeroFusions = 0;

  if (uf->fp_native_domain &&
      (fpNativeDomainRoot.IsNull() || !(fpNativeDomainRoot == form)))
  {
    if (!fpNativeDomainRoot.IsNull())
    {
      BBTermMemo.clear();
      BBFormMemo.clear();
    }
    fpNativeDomainRoot = form;
    collectFpNativeDomainFacts(form);
  }

  if (uf->conjoin_to_top && cb != NULL)
  {
    ASTNodeMap n = cb->getAllFixed();
    for (ASTNodeMap::const_iterator it = n.begin(); it != n.end(); it++)
      fixedFromBottom.insert(it->first);

    // Mark the top node as true.
    cb->setNodeToTrue(form);
    cb->propagate();
  }

  BBNodeSet support;
  BBNode r = BBForm(form, support);

  vector<BBNode> v;
  v.insert(v.end(), support.begin(), support.end());
  v.push_back(r);

  if (!uf->conjoin_to_top)
  {
    assert(support.size() == 0);
  }

  if (cb != NULL && !cb->isUnsatisfiable())
  {
    ASTNodeSet visited;
    assert(cb->checkAtFixedPoint(form, visited));
  }
  if (uf->stats_flag && uf->fp_native_domain)
  {
    std::cerr << "FP native domain finite terms: "
              << fpNativeFiniteTerms.size() << '\n';
    std::cerr << "FP native domain cmp finite operands: "
              << fpNativeFiniteCmpOperands << '\n';
    std::cerr << "FP native domain eq finite operands: "
              << fpNativeFiniteEqOperands << '\n';
    std::cerr << "FP native domain classifications: "
              << fpNativeFiniteClassifications << '\n';
    std::cerr << "FP native domain arith finite operands: "
              << fpNativeFiniteArithOperands << '\n';
    std::cerr << "FP native domain finite round-packs: "
              << fpNativeFiniteRoundPacks << '\n';
    std::cerr << "FP native domain zero-magnitude facts: "
              << fpNativeZeroMagnitudeFacts.size() << '\n';
    std::cerr << "FP native domain zero-magnitude terms: "
              << fpNativeZeroMagnitudeTerms.size() << '\n';
    std::cerr << "FP native domain zero cmp operands: "
              << fpNativeZeroCmpOperands << '\n';
    std::cerr << "FP native domain zero eq operands: "
              << fpNativeZeroEqOperands << '\n';
    std::cerr << "FP native domain zero classifications: "
              << fpNativeZeroClassifications << '\n';
    std::cerr << "FP native domain isZero predicates: "
              << fpNativeIsZeroPredicates << '\n';
    std::cerr << "FP native domain isZero add predicates: "
              << fpNativeIsZeroAddPredicates << '\n';
    std::cerr << "FP native domain isZero add fused predicates: "
              << fpNativeIsZeroAddFusedPredicates << '\n';
    std::cerr << "FP native domain isZero add exclusive results: "
              << fpNativeIsZeroAddExclusiveResults << '\n';
    std::cerr << "FP native domain isZero add pre-memoized results: "
              << fpNativeIsZeroAddMemoizedResults << '\n';
    std::cerr << "FP native domain isZero add known-zero results: "
              << fpNativeIsZeroAddKnownZeroResults << '\n';
    std::cerr << "FP native domain isZero add both-finite operands: "
              << fpNativeIsZeroAddBothFiniteOperands << '\n';
    std::cerr << "FP native domain isZero add known-same-sign operands: "
              << fpNativeIsZeroAddKnownSameSignOperands << '\n';
    std::cerr << "FP native domain isZero add known-opposite-sign operands: "
              << fpNativeIsZeroAddKnownOppositeSignOperands << '\n';
    std::cerr << "FP native domain isZero add one-known-sign operand: "
              << fpNativeIsZeroAddOneKnownSignOperand << '\n';
    std::cerr << "FP native domain zero add fast-paths: "
              << fpNativeZeroAddFastPaths << '\n';
    std::cerr << "FP native domain zero mul fast-paths: "
              << fpNativeZeroMulFastPaths << '\n';
    std::cerr << "FP native domain zero to-fp fast-paths: "
              << fpNativeZeroToFpFastPaths << '\n';
    std::cerr << "FP native domain finite nonnegative terms: "
              << fpNativeFiniteNonnegativeTerms.size() << '\n';
    std::cerr << "FP native domain finite nonpositive terms: "
              << fpNativeFiniteNonpositiveTerms.size() << '\n';
    std::cerr << "FP native domain known-positive add paths: "
              << fpNativeKnownPositiveAddPaths << '\n';
    std::cerr << "FP native domain known-negative add paths: "
              << fpNativeKnownNegativeAddPaths << '\n';
    std::cerr << "FP native domain known-positive mul paths: "
              << fpNativeKnownPositiveMulPaths << '\n';
    std::cerr << "FP native domain known-negative mul paths: "
              << fpNativeKnownNegativeMulPaths << '\n';
  }
  if (uf->stats_flag && uf->fp_native_add_iszero)
    std::cerr << "FP native add-isZero fused predicates: "
              << fpNativeAddIsZeroFusions << '\n';

  if (v.size() == 1)
    return v[0];
  else
    return nf->CreateNode(AND, v);
}

// The operands of a node, in the order the blaster reaches them, where that
// is not left to right. Only the mirrored floating-point comparisons: to
// blast fp.lt(a,b) BBcompareFP treats it as fp.gt(b,a) and blasts b first.
// A walk that primed them left to right would build the same nodes in the
// other order, and the CNF with them.
static WalkOperands bbOperands(const ASTNode& n)
{
  const Kind k = n.GetKind();
  if (k != FP_LT && k != FP_LEQ)
    return WalkOperands::all(n);

  return WalkOperands::reversed(n);
}

// Blast everything below `n` before `n` itself, so that the calls the
// blaster makes on its operands all land on a memo and its recursion never
// goes more than one deep. BBForm reaches its operands by calling itself for
// the connectives; BBTerm reaches its own from 24 places across a 450-line
// switch. Neither is restated: filling their memos from the bottom is what
// makes them stack-safe.
//
// One walk over both memos rather than one each. The two sides reach each
// other freely -- an ITE's condition is a formula inside a term, an
// equality's operands are terms inside a formula -- so a walk that stopped
// at the type boundary and left the far side to "the other walk" only works
// if the other walk is running. It is not: it is guarded against re-entering
// while this one is in progress. That is how a term below a formula below a
// term used to go down the stack, and a walk that crosses the boundary
// itself has no such hole. See DeepDag_Test.cpp.
//
// It is sound because of what the blaster does not do. No arm of either
// function stops before an operand, so every node primed is one that would
// have been blasted anyway; the order is the order they would have been
// blasted in, operands first and each finished before the next starts. That
// is load-bearing -- the CNF must not depend on the order operands happen to
// be evaluated in, which is why BBForm blasts an ITE's arms into named
// variables -- and it is what `bbOperands` above exists for.
void BitBlaster::primeMemos(const ASTNode& n, BBNodeSet& support)
{
  primeMemo(
      n,
      [this](const ASTNode& node)
      {
        if (node.GetType() == BOOLEAN_TYPE)
        {
          // Ahead of the constant test below, because BBForm memoises TRUE
          // and FALSE: the walk hands them over rather than skipping them.
          if (BBFormMemo.find(node) != BBFormMemo.end())
            return Walk::Skip; // BBForm would take it from the memo.
          return node.Degree() == 0 ? Walk::Visit : Walk::Descend;
        }
        // A constant operand is skipped: the kinds that carry one --
        // BVEXTRACT's indices, BVSX's width -- never blast it, and blasting
        // it here would put a node in the memo the pass never asked for.
        if (node.isConstant())
          return Walk::Skip;
        if (BBTermMemo.find(node) != BBTermMemo.end())
          return Walk::Skip;
        return node.Degree() == 0 ? Walk::Visit : Walk::Descend;
      },
      bbOperands,
      [this, &support](const ASTNode& node, PrimeMemoReady)
      {
        if (node.GetType() == BOOLEAN_TYPE)
          BBForm(node, support, true);
        else
          BBTerm(node, support, true);
      });
}

// bit blast a formula (boolean term).  Result is one bit wide,
const BBNode BitBlaster::BBForm(const ASTNode& form, BBNodeSet& support)
{
  return BBForm(form, support, false);
}

const BBNode BitBlaster::BBForm(const ASTNode& form, BBNodeSet& support,
                                const bool knownMissing)
{
  // The other half of the audit above: the two memos are primed by one walk,
  // so the walk is held to both functions at once.
  PrimeAudit::Running running(memoAudit, form);

  auto it = BBFormMemo.end();
  if (!knownMissing)
  {
    it = BBFormMemo.find(form);
    if (it != BBFormMemo.end())
    {
      // already there.  Just return it.
      return it->second;
    }
  }

  // Same trigger as BBTerm's, and for the same reason: a node built during a
  // priming walk -- a rewritten condition under a term simplify_during_bb
  // replaced -- is not in the memo, and descending it mid-priming is
  // unbudgeted recursion that nests with the input.
  if (!knownMissing && (priming != 0 || unprimedDepth >= unprimedDepthLimit))
  {
    ++priming;
    primeMemos(form, support);
    --priming;

    it = BBFormMemo.find(form);
    if (it != BBFormMemo.end())
      return it->second;
  }

  UnprimedDepth depth(unprimedDepth, priming == 0);

  const Kind k = form.GetKind();
  if (!is_Form_kind(k))
  {
    FatalError("BBForm: Illegal kind: ", form);
  }

  //  Not returning until end, and memoizing everything, makes it easier
  // to trace coherently.

  // Various special cases
  BBNode result;
  switch (k)
  {

    case DISTINCT:
      FatalError("BBForm: DISTINCT crossed the completed-root lowering "
                 "barrier",
                 form);
      break;

    case UF_APPLY:
      FatalError("BBForm: UF_APPLY crossed the completed-root lowering "
                 "barrier",
                 form);
      break;

    case TRUE:
    {
      result = nf->getTrue();
      break;
    }

    case FALSE:
    {
      result = nf->getFalse();
      break;
    }

    case SYMBOL:
      assert(form.GetType() == BOOLEAN_TYPE);

      result = nf->CreateSymbol(form, 0); // 1 bit symbol.
      break;

    case BOOLEXTRACT:
    {
      // exactly two children
      const BBNodeVec bbchild = BBTerm(form[0], support);
      unsigned int index = form[1].GetUnsignedConst();
      result = bbchild[index];
      break;
    }

    case NOT:
      result = nf->CreateNode(NOT, BBForm(form[0], support));
      break;

    case ITE:
    {
      // The order that arguments to a function are evaluated in is
      // unspecified, so bit-blast each child into a named variable first.
      // Otherwise the nodes are created in a compiler-dependent order, and
      // the CNF that STP produces isn't the same across compilers.
      const BBNode cond = BBForm(form[0], support);
      const BBNode thn = BBForm(form[1], support);
      const BBNode els = BBForm(form[2], support);
      result = nf->CreateNode(ITE, cond, thn, els);
      break;
    }

    case AND:
    case OR:
    case NAND:
    case NOR:
    case IFF:
    case XOR:
    case IMPLIES:
    {
      BBNodeVec bbkids; // bit-blasted children (formulas)

      auto kids_end = form.end();
      for (auto it = form.begin(); it != kids_end; it++)
      {
        bbkids.push_back(BBForm(*it, support));
      }
      result = nf->CreateNode(k, bbkids);
      break;
    }

    case EQ:
    {
      const BBNodeVec left = BBTerm(form[0], support);
      const BBNodeVec right = BBTerm(form[1], support);
      assert(left.size() == right.size());

      if (left.size() >= uf->bv_abstraction_width)
        uf->coverage.bv_candidates[UserDefinedFlags::ABSTRACT_EQ]++;

      if (uf->bv_eq_abstraction &&
          left.size() >= uf->bv_abstraction_width)
      {
        uf->coverage.bv_abstracted[UserDefinedFlags::ABSTRACT_EQ]++;
        ensureProxyCIs(nf, form[0], left, sideConstraints_);
        ensureProxyCIs(nf, form[1], right, sideConstraints_);
        BBNodeAIG abstractCI(Aig_ObjCreateCi(nf->aigMgr));
        abstractCI.symbol_index = nf->aigMgr->vCis->nSize - 1;
        abstractedEQs_.push_back({form, abstractCI, form[0], form[1]});
        result = abstractCI;
      }
      else
      {
        result = BBEQ(left, right);
      }
      break;
    }

    case BVLE:
    case BVGE:
    case BVGT:
    case BVLT:
    case BVSLE:
    case BVSGE:
    case BVSGT:
    case BVSLT:
    {
      if (form[0].GetValueWidth() >= uf->bv_abstraction_width)
        uf->coverage.bv_candidates[UserDefinedFlags::ABSTRACT_COMPARE]++;

      if (uf->bv_term_abstraction && uf->bv_term_abstraction_compare)
      {
        const BBNodeVec& left = BBTerm(form[0], support);
        const BBNodeVec& right = BBTerm(form[1], support);
        if (left.size() >= uf->bv_abstraction_width)
        {
          uf->coverage.bv_abstracted[UserDefinedFlags::ABSTRACT_COMPARE]++;
          ensureProxyCIs(nf, form[0], left, sideConstraints_);
          ensureProxyCIs(nf, form[1], right, sideConstraints_);
          BBNodeAIG abstractCI(Aig_ObjCreateCi(nf->aigMgr));
          abstractCI.symbol_index = nf->aigMgr->vCis->nSize - 1;

          RawBVTermAbstraction raw;
          raw.termNode = form;
          raw.opKind = k;
          raw.operands[0] = form[0];
          raw.operands[1] = form[1];
          raw.numOperands = 2;
          raw.width = left.size();
          raw.condCISymbolIndex = abstractCI.symbol_index;
          abstractedTerms_.push_back(raw);
          result = abstractCI;
          break;
        }
      }
      result = BBcompare(form, support);
      break;
    }

    case BVUADDO:
    case BVSADDO:
    case BVUMULO:
    case BVSMULO:
    case BVUSUBO:
    case BVSSUBO:
    {
      result = BBOverflow(form, support);
      break;
    }
    case FP_GT:
    case FP_LT:
    case FP_GEQ:
    case FP_LEQ:
    {
      result = BBcompareFP(form, support);
      break;
    }

    case FP_EQ:
    case FP_SMT_EQ:
    {
      result = BBeqFP(form, support);
      break;
    }

    case FP_ISNORMAL:
    case FP_ISSUBNORMAL:
    case FP_ISZERO:
    case FP_ISINFINITE:
    case FP_ISNAN:
    case FP_ISNEGATIVE:
    case FP_ISPOSITIVE:
    {
      result = BBclassifyFP(form, support);
      break;
    }
    default:
      FatalError("BBForm: Illegal kind: ", form);
      break;
  }

  assert(!result.IsNull());

  if (debug_do_check)
    check(result, form);

  updateForm(form, result, support);

  if (!uf->conjoin_to_top)
  {
    assert(support.size() == 0);
  }

  return (BBFormMemo[form] = result);
}

// Bit blast a sum of two equal length BVs.
// Update sum vector destructively with new sum.
void BitBlaster::BBPlus2(BBNodeVec& sum,
                         const BBNodeVec& y, BBNode cin)
{

  const int bitWidth = sum.size();
  assert(y.size() == (unsigned)bitWidth);
  // Revision 320 avoided creating the nextcin, at I suspect unjustified cost.
  for (int i = 0; i < bitWidth; i++)
  {
    BBNode nextcin = Majority(sum[i], y[i], cin);
    sum[i] = nf->CreateNode(XOR, sum[i], y[i], cin);
    cin = nextcin;
  }
}

// Stores result - x in result, destructively
void BitBlaster::BBSub(BBNodeVec& result,
                       const BBNodeVec& y,
                       BBNodeSet& /*support*/)
{
  BBNodeVec compsubtrahend = BBNeg(y);
  BBPlus2(result, compsubtrahend, nf->getTrue());
}

// Add one bit
BBNodeVec BitBlaster::BBAddOneBit(const BBNodeVec& x,
                                  BBNode cin)
{
  BBNodeVec result;
  result.reserve(x.size());
  const BBNodeVec::const_iterator itend = x.end();
  for (BBNodeVec::const_iterator it = x.begin(); it < itend; it++)
  {
    BBNode nextcin = nf->CreateNode(AND, *it, cin);
    result.push_back(nf->CreateNode(XOR, *it, cin));
    cin = nextcin;
  }
  return result;
}

// Increment bit-blasted vector and return result.
BBNodeVec BitBlaster::BBInc(const BBNodeVec& x)
{
  return BBAddOneBit(x, nf->getTrue());
}

// Return formula for majority function of three bits.
// Pass arguments by reference to reduce refcounting.
BBNode BitBlaster::Majority(const BBNode& a,
                            const BBNode& b,
                            const BBNode& c)
{
  // Checking explicitly for constant a, b and c could
  // be more efficient, because they are repeated in the logic.
  if (nf->getTrue() == a)
  {
    return nf->CreateNode(OR, b, c);
  }
  else if (nf->getFalse() == a)
  {
    return nf->CreateNode(AND, b, c);
  }
  else if (nf->getTrue() == b)
  {
    return nf->CreateNode(OR, a, c);
  }
  else if (nf->getFalse() == b)
  {
    return nf->CreateNode(AND, a, c);
  }
  else if (nf->getTrue() == c)
  {
    return nf->CreateNode(OR, a, b);
  }
  else if (nf->getFalse() == c)
  {
    return nf->CreateNode(AND, a, b);
  }
  // there are lots more simplifications, but I'm not sure they're
  // worth doing explicitly (e.g., a = b, a = ~b, etc.)
  else
  {
    // Argument evaluation order is unspecified, so build each conjunction into
    // a named variable first. Otherwise the AIG nodes are created in a
    // compiler-dependent order, and the CNF isn't the same across compilers.
    const BBNode ab = nf->CreateNode(AND, a, b);
    const BBNode bc = nf->CreateNode(AND, b, c);
    const BBNode ac = nf->CreateNode(AND, a, c);
    return nf->CreateNode(OR, ab, bc, ac);
  }
}

// Bitwise complement
BBNodeVec BitBlaster::BBNeg(const BBNodeVec& x)
{
  BBNodeVec result;
  result.reserve(x.size());
  // Negate each bit.
  const BBNodeVec::const_iterator& xend = x.end();
  for (BBNodeVec::const_iterator it = x.begin(); it < xend; it++)
  {
    result.push_back(nf->CreateNode(NOT, *it));
  }
  return result;
}

// Compute unary minus
BBNodeVec BitBlaster::BBUminus(const BBNodeVec& x)
{
  BBNodeVec xneg = BBNeg(x);
  return BBInc(xneg);
}

// AND each bit of vector y with single bit b and return the result.
BBNodeVec BitBlaster::BBAndBit(const BBNodeVec& y,
                               BBNode b)
{
  if (nf->getTrue() == b)
  {
    return y;
  }

  BBNodeVec result;
  result.reserve(y.size());

  const BBNodeVec::const_iterator yend = y.end();
  for (BBNodeVec::const_iterator yit = y.begin(); yit < yend; yit++)
  {
    result.push_back(nf->CreateNode(AND, *yit, b));
  }
  return result;
}

typedef enum { SYMBOL_MT, ZERO_MT, ONE_MT, MINUS_ONE_MT } mult_type;

void printP(mult_type* m, int width)
{
  for (int i = width - 1; i >= 0; i--)
  {
    if (m[i] == SYMBOL_MT)
      cerr << "s";
    else if (m[i] == ZERO_MT)
      cerr << "0";
    else if (m[i] == ONE_MT)
      cerr << "1";
    else if (m[i] == MINUS_ONE_MT)
      cerr << "-1";
  }
}

void convert(const BBNodeVec& v, BBNodeManagerAIG* nf, mult_type* result)
{
  const BBNode& BBTrue = nf->getTrue();
  const BBNode& BBFalse = nf->getFalse();

  for (size_t i = 0; i < v.size(); i++)
  {
    if (v[i] == BBTrue)
      result[i] = ONE_MT;
    else if (v[i] == BBFalse)
      result[i] = ZERO_MT;
    else
      result[i] = SYMBOL_MT;
  }

  // find runs of ones.
  int lastOne = -1;
  for (size_t i = 0; i < v.size(); i++)
  {
    assert(result[i] != MINUS_ONE_MT);

    if (result[i] == ONE_MT && lastOne == -1)
      lastOne = i;

    if (result[i] != ONE_MT && lastOne != -1 && (i - lastOne >= 3))
    {
      result[lastOne] = MINUS_ONE_MT;
      for (int j = lastOne + 1; j < (int)i; j++)
        result[j] = ZERO_MT;
      // Should this be lastOne = i?
      lastOne = i;
      result[i] = ONE_MT;
    }
    else if (result[i] != ONE_MT)
      lastOne = -1;
  }

  // finished with a one.
  if (lastOne != -1 && (v.size() - lastOne > 1))
  {
    result[lastOne] = MINUS_ONE_MT;
    for (unsigned j = lastOne + 1; j < v.size(); j++)
      result[j] = ZERO_MT;
  }
}

// Cost of using v as the multiplier. mult_Booth emits one partial-product row
// per symbolic bit and one per non-zero digit left after recoding, but the two
// are not priced alike. A symbolic row is a fresh AND gate for every bit of the
// other operand; a constant row costs no gates at all, since AND with true is
// the bit itself and a negated bit is just a complemented AIG edge. What a
// constant row does cost is the column height it adds, which is what the
// addition network then has to reduce -- and reducing that count is exactly
// what recoding a run achieves.
//
// So "symbolic" is the figure that dominates, and "rows" only separates
// operands that tie on it. Constant zeros -- including the ones a zero-extend
// leaves behind, and the ones recoding creates inside a run -- cost nothing
// either way. "recoded" reports how many runs were rewritten into a
// subtract/add pair; zero means mult_Booth would leave the vector alone, so
// there is nothing to be gained by preferring it over mult_normal.
//
// This asks convert(), so it sees whatever the bit-blasted vector actually
// holds -- bits that constant bit propagation or simplification fixed count
// just as much as the bits of a BVCONST term.
int boothRows(const BBNodeVec& v, BBNodeManagerAIG* nf, int& recoded,
              int& symbolic)
{
  recoded = 0;
  symbolic = 0;
  if (v.size() == 0)
    return 0;

  mult_type* t = (mult_type*)alloca(sizeof(mult_type) * v.size());
  convert(v, nf, t);

  int rows = 0;
  for (size_t i = 0; i < v.size(); i++)
  {
    if (t[i] == MINUS_ONE_MT)
    {
      recoded++;
      rows++;
    }
    else if (t[i] == ONE_MT)
      rows++;
    else if (t[i] == SYMBOL_MT)
    {
      symbolic++;
      rows++;
    }
  }
  return rows;
}

// Multiply "multiplier" by y[start ... bitWidth].
void pushP(vector<vector<BBNode>>& products, const int start,
           const BBNodeVec& y, const BBNode& multiplier, BBNodeManagerAIG* nf)
{
  const int bitWidth = y.size();

  int c = 0;
  for (int i = start; i < bitWidth; i++)
  {
    BBNode n = nf->CreateNode(AND, y[c], multiplier);
    if (n != nf->getFalse())
      products[i].push_back(n);
    c++;
  }
}

const bool debug_multiply = false;

BBNodeVec BitBlaster::buildAdditionNetworkResult(
    vector<list<BBNode>>& products, BBNodeSet& support, const ASTNode& n)
{
  const int bitWidth = n.GetValueWidth();

  // If we have details of the partial products which can be true,
  int ignore = -1;
  simplifier::constantBitP::MultiplicationStats* ms = getMS(n, ignore);
  if (!uf->upper_multiplication_bound)
    ms = NULL;

  BBNodeVec results;
  for (int i = 0; i < bitWidth; i++)
  {

    buildAdditionNetworkResult(products[i], products[i + 1], support,
                               (i + 1 == bitWidth),
                               (ms != NULL && (ms->sumH[i] == 0)));

    assert(products[i].size() == 1);
    results.push_back(products[i].back());
  }

  assert(products[bitWidth].size() ==
         0); // products[bitwidth] is defined but should never be used.
  assert(results.size() == ((unsigned)bitWidth));
  return results;
}

// Use full adders to create an addition network that adds together each of the
// partial products. Puts the carries into the "to" list.

void BitBlaster::buildAdditionNetworkResult(
    list<BBNode>& from, list<BBNode>& to, BBNodeSet& support,
    const bool at_end, const bool all_false)
{

  while (from.size() >= 2)
  {
    BBNode c;

    if (from.size() == 2)
      c = nf->getFalse();
    else
    {
      c = from.back();
      from.pop_back();
    }

    const BBNode a = from.back();
    from.pop_back();
    const BBNode b = from.back();
    from.pop_back();

    // Nothing can be true. All must be false.
    if (uf->conjoin_to_top && all_false)
    {
      if (BBFalse != a)
        support.insert(nf->CreateNode(NOT, a));
      if (BBFalse != b)
        support.insert(nf->CreateNode(NOT, b));
      if (BBFalse != c)
        support.insert(nf->CreateNode(NOT, c));
      continue;
    }

    BBNode carry, sum;

    if (uf->adder_variant)
    {
      carry = Majority(a, b, c);
      sum = nf->CreateNode(XOR, a, b, c);
    }
    else
    {
      // As in Majority(), the conjunctions have to be built into named
      // variables so that the order they're created in doesn't depend on the
      // compiler's choice of argument evaluation order.
      const BBNode ab = nf->CreateNode(AND, a, b);
      const BBNode bc = nf->CreateNode(AND, b, c);
      const BBNode ac = nf->CreateNode(AND, a, c);
      carry = nf->CreateNode(OR, ab, bc, ac);
      sum = nf->CreateNode(XOR, nf->CreateNode(XOR, c, b), a);
    }

    if (debug_multiply)
    {
      cerr << "a" << a;
      cerr << "b" << b;
      cerr << "c" << c;
      cerr << "Carry" << carry;
      cerr << "Sum" << sum;
    }

    from.push_back(sum);

    if (!at_end && carry != BBFalse)
      to.push_back(carry);
  }
  if (0 == from.size())
    from.push_back(BBFalse);

  assert(1 == from.size());
}

const bool debug_bounds = false;

bool BitBlaster::statsFound(const ASTNode& n)
{
  if (NULL == cb)
    return false;

  if (NULL == cb->msm)
    return false;

  if (booth_recoded.find(n) !=
      booth_recoded.end()) // Sums are wrong for recoded.
    return false;

  simplifier::constantBitP::MultiplicationStatsMap::NodeToStats::const_iterator
      it;
  it = cb->msm->map.find(n);
  return (it != cb->msm->map.end());
}

// Make sure x and y are the parameters in the correct order. THIS ISNT
// COMMUTATIVE.
BBNodeVec BitBlaster::multWithBounds(
    const ASTNode& n, vector<list<BBNode>>& products, BBNodeSet& toConjoinToTop)
{
  const int bitWidth = n.GetValueWidth();

  int ignored = 0;
  assert(uf->upper_multiplication_bound);
  simplifier::constantBitP::MultiplicationStats& ms = *getMS(n, ignored);

  // If all of the partial products in the column must be zero, then replace
  for (int i = 0; i < bitWidth; i++)
  {
    if (uf->conjoin_to_top && ms.columnH[i] == 0)
    {
      while (products[i].size() > 0)
      {
        BBNode c = products[i].back(); // DONT take a reference of the back().
        products[i].pop_back();
        toConjoinToTop.insert(nf->CreateNode(NOT, c));
      }
      products[i].push_back(nf->getFalse());
    }
  }

  BBNodeVec result;

  if (debug_bounds)
  {
    ms.print();
  }

  vector<BBNode> prior;
  for (int i = 0; i < bitWidth; i++)
  {
    if (debug_bounds)
    {
      cerr << "  " << products[i].size();
      cerr << "[" << ms.columnL[i] << ":" << ms.columnH[i] << "][" << ms.sumL[i]
           << ":" << ms.sumH[i] << "]";
    }

    vector<BBNode> output;

    mult_BubbleSorterWithBounds(toConjoinToTop, products[i], output, prior,
                                ms.sumL[i], ms.sumH[i]);
    prior = output;

    assert(products[i].size() == 1);
    result.push_back(products[i].back());
  }

  if (debug_bitblaster)
    cerr << endl << endl;

  assert(result.size() == ((unsigned)bitWidth));
  return result;
}

void BitBlaster::mult_Booth(
    const BBNodeVec& x_i, const BBNodeVec& y_i, BBNodeSet& /*support*/,
    const ASTNode& xN, const ASTNode& yN, vector<list<BBNode>>& products,
    const ASTNode& n)
{
  const unsigned bitWidth = x_i.size();
  assert(x_i.size() == y_i.size());

  const BBNodeVec& x = x_i;
  const BBNodeVec& y = y_i;

  const BBNode& BBTrue = nf->getTrue();
  const BBNode& BBFalse = nf->getFalse();

  for (unsigned i = 0; i < bitWidth; i++)
  {
    assert(products[i].size() == 0);
  }

  BBNodeVec notY;
  for (unsigned i = 0; i < y.size(); i++)
  {
    notY.push_back(nf->CreateNode(NOT, y[i]));
  }

  mult_type* xt = (mult_type*)alloca(sizeof(mult_type) * x.size());
  convert(x, nf, xt);

  if (debug_multiply)
  {
    cerr << "--------" << endl;
    cerr << "x:";
    printP(xt, x.size());
    cerr << xN << endl;
  }

  mult_type* yt = (mult_type*)alloca(sizeof(mult_type) * x.size());
  convert(y, nf, yt);

  if (debug_multiply)
  {
    cerr << "y:";
    printP(yt, y.size());
    cerr << yN << endl;
  }

  // We store them into here before sorting them.
  vector<vector<BBNode>> t_products(bitWidth);

  for (unsigned i = 0; i < bitWidth; i++)
  {
    if (x[i] != BBTrue && x[i] != BBFalse)
    {
      pushP(t_products, i, y, x[i], nf);
    }

    // A bit can not be true or false, as well as one of these two.
    if (xt[i] == MINUS_ONE_MT)
    {
      pushP(t_products, i, notY, BBTrue, nf);
      t_products[i].push_back(BBTrue);
      booth_recoded.insert(n);
    }

    else if (xt[i] == ONE_MT)
    {
      pushP(t_products, i, y, BBTrue, nf);
    }

    if (t_products[i].size() == 0)
      t_products[i].push_back(BBFalse);

    sort(t_products[i].begin(), t_products[i].end());
    for (unsigned j = 0; j < t_products[i].size(); j++)
      products[i].push_back(t_products[i][j]);
  }
}

// Radix-4 modified Booth recoding.
//
// mult_Booth only rewrites runs of *constant* one bits, so a symbolic
// multiplier still costs one partial-product row per bit. This groups the
// multiplier into overlapping three-bit windows instead, halving the rows to
// ceil(width/2). Each window picks a digit in {-2,-1,0,1,2}:
//
//   b(2i+1) b(2i) b(2i-1)   digit         b(-1) reads as zero
//     0 0 0                   0
//     0 0 1 / 0 1 0          +1
//     0 1 1                  +2
//     1 0 0                  -2
//     1 0 1 / 1 1 0          -1
//     1 1 1                   0
//
// which is carried as three signals: neg = b(2i+1), one = b(2i) xor b(2i-1),
// and two = the pair of patterns that select twice y. Row bit j is then a
// select between y[j] and y[j-1], conditionally inverted, and the inversion is
// completed by adding neg itself into the row's lowest column -- the usual
// two's complement identity -y = ~y + 1, made conditional. The all-ones window
// falls out correctly: it selects nothing, inverts to all ones, and the added
// one carries it back to zero.
//
// The trade is that halving the rows has to pay for a costlier row: a naive row
// is one AND per bit, a radix-4 row is a select plus an XOR. Whether that is
// worthwhile in CNF rather than in silicon is a question for measurement.
//
// Truncation keeps the negative digits honest: BVMULT is same-width, so bits
// above the width are dropped and each row only needs to be right modulo
// 2^width.
void BitBlaster::mult_Booth_radix4(const BBNodeVec& x, const BBNodeVec& y,
                                   vector<list<BBNode>>& products,
                                   const ASTNode& n)
{
  const unsigned bitWidth = x.size();
  const BBNode& BBFalse = nf->getFalse();

  // The column bounds in MultiplicationStatsMap describe the un-recoded matrix
  // of AND terms. This matrix holds conditionally negated selects instead, so
  // those bounds do not apply to it -- mark the node so statsFound() keeps them
  // away, exactly as mult_Booth does once it has recoded a run.
  booth_recoded.insert(n);

  for (unsigned base = 0; base < bitWidth; base += 2)
  {
    const BBNode& below = (base == 0) ? BBFalse : x[base - 1];
    const BBNode& low = x[base];
    const BBNode& high = (base + 1 < bitWidth) ? x[base + 1] : BBFalse;

    const BBNode& neg = high;
    const BBNode one = nf->CreateNode(XOR, low, below);
    // twice y is selected by 011 and by 100, i.e. when low and below agree with
    // each other and disagree with high.
    // Sequenced deliberately; see the note in BBcompareFP.
    const BBNode lowAgrees = nf->CreateNode(NOT, nf->CreateNode(XOR, low, below));
    const BBNode highDiffers = nf->CreateNode(XOR, high, below);
    const BBNode two = nf->CreateNode(AND, lowAgrees, highDiffers);

    for (unsigned j = 0; base + j < bitWidth; j++)
    {
      const BBNode single = nf->CreateNode(AND, one, y[j]);
      const BBNode dbl =
          (j == 0) ? BBFalse : nf->CreateNode(AND, two, y[j - 1]);
      const BBNode selected = nf->CreateNode(OR, single, dbl);
      products[base + j].push_back(nf->CreateNode(XOR, selected, neg));
    }

    // The +1 that completes a negated row, and nothing when the digit is
    // positive.
    products[base].push_back(neg);
  }
}

void BitBlaster::mult_allPairs(
    const BBNodeVec& x, const BBNodeVec& y, BBNodeSet& /*support*/,
    vector<list<BBNode>>& products)
{
  // Make a table of partial products.
  const int bitWidth = x.size();
  assert(x.size() == y.size());
  assert(bitWidth > 0);

  for (int i = 0; i < bitWidth; i++)
  {
    assert(!x[i].IsNull());
    assert(!y[i].IsNull());
  }

  for (int i = 0; i < bitWidth; i++)
  {
    for (int j = 0; j <= i; j++)
    {
      BBNode n = nf->CreateNode(AND, x[i - j], y[j]);

      if (n != nf->getFalse())
        products[i].push_back(n);
    }

    if (0 == products[i].size())
      products[i].push_back(nf->getFalse());
  }
}

MultiplicationStats* BitBlaster::getMS(const ASTNode& n,
                                       int& highestZero)
{
  MultiplicationStats* ms = NULL;
  highestZero = -1;

  if (statsFound(n))
  {
    simplifier::constantBitP::MultiplicationStatsMap::NodeToStats::iterator it;
    it = cb->msm->map.find(n);
    if (it != cb->msm->map.end())
    {
      ms = &(it->second);

      assert(ms->x.getWidth() == ms->y.getWidth());
      assert(ms->r.getWidth() == ms->y.getWidth());
      assert(ms->r.getWidth() == ms->bitWidth);
    }

    for (unsigned i = 0; i < n.GetValueWidth(); i++)
      if (ms->sumH[i] == 0)
        highestZero = i;

    return ms;
  }

  return NULL;
}

// Each bit of 'x' is taken in turn and multiplied by a shifted y.
BBNodeVec BitBlaster::mult_normal(const BBNodeVec& x,
                                  const BBNodeVec& y,
                                  BBNodeSet& support,
                                  const ASTNode& n)
{
  const int bitWidth = n.GetValueWidth();

  // If we have details of the partial products which can be true,
  int highestZero = -1;
  const simplifier::constantBitP::MultiplicationStats* ms =
      getMS(n, highestZero);
  if (!uf->upper_multiplication_bound)
    ms = NULL;

  BBNodeVec ycopy(y);

  BBNodeVec prod = BBNodeVec(
      BBAndBit(y, *x.begin())); // start prod with first partial product.

  for (int i = 1; i < bitWidth; i++) // start loop at next bit.
  {
    const BBNode& xit = x[i];

    // shift first
    BBLShift(ycopy, 1);

    if (nf->getFalse() == xit)
    {
      // If this bit is zero, the partial product will
      // be zero.  No reason to add that in.
      continue;
    }

    BBNodeVec pprod = BBAndBit(ycopy, xit);

    // Iterate through from the current location upwards, setting anything to
    // zero that can be..
    if (ms != NULL && highestZero >= i && uf->conjoin_to_top)
    {
      for (int column = i; column <= highestZero; column++)
      {
        if (ms->sumH[column] == 0 && (nf->getFalse() != prod[column]))
        {
          support.insert(nf->CreateNode(NOT, prod[column]));
          prod[column] = BBFalse;
        }
      }
    }

    BBPlus2(prod, pprod, nf->getFalse());
  }
  
  return prod;
}

// assumes the prior column is sorted.
void BitBlaster::mult_BubbleSorterWithBounds(
    BBNodeSet& support, list<BBNode>& current, vector<BBNode>& currentSorted,
    vector<BBNode>& priorSorted, const int minTrue, const int maxTrue)
{

  // Add the carry from the prior column. i.e. each second sorted formula.
  for (unsigned k = 1; k < priorSorted.size(); k += 2)
  {
    current.push_back(priorSorted[k]);
  }

  const int height = current.size();

  // Set the current sorted to all false.
  currentSorted.clear();
  {
    vector<BBNode> temp(height, nf->getFalse());
    currentSorted = temp;
  }

  // n^2 sorting network.
  for (int l = 0; l < height; l++)
  {
    vector<BBNode> oldSorted(currentSorted);
    BBNode c = current.back();
    current.pop_back();
    currentSorted[0] = nf->CreateNode(OR, oldSorted[0], c);

    for (int j = 1; j <= l; j++)
    {
      currentSorted[j] = nf->CreateNode(
          OR, nf->CreateNode(AND, oldSorted[j - 1], c), oldSorted[j]);
    }
  }

  assert(current.size() == 0);

  for (int k = 0; k < height; k++)
    assert(!currentSorted[k].IsNull());

  if (uf->conjoin_to_top)
  {
    // minTrue/maxTrue are the bounds constant bit propagation recorded for this
    // node. They can ask for more true bits than the column has entries: the
    // formula reaching the bit-blaster may have been rewritten since the bounds
    // were taken, and nothing invalidates them when it is. Requiring more than
    // 'height' ones, or at most a negative number of them, is unsatisfiable.
    // Conjoining false settles the query, so the result bit is arbitrary - but
    // one still has to be produced, because the caller consumes exactly one.
    if (minTrue > height || maxTrue < 0)
    {
      support.insert(BBFalse);
      current.push_back(BBFalse);
      return;
    }

    for (int j = 0; j < minTrue; j++)
    {
      support.insert(currentSorted[j]);
      currentSorted[j] = BBTrue;
    }

    for (int j = height - 1; j >= maxTrue; j--)
    {
      support.insert(nf->CreateNode(NOT, currentSorted[j]));
      currentSorted[j] = BBFalse;
    }
  }

  BBNode resultNode = nf->getFalse();

  // Constrain to equal the result
  for (int k = 1; k < height; k += 2)
  {
    BBNode part = nf->CreateNode(AND, nf->CreateNode(NOT, currentSorted[k]),
                                 currentSorted[k - 1]);
    resultNode = nf->CreateNode(OR, resultNode, part);
  }

  // constraint the all '1's case.
  if (height % 2 == 1)
    resultNode = nf->CreateNode(OR, resultNode, currentSorted.at(height - 1));

  current.push_back(resultNode);
}

// If a bit has a fixed value, then it should equal BBTrue or BBFalse in the
// input vectors.
void BitBlaster::checkFixed(const BBNodeVec& v,
                            const ASTNode& n)
{
  if (cb == NULL)
  {
    return;
  }

  if (cb->isUnsatisfiable())
  {
    return;
  }

  if (cb->fixedMap->map->find(n) != cb->fixedMap->map->end())
  {
    FixedBits* b = cb->fixedMap->map->find(n)->second;
    for (unsigned i = 0; i < b->getWidth(); i++)
    {
      if (b->isFixed(i))
      {
        if (b->getValue(i))
        {
          assert(v[i] == BBTrue);
        }
        else
        {
          if (v[i] != BBFalse)
          {
            cerr << *b;
            cerr << i << endl;
            cerr << n;
            cerr << (v[i] == BBTrue) << endl;
          }

          assert(v[i] == BBFalse);
        }
      }
    }
  }
}

// If it's not booth encoded, and the column sum is zero,
// then set that all the partial products must be zero.
// For this to do anything constant bit propagation must be
// turned on, and upper_multiplication_bound must be set.
void BitBlaster::setColumnsToZero(
    vector<list<BBNode>>& products, BBNodeSet& support, const ASTNode& n)
{
  const int bitWidth = n.GetValueWidth();

  // If we have details of the partial products which can be true,
  int highestZero = -1;
  simplifier::constantBitP::MultiplicationStats* ms = getMS(n, highestZero);
  if (!uf->upper_multiplication_bound)
    ms = NULL;

  if (ms == NULL)
    return;

  for (int i = 0; i < bitWidth; i++)
  {
    if (ms->sumH[i] == 0)
    {
      while (products[i].size() > 0)
      {
        BBNode curr = products[i].back();
        products[i].pop_back();

        if (BBFalse == curr)
          continue;

        support.insert(nf->CreateNode(NOT, curr));
      }
      products[i].push_back(BBFalse);
    }
  }
}

// Fill the partial-product matrix by Booth recoding a constant multiplier,
// choosing whichever operand is the cheaper one to decompose.
//
// Only the operand mult_Booth decomposes into partial products is worth
// recoding: the other is added whole once per row, so its bit pattern does not
// change the row count, and its constant bits are folded inside each row by the
// AIG. The choice is therefore which operand to hand it first, and the cost
// that dominates is the number of symbolic rows -- each is a fresh AND gate per
// bit of the other operand, whereas a constant row costs no gates and only adds
// column height. Rows overall break a tie.
//
// The test is on the bit-blasted vectors rather than on BVCONST, because that
// is what convert() itself looks at: a run of ones that constant bit
// propagation established is worth just as much as one written down in the
// input. Testing the term instead would both miss those and route constants
// with no run of ones -- which encode the same either way -- down a path that
// only churns the encoding.
//
// Returns false, leaving products untouched, when neither operand recodes.
// That is the symbolic x symbolic case, and the caller picks the fallback.
bool BitBlaster::mult_Booth_constant(const BBNodeVec& x, const BBNodeVec& y,
                                     BBNodeSet& support,
                                     vector<list<BBNode>>& products,
                                     const ASTNode& n)
{
  int xRecoded = 0, yRecoded = 0, xSymbolic = 0, ySymbolic = 0;
  const int xRows = boothRows(x, nf, xRecoded, xSymbolic);
  const int yRows = boothRows(y, nf, yRecoded, ySymbolic);

  if (xRecoded == 0 && yRecoded == 0)
    return false;

  // BBMult swapped x to the constant side, so track which AST child each vector
  // now names -- xN/yN are used only for debug output, but keeping them
  // consistent costs nothing.
  const bool swapped =
      (BVCONST != n[0].GetKind()) && (BVCONST == n[1].GetKind());
  const ASTNode& xN = swapped ? n[1] : n[0];
  const ASTNode& yN = swapped ? n[0] : n[1];

  const bool useY = (yRecoded > 0) &&
                    (xRecoded == 0 || ySymbolic < xSymbolic ||
                     (ySymbolic == xSymbolic && yRows < xRows));

  if (useY)
    mult_Booth(y, x, support, yN, xN, products, n);
  else
    mult_Booth(x, y, support, xN, yN, products, n);

  // No setColumnsToZero() by the callers, unlike the other Booth variants. It
  // would do nothing: it reaches the constant-bit multiplication bounds through
  // statsFound(), which refuses any node mult_Booth has recoded -- the column
  // sums it holds describe the un-recoded matrix and are wrong once a run has
  // become a subtract/add pair. Those variants call mult_Booth
  // unconditionally, so for them the node is often not recoded and the call
  // still pays; this path is only taken when the multiplier did recode, so the
  // bounds are never available. The all-false argument of
  // buildAdditionNetworkResult() is unreachable for the same reason. Measured
  // over 1276 multiplies: the bounds were live 0 times.
  return true;
}

// Multiply two bitblasted numbers
// The exact circuit for BVMULT, BVDIV and BVMOD, which are the three the
// term abstraction can replace by free bits. Division and remainder share a
// blast, and division's zero divisor is totalised here rather than inside
// it: BBDivMod's restoring loop finds every shifted remainder at or above a
// zero divisor and hands the dividend back, which is what SMT-LIB asks of
// the remainder but not of the quotient.
BBNodeVec BitBlaster::BBExactBinaryOp(const ASTNode& term, const BBNodeVec& x,
                                      const BBNodeVec& y, BBNodeSet& support)
{
  const Kind k = term.GetKind();
  const unsigned width = term.GetValueWidth();
  assert(x.size() == width);
  assert(y.size() == width);

  if (k == BVMULT)
    return BBMult(x, y, support, term);

  assert(k == BVDIV || k == BVMOD);

  BBNodeVec q(width);
  BBNodeVec r(width);
  BBDivMod(x, y, q, r, width, support);

  if (k == BVMOD)
    return r;

  BBNodeVec zero(width, BBFalse);
  BBNodeVec max(width, BBTrue);
  return BBITE(BBEQ(zero, y), max, q);
}

BBNodeVec BitBlaster::BBMult(const BBNodeVec& _x,
                             const BBNodeVec& _y,
                             BBNodeSet& support,
                             const ASTNode& n)
{

  //  if (uf->isSet("print_on_mult", "0"))
  //   cerr << "--mult--";

  BBNodeVec x = _x;
  BBNodeVec y = _y;

  if ((BVCONST != n[0].GetKind()) && (BVCONST == n[1].GetKind()))
  {
    x = _y;
    y = _x;
  }

  const unsigned bitWidth = n.GetValueWidth();
  assert(x.size() == bitWidth);
  assert(y.size() == bitWidth);

  vector<list<BBNode>> products(bitWidth +
                                1); // Create one extra to avoid special cases.

  switch (uf->multiplication_variant)
  {
    case 1: 
    {
      return mult_normal(x, y, support, n);
      break;
    }
  // else if (multiplication_variant == "2")
  // V2 used to be V3 with normal rather than booth recoding.
  // To recreate V2, use V3 and turn off Booth recoding.

    case 3: 
    {
      mult_Booth(_x, _y, support, n[0], n[1], products, n);
      setColumnsToZero(products, support, n);
      return buildAdditionNetworkResult(products, support, n);
    }
  
    case 4:
    {
      mult_Booth(_x, _y, support, n[0], n[1], products, n);
      vector<BBNode> prior;

      for (unsigned i = 0; i < bitWidth; i++)
      {
        vector<BBNode> output;
        mult_BubbleSorterWithBounds(support, products[i], output, prior);
        prior = output;
        assert(products[i].size() == 1);
      }
      return buildAdditionNetworkResult(products, support, n);
    }

    case 5: 
    {
      if (!statsFound(n) || !uf->upper_multiplication_bound)
      {
        mult_Booth(_x, _y, support, n[0], n[1], products, n);
        setColumnsToZero(products, support, n);
        return buildAdditionNetworkResult(products, support, n);
      }

      mult_allPairs(x, y, support, products);
      setColumnsToZero(products, support, n);
      return multWithBounds(n, products, support);
    }
  
    case 6:
    {
      mult_Booth(_x, _y, support, n[0], n[1], products, n);
      setColumnsToZero(products, support, n);
      return v6(products, support, n);
    }

    case 7: 
    {
      mult_Booth(_x, _y, support, n[0], n[1], products, n);
      setColumnsToZero(products, support, n);
      return v7(products, support, n);
    }

    case 8:
    {
      mult_Booth(_x, _y, support, n[0], n[1], products, n);
      setColumnsToZero(products, support, n);
      return v8(products, support, n);
    }

    case 9:
    {
      mult_Booth(_x, _y, support, n[0], n[1], products, n);
      setColumnsToZero(products, support, n);
      return v9(products, support, n);
    }

    case 13:
    {
      mult_Booth(_x, _y, support, n[0], n[1], products, n);
      setColumnsToZero(products, support, n);
      return v13(products, support, n);
    }

    case 14:
    {
      // Variant 1, except that a multiplier holding a run of constant one bits
      // is Booth recoded.
      //
      // mult_normal walks the set bits of the multiplier and pays for one
      // ripple-carry adder per set bit, so a constant containing a run of ones
      // costs far more than it needs to: multiplying by 4095 builds twelve
      // adders where two suffice.  Booth recoding rewrites each run of ones
      // into a subtract/add pair, which is where nearly all of the encoding
      // cost of a constant multiply goes.
      //
      // Symbolic x symbolic keeps mult_normal: routing it through mult_Booth
      // would recode nothing and only change the summation strategy, which the
      // existing Booth variants already offer.
      if (mult_Booth_constant(x, y, support, products, n))
        return buildAdditionNetworkResult(products, support, n);
      return mult_normal(x, y, support, n);
    }

    case 15:
    {
      // Radix-4 modified Booth: half as many partial-product rows, at the cost
      // of a costlier row. Unlike the other Booth variants this recodes
      // symbolic multipliers too, so it applies to every multiply rather than
      // only to those with a constant operand.
      //
      // No setColumnsToZero() here: mult_Booth_radix4 marks the node recoded,
      // because the constant-bit column bounds describe the un-recoded matrix
      // of AND terms and would be wrong applied to conditionally negated
      // selects.
      mult_Booth_radix4(x, y, products, n);
      return buildAdditionNetworkResult(products, support, n);
    }

    case 16:
    {
      // 14 and 15 win on different multiplies: 14's radix-2 constant recoding
      // is the better encoding when the multiplier is constant, and 15's
      // radix-4 is the only one of the two that does anything at all when it is
      // symbolic. This picks between them per multiply rather than per query.
      if (!mult_Booth_constant(x, y, support, products, n))
        mult_Booth_radix4(x, y, products, n);
      return buildAdditionNetworkResult(products, support, n);
    }

    default:
    {
      cerr << "Unk variant" << uf->multiplication_variant;
      FatalError("sda44f");
    }
  }
}

// Takes an unsorted array, and returns a sorted array.
BBNodeVec BitBlaster::batcher(const vector<BBNode>& in)
{
  assert(in.size() != 0);

  if (in.size() == 1)
    return in;

  vector<BBNode> a;
  vector<BBNode> b;

  // half way rounded up.
  const unsigned halfWay = (((in.size() % 2) == 0 ? 0 : 1) + (in.size() / 2));
  for (unsigned i = 0; i < halfWay; i++)
    a.push_back(in[i]);

  for (unsigned i = halfWay; i < in.size(); i++)
    b.push_back(in[i]);

  assert(a.size() >= b.size());
  assert(a.size() + b.size() == in.size());
  vector<BBNode> result = mergeSorted(batcher(a), batcher(b));

  for (unsigned k = 0; k < result.size(); k++)
    assert(!result[k].IsNull());

  assert(result.size() == in.size());
  return result;
}

// assumes that the prior column is sorted.
void BitBlaster::sortingNetworkAdd(
    BBNodeSet& /*support*/, list<BBNode>& current, vector<BBNode>& currentSorted,
    vector<BBNode>& priorSorted)
{

  vector<BBNode> toSort;

  // convert the list to a vector.
  while (current.size() != 0)
  {
    BBNode currentN = current.front();
    assert(!currentN.IsNull());
    toSort.push_back(currentN);
    current.pop_front();
  }

  vector<BBNode> sorted = batcher(toSort);

  assert(sorted.size() == toSort.size());

  vector<BBNode> sortedCarryIn;
  for (unsigned k = 1; k < priorSorted.size(); k += 2)
  {
    sortedCarryIn.push_back(priorSorted[k]);
  }

  if (sorted.size() >= sortedCarryIn.size())
    currentSorted = mergeSorted(sorted, sortedCarryIn);
  else
    currentSorted = mergeSorted(sortedCarryIn, sorted);

  assert(currentSorted.size() == sortedCarryIn.size() + toSort.size());
  int height = currentSorted.size();

  assert(current.size() == 0);

  for (int k = 0; k < height; k++)
    assert(!currentSorted[k].IsNull());

  BBNode resultNode = nf->getFalse();

  // Constrain to equal the result
  for (int k = 1; k < height; k += 2)
  {
    BBNode part = nf->CreateNode(AND, nf->CreateNode(NOT, currentSorted[k]),
                                 currentSorted[k - 1]);
    resultNode = nf->CreateNode(OR, resultNode, part);
  }

  // constraint the all '1's case.
  if (height % 2 == 1)
    resultNode = nf->CreateNode(OR, resultNode, currentSorted.at(height - 1));

  current.push_back(resultNode);
}

BBNodeVec BitBlaster::v6(vector<list<BBNode>>& products,
                         BBNodeSet& support,
                         const ASTNode& n)
{
  const int bitWidth = n.GetValueWidth();

  vector<BBNode> prior;

  for (int i = 0; i < bitWidth; i++)
  {
    vector<BBNode> output;
    sortingNetworkAdd(support, products[i], output, prior);
    prior = output;
    assert(products[i].size() == 1);
  }

  // This converts the array of lists to a vector.
  return buildAdditionNetworkResult(products, support, n);
}

BBNodeVec
BitBlaster::v13(vector<list<BBNode>>& products,
                BBNodeSet& support, const ASTNode& n)
{
  const int bitWidth = n.GetValueWidth();

  int ignore = -1;
  simplifier::constantBitP::MultiplicationStats* ms = getMS(n, ignore);
  if (!uf->upper_multiplication_bound)
    ms = NULL;

  bool done = false;

  vector<BBNode> a(bitWidth);
  vector<BBNode> b(bitWidth);

  while (!done)
  {
    done = true;

    for (int i = 0; i < bitWidth; i++)
    {
      if (products[i].size() > 2)
        done = false;
      if (products[i].size() > 0)
      {
        a[i] = products[i].back();
        products[i].pop_back();
      }
      else
        a[i] = BBFalse;

      if (products[i].size() > 0)
      {
        b[i] = products[i].back();
        products[i].pop_back();
      }
      else
        b[i] = BBFalse;

      if (ms != NULL && ms->sumH[i] == 0)
      {
        if (a[i] != BBFalse)
        {
          support.insert(nf->CreateNode(NOT, a[i]));
          a[i] = BBFalse;
        }

        if (b[i] != BBFalse)
        {
          support.insert(nf->CreateNode(NOT, b[i]));
          b[i] = BBFalse;
        }
      }
      assert(!a[i].IsNull());
      assert(!b[i].IsNull());
    }
    BBPlus2(a, b, BBFalse);
    for (int i = 0; i < bitWidth; i++)
      products[i].push_back(a[i]);
  }

  BBNodeVec results;
  for (int i = 0; i < bitWidth; i++)
  {
    assert(products[i].size() == 1);
    results.push_back(products[i].back());
  }

  assert(results.size() == ((unsigned)bitWidth));
  return results;
}

// Sorting network that delivers carries directly to the correct column.
// For instance, if there are 6 true in a column, then a carry will flow to
// column+1, and column+2.
BBNodeVec BitBlaster::v9(vector<list<BBNode>>& products,
                         BBNodeSet& support,
                         const ASTNode& n)
{
  const unsigned bitWidth = n.GetValueWidth();

  vector<vector<BBNode>> toAdd(bitWidth);

  for (unsigned column = 0; column < bitWidth; column++)
  {
    vector<BBNode> sorted; // The current column (sorted) gets put into here.
    vector<BBNode> prior;  // Prior is always empty in this..

    [[maybe_unused]] const unsigned size = products[column].size();
    sortingNetworkAdd(support, products[column], sorted, prior);

    assert(products[column].size() == 1);
    assert(sorted.size() == size);

    for (unsigned k = 2; k <= sorted.size(); k++)
    {
      BBNode part;
      if (k == sorted.size())
        part = sorted[k - 1];
      else
      {
        // We expect the 1's to be sorted first.
        assert((sorted[k - 1] != BBFalse) || (sorted[k] != BBTrue));
        part =
            nf->CreateNode(AND, nf->CreateNode(NOT, sorted[k]), sorted[k - 1]);

        if (part == BBFalse)
          continue; // shortcut.
      }

      int position = k;
      int increment = 1;
      while (position != 0)
      {
        if (column + increment >= bitWidth)
          break;

        position >>= 1;
        if ((position & 1) != 0) // bit is set.
          toAdd[column + increment].push_back(part);

        increment++;
      }
    }

    for (unsigned carry_column = column + 1; carry_column < bitWidth;
         carry_column++)
    {
      if (toAdd[carry_column].size() == 0)
        continue;
      BBNode disjunct = BBFalse;
      for (unsigned l = 0; l < toAdd[carry_column].size(); l++)
      {
        disjunct = nf->CreateNode(OR, disjunct, toAdd[carry_column][l]);
      }

      if (disjunct != BBFalse)
        products[carry_column].push_back(disjunct);
      toAdd[carry_column].clear();
    }
  }
  for (unsigned i = 0; i < bitWidth; i++)
  {
    assert(toAdd[i].size() == 0);
  }

  // This converts the array of lists to a vector.
  return buildAdditionNetworkResult(products, support, n);
}

BBNodeVec BitBlaster::v7(vector<list<BBNode>>& products,
                         BBNodeSet& support,
                         const ASTNode& n)
{
  const int bitWidth = n.GetValueWidth();

  // If we have details of the partial products which can be true,
  int ignore = -1;
  simplifier::constantBitP::MultiplicationStats* ms = getMS(n, ignore);
  if (!uf->upper_multiplication_bound)
    ms = NULL;

  vector<list<BBNode>> later(bitWidth + 1);
  vector<list<BBNode>> next(bitWidth + 1);

  for (int i = 0; i < bitWidth; i++)
  {
    next[i + 1].clear();
    buildAdditionNetworkResult(products[i], next[i + 1], support,
                               bitWidth == i + 1,
                               (ms != NULL && (ms->sumH[i] == 0)));

    // Calculate the carries of carries.
    for (int j = i + 1; j < bitWidth; j++)
    {
      if (next[j].size() == 0)
        break;

      next[j + 1].clear();
      buildAdditionNetworkResult(next[j], next[j + 1], support,
                                 bitWidth == j + 1, false);
    }

    // Put the carries of the carries away until later.
    for (int j = i + 1; j < bitWidth; j++)
    {
      if (next[j].size() == 0)
        break;

      assert(next[j].size() <= 1);
      later[j].push_back(next[j].back());
    }
  }

  for (int i = 0; i < bitWidth; i++)
  {
    // Copy all the laters into products
    while (later[i].size() > 0)
    {
      products[i].push_front(later[i].front());
      later[i].pop_front();
    }
  }

  BBNodeVec results;
  for (int i = 0; i < bitWidth; i++)
  {

    buildAdditionNetworkResult((products[i]), (products[i + 1]), support,
                               bitWidth == i + 1, false);

    results.push_back(products[i].back());
    products[i].pop_back();
  }

  assert(results.size() == ((unsigned)bitWidth));
  return results;
}

BBNodeVec BitBlaster::v8(vector<list<BBNode>>& products,
                         BBNodeSet& support,
                         const ASTNode& n)
{
  const int bitWidth = n.GetValueWidth();

  // If we have details of the partial products which can be true,
  int ignore = -1;
  simplifier::constantBitP::MultiplicationStats* ms = getMS(n, ignore);
  if (!uf->upper_multiplication_bound)
    ms = NULL;

  vector<list<BBNode>> later(bitWidth + 1); // +1 then ignore the topmost.
  vector<list<BBNode>> next(bitWidth + 1);

  for (int i = 0; i < bitWidth; i++)
  {
    // Put all the products into next.
    next[i + 1].clear();
    buildAdditionNetworkResult((products[i]), (next[i + 1]), support,
                               i + 1 == bitWidth,
                               (ms != NULL && (ms->sumH[i] == 0)));

    // Calculate the carries of carries.
    for (int j = i + 1; j < bitWidth; j++)
    {
      if (next[j].size() == 0)
        break;

      next[j + 1].clear();
      buildAdditionNetworkResult(next[j], next[j + 1], support,
                                 j + 1 == bitWidth, false);
    }

    // Put the carries of the carries away until later.
    for (int j = i + 1; j < bitWidth; j++)
    {
      if (next[j].size() == 0)
        break;

      assert(next[j].size() <= 1);
      later[j].push_back(next[j].back());
    }
  }

  for (int i = 0; i < bitWidth; i++)
  {
    // Copy all the laters into products
    while (later[i].size() > 0)
    {
      products[i].push_back(later[i].back());
      later[i].pop_back();
    }
  }

  BBNodeVec results;
  for (int i = 0; i < bitWidth; i++)
  {
    buildAdditionNetworkResult(products[i], products[i + 1], support,
                               i + 1 == bitWidth, false);
    results.push_back(products[i].back());
    products[i].pop_back();
  }

  assert(results.size() == ((unsigned)bitWidth));
  return results;
}

// compare element 1 with 2, 3 with 4, and so on.
vector<BBNode>
BitBlaster::compareOddEven(const vector<BBNode>& in)
{
  vector<BBNode> result(in);

  for (unsigned i = 2; i < in.size(); i += 2)
  {
    BBNode a = in[i - 1];
    BBNode b = in[i];
    // comparators++;
    result[i - 1] = nf->CreateNode(OR, a, b);
    result[i] = nf->CreateNode(AND, a, b);
  }
  return result;
}

vector<BBNode>
BitBlaster::mergeSorted(const vector<BBNode>& in1,
                        const vector<BBNode>& in2)
{

  assert(in1.size() >= in2.size());
  assert(in1.size() > 0);

  vector<BBNode> result;

  if (in2.size() == 0)
  {
    result = in1;
  }
  else if (in1.size() == 1 && in2.size() == 1)
  {
    // comparators++;
    result.push_back(nf->CreateNode(OR, in1[0], in2[0]));
    result.push_back(nf->CreateNode(AND, in1[0], in2[0]));
  }
  else
  {
    vector<BBNode> evenL;
    vector<BBNode> oddL;
    for (unsigned i = 0; i < in1.size(); i++)
    {
      if (i % 2 == 0)
        evenL.push_back(in1[i]);
      else
        oddL.push_back(in1[i]);
    }

    vector<BBNode> evenR; // Take the even of each.
    vector<BBNode> oddR;  // Take the odd of each
    for (unsigned i = 0; i < in2.size(); i++)
    {
      if (i % 2 == 0)
        evenR.push_back(in2[i]);
      else
        oddR.push_back(in2[i]);
    }

    vector<BBNode> even = evenL.size() < evenR.size()
                              ? mergeSorted(evenR, evenL)
                              : mergeSorted(evenL, evenR);
    vector<BBNode> odd = oddL.size() < oddR.size() ? mergeSorted(oddR, oddL)
                                                   : mergeSorted(oddL, oddR);

    for (unsigned i = 0; i < std::max(even.size(), odd.size()); i++)
    {
      if (even.size() > i)
        result.push_back(even[i]);

      if (odd.size() > i)
        result.push_back(odd[i]);
    }
    result = compareOddEven(result);
  }

  assert(result.size() == in1.size() + in2.size());
  return result;
}

// This implements a variant of binary long division.
// q and r are "out" parameters.  rwidth puts a bound on the
// recursion depth.
void BitBlaster::BBDivMod(const BBNodeVec& y,
                          const BBNodeVec& x,
                          BBNodeVec& q, BBNodeVec& r,
                          unsigned int rwidth,
                          BBNodeSet& support)
{
  const unsigned int width = y.size();
  const BBNodeVec zero = BBfill(width, nf->getFalse());
  BBNodeVec one = zero;
  one[0] = nf->getTrue();

  // check if y is already zero.
  bool isZero = true;
  for (unsigned i = 0; i < rwidth; i++)
    if (y[i] != nf->getFalse())
    {
      isZero = false;
      break;
    }

  if (isZero || rwidth == 0)
  {
    // When we have shifted the entire width, y is guaranteed to be 0.
    q = zero;
    r = zero;
  }
  else
  {
    BBNodeVec q1, r1;
    BBNodeVec yrshift1(y);
    BBRShift(yrshift1, 1);

    // recursively divide y/2 by x.
    BBDivMod(yrshift1, x, q1, r1, rwidth - 1, support);

    BBNodeVec q1lshift1(q1);
    BBLShift(q1lshift1, 1);

    BBNodeVec r1lshift1(r1);
    BBLShift(r1lshift1, 1);

    BBNodeVec r1lshift1plusyodd(r1lshift1);
    r1lshift1plusyodd[0] = y[0];

    // By extending rminusx by one bit, we can use that top-bit
    // to check whether r>=x. We need to compute rminusx anyway,
    // so this saves having a separate compare circut.
    BBNodeVec rminusx(r1lshift1plusyodd);
    rminusx.push_back(nf->getFalse());
    BBNodeVec xCopy(x);
    xCopy.push_back(nf->getFalse());
    BBSub(rminusx, xCopy, support);
    BBNode sign = rminusx[width];
    rminusx.pop_back();

    // Adjusted q, r values when when r is too large.
    // q1lshift1 has zero in the least significant digit.
    // BBNodeVec ygtrxqval = BBITE(sign, q1lshift1, BBInc(q1lshift1));
    q1lshift1[0] = nf->CreateNode(NOT, sign);
    BBNodeVec ygtrxrval = BBITE(sign, r1lshift1plusyodd, rminusx);

    BBNodeVec notylessxqval;
    BBNodeVec notylessxrval;

    /* variant_1 removes the equality check of (x=y). When we get to here I
     think
     that r and q already have the proper values.
     Let x =y, so we are solving y/y.
     As a first step solve (y/2)/y.
     If y != 0, then y/2 < y. (strictly less than).
     By the last rule in this block, that will return q=0, r=(y/2)
     On return, that will be rightshifted, and the parity bit added back,
     giving q = 0, r=y.
     By the immediately preceeding rule, 0 <= 0 is true, so q becomes 1,
     and r becomes 0.
     So q and r are already set correctly when we get here.

     If y=0 & x=0, then (y/2)/0 will return q=0, r=0.
     By the preceeding rule  0 <= 0 is true, so q =1, r=0.
     So q and r are already set correctly when we get here.
     */

    if (uf->division_variant_1)
    {
      notylessxqval = q1lshift1;
      notylessxrval = ygtrxrval;
    }
    else
    {
      // q & r values when y >= x
      BBNode yeqx = BBEQ(y, x);
      // *** Problem: the bbfill for qval is wrong.  Should be 1, not -1.
      notylessxqval = BBITE(yeqx, one, q1lshift1);
      notylessxrval = BBITE(yeqx, zero, ygtrxrval);
    }

    /****************/
    BBNode ylessx;
    if (uf->division_variant_2)
    {
      ylessx = BBBVLE(y, x, false, true);
    }
    else
    {
      // y < x <=> not x >= y.
      ylessx = nf->CreateNode(NOT, BBBVLE(x, y, false));
    }

    if (uf->division_variant_3)
    {
      q = notylessxqval;
      r = notylessxrval;
    }
    else
    {
      // This variant often helps somehow. I don't know why.
      // Even though it uses more memory..
      q = BBITE(ylessx, zero, notylessxqval);
      r = BBITE(ylessx, y, notylessxrval);
    }
  }
}

// build ITE's (ITE cond then[i] else[i]) for each i.
BBNodeVec BitBlaster::BBITE(const BBNode& cond,
                            const BBNodeVec& thn,
                            const BBNodeVec& els)
{
  // Fast exits.
  if (cond == nf->getTrue())
  {
    return thn;
  }
  else if (cond == nf->getFalse())
  {
    return els;
  }

  BBNodeVec result;
  result.reserve(els.size());
  const BBNodeVec::const_iterator th_it_end = thn.end();
  BBNodeVec::const_iterator el_it = els.begin();
  for (BBNodeVec::const_iterator th_it = thn.begin();
       th_it < th_it_end; th_it++, el_it++)
  {
    result.push_back(nf->CreateNode(ITE, cond, *th_it, *el_it));
  }
  return result;
}

// Workhorse for comparison routines.  This does a signed BVLE if is_signed
// is true, else it's unsigned.  All other comparison operators can be reduced
// to this by swapping args or complementing the result bit.
BBNode BitBlaster::BBBVLE(const BBNodeVec& left,
                          const BBNodeVec& right,
                          bool is_signed, bool is_bvlt)
{
  if (uf->bbbvle_variant)
    return BBBVLE_variant1(left, right, is_signed, is_bvlt);
  else
    return BBBVLE_variant2(left, right, is_signed, is_bvlt);
}

BBNode BitBlaster::BBBVLE_variant1(
    const BBNodeVec& left_, const BBNodeVec& right_, bool is_signed,
    bool is_bvlt)
{
  const BBNodeVec& left = !is_bvlt ? left_ : right_;
  const BBNodeVec& right = !is_bvlt ? right_ : left_;

  // "thisbit" represents BVLE of the suffixes of the BVs
  // from that position .  if R < L, return TRUE, else if L < R
  // return FALSE, else return BVLE of lower-order bits.  MSB is
  // treated separately, because signed comparison is done by
  // complementing the MSB of each BV, then doing an unsigned
  // comparison.
  BBNodeVec::const_iterator lit = left.begin();
  BBNodeVec::const_iterator litend = left.end();
  BBNodeVec::const_iterator rit = right.begin();
  BBNode prevbit = nf->getTrue();
  for (; lit < litend - 1; lit++, rit++)
  {
    BBNode thisbit =
        nf->CreateNode(ITE, nf->CreateNode(IFF, *rit, *lit), prevbit, *rit);
    prevbit = thisbit;
  }

  // Handle MSB -- negate MSBs if signed comparison
  BBNode lmsb = *lit;
  BBNode rmsb = *rit;
  if (is_signed)
  {
    lmsb = nf->CreateNode(NOT, *lit);
    rmsb = nf->CreateNode(NOT, *rit);
  }

  BBNode msb =
      nf->CreateNode(ITE, nf->CreateNode(IFF, rmsb, lmsb), prevbit, rmsb);

  if (is_bvlt)
  {
    msb = nf->CreateNode(NOT, msb);
  }
  return msb;
}

BBNode BitBlaster::BBBVLE_variant2(
    const BBNodeVec& left, const BBNodeVec& right, bool is_signed, bool is_bvlt)
{
  BBNodeVec::const_reverse_iterator lit = left.rbegin();
  const BBNodeVec::const_reverse_iterator litend = left.rend();
  BBNodeVec::const_reverse_iterator rit = right.rbegin();

  BBNode this_compare_bit =
      is_signed ? nf->CreateNode(AND, *lit, nf->CreateNode(NOT, *rit))
                : nf->CreateNode(AND, nf->CreateNode(NOT, *lit), *rit);

  BBNodeVec bit_comparisons;
  bit_comparisons.reserve(left.size() + 1);

  bit_comparisons.push_back(this_compare_bit);

  //(lit IFF rit) is the same as (NOT(lit) XOR rit)
  BBNode prev_eq_bit = nf->CreateNode(XOR, nf->CreateNode(NOT, *lit), *rit);
  for (lit++, rit++; lit < litend; lit++, rit++)
  {
    this_compare_bit = nf->CreateNode(AND, nf->CreateNode(NOT, *lit), *rit);

    BBNode thisbit_output = nf->CreateNode(AND, this_compare_bit, prev_eq_bit);
    bit_comparisons.push_back(thisbit_output);

    BBNode this_eq_bit = nf->CreateNode(
        AND, nf->CreateNode(XOR, nf->CreateNode(NOT, *lit), *rit), prev_eq_bit);
    prev_eq_bit = this_eq_bit;
  }

  if (!is_bvlt)
  {
    bit_comparisons.push_back(prev_eq_bit);
  }

  // Either zero or one of the nodes in bit_comparisons can be true.

  BBNode output;
  output = nf->CreateNode(OR, bit_comparisons);
  return output;
}

// Left shift  within fixed field inserting zeros at LSB.
// Writes result into first argument.
void BitBlaster::BBLShift(BBNodeVec& x,
                          unsigned int shift)
{
  // left shift x (destructively) within width.
  // loop backwards so that copy to self works correctly. (DON'T use STL
  // insert!)
  for (int i = ((int)x.size()) - 1; i >= 0; i--)
  {
    if (i - (int)shift >= 0)
      x[i] = x[i - (int)shift];
    else
      x[i] = nf->getFalse(); // new LSB is zero.
  }
}

// Right shift within fixed field inserting zeros at MSB.
// Writes result into first argument.
void BitBlaster::BBRShift(BBNodeVec& x,
                          unsigned int shift)
{
  // right shift x (destructively) within width.
  const BBNodeVec::iterator xend = x.end();
  BBNodeVec::iterator xit = x.begin();
  for (; xit < xend; xit++)
  {
    if (xit + shift < xend)
      *xit = *(xit + shift);
    else
      *xit = nf->getFalse(); // new MSB is zero.
  }
}

// Return bit-blasted form for BVLE, BVGE, BVGT, SBLE, etc.
BBNode BitBlaster::BBcompare(const ASTNode& form,
                             BBNodeSet& support)
{
  const BBNodeVec& left = BBTerm(form[0], support);
  const BBNodeVec& right = BBTerm(form[1], support);

  const Kind k = form.GetKind();
  switch (k)
  {
    case BVLE:
    {
      return BBBVLE(left, right, false);
      break;
    }
    case BVGE:
    {
      return BBBVLE(right, left, false);
      break;
    }
    case BVGT:
    {
      return BBBVLE(right, left, false, true);
      break;
    }
    case BVLT:
    {
      return BBBVLE(left, right, false, true);
      break;
    }
    case BVSLE:
    {
      return BBBVLE(left, right, true);
      break;
    }
    case BVSGE:
    {
      return BBBVLE(right, left, true);
      break;
    }
    case BVSGT:
    {
      return nf->CreateNode(NOT, BBBVLE(left, right, true));
      break;
    }
    case BVSLT:
    {
      return nf->CreateNode(NOT, BBBVLE(right, left, true));
      break;
    }
    default:
      cerr << "BBCompare: Illegal kind" << form << endl;
      FatalError("", form);
  }
}

// A packed IEEE-754 operand is NaN iff its exponent field is all ones and
// its significand field is nonzero -- true of every NaN payload, so no
// canonical pattern is assumed. Bit i is bit i of the IEEE encoding:
// significand field in bits [0, sb-2], exponent field in bits [sb-1, w-2],
// sign at w-1.
BBNode BitBlaster::BBfpIsNaN(const BBNodeVec& p, unsigned sb, unsigned w)
{
  BBNodeVec expField(p.begin() + (sb - 1), p.begin() + (w - 1));
  BBNodeVec sigField(p.begin(), p.begin() + (sb - 1));
  const BBNode expAllOnes = nf->CreateNode(AND, expField);
  const BBNode sigNonZero = nf->CreateNode(OR, sigField);
  return nf->CreateNode(AND, expAllOnes, sigNonZero);
}

// Zero iff the whole magnitude (everything below the sign bit) is zero, so
// both +0 and -0 satisfy it.
BBNode BitBlaster::BBfpIsZero(const BBNodeVec& p, unsigned w)
{
  BBNodeVec magnitude(p.begin(), p.begin() + (w - 1));
  return nf->CreateNode(NOR, magnitude);
}

namespace
{
bool fpNativePackedFiniteBits(const std::string& bits, const unsigned eb)
{
  if (bits.size() <= eb)
    return false;
  for (unsigned i = 0; i < eb; ++i)
    if (bits[1 + i] != '1')
      return true;
  return false;
}

bool fpNativePackedZeroMagnitudeBits(const std::string& bits)
{
  if (bits.empty())
    return false;
  for (size_t i = 1; i < bits.size(); ++i)
    if (bits[i] != '0')
      return false;
  return true;
}

// Numeric ordering for finite packed IEEE values. The two signed zeros are
// equal; otherwise the magnitude order reverses on the negative side.
int fpNativePackedCompareBits(const std::string& a, const std::string& b)
{
  assert(a.size() == b.size() && !a.empty());
  if (fpNativePackedZeroMagnitudeBits(a) &&
      fpNativePackedZeroMagnitudeBits(b))
    return 0;
  if (a[0] != b[0])
    return a[0] == '1' ? -1 : 1;
  const int magnitude = a.substr(1).compare(b.substr(1));
  if (magnitude == 0)
    return 0;
  const int ordered = magnitude < 0 ? -1 : 1;
  return a[0] == '1' ? -ordered : ordered;
}

std::string fpNativePackedNegateBits(std::string bits)
{
  assert(!bits.empty());
  bits[0] = bits[0] == '1' ? '0' : '1';
  return bits;
}

std::string fpNativePackedAbsBits(std::string bits)
{
  assert(!bits.empty());
  bits[0] = '0';
  return bits;
}

bool fpNativePackedValueBits(const SourceSort& sort,
                             const std::string& bits, long double& out)
{
  if (sort.kind() != SourceSort::Kind::FloatingPoint)
    return false;
  const unsigned eb = sort.exponentWidth();
  const unsigned sb = sort.significandWidth();
  if (bits.size() != eb + sb || eb < 2 || sb < 2 || eb >= 31 ||
      sb > static_cast<unsigned>(std::numeric_limits<long double>::digits))
    return false;

  unsigned exponent = 0;
  for (unsigned i = 0; i < eb; ++i)
    exponent = (exponent << 1) |
               static_cast<unsigned>(bits[1 + i] == '1');
  if (exponent == (1u << eb) - 1)
    return false;

  long double significand = 0.0L;
  for (unsigned i = 0; i + 1 < sb; ++i)
    if (bits[1 + eb + i] == '1')
      significand +=
          std::ldexp(1.0L, static_cast<int>(sb - 2 - i));

  const int bias = static_cast<int>((1u << (eb - 1)) - 1);
  if (exponent == 0)
    out = std::ldexp(significand,
                     1 - bias - static_cast<int>(sb - 1));
  else
  {
    significand += std::ldexp(1.0L, static_cast<int>(sb - 1));
    out = std::ldexp(significand,
                     static_cast<int>(exponent) - bias -
                         static_cast<int>(sb - 1));
  }
  if (bits[0] == '1')
    out = -out;
  return std::isfinite(out) &&
         (out != 0.0L || (exponent == 0 && significand == 0.0L));
}

bool fpNativeFixedRoundingMode(const ASTNode& n, unsigned& mode)
{
  if (n.GetKind() != BVCONST || n.GetValueWidth() != 5)
    return false;
  mode = static_cast<unsigned>(n.GetUnsignedConst());
  switch (mode)
  {
    case symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN:
    case symbolic_fp::ROUND_NEAREST_TIES_TO_AWAY:
    case symbolic_fp::ROUND_TOWARD_POSITIVE:
    case symbolic_fp::ROUND_TOWARD_NEGATIVE:
    case symbolic_fp::ROUND_TOWARD_ZERO: return true;
    default: return false;
  }
}

bool fpNativeExactBinaryEndpoint(const SourceSort& sort, const Kind kind,
                                 const std::string& left,
                                 const std::string& right,
                                 const unsigned mode, std::string& result)
{
  PackedFpBinaryOp operation;
  switch (kind)
  {
    case FP_ADD: operation = PackedFpBinaryOp::Add; break;
    case FP_SUB: operation = PackedFpBinaryOp::Subtract; break;
    case FP_MUL: operation = PackedFpBinaryOp::Multiply; break;
    default: return false;
  }

  std::string error;
  if (!packedFPBinaryOp(left, right, sort.exponentWidth(),
                        sort.significandWidth(), mode, operation, result,
                        error))
    return false;
  return fpNativePackedFiniteBits(result, sort.exponentWidth());
}

} // namespace

bool BitBlaster::fpNativeConstantZeroMagnitude(const ASTNode& n) const
{
  const SourceSort sort = n.GetSourceSort();
  if (n.GetKind() != BVCONST ||
      sort.kind() != SourceSort::Kind::FloatingPoint)
    return false;

  const unsigned w = sort.packedWidth();
  if (w < 2 || n.GetValueWidth() != w)
    return false;

  for (unsigned i = 0; i + 1 < w; ++i)
    if (CONSTANTBV::BitVector_bit_test(n.GetBVConst(), i))
      return false;
  return true;
}

bool BitBlaster::fpNativeConstantFinite(const ASTNode& n) const
{
  long double ignored = 0.0L;
  return fpNativeConstantValue(n, ignored);
}

bool BitBlaster::fpNativeConstantValue(const ASTNode& n,
                                       long double& out) const
{
  const SourceSort sort = n.GetSourceSort();
  if (n.GetKind() != BVCONST ||
      sort.kind() != SourceSort::Kind::FloatingPoint)
    return false;

  const unsigned sb = sort.significandWidth();
  const unsigned w = sort.packedWidth();
  const unsigned eb = sort.exponentWidth();
  if (sb < 2 || w <= sb || eb >= 31 ||
      sb > static_cast<unsigned>(std::numeric_limits<long double>::digits))
    return false;

  CBV bv = n.GetBVConst();
  bool expAllOnes = true;
  for (unsigned i = sb - 1; i < w - 1; i++)
    expAllOnes &= CONSTANTBV::BitVector_bit_test(bv, i);
  if (expAllOnes)
    return false;

  const bool negative = CONSTANTBV::BitVector_bit_test(bv, w - 1);
  unsigned exponent = 0;
  for (unsigned i = 0; i < eb; i++)
    if (CONSTANTBV::BitVector_bit_test(bv, sb - 1 + i))
      exponent |= 1u << i;

  long double significand = 0.0L;
  for (unsigned i = 0; i + 1 < sb; i++)
    if (CONSTANTBV::BitVector_bit_test(bv, i))
      significand += std::ldexp(1.0L, static_cast<int>(i));

  const int bias = static_cast<int>((1u << (eb - 1)) - 1);
  if (exponent == 0)
  {
    out = std::ldexp(significand,
                     static_cast<int>(1 - bias - (sb - 1)));
  }
  else
  {
    significand += std::ldexp(1.0L, static_cast<int>(sb - 1));
    out = std::ldexp(significand,
                     static_cast<int>(exponent) - bias -
                         static_cast<int>(sb - 1));
  }
  if (negative)
    out = -out;
  // Reject a target nonzero that lies outside the host exponent range. In
  // particular, decoding a negative tiny value as host -0 must never turn a
  // negative lower bound into a semantic nonnegativity proof.
  return std::isfinite(out) &&
         (out != 0.0L || (exponent == 0 && significand == 0.0L));
}

bool BitBlaster::fpNativeConstantBits(const ASTNode& n,
                                     std::string& out) const
{
  const SourceSort sort = n.GetSourceSort();
  if (n.GetKind() != BVCONST ||
      sort.kind() != SourceSort::Kind::FloatingPoint ||
      n.GetValueWidth() != sort.packedWidth())
    return false;

  const unsigned width = n.GetValueWidth();
  out.resize(width);
  for (unsigned i = 0; i < width; ++i)
    out[width - 1 - i] =
        CONSTANTBV::BitVector_bit_test(n.GetBVConst(), i) ? '1' : '0';
  return true;
}

bool BitBlaster::fpNativeMaxFiniteValue(const SourceSort& sort,
                                        long double& out) const
{
  if (sort.kind() != SourceSort::Kind::FloatingPoint)
    return false;

  const unsigned eb = sort.exponentWidth();
  const unsigned sb = sort.significandWidth();
  if (eb < 2 || sb < 2 || eb >= 31 || sb > 113)
    return false;

  const int bias = static_cast<int>((1u << (eb - 1)) - 1);
  const int maxExp = static_cast<int>((1u << eb) - 2) - bias;
  const long double sig =
      2.0L - std::ldexp(1.0L, -static_cast<int>(sb - 1));
  out = std::ldexp(sig, maxExp);
  return std::isfinite(out);
}

BitBlaster::FpNativeInterval BitBlaster::fpNativeRoundedRange(
    const SourceSort& sort, const long double lower,
    const long double upper) const
{
  FpNativeInterval out;
  if (!std::isfinite(lower) || !std::isfinite(upper))
    return out;

  long double maxFinite = 0.0L;
  if (!fpNativeMaxFiniteValue(sort, maxFinite))
    return out;

  if (lower < -maxFinite || upper > maxFinite)
    return out;

  const unsigned eb = sort.exponentWidth();
  const unsigned sb = sort.significandWidth();
  const int bias = static_cast<int>((1u << (eb - 1)) - 1);
  const int maxExp = static_cast<int>((1u << eb) - 2) - bias;
  const long double maxUlp =
      std::ldexp(1.0L, maxExp - static_cast<int>(sb - 1));
  const long double lo = std::max(-maxFinite, lower - maxUlp);
  const long double hi = std::min(maxFinite, upper + maxUlp);

  out.known = true;
  out.lower = lo;
  out.upper = hi;
  return out;
}

BitBlaster::FpNativeInterval BitBlaster::fpNativeExactRoundedRange(
    const SourceSort& sort, const Kind kind, const ASTNode& roundingMode,
    const FpNativeInterval& a, const FpNativeInterval& b) const
{
  FpNativeInterval out;
  if (!a.exact || !b.exact)
    return out;

  unsigned fixedMode = 0;
  const bool fixed = fpNativeFixedRoundingMode(roundingMode, fixedMode);
  const unsigned lowerMode =
      fixed ? fixedMode
            : static_cast<unsigned>(symbolic_fp::ROUND_TOWARD_NEGATIVE);
  const unsigned upperMode =
      fixed ? fixedMode
            : static_cast<unsigned>(symbolic_fp::ROUND_TOWARD_POSITIVE);

  using EndpointPair = std::pair<std::string, std::string>;
  std::vector<EndpointPair> lowerInputs;
  std::vector<EndpointPair> upperInputs;
  if (kind == FP_ADD)
  {
    lowerInputs.emplace_back(a.lowerBits, b.lowerBits);
    upperInputs.emplace_back(a.upperBits, b.upperBits);
  }
  else if (kind == FP_SUB)
  {
    lowerInputs.emplace_back(a.lowerBits, b.upperBits);
    upperInputs.emplace_back(a.upperBits, b.lowerBits);
  }
  else if (kind == FP_MUL)
  {
    const std::string as[2] = {a.lowerBits, a.upperBits};
    const std::string bs[2] = {b.lowerBits, b.upperBits};
    for (const std::string& av : as)
      for (const std::string& bv : bs)
      {
        lowerInputs.emplace_back(av, bv);
        upperInputs.emplace_back(av, bv);
      }
  }
  else
    return out;

  std::string lower;
  for (const EndpointPair& input : lowerInputs)
  {
    std::string value;
    if (!fpNativeExactBinaryEndpoint(sort, kind, input.first, input.second,
                                     lowerMode, value))
      return out;
    if (lower.empty() || fpNativePackedCompareBits(value, lower) < 0)
      lower = value;
  }

  std::string upper;
  for (const EndpointPair& input : upperInputs)
  {
    std::string value;
    if (!fpNativeExactBinaryEndpoint(sort, kind, input.first, input.second,
                                     upperMode, value))
      return out;
    if (upper.empty() || fpNativePackedCompareBits(value, upper) > 0)
      upper = value;
  }

  long double lo = 0.0L;
  long double hi = 0.0L;
  if (lower.empty() || upper.empty() ||
      fpNativePackedCompareBits(lower, upper) > 0 ||
      !fpNativePackedValueBits(sort, lower, lo) ||
      !fpNativePackedValueBits(sort, upper, hi))
    return out;

  out.known = true;
  out.exact = true;
  out.lower = lo;
  out.upper = hi;
  out.lowerBits = lower;
  out.upperBits = upper;
  return out;
}

BitBlaster::FpNativeInterval BitBlaster::fpNativeInterval(const ASTNode& n)
{
  const auto cached = fpNativeIntervals.find(n);
  if (cached != fpNativeIntervals.end())
    return cached->second;

  FpNativeInterval out = fpNativeIntervalUncached(n);
  fpNativeIntervals.emplace(n, out);
  return out;
}

BitBlaster::FpNativeInterval BitBlaster::fpNativeIntervalUncached(
    const ASTNode& n)
{
  FpNativeInterval out;
  if (!uf->fp_native_domain)
    return out;

  const SourceSort sort = n.GetSourceSort();
  if (sort.kind() != SourceSort::Kind::FloatingPoint)
    return out;

  long double value = 0.0L;
  if (fpNativeConstantValue(n, value))
  {
    out.known = true;
    out.lower = value;
    out.upper = value;
    out.exact = fpNativeConstantBits(n, out.lowerBits);
    if (out.exact)
      out.upperBits = out.lowerBits;
    return out;
  }

  if (fpNativeKnownZeroMagnitude(n))
  {
    out.known = true;
    out.exact = true;
    out.lower = 0.0L;
    out.upper = 0.0L;
    out.lowerBits.assign(sort.packedWidth(), '0');
    out.upperBits = out.lowerBits;
    return out;
  }

  if (n.GetKind() == SYMBOL)
  {
    const auto it = fpNativeBounds.find(n);
    if (it != fpNativeBounds.end() && it->second.hasLower &&
        it->second.hasUpper && it->second.lower <= it->second.upper)
    {
      out.known = true;
      out.lower = it->second.lower;
      out.upper = it->second.upper;
      if (it->second.lowerExact && it->second.upperExact &&
          fpNativePackedCompareBits(it->second.lowerBits,
                                    it->second.upperBits) <= 0)
      {
        out.exact = true;
        out.lowerBits = it->second.lowerBits;
        out.upperBits = it->second.upperBits;
      }
    }
    return out;
  }

  switch (n.GetKind())
  {
    case FP_NEG:
    {
      const FpNativeInterval x = fpNativeInterval(n[0]);
      if (!x.known)
        return out;
      out.known = true;
      out.lower = -x.upper;
      out.upper = -x.lower;
      if (x.exact)
      {
        out.exact = true;
        out.lowerBits = fpNativePackedNegateBits(x.upperBits);
        out.upperBits = fpNativePackedNegateBits(x.lowerBits);
      }
      return out;
    }

    case FP_ABS:
    {
      const FpNativeInterval x = fpNativeInterval(n[0]);
      if (!x.known)
        return out;
      out.known = true;
      if (x.lower >= 0.0L)
      {
        out.lower = x.lower;
        out.upper = x.upper;
        if (x.exact)
        {
          out.exact = true;
          out.lowerBits = fpNativePackedAbsBits(x.lowerBits);
          out.upperBits = fpNativePackedAbsBits(x.upperBits);
        }
      }
      else if (x.upper <= 0.0L)
      {
        out.lower = -x.upper;
        out.upper = -x.lower;
        if (x.exact)
        {
          out.exact = true;
          out.lowerBits = fpNativePackedAbsBits(x.upperBits);
          out.upperBits = fpNativePackedAbsBits(x.lowerBits);
        }
      }
      else
      {
        out.lower = 0.0L;
        out.upper = std::max(-x.lower, x.upper);
        if (x.exact)
        {
          out.exact = true;
          out.lowerBits.assign(sort.packedWidth(), '0');
          const std::string negativeMagnitude =
              fpNativePackedAbsBits(x.lowerBits);
          const std::string positiveMagnitude =
              fpNativePackedAbsBits(x.upperBits);
          out.upperBits =
              fpNativePackedCompareBits(negativeMagnitude,
                                        positiveMagnitude) >= 0
                  ? negativeMagnitude
                  : positiveMagnitude;
        }
      }
      return out;
    }

    case ITE:
    {
      if (n.Degree() != 3)
        return out;
      const FpNativeInterval t = fpNativeInterval(n[1]);
      const FpNativeInterval e = fpNativeInterval(n[2]);
      if (!t.known || !e.known)
        return out;
      out.known = true;
      out.lower = std::min(t.lower, e.lower);
      out.upper = std::max(t.upper, e.upper);
      if (t.exact && e.exact)
      {
        out.exact = true;
        out.lowerBits = fpNativePackedCompareBits(t.lowerBits, e.lowerBits) <= 0
                            ? t.lowerBits
                            : e.lowerBits;
        out.upperBits = fpNativePackedCompareBits(t.upperBits, e.upperBits) >= 0
                            ? t.upperBits
                            : e.upperBits;
      }
      return out;
    }

    case FP_ADD:
    case FP_SUB:
    case FP_MUL:
    {
      if (n.Degree() != 3)
        return out;
      const FpNativeInterval a = fpNativeInterval(n[1]);
      const FpNativeInterval b = fpNativeInterval(n[2]);
      if (!a.known || !b.known)
        return out;

      const FpNativeInterval exact =
          fpNativeExactRoundedRange(sort, n.GetKind(), n[0], a, b);
      if (exact.known)
        return exact;

      if (n.GetKind() == FP_ADD)
        return fpNativeRoundedRange(sort, a.lower + b.lower,
                                    a.upper + b.upper);
      if (n.GetKind() == FP_SUB)
        return fpNativeRoundedRange(sort, a.lower - b.upper,
                                    a.upper - b.lower);

      const long double vals[4] = {a.lower * b.lower, a.lower * b.upper,
                                   a.upper * b.lower, a.upper * b.upper};
      return fpNativeRoundedRange(sort, *std::min_element(vals, vals + 4),
                                  *std::max_element(vals, vals + 4));
    }

    default:
      return out;
  }
}

bool BitBlaster::fpNativeKnownFinite(const ASTNode& n)
{
  return fpNativeInterval(n).known;
}

bool BitBlaster::fpNativeKnownZeroMagnitude(const ASTNode& n)
{
  if (!uf->fp_native_domain ||
      n.GetSourceSort().kind() != SourceSort::Kind::FloatingPoint)
    return false;

  if (fpNativeZeroMagnitudeTerms.find(n) !=
      fpNativeZeroMagnitudeTerms.end())
    return true;
  if (fpNativeUnknownZeroMagnitudeTerms.find(n) !=
      fpNativeUnknownZeroMagnitudeTerms.end())
    return false;

  bool knownZero = fpNativeConstantZeroMagnitude(n);
  if (!knownZero)
  {
    switch (n.GetKind())
    {
      case FP_NEG:
      case FP_ABS:
        knownZero = n.Degree() == 1 && fpNativeKnownZeroMagnitude(n[0]);
        break;

      case ITE:
        knownZero = n.Degree() == 3 &&
                    fpNativeKnownZeroMagnitude(n[1]) &&
                    fpNativeKnownZeroMagnitude(n[2]);
        break;

      case FP_ADD:
      case FP_SUB:
        knownZero = n.Degree() == 3 &&
                    fpNativeKnownZeroMagnitude(n[1]) &&
                    fpNativeKnownZeroMagnitude(n[2]);
        break;

      case FP_MUL:
        if (n.Degree() == 3)
        {
          const bool aZero = fpNativeKnownZeroMagnitude(n[1]);
          knownZero =
              (aZero && fpNativeKnownFinite(n[2])) ||
              (fpNativeKnownZeroMagnitude(n[2]) &&
               fpNativeKnownFinite(n[1]));
        }
        break;

      case FP_TOFP:
        knownZero = n.Degree() == 4 && fpNativeKnownZeroMagnitude(n[3]);
        break;

      default:
        break;
    }
  }

  if (knownZero)
  {
    if (n.GetKind() != BVCONST)
      fpNativeZeroMagnitudeTerms.insert(n);
  }
  else
    fpNativeUnknownZeroMagnitudeTerms.insert(n);
  return knownZero;
}

bool BitBlaster::fpNativeKnownFiniteNonnegative(const ASTNode& n)
{
  if (!uf->fp_native_domain ||
      n.GetSourceSort().kind() != SourceSort::Kind::FloatingPoint)
    return false;

  if (fpNativeFiniteNonnegativeTerms.find(n) !=
      fpNativeFiniteNonnegativeTerms.end())
    return true;
  if (fpNativeUnknownFiniteNonnegativeTerms.find(n) !=
      fpNativeUnknownFiniteNonnegativeTerms.end())
    return false;

  // A magnitude-zero fact proves semantic nonnegativity even for -0. It
  // deliberately does not prove that the packed sign bit is clear.
  bool known = fpNativeKnownZeroMagnitude(n);
  if (!known)
  {
    long double value = 0.0L;
    if (fpNativeConstantValue(n, value))
      known = value >= 0.0L;
    else
    {
      switch (n.GetKind())
      {
        case SYMBOL:
        {
          const auto it = fpNativeBounds.find(n);
          known = it != fpNativeBounds.end() && it->second.hasLower &&
                  it->second.hasUpper && it->second.lower >= 0.0L &&
                  fpNativeKnownFinite(n);
          break;
        }

        case FP_ABS:
          known = n.Degree() == 1 && fpNativeKnownFinite(n[0]);
          break;

        case FP_NEG:
          known = n.Degree() == 1 &&
                  fpNativeKnownFiniteNonpositive(n[0]);
          break;

        case ITE:
          known = n.Degree() == 3 &&
                  fpNativeKnownFiniteNonnegative(n[1]) &&
                  fpNativeKnownFiniteNonnegative(n[2]);
          break;

        case FP_ADD:
          // The operands establish the result's mathematical sign. A
          // separate finite-result proof is required before propagating the
          // fact through this term: positive overflow is infinity.
          known = n.Degree() == 3 &&
                  fpNativeKnownFiniteNonnegative(n[1]) &&
                  fpNativeKnownFiniteNonnegative(n[2]) &&
                  fpNativeKnownFinite(n);
          break;

        case FP_SUB:
          known = n.Degree() == 3 &&
                  fpNativeKnownFiniteNonnegative(n[1]) &&
                  fpNativeKnownFiniteNonpositive(n[2]) &&
                  fpNativeKnownFinite(n);
          break;

        case FP_MUL:
          if (n.Degree() == 3)
          {
            const bool aNonnegative =
                fpNativeKnownFiniteNonnegative(n[1]);
            const bool aNonpositive =
                fpNativeKnownFiniteNonpositive(n[1]);
            const bool bNonnegative =
                fpNativeKnownFiniteNonnegative(n[2]);
            const bool bNonpositive =
                fpNativeKnownFiniteNonpositive(n[2]);
            known = ((aNonnegative && bNonnegative) ||
                     (aNonpositive && bNonpositive)) &&
                    fpNativeKnownFinite(n);
          }
          break;

        case FP_TOFP:
          known = n.Degree() == 4 &&
                  fpNativeKnownFiniteNonnegative(n[3]) &&
                  fpNativeKnownFinite(n);
          break;

        default:
          break;
      }
    }
  }

  if (known)
  {
    if (n.GetKind() != BVCONST)
      fpNativeFiniteNonnegativeTerms.insert(n);
  }
  else
    fpNativeUnknownFiniteNonnegativeTerms.insert(n);
  return known;
}

bool BitBlaster::fpNativeKnownFiniteNonpositive(const ASTNode& n)
{
  if (!uf->fp_native_domain ||
      n.GetSourceSort().kind() != SourceSort::Kind::FloatingPoint)
    return false;

  if (fpNativeFiniteNonpositiveTerms.find(n) !=
      fpNativeFiniteNonpositiveTerms.end())
    return true;
  if (fpNativeUnknownFiniteNonpositiveTerms.find(n) !=
      fpNativeUnknownFiniteNonpositiveTerms.end())
    return false;

  // Magnitude zero belongs to both semantic sign domains. In particular,
  // neither this predicate nor its nonnegative twin constrains the packed
  // sign bit of zero.
  bool known = fpNativeKnownZeroMagnitude(n);
  if (!known)
  {
    long double value = 0.0L;
    if (fpNativeConstantValue(n, value))
      known = value <= 0.0L;
    else
    {
      switch (n.GetKind())
      {
        case SYMBOL:
        {
          const auto it = fpNativeBounds.find(n);
          known = it != fpNativeBounds.end() && it->second.hasLower &&
                  it->second.hasUpper && it->second.upper <= 0.0L &&
                  fpNativeKnownFinite(n);
          break;
        }

        case FP_NEG:
          known = n.Degree() == 1 &&
                  fpNativeKnownFiniteNonnegative(n[0]);
          break;

        case ITE:
          known = n.Degree() == 3 &&
                  fpNativeKnownFiniteNonpositive(n[1]) &&
                  fpNativeKnownFiniteNonpositive(n[2]);
          break;

        case FP_ADD:
          known = n.Degree() == 3 &&
                  fpNativeKnownFiniteNonpositive(n[1]) &&
                  fpNativeKnownFiniteNonpositive(n[2]) &&
                  fpNativeKnownFinite(n);
          break;

        case FP_SUB:
          known = n.Degree() == 3 &&
                  fpNativeKnownFiniteNonpositive(n[1]) &&
                  fpNativeKnownFiniteNonnegative(n[2]) &&
                  fpNativeKnownFinite(n);
          break;

        case FP_MUL:
          if (n.Degree() == 3)
          {
            const bool aNonnegative =
                fpNativeKnownFiniteNonnegative(n[1]);
            const bool aNonpositive =
                fpNativeKnownFiniteNonpositive(n[1]);
            const bool bNonnegative =
                fpNativeKnownFiniteNonnegative(n[2]);
            const bool bNonpositive =
                fpNativeKnownFiniteNonpositive(n[2]);
            known = ((aNonnegative && bNonpositive) ||
                     (aNonpositive && bNonnegative)) &&
                    fpNativeKnownFinite(n);
          }
          break;

        case FP_TOFP:
          known = n.Degree() == 4 &&
                  fpNativeKnownFiniteNonpositive(n[3]) &&
                  fpNativeKnownFinite(n);
          break;

        default:
          break;
      }
    }
  }

  if (known)
  {
    if (n.GetKind() != BVCONST)
      fpNativeFiniteNonpositiveTerms.insert(n);
  }
  else
    fpNativeUnknownFiniteNonpositiveTerms.insert(n);
  return known;
}


bool BitBlaster::fpNativeBoundPredicate(const ASTNode& n, ASTNode& symbol,
                                        ASTNode& constant,
                                        long double& value,
                                        bool& lowerBound) const
{
  const Kind k = n.GetKind();
  if ((k != FP_LT && k != FP_LEQ && k != FP_GT && k != FP_GEQ) ||
      n.Degree() != 2)
    return false;

  const bool flipped = (k == FP_GT || k == FP_GEQ);
  const ASTNode& left = flipped ? n[1] : n[0];
  const ASTNode& right = flipped ? n[0] : n[1];

  if (left.GetKind() == SYMBOL &&
      left.GetSourceSort().kind() == SourceSort::Kind::FloatingPoint &&
      fpNativeConstantValue(right, value))
  {
    symbol = left;
    constant = right;
    lowerBound = false;
    return true;
  }

  if (right.GetKind() == SYMBOL &&
      right.GetSourceSort().kind() == SourceSort::Kind::FloatingPoint &&
      fpNativeConstantValue(left, value))
  {
    symbol = right;
    constant = left;
    lowerBound = true;
    return true;
  }

  return false;
}

bool BitBlaster::fpNativeMagnitudeZeroPredicate(const ASTNode& n,
                                                ASTNode& term) const
{
  if (n.GetKind() == FP_ISZERO && n.Degree() == 1 &&
      n[0].GetKind() == FP_MUL &&
      n[0].GetSourceSort().kind() == SourceSort::Kind::FloatingPoint)
  {
    term = n[0];
    return true;
  }

  if (n.GetKind() != EQ || n.Degree() != 2)
    return false;

  auto match = [&](const ASTNode& extract, const ASTNode& zero) {
    if (extract.GetKind() != BVEXTRACT || extract.Degree() != 3 ||
        zero.GetKind() != BVCONST ||
        !CONSTANTBV::BitVector_is_empty(zero.GetBVConst()))
      return false;

    const ASTNode& candidate = extract[0];
    const SourceSort sort = candidate.GetSourceSort();
    if (candidate.GetKind() != SYMBOL ||
        sort.kind() != SourceSort::Kind::FloatingPoint)
      return false;

    const unsigned w = sort.packedWidth();
    if (w < 2 || candidate.GetValueWidth() != w ||
        extract.GetValueWidth() != w - 1 || zero.GetValueWidth() != w - 1 ||
        extract[1].GetUnsignedConst() != w - 2 ||
        extract[2].GetUnsignedConst() != 0)
      return false;

    term = candidate;
    return true;
  };

  return match(n[0], n[1]) || match(n[1], n[0]);
}

void BitBlaster::collectFpNativeDomainBounds(const ASTNode& n)
{
  // Bounds are useful only when they occur in the top-level conjunction.
  // Walk that conjunction explicitly: native-domain collection is enabled
  // for every query, including deep formulas with no floating-point terms.
  // Recursing down a long AND spine would therefore reintroduce a stack limit
  // into the otherwise stack-safe bit-blaster.
  ASTVec pending(1, n);
  while (!pending.empty())
  {
    const ASTNode current = pending.back();
    pending.pop_back();
    if (current.GetKind() == AND)
    {
      for (auto it = current.end(); it != current.begin();)
        pending.push_back(*--it);
      continue;
    }

    ASTNode zeroSymbol;
    if (fpNativeMagnitudeZeroPredicate(current, zeroSymbol))
    {
      fpNativeZeroMagnitudeFacts.insert(zeroSymbol);
      fpNativeZeroMagnitudeTerms.insert(zeroSymbol);
      fpNativeFiniteTerms.insert(zeroSymbol);
    }

    ASTNode symbol;
    ASTNode constant;
    long double value = 0.0L;
    bool lowerBound = false;
    if (!fpNativeBoundPredicate(current, symbol, constant, value, lowerBound))
      continue;

    FpNativeBounds& seen = fpNativeBounds[symbol];
    if (lowerBound)
    {
      if (!seen.hasLower || value >= seen.lower)
      {
        seen.lower = value;
        seen.lowerExact = fpNativeConstantBits(constant, seen.lowerBits);
      }
      seen.hasLower = true;
    }
    else
    {
      if (!seen.hasUpper || value <= seen.upper)
      {
        seen.upper = value;
        seen.upperExact = fpNativeConstantBits(constant, seen.upperBits);
      }
      seen.hasUpper = true;
    }
  }
}

void BitBlaster::collectFpNativeDomainFacts(const ASTNode& root)
{
  fpNativeFiniteTerms.clear();
  fpNativeZeroMagnitudeFacts.clear();
  fpNativeZeroMagnitudeTerms.clear();
  fpNativeUnknownZeroMagnitudeTerms.clear();
  fpNativeFiniteNonnegativeTerms.clear();
  fpNativeUnknownFiniteNonnegativeTerms.clear();
  fpNativeFiniteNonpositiveTerms.clear();
  fpNativeUnknownFiniteNonpositiveTerms.clear();
  fpNativeBounds.clear();
  fpNativeIntervals.clear();
  fpNativeParentUses.clear();
  fpNativeFiniteCmpOperands = 0;
  fpNativeFiniteEqOperands = 0;
  fpNativeFiniteClassifications = 0;
  fpNativeFiniteArithOperands = 0;
  fpNativeFiniteRoundPacks = 0;
  fpNativeZeroCmpOperands = 0;
  fpNativeZeroEqOperands = 0;
  fpNativeZeroClassifications = 0;
  fpNativeIsZeroPredicates = 0;
  fpNativeIsZeroAddPredicates = 0;
  fpNativeIsZeroAddFusedPredicates = 0;
  fpNativeIsZeroAddExclusiveResults = 0;
  fpNativeIsZeroAddMemoizedResults = 0;
  fpNativeIsZeroAddKnownZeroResults = 0;
  fpNativeIsZeroAddBothFiniteOperands = 0;
  fpNativeIsZeroAddKnownSameSignOperands = 0;
  fpNativeIsZeroAddKnownOppositeSignOperands = 0;
  fpNativeIsZeroAddOneKnownSignOperand = 0;
  fpNativeZeroAddFastPaths = 0;
  fpNativeZeroMulFastPaths = 0;
  fpNativeZeroToFpFastPaths = 0;
  fpNativeKnownPositiveAddPaths = 0;
  fpNativeKnownNegativeAddPaths = 0;
  fpNativeKnownPositiveMulPaths = 0;
  fpNativeKnownNegativeMulPaths = 0;
  if (uf->stats_flag)
  {
    ASTNodeSet visited;
    std::vector<ASTNode> pending(1, root);
    while (!pending.empty())
    {
      const ASTNode n = pending.back();
      pending.pop_back();
      if (!visited.insert(n).second)
        continue;
      for (const ASTNode& child : n)
      {
        ++fpNativeParentUses[child];
        pending.push_back(child);
      }
    }
  }

  collectFpNativeDomainBounds(root);
  for (const auto& entry : fpNativeBounds)
    if (entry.second.hasLower && entry.second.hasUpper)
      fpNativeFiniteTerms.insert(entry.first);
}

// Bit-blasted form for the four ordering comparisons (FP_GT, FP_LT, FP_GEQ,
// FP_LEQ) over packed IEEE-754 operands. FloatBlast leaves these comparisons
// in place when both operands are packed views (symbols, interned
// constants, muxes over those);
// their packed bits are compared directly, with no unpacking. Sign-magnitude
// maps onto an unsigned total order with a per-bit XOR against the sign:
//
//   key(f) = not(sign(f)) ++ (f[w-2:0] xor sign(f))
//   a >  b = not(isNaN(a)) and not(isNaN(b))
//            and not(isZero(a) and isZero(b)) and key(a) >u  key(b)
//   a >= b = not(isNaN(a)) and not(isNaN(b))
//            and (   (isZero(a) and isZero(b)) or  key(a) >=u key(b))
//
// The keys order every pair correctly except the two zeros: key(-0) and
// key(+0) are adjacent with no other float's key between them, and +0 and
// -0 compare EQUAL. So exactly one pair is misordered per direction --
// strictly, key(+0) > key(-0) must be suppressed (the both-zero conjunct);
// non-strictly, key(-0) >= key(+0) must be granted (the both-zero
// disjunct). isNaN tests the exponent and significand fields, so operands
// with arbitrary NaN payloads compare as NaN.
BBNode BitBlaster::BBcompareFP(const ASTNode& form, BBNodeSet& support)
{
  const Kind k = form.GetKind();
  assert(k == FP_GT || k == FP_LT || k == FP_GEQ || k == FP_LEQ);
  // fp.lt(a,b) is exactly fp.gt(b,a), and fp.leq(a,b) exactly fp.geq(b,a).
  const bool mirrored = (k == FP_LT || k == FP_LEQ);
  const bool strict = (k == FP_GT || k == FP_LT);
  const ASTNode& a = mirrored ? form[1] : form[0];
  const ASTNode& b = mirrored ? form[0] : form[1];

  const SourceSort sort = a.GetSourceSort();
  assert(sort.kind() == SourceSort::Kind::FloatingPoint);
  const unsigned sb = sort.significandWidth();
  const unsigned w = sort.exponentWidth() + sb;
  assert(a.GetValueWidth() == w);
  assert(b.GetValueWidth() == w);
  assert(sb >= 2 && w >= sb + 1);

  // Bit i of a packed operand is bit i of the IEEE encoding: significand
  // field in bits [0, sb-2], exponent field in bits [sb-1, w-2], sign at
  // w-1.
  const BBNodeVec aBits = BBTerm(a, support);
  const BBNodeVec bBits = BBTerm(b, support);
  const bool aFinite = fpNativeKnownFinite(a);
  const bool bFinite = fpNativeKnownFinite(b);
  const bool aKnownZero = fpNativeKnownZeroMagnitude(a);
  const bool bKnownZero = fpNativeKnownZeroMagnitude(b);
  fpNativeFiniteCmpOperands += static_cast<size_t>(aFinite) +
                               static_cast<size_t>(bFinite);
  fpNativeZeroCmpOperands += static_cast<size_t>(aKnownZero) +
                             static_cast<size_t>(bKnownZero);

  // Once a top-level magnitude constraint establishes an operand as either
  // signed zero, comparison with it only needs the other operand's sign,
  // zero test, and (unless finite) NaN test. This retains the SMT-LIB rule
  // that +0 and -0 compare equal.
  if (aKnownZero && bKnownZero)
    return strict ? nf->getFalse() : nf->getTrue();

  if (aKnownZero || bKnownZero)
  {
    const bool zeroOnLeft = aKnownZero;
    const BBNodeVec& otherBits = zeroOnLeft ? bBits : aBits;
    const bool otherFinite = zeroOnLeft ? bFinite : aFinite;
    const BBNode otherZero = BBfpIsZero(otherBits, w);
    const BBNode sign = otherBits[w - 1];
    BBNode ordered;
    if (zeroOnLeft)
      ordered = strict
                    ? nf->CreateNode(AND, sign,
                                     nf->CreateNode(NOT, otherZero))
                    : nf->CreateNode(OR, sign, otherZero);
    else
      ordered = strict
                    ? nf->CreateNode(AND, nf->CreateNode(NOT, sign),
                                     nf->CreateNode(NOT, otherZero))
                    : nf->CreateNode(OR, nf->CreateNode(NOT, sign),
                                     otherZero);

    if (otherFinite)
      return ordered;
    const BBNode notNaN =
        nf->CreateNode(NOT, BBfpIsNaN(otherBits, sb, w));
    return nf->CreateNode(AND, notNaN, ordered);
  }

  auto key = [this](const BBNodeVec& p, unsigned width) {
    const BBNode& sign = p[width - 1];
    BBNodeVec k;
    k.reserve(width);
    for (unsigned i = 0; i < width - 1; i++)
      k.push_back(nf->CreateNode(XOR, p[i], sign));
    k.push_back(nf->CreateNode(NOT, sign));
    return k;
  };

  const BBNode aIsNaN = aFinite ? nf->getFalse() : BBfpIsNaN(aBits, sb, w);
  const BBNode bIsNaN = bFinite ? nf->getFalse() : BBfpIsNaN(bBits, sb, w);
  const BBNode aNotNaN = nf->CreateNode(NOT, aIsNaN);
  const BBNode bNotNaN = nf->CreateNode(NOT, bIsNaN);
  // Both operands' circuits are built before they are combined. Written as
  // two statements because C++ does not sequence a call's arguments against
  // each other: as one expression, which operand's AIG nodes get built first
  // is the compiler's choice, and the numbering it decides reaches the CNF.
  const BBNode aZero = BBfpIsZero(aBits, w);
  const BBNode bZero = BBfpIsZero(bBits, w);
  const BBNode bothZero = nf->CreateNode(AND, aZero, bZero);
  const BBNodeVec aKey = key(aBits, w);
  const BBNodeVec bKey = key(bBits, w);
  // key(a) >u key(b) when strict, key(a) >=u key(b) otherwise.
  const BBNode ordered = strict ? BBBVLE(bKey, aKey, false, true)
                                : BBBVLE(bKey, aKey, false);
  const BBNode zeroCorrected =
      strict ? nf->CreateNode(AND, nf->CreateNode(NOT, bothZero), ordered)
             : nf->CreateNode(OR, bothZero, ordered);

  if (aFinite && bFinite)
    return zeroCorrected;

  BBNodeVec conjuncts;
  conjuncts.reserve(3);
  conjuncts.push_back(aNotNaN);
  conjuncts.push_back(bNotNaN);
  conjuncts.push_back(zeroCorrected);
  return nf->CreateNode(AND, conjuncts);
}

// Bit-blasted form for the two equalities (FP_EQ, FP_SMT_EQ) over packed
// IEEE-754 operands; FloatBlast leaves them in place under the same gate as
// the ordering comparisons (see BBcompareFP). No unpacking and no
// comparator is needed: an IEEE interchange format encodes every value
// exactly once, so equality is bit equality -- except at the two corners,
// where the two kinds make opposite choices.
//
//   fp.eq: NaN equals nothing (whatever its payload), and +0 equals -0.
//     fp.eq(a,b) = not(isNaN(a)) and not(isNaN(b))
//                  and (bits(a) = bits(b) or (isZero(a) and isZero(b)))
//
//   SMT =: the SMT domain has one abstract NaN, so all NaN payloads are
//   equal, and two distinct zeros, so +0 and -0 are not.
//     a = b = (isNaN(a) and isNaN(b)) or bits(a) = bits(b)
BBNode BitBlaster::BBeqFP(const ASTNode& form, BBNodeSet& support)
{
  const Kind k = form.GetKind();
  assert(k == FP_EQ || k == FP_SMT_EQ);

  const SourceSort sort = form[0].GetSourceSort();
  assert(sort.kind() == SourceSort::Kind::FloatingPoint);
  const unsigned sb = sort.significandWidth();
  const unsigned w = sort.exponentWidth() + sb;
  assert(form[0].GetValueWidth() == w);
  assert(form[1].GetValueWidth() == w);
  assert(sb >= 2 && w >= sb + 1);

  const BBNodeVec aBits = BBTerm(form[0], support);
  const BBNodeVec bBits = BBTerm(form[1], support);
  const bool aFinite = fpNativeKnownFinite(form[0]);
  const bool bFinite = fpNativeKnownFinite(form[1]);
  // A direct product-zero fact must retain one predicate that checks the
  // product bits; otherwise simplifying that very predicate to true would
  // discard the operand restriction the fact represents. Consumers can use
  // the fact, while this witness equality keeps the producer relation live.
  const bool aDirectProductZero =
      form[0].GetKind() == FP_MUL &&
      fpNativeZeroMagnitudeFacts.find(form[0]) !=
          fpNativeZeroMagnitudeFacts.end();
  const bool bDirectProductZero =
      form[1].GetKind() == FP_MUL &&
      fpNativeZeroMagnitudeFacts.find(form[1]) !=
          fpNativeZeroMagnitudeFacts.end();
  const bool aKnownZero =
      fpNativeKnownZeroMagnitude(form[0]) && !aDirectProductZero;
  const bool bKnownZero =
      fpNativeKnownZeroMagnitude(form[1]) && !bDirectProductZero;
  fpNativeFiniteEqOperands += static_cast<size_t>(aFinite) +
                              static_cast<size_t>(bFinite);
  fpNativeZeroEqOperands += static_cast<size_t>(aKnownZero) +
                            static_cast<size_t>(bKnownZero);

  if (aKnownZero || bKnownZero)
  {
    const BBNode otherZero =
        (aKnownZero && bKnownZero)
            ? nf->getTrue()
            : BBfpIsZero(aKnownZero ? bBits : aBits, w);

    // fp.eq identifies the two signed zeros. Structural SMT equality keeps
    // them distinct, so it additionally compares the surviving sign bits.
    if (k == FP_EQ)
      return otherZero;
    const BBNode signsEqual =
        nf->CreateNode(IFF, aBits[w - 1], bBits[w - 1]);
    return nf->CreateNode(AND, otherZero, signsEqual);
  }

  const BBNode sameBits = BBEQ(aBits, bBits);

  if (k == FP_SMT_EQ)
  {
    if (aFinite || bFinite)
      return sameBits;

    // Sequenced deliberately; see the note in BBcompareFP.
    const BBNode aNaN = BBfpIsNaN(aBits, sb, w);
    const BBNode bNaN = BBfpIsNaN(bBits, sb, w);
    const BBNode bothNaN = nf->CreateNode(AND, aNaN, bNaN);
    return nf->CreateNode(OR, bothNaN, sameBits);
  }

  // One not-NaN test suffices, not two: when the result can be true at
  // all, either bits(a) = bits(b) -- identical patterns, so the operands
  // are NaN or not together and one test implies the other -- or both
  // operands are zeros, which are never NaN. Testing only one side
  // computes the same Boolean function (the exhaustive differential
  // passes with either or both tests; no test CAN distinguish them, so
  // this comment is the argument that keeps the dropped test dropped).
  // Sequenced deliberately; see the note in BBcompareFP.
  const BBNode aZero = BBfpIsZero(aBits, w);
  const BBNode bZero = BBfpIsZero(bBits, w);
  const BBNode bothZero = nf->CreateNode(AND, aZero, bZero);
  const BBNode sameValue = nf->CreateNode(OR, sameBits, bothZero);

  if (aFinite || bFinite)
    return sameValue;

  // Test the constant side when there is one: its isNaN folds away
  // entirely and the symbolic side's isNaN circuit is never built. The
  // choice is per-node and deterministic.
  const BBNodeVec& nanSide = form[0].isConstant() ? aBits : bBits;
  const BBNode notNaN = nf->CreateNode(NOT, BBfpIsNaN(nanSide, sb, w));
  return nf->CreateNode(AND, notNaN, sameValue);
}

// Bit-blasted form for the seven classification predicates over a packed
// IEEE-754 operand. Each is a test on the exponent field e and the stored
// significand m, both directly visible in the packed encoding, so the
// SymFPU route pays a full unpack to read flags that are already there:
//
//   isZero        e = 0        and m = 0    (either sign)
//   isSubnormal   e = 0        and m != 0
//   isNormal      e != 0       and e != all-ones
//   isInfinite    e = all-ones and m = 0
//   isNaN         e = all-ones and m != 0   (any payload)
//   isNegative    sign set     and not NaN
//   isPositive    sign clear   and not NaN
//
// The two sign predicates are the ones with corners: -0 IS negative and +0
// IS positive (the sign bit alone decides among the finite values), while a
// NaN is neither, because its sign bit carries no meaning. isNormal has to
// exclude the all-ones exponent as well as the zero one, or infinities and
// NaNs count as normal.
BBNode BitBlaster::BBclassifyFP(const ASTNode& form, BBNodeSet& support)
{
  const Kind k = form.GetKind();

  const SourceSort sort = form[0].GetSourceSort();
  assert(sort.kind() == SourceSort::Kind::FloatingPoint);
  const unsigned sb = sort.significandWidth();
  const unsigned w = sort.exponentWidth() + sb;
  assert(form[0].GetValueWidth() == w);
  assert(sb >= 2 && w >= sb + 1);

  const bool isZeroAdd =
      k == FP_ISZERO && form[0].GetKind() == FP_ADD &&
      form[0].Degree() == 3 && uf->fp_native_arith;
  const bool addMemoizedBefore =
      isZeroAdd && BBTermMemo.find(form[0]) != BBTermMemo.end();
  // As in BBeqFP, a product's own asserted/derived zero predicate is the
  // witness that must continue checking its computed magnitude.
  const bool directProductZero =
      form[0].GetKind() == FP_MUL &&
      fpNativeZeroMagnitudeFacts.find(form[0]) !=
          fpNativeZeroMagnitudeFacts.end();
  const bool knownZero =
      fpNativeKnownZeroMagnitude(form[0]) && !directProductZero;
  const bool knownFinite = fpNativeKnownFinite(form[0]);
  if (knownFinite)
    ++fpNativeFiniteClassifications;
  if (knownZero)
    ++fpNativeZeroClassifications;

  if (uf->stats_flag && k == FP_ISZERO)
  {
    ++fpNativeIsZeroPredicates;
    if (isZeroAdd)
    {
      ++fpNativeIsZeroAddPredicates;
      const auto uses = fpNativeParentUses.find(form[0]);
      if (uses != fpNativeParentUses.end() && uses->second == 1)
        ++fpNativeIsZeroAddExclusiveResults;
      if (addMemoizedBefore)
        ++fpNativeIsZeroAddMemoizedResults;
      if (knownZero)
        ++fpNativeIsZeroAddKnownZeroResults;

      const bool aFinite = fpNativeKnownFinite(form[0][1]);
      const bool bFinite = fpNativeKnownFinite(form[0][2]);
      if (aFinite && bFinite)
        ++fpNativeIsZeroAddBothFiniteOperands;

      if (uf->fp_native_known_sign)
      {
        const bool aNonnegative =
            fpNativeKnownFiniteNonnegative(form[0][1]);
        const bool aNonpositive =
            fpNativeKnownFiniteNonpositive(form[0][1]);
        const bool bNonnegative =
            fpNativeKnownFiniteNonnegative(form[0][2]);
        const bool bNonpositive =
            fpNativeKnownFiniteNonpositive(form[0][2]);
        const bool aKnownSign = aNonnegative || aNonpositive;
        const bool bKnownSign = bNonnegative || bNonpositive;
        if ((aNonnegative && bNonnegative) ||
            (aNonpositive && bNonpositive))
          ++fpNativeIsZeroAddKnownSameSignOperands;
        if ((aNonnegative && bNonpositive) ||
            (aNonpositive && bNonnegative))
          ++fpNativeIsZeroAddKnownOppositeSignOperands;
        if (aKnownSign != bKnownSign)
          ++fpNativeIsZeroAddOneKnownSignOperand;
      }
    }
  }

  if (isZeroAdd && uf->fp_native_add_iszero && !addMemoizedBefore)
  {
    ++fpNativeAddIsZeroFusions;
    if (uf->stats_flag)
      ++fpNativeIsZeroAddFusedPredicates;
    return knownZero ? nf->getTrue() : BBfpAddIsZero(form[0], support);
  }

  const BBNodeVec p = BBTerm(form[0], support);

  switch (k)
  {
    case FP_ISZERO:
      return knownZero ? nf->getTrue() : BBfpIsZero(p, w);

    case FP_ISNAN:
      return knownFinite ? nf->getFalse() : BBfpIsNaN(p, sb, w);

    case FP_ISSUBNORMAL:
    {
      if (knownZero)
        return nf->getFalse();
      BBNodeVec expField(p.begin() + (sb - 1), p.begin() + (w - 1));
      BBNodeVec sigField(p.begin(), p.begin() + (sb - 1));
      const BBNode expZero = nf->CreateNode(NOR, expField);
      const BBNode sigNonZero = nf->CreateNode(OR, sigField);
      return nf->CreateNode(AND, expZero, sigNonZero);
    }

    case FP_ISNORMAL:
    {
      if (knownZero)
        return nf->getFalse();
      // Built as NOT(AND(e)) rather than NAND(e) so the all-ones test is
      // the same AIG node isNaN and isInfinite build over this operand.
      BBNodeVec expField(p.begin() + (sb - 1), p.begin() + (w - 1));
      const BBNode expNonZero = nf->CreateNode(OR, expField);
      if (knownFinite)
        return expNonZero;
      const BBNode expAllOnes = nf->CreateNode(AND, expField);
      const BBNode expNotOnes = nf->CreateNode(NOT, expAllOnes);
      return nf->CreateNode(AND, expNonZero, expNotOnes);
    }

    case FP_ISINFINITE:
    {
      if (knownFinite)
        return nf->getFalse();
      BBNodeVec expField(p.begin() + (sb - 1), p.begin() + (w - 1));
      BBNodeVec sigField(p.begin(), p.begin() + (sb - 1));
      const BBNode expAllOnes = nf->CreateNode(AND, expField);
      const BBNode sigZero = nf->CreateNode(NOR, sigField);
      return nf->CreateNode(AND, expAllOnes, sigZero);
    }

    case FP_ISNEGATIVE:
    {
      if (knownFinite)
        return p[w - 1];
      const BBNode notNaN = nf->CreateNode(NOT, BBfpIsNaN(p, sb, w));
      return nf->CreateNode(AND, p[w - 1], notNaN);
    }

    case FP_ISPOSITIVE:
    {
      const BBNode signClear = nf->CreateNode(NOT, p[w - 1]);
      if (knownFinite)
        return signClear;
      const BBNode notNaN = nf->CreateNode(NOT, BBfpIsNaN(p, sb, w));
      return nf->CreateNode(AND, signClear, notNaN);
    }

    default:
      FatalError("BBclassifyFP: Illegal kind", form);
      return BBNode();
  }
}

/****************************************************************
 * Native fp.mul (--bb.fp-native-arith)                         *
 ****************************************************************/

// Count of leading zeros of v (scanning from the MSB down), as an unsigned
// binary vector of countWidth bits. An all-zero v counts v.size(). Built as
// a priority chain: scanning positions from the LSB up, each set bit
// overrides the count implied by the lower ones, so the MSB wins.
BBNodeVec BitBlaster::BBfpCLZ(const BBNodeVec& v, unsigned countWidth)
{
  const unsigned n = v.size();
  auto constVec = [&](unsigned value) {
    BBNodeVec c(countWidth);
    for (unsigned i = 0; i < countWidth; i++)
      c[i] = ((value >> i) & 1) ? nf->getTrue() : nf->getFalse();
    return c;
  };
  BBNodeVec count = constVec(n);
  for (unsigned i = 0; i < n; i++)
    count = BBITE(v[i], constVec(n - 1 - i), count);
  return count;
}

// Logarithmic left shifter, zero fill. The amount is unsigned binary; any
// amount >= v.size() shifts everything out.
BBNodeVec BitBlaster::BBfpShiftLeft(const BBNodeVec& v, const BBNodeVec& amt)
{
  BBNodeVec r = v;
  for (unsigned s = 0; s < amt.size(); s++)
  {
    const unsigned k = 1u << s;
    if (k >= r.size())
    {
      const BBNodeVec zeros = BBfill(r.size(), nf->getFalse());
      r = BBITE(amt[s], zeros, r);
      continue;
    }
    BBNodeVec shifted(r.size());
    for (unsigned i = 0; i < r.size(); i++)
      shifted[i] = (i >= k) ? r[i - k] : nf->getFalse();
    r = BBITE(amt[s], shifted, r);
  }
  return r;
}

// Logarithmic right shifter that ORs every shifted-out bit into sticky --
// the rounding circuits must not lose shifted-out precision.
BBNodeVec BitBlaster::BBfpShiftRightSticky(const BBNodeVec& v,
                                           const BBNodeVec& amt,
                                           BBNode& sticky)
{
  BBNodeVec r = v;
  for (unsigned s = 0; s < amt.size(); s++)
  {
    const unsigned k = 1u << s;
    if (k >= r.size())
    {
      const BBNode all = nf->CreateNode(OR, r);
      sticky = nf->CreateNode(OR, sticky, nf->CreateNode(AND, amt[s], all));
      const BBNodeVec zeros = BBfill(r.size(), nf->getFalse());
      r = BBITE(amt[s], zeros, r);
      continue;
    }
    BBNodeVec dropped(r.begin(), r.begin() + k);
    const BBNode droppedAny = nf->CreateNode(OR, dropped);
    sticky =
        nf->CreateNode(OR, sticky, nf->CreateNode(AND, amt[s], droppedAny));
    BBNodeVec shifted(r.size());
    for (unsigned i = 0; i < r.size(); i++)
      shifted[i] = (i + k < r.size()) ? r[i + k] : nf->getFalse();
    r = BBITE(amt[s], shifted, r);
  }
  return r;
}

// v + inc (a single carry-in bit), one bit wider than v -- the rounding
// increment, whose carry-out is the significand overflowing to 10...0.
BBNodeVec BitBlaster::BBfpIncrement(const BBNodeVec& v, const BBNode& inc)
{
  BBNodeVec r(v.size() + 1);
  BBNode carry = inc;
  for (unsigned i = 0; i < v.size(); i++)
  {
    r[i] = nf->CreateNode(XOR, v[i], carry);
    carry = nf->CreateNode(AND, v[i], carry);
  }
  r[v.size()] = carry;
  return r;
}

unsigned BitBlaster::BBfpExpWidth(unsigned eb, unsigned sb)
{
  const unsigned bias = (1u << (eb - 1)) - 1;
  unsigned E = eb + 2;
  while ((1u << (E - 1)) <= bias + 2 * sb + 4)
    E++;
  return E;
}

BitBlaster::FpOperand BitBlaster::BBfpUnpack(const BBNodeVec& p, unsigned sb,
                                             unsigned w, unsigned E,
                                             BBNodeSet& support,
                                             const bool knownFinite,
                                             const bool knownZeroMagnitude)
{
  const unsigned eb = w - sb;
  const unsigned bias = (1u << (eb - 1)) - 1;
  FpOperand o;
  o.sign = p[w - 1];
  BBNodeVec exp = knownZeroMagnitude
                      ? BBfill(eb, nf->getFalse())
                      : BBNodeVec(p.begin() + (sb - 1), p.begin() + (w - 1));
  BBNodeVec sig = knownZeroMagnitude
                      ? BBfill(sb - 1, nf->getFalse())
                      : BBNodeVec(p.begin(), p.begin() + (sb - 1));
  const BBNode expZero = nf->CreateNode(NOR, exp);
  const BBNode sigZero = nf->CreateNode(NOR, sig);
  o.isZero = knownZeroMagnitude
                 ? nf->getTrue()
                 : nf->CreateNode(AND, expZero, sigZero);
  if (knownFinite || knownZeroMagnitude)
  {
    o.isInf = nf->getFalse();
    o.isNaN = nf->getFalse();
  }
  else
  {
    const BBNode expOnes = nf->CreateNode(AND, exp);
    const BBNode sigNonzero = nf->CreateNode(OR, sig);
    o.isInf = nf->CreateNode(AND, expOnes, sigZero);
    o.isNaN = nf->CreateNode(AND, expOnes, sigNonzero);
  }
  const BBNode hidden = nf->CreateNode(NOT, expZero);
  o.msig = sig;
  o.msig.push_back(hidden);
  // Unbiased exponent, with subnormals reading their exponent field as 1
  // (the scale the field's zero encoding shares).
  BBNodeVec one(eb, nf->getFalse());
  one[0] = nf->getTrue();
  BBNodeVec e = BBITE(hidden, exp, one);
  while (e.size() < E)
    e.push_back(nf->getFalse());
  BBNodeVec biasV(E, nf->getFalse());
  for (unsigned i = 0; i < E; i++)
    if ((bias >> i) & 1)
      biasV[i] = nf->getTrue();
  BBSub(e, biasV, support);
  o.eUnb = e;
  return o;
}

BBNodeVec BitBlaster::BBfpRoundPack(const BBNodeVec& rm, const BBNode& sgn,
                                    const BBNodeVec& rsigIn,
                                    const BBNode& guardIn,
                                    const BBNode& stickyIn,
                                    const BBNodeVec& beIn, unsigned sb,
                                    unsigned eb, BBNodeSet& support,
                                    const bool resultKnownFinite)
{
  const unsigned w = eb + sb;
  const unsigned maxbe = (1u << eb) - 2;
  const unsigned E = beIn.size();
  const BBNode& rne = rm[0];
  const BBNode& rtp = rm[1];
  const BBNode& rtn = rm[2];
  const BBNode& rna = rm[4];

  auto constVec = [&](unsigned value, unsigned width) {
    BBNodeVec c(width);
    for (unsigned i = 0; i < width; i++)
      c[i] = ((value >> i) & 1) ? nf->getTrue() : nf->getFalse();
    return c;
  };

  BBNodeVec rsig = rsigIn;
  BBNode guard = guardIn;
  BBNode sticky = stickyIn;
  BBNodeVec be = beIn;

  // Subnormal range: biased exponent <= 0 needs a right shift of 1 - be,
  // clamped -- anything past guard is pure sticky.
  const unsigned dmax = sb + 2;
  const BBNode beNonPos =
      nf->CreateNode(OR, be[E - 1], nf->CreateNode(NOR, be));
  BBNodeVec shiftFull = constVec(1, E);
  BBSub(shiftFull, be, support); // 1 - be, signed
  const BBNode tooFar = nf->CreateNode(
      NOT, BBBVLE(shiftFull, constVec(dmax, E), true /*signed*/));
  const unsigned dw = [](unsigned x) {
    unsigned bb = 1;
    while ((1u << bb) <= x)
      bb++;
    return bb;
  }(dmax);
  BBNodeVec d(dw);
  for (unsigned i = 0; i < dw; i++)
  {
    const BBNode inRange = nf->CreateNode(ITE, tooFar,
                                          ((dmax >> i) & 1) ? nf->getTrue()
                                                            : nf->getFalse(),
                                          shiftFull[i]);
    d[i] = nf->CreateNode(AND, beNonPos, inRange);
  }
  BBNodeVec vg = rsig;
  vg.insert(vg.begin(), guard); // [guard, rsig...]
  vg = BBfpShiftRightSticky(vg, d, sticky);
  guard = vg[0];
  for (unsigned i = 0; i < sb; i++)
    rsig[i] = vg[i + 1];
  // After a subnormal shift the value sits at the exp=1 scale (the encoding
  // with exponent field 0 shares it).
  BBNodeVec beAfter = BBITE(beNonPos, constVec(1, E), be);

  // Round.
  const BBNode gs = nf->CreateNode(OR, guard, sticky);
  BBNodeVec upCases;
  upCases.push_back(nf->CreateNode(
      AND, rne, guard, nf->CreateNode(OR, sticky, rsig[0])));
  upCases.push_back(nf->CreateNode(AND, rna, guard));
  upCases.push_back(
      nf->CreateNode(AND, rtp, nf->CreateNode(NOT, sgn), gs));
  upCases.push_back(nf->CreateNode(AND, rtn, sgn, gs));
  const BBNode roundUp = nf->CreateNode(OR, upCases);
  const BBNodeVec rr = BBfpIncrement(rsig, roundUp);
  const BBNode carry = rr[sb];
  BBNodeVec rsigF(sb);
  for (unsigned i = 0; i < sb; i++)
    rsigF[i] = nf->CreateNode(ITE, carry, rr[i + 1], rr[i]);
  BBNodeVec beF = beAfter;
  BBPlus2(beF, BBfill(E, nf->getFalse()), carry);

  // Pack the finite result. A significand without its leading 1 is
  // subnormal: exponent field 0 (beAfter is 1 there, the same scale).
  const BBNode isNormRes = rsigF[sb - 1];
  BBNodeVec res(w);
  for (unsigned i = 0; i < sb - 1; i++)
    res[i] = rsigF[i];
  for (unsigned i = 0; i < eb; i++)
    res[sb - 1 + i] = nf->CreateNode(AND, isNormRes, beF[i]);
  res[w - 1] = sgn;

  if (resultKnownFinite)
  {
    ++fpNativeFiniteRoundPacks;
    return res;
  }

  // Overflow, checked after rounding; saturation is mode- and sign-
  // dependent: to infinity for the nearest modes, to the largest finite
  // value for RTZ and for the directed mode pointing away from the sign.
  const BBNode ovf =
      nf->CreateNode(NOT, BBBVLE(beF, constVec(maxbe, E), true /*signed*/));
  BBNodeVec infCases;
  infCases.push_back(rne);
  infCases.push_back(rna);
  infCases.push_back(nf->CreateNode(AND, rtp, nf->CreateNode(NOT, sgn)));
  infCases.push_back(nf->CreateNode(AND, rtn, sgn));
  const BBNode roundsToInf = nf->CreateNode(OR, infCases);

  BBNodeVec inf(w, nf->getFalse());
  BBNodeVec maxFin(w, nf->getFalse());
  for (unsigned i = 0; i < eb; i++)
    inf[sb - 1 + i] = nf->getTrue();
  for (unsigned i = 0; i < sb - 1; i++)
    maxFin[i] = nf->getTrue();
  for (unsigned i = 1; i < eb; i++)
    maxFin[sb - 1 + i] = nf->getTrue(); // maxbe = 2^eb - 2: LSB clear
  inf[w - 1] = sgn;
  maxFin[w - 1] = sgn;

  return BBITE(ovf, BBITE(roundsToInf, inf, maxFin), res);
}

// Bit-blasted fp.mul over packed IEEE-754 operands: a hand-written
// unpack / multiply / round / pack circuit, no SymFPU. FloatBlast leaves
// FP_MUL in place under a surviving native predicate when
// --bb.fp-native-arith is on and both float operands are packed views.
//
// Shape (fields as in BBcompareFP: significand in bits [0, sb-2], exponent
// in [sb-1, w-2], sign at w-1):
//   1. Normalise each operand to a significand with an explicit leading 1
//      (subnormals shift up by their leading-zero count) and an unbiased
//      exponent in eb+2 signed bits -- wide enough for every intermediate
//      sum this circuit forms.
//   2. Multiply the sb-bit significands into 2sb bits (school multiplier;
//      the partial-product array is the irreducible core).
//   3. Normalise the product (top bit at 2sb-1 or 2sb-2), extracting
//      guard and sticky.
//   4. If the biased exponent fell to 0 or below, shift right into the
//      subnormal range, accumulating sticky; a shift past the significand
//      leaves all-sticky (which rounding may still pull up to the minimum
//      subnormal, e.g. under RTP).
//   5. Round per mode -- the increment's carry renormalises, and a
//      subnormal that rounds up to the hidden bit becomes the smallest
//      normal with the same biased exponent.
//   6. Overflow saturates per mode: RNE/RNA to infinity, RTZ to the
//      largest finite, RTP/RTN to whichever of the two matches the sign.
//   7. Specials are muxed over the computed result: NaN (any NaN operand,
//      or zero times infinity), then infinity, then zero. The NaN produced
//      is the canonical quiet NaN (positive, significand MSB set), the
//      same value the SymFPU path packs.
BBNodeVec BitBlaster::BBfpMul(const ASTNode& term, BBNodeSet& support)
{
  assert(term.GetKind() == FP_MUL);
  assert(term.Degree() == 3);

  const SourceSort sort = term.GetSourceSort();
  assert(sort.kind() == SourceSort::Kind::FloatingPoint);
  const unsigned sb = sort.significandWidth();
  const unsigned w = sort.exponentWidth() + sb;
  const unsigned eb = w - sb;
  assert(sb >= 2 && eb >= 2);
  const unsigned bias = (1u << (eb - 1)) - 1;
  const unsigned E = BBfpExpWidth(eb, sb);

  const BBNodeVec rm = BBTerm(term[0], support); // one-hot, see
                                                 // rounding_modes.h
  const BBNodeVec pa = BBTerm(term[1], support);
  const BBNodeVec pb = BBTerm(term[2], support);
  assert(pa.size() == w && pb.size() == w);

  const bool aKnownZero = fpNativeKnownZeroMagnitude(term[1]);
  const bool bKnownZero = fpNativeKnownZeroMagnitude(term[2]);
  const bool aFinite = fpNativeKnownFinite(term[1]);
  const bool bFinite = fpNativeKnownFinite(term[2]);
  const bool knownSignEnabled = uf->fp_native_known_sign;
  const bool aNonnegative =
      knownSignEnabled && fpNativeKnownFiniteNonnegative(term[1]);
  const bool aNonpositive =
      knownSignEnabled && fpNativeKnownFiniteNonpositive(term[1]);
  const bool bNonnegative =
      knownSignEnabled && fpNativeKnownFiniteNonnegative(term[2]);
  const bool bNonpositive =
      knownSignEnabled && fpNativeKnownFiniteNonpositive(term[2]);
  const bool knownSignOperands =
      (aNonnegative || aNonpositive) && (bNonnegative || bNonpositive);
  // A term proved both nonnegative and nonpositive is semantically zero. Its
  // core sign is immaterial because the exact packed zero sign is muxed below.
  const bool knownNegativeProduct =
      knownSignOperands &&
      ((aNonpositive && !aNonnegative) !=
       (bNonpositive && !bNonnegative));
  fpNativeFiniteArithOperands += static_cast<size_t>(aFinite) +
                                 static_cast<size_t>(bFinite);

  // zero * finite is an exact signed zero in every rounding mode. Requiring
  // the other operand to be finite is essential: zero * infinity and zero *
  // NaN must still take the invalid/NaN special paths below.
  if ((aKnownZero && bFinite) || (bKnownZero && aFinite))
  {
    ++fpNativeZeroMulFastPaths;
    BBNodeVec zero(w, nf->getFalse());
    zero[w - 1] = nf->CreateNode(XOR, pa[w - 1], pb[w - 1]);
    return zero;
  }

  if (knownSignOperands)
  {
    assert(aFinite && bFinite);
    if (knownNegativeProduct)
      ++fpNativeKnownNegativeMulPaths;
    else
      ++fpNativeKnownPositiveMulPaths;
  }

  auto constVec = [&](unsigned value, unsigned width) {
    BBNodeVec c(width);
    for (unsigned i = 0; i < width; i++)
      c[i] = ((value >> i) & 1) ? nf->getTrue() : nf->getFalse();
    return c;
  };
  auto zext = [&](const BBNodeVec& v, unsigned width) {
    BBNodeVec c = v;
    while (c.size() < width)
      c.push_back(nf->getFalse());
    return c;
  };

  // The un-normalised field split (see BBfpUnpack): consuming a packed
  // operand -- a leaf or a chained native result -- is only wiring and
  // four classification gates; normalisation is deferred to the product.
  const FpOperand a =
      BBfpUnpack(pa, sb, w, E, support, aFinite, aKnownZero);
  const FpOperand b =
      BBfpUnpack(pb, sb, w, E, support, bFinite, bKnownZero);

  // A semantic-sign fact does not fix the packed sign of zero. Raw operand
  // signs therefore select an exact zero result, while every nonzero result
  // rounds with the constant product sign proved above.
  const BBNode zeroSign = nf->CreateNode(XOR, a.sign, b.sign);
  const BBNode roundSign = knownSignOperands
                               ? (knownNegativeProduct ? nf->getTrue()
                                                       : nf->getFalse())
                               : zeroSign;

  // Significand product, 2sb bits, of the raw hidden-bit significands --
  // in [0, 4) counting subnormal fractions.
  BBNodeVec prod = BBfill(2 * sb, nf->getFalse());
  for (unsigned i = 0; i < sb; i++)
  {
    const BBNodeVec row = BBAndBit(b.msig, a.msig[i]);
    BBNodeVec addend = BBfill(2 * sb, nf->getFalse());
    for (unsigned j = 0; j < sb; j++)
      addend[i + j] = row[j];
    BBPlus2(prod, addend, nf->getFalse());
  }

  // One normalisation for the whole product: shift its leading 1 to the
  // top and fold the shift count into the exponent. This also absorbs the
  // subnormal operands' missing normalisation (their leading zeros simply
  // appear here). A zero product leaves garbage, muxed out by the
  // specials below (zero operands) or rounded from all-sticky=0 to zero.
  const unsigned lw2 = [](unsigned x) { // bits to count up to x
    unsigned bb = 1;
    while ((1u << bb) <= x)
      bb++;
    return bb;
  }(2 * sb);
  const BBNodeVec ell = BBfpCLZ(prod, lw2);
  const BBNodeVec pn = BBfpShiftLeft(prod, ell);
  BBNodeVec rsig(pn.begin() + sb, pn.end()); // top sb bits: 1.frac
  BBNode guard = pn[sb - 1];
  auto orVec = [&](BBNodeVec v) {
    return v.empty() ? nf->getFalse() : nf->CreateNode(OR, v);
  };
  BBNodeVec lowBits(pn.begin(), pn.begin() + (sb - 1));
  BBNode sticky = orVec(lowBits);

  // Biased result exponent: eUnbA + eUnbB + bias + 1 - leading zeros.
  BBNodeVec be = a.eUnb;
  BBPlus2(be, b.eUnb, nf->getFalse());
  BBPlus2(be, constVec(bias, E), nf->getTrue());
  BBNodeVec ellE = zext(ell, E);
  BBSub(be, ellE, support);

  // A top-level magnitude constraint on this product is useful to consumers,
  // but must not erase the producer relation that enforces the constraint.
  // In particular, do not simplify this product's overflow path merely by
  // assuming its own output is zero; the full product circuit remains the
  // witness that restricts its operands.
  const bool directlyConstrainedZero =
      fpNativeZeroMagnitudeFacts.find(term) !=
      fpNativeZeroMagnitudeFacts.end();
  const bool resultFinite =
      !directlyConstrainedZero && fpNativeKnownFinite(term);
  BBNodeVec res = BBfpRoundPack(rm, roundSign, rsig, guard, sticky, be, sb, eb,
                                support, resultFinite);

  // Specials, outermost first: NaN (any NaN operand, or zero times
  // infinity), then infinity, then zero.
  auto packSpecial = [&](bool isnan, bool isinf) {
    BBNodeVec s(w, nf->getFalse());
    if (isnan || isinf)
      for (unsigned i = 0; i < eb; i++)
        s[sb - 1 + i] = nf->getTrue();
    if (isnan)
      s[sb - 2] = nf->getTrue(); // canonical quiet NaN, positive
    else
      s[w - 1] = zeroSign;
    return s;
  };
  BBNodeVec nanCases;
  if (!aFinite)
    nanCases.push_back(a.isNaN);
  if (!bFinite)
    nanCases.push_back(b.isNaN);
  if (!bFinite)
    nanCases.push_back(nf->CreateNode(AND, a.isZero, b.isInf));
  if (!aFinite)
    nanCases.push_back(nf->CreateNode(AND, a.isInf, b.isZero));
  const BBNode anyNaN =
      nanCases.empty() ? nf->getFalse() : nf->CreateNode(OR, nanCases);
  const BBNode anyInf =
      aFinite ? (bFinite ? nf->getFalse() : b.isInf)
              : (bFinite ? a.isInf : nf->CreateNode(OR, a.isInf, b.isInf));
  const BBNode anyZero = nf->CreateNode(OR, a.isZero, b.isZero);

  res = BBITE(anyZero, packSpecial(false, false), res);
  if (!(aFinite && bFinite))
  {
    res = BBITE(anyInf, packSpecial(false, true), res);
    res = BBITE(anyNaN, packSpecial(true, false), res);
  }
  return res;
}

// Bit-blasted fp.add over packed IEEE-754 operands, under the same flag
// and gate as BBfpMul. Single wide exact datapath:
//   1. Split both operands un-normalised (BBfpUnpack) and order them by
//      (exponent, significand) -- with un-normalised significands that
//      lexicographic order IS magnitude order, because any operand whose
//      exponent exceeds the minimum is normal.
//   2. Align the smaller significand by the exponent difference in a
//      W = 2sb+4 bit frame, wide enough that alignment down to the clamp
//      loses only bits below the frame, collected as a sticky flag.
//   3. One adder does both effective operations: adding the aligned
//      significand, or its complement with a borrow that also accounts
//      for the sticky tail (the true difference is then the computed
//      integer plus a nonzero fraction, which the final sticky keeps).
//      The swap guarantees the difference is non-negative.
//   4. One leading-zero normalisation covers both the 1-bit carry of an
//      addition and arbitrary cancellation of a subtraction; the shift
//      count folds into the exponent exactly as in the multiplier.
//   5. The shared rounder/packer finishes; zero operands need no special
//      case (adding a zero significand is exact), only the sign of an
//      EXACT zero result is mode-dependent: -0 under RTN, else +0.
//   6. Specials: NaN operands and infinity minus infinity give NaN;
//      otherwise any infinite operand's infinity wins, keeping its sign.
//
// fp.isZero needs much less than this packed result. Every finite value in a
// binary IEEE format is an integer multiple of that format's minimum
// subnormal. The exact sum of two finite operands is therefore another such
// multiple. If it is nonzero but smaller than the minimum normal it is itself
// an exactly representable subnormal; if it is at least the minimum normal,
// no rounding mode can turn it into zero. Thus fp.add rounds to either signed
// zero iff the exact real sum is zero. For nonzero operands that means equal
// packed magnitudes and opposite signs; every combination of signed zeros is
// also zero. NaNs and infinities are excluded explicitly.
BBNode BitBlaster::BBfpAddIsZero(const ASTNode& term, BBNodeSet& support)
{
  assert(term.GetKind() == FP_ADD);
  assert(term.Degree() == 3);

  const SourceSort sort = term.GetSourceSort();
  assert(sort.kind() == SourceSort::Kind::FloatingPoint);
  const unsigned sb = sort.significandWidth();
  const unsigned w = sort.packedWidth();
  const unsigned eb = sort.exponentWidth();
  (void)eb;
  assert(sb >= 2 && eb >= 2 && w == sb + eb);

  const bool aKnownZero = fpNativeKnownZeroMagnitude(term[1]);
  const bool bKnownZero = fpNativeKnownZeroMagnitude(term[2]);
  if (aKnownZero && bKnownZero)
    return nf->getTrue();

  if (aKnownZero || bKnownZero)
  {
    const BBNodeVec other = BBTerm(aKnownZero ? term[2] : term[1], support);
    return BBfpIsZero(other, w);
  }

  const BBNodeVec pa = BBTerm(term[1], support);
  const BBNodeVec pb = BBTerm(term[2], support);
  assert(pa.size() == w && pb.size() == w);

  BBNodeVec aMagnitude(pa.begin(), pa.begin() + (w - 1));
  const BBNodeVec bMagnitude(pb.begin(), pb.begin() + (w - 1));
  const BBNode sameMagnitude = BBEQ(aMagnitude, bMagnitude);
  const BBNode oppositeSigns = nf->CreateNode(XOR, pa[w - 1], pb[w - 1]);
  // Under sameMagnitude, testing one side for magnitude zero proves that
  // both operands are signed zeros.
  const BBNode bothZero = nf->CreateNode(NOR, aMagnitude);
  const BBNode exactZero = nf->CreateNode(
      AND, sameMagnitude, nf->CreateNode(OR, oppositeSigns, bothZero));

  const bool aFinite = fpNativeKnownFinite(term[1]);
  const bool bFinite = fpNativeKnownFinite(term[2]);
  if (aFinite && bFinite)
    return exactZero;

  auto finite = [&](const BBNodeVec& p) {
    BBNodeVec exponent(p.begin() + (sb - 1), p.begin() + (w - 1));
    return nf->CreateNode(NOT, nf->CreateNode(AND, exponent));
  };
  if (aFinite)
    return nf->CreateNode(AND, finite(pb), exactZero);
  if (bFinite)
    return nf->CreateNode(AND, finite(pa), exactZero);
  return nf->CreateNode(AND, finite(pa), finite(pb), exactZero);
}

BBNodeVec BitBlaster::BBfpAdd(const ASTNode& term, BBNodeSet& support)
{
  assert(term.GetKind() == FP_ADD);
  assert(term.Degree() == 3);

  const SourceSort sort = term.GetSourceSort();
  assert(sort.kind() == SourceSort::Kind::FloatingPoint);
  const unsigned sb = sort.significandWidth();
  const unsigned w = sort.exponentWidth() + sb;
  const unsigned eb = w - sb;
  assert(sb >= 2 && eb >= 2);
  const unsigned bias = (1u << (eb - 1)) - 1;
  const unsigned E = BBfpExpWidth(eb, sb);

  const BBNodeVec rm = BBTerm(term[0], support);
  const BBNodeVec pa = BBTerm(term[1], support);
  const BBNodeVec pb = BBTerm(term[2], support);
  assert(pa.size() == w && pb.size() == w);

  const bool aKnownZero = fpNativeKnownZeroMagnitude(term[1]);
  const bool bKnownZero = fpNativeKnownZeroMagnitude(term[2]);
  const bool aFinite = fpNativeKnownFinite(term[1]);
  const bool bFinite = fpNativeKnownFinite(term[2]);
  const bool knownSignEnabled = uf->fp_native_known_sign;
  const bool aNonnegative =
      knownSignEnabled && fpNativeKnownFiniteNonnegative(term[1]);
  const bool aNonpositive =
      knownSignEnabled && fpNativeKnownFiniteNonpositive(term[1]);
  const bool bNonnegative =
      knownSignEnabled && fpNativeKnownFiniteNonnegative(term[2]);
  const bool bNonpositive =
      knownSignEnabled && fpNativeKnownFiniteNonpositive(term[2]);
  const bool sameNonnegative = aNonnegative && bNonnegative;
  const bool sameNonpositive = aNonpositive && bNonpositive;
  const bool knownSameSign = sameNonnegative || sameNonpositive;
  // If both sides hold, both operands are semantic zeros; choose a positive
  // core and let the explicit zero-sign mux below select the packed result.
  const bool knownNegativeSum = sameNonpositive && !sameNonnegative;
  fpNativeFiniteArithOperands += static_cast<size_t>(aFinite) +
                                 static_cast<size_t>(bFinite);

  // A signed zero is an additive identity for every nonzero finite value.
  // When the other operand is also zero, IEEE-754 chooses the common sign,
  // or -0 only under RTN when the signs differ.
  if ((aKnownZero && bFinite) || (bKnownZero && aFinite))
  {
    ++fpNativeZeroAddFastPaths;
    const bool zeroOnLeft = aKnownZero;
    const BBNodeVec& zeroBits = zeroOnLeft ? pa : pb;
    const BBNodeVec& otherBits = zeroOnLeft ? pb : pa;
    const bool otherKnownZero = zeroOnLeft ? bKnownZero : aKnownZero;
    const BBNode otherZero = otherKnownZero
                                 ? nf->getTrue()
                                 : BBfpIsZero(otherBits, w);
    const BBNode oppositeSigns = nf->CreateNode(
        XOR, zeroBits[w - 1], otherBits[w - 1]);
    const BBNode bothNegative = nf->CreateNode(
        AND, zeroBits[w - 1], otherBits[w - 1]);
    const BBNode zeroSign = nf->CreateNode(
        OR, bothNegative,
        nf->CreateNode(AND, oppositeSigns, rm[2]));

    BBNodeVec result = otherKnownZero
                           ? BBfill(w, nf->getFalse())
                           : otherBits;
    result[w - 1] =
        nf->CreateNode(ITE, otherZero, zeroSign, otherBits[w - 1]);
    return result;
  }

  if (knownSameSign)
  {
    assert(aFinite && bFinite);
    if (knownNegativeSum)
      ++fpNativeKnownNegativeAddPaths;
    else
      ++fpNativeKnownPositiveAddPaths;
  }

  auto constVec = [&](unsigned value, unsigned width) {
    BBNodeVec c(width);
    for (unsigned i = 0; i < width; i++)
      c[i] = ((value >> i) & 1) ? nf->getTrue() : nf->getFalse();
    return c;
  };
  auto zext = [&](const BBNodeVec& v, unsigned width) {
    BBNodeVec c = v;
    while (c.size() < width)
      c.push_back(nf->getFalse());
    return c;
  };

  const FpOperand a =
      BBfpUnpack(pa, sb, w, E, support, aFinite, aKnownZero);
  const FpOperand b =
      BBfpUnpack(pb, sb, w, E, support, bFinite, bKnownZero);
  const BBNode effSub = knownSameSign
                            ? nf->getFalse()
                            : nf->CreateNode(XOR, a.sign, b.sign);

  // General addition orders by magnitude: (eUnb, msig)
  // lexicographically. For finite operands with the same known semantic sign
  // the operation is always magnitude addition; when exponents tie either
  // operand may be aligned, so the significand comparison and cancellation
  // logic are unnecessary.
  const BBNode eLess = BBBVLE(a.eUnb, b.eUnb, true /*signed*/, true);
  BBNode swap = eLess;
  if (!knownSameSign)
  {
    const BBNode eEq = BBEQ(a.eUnb, b.eUnb);
    const BBNode mLess = BBBVLE(a.msig, b.msig, false, true);
    swap = nf->CreateNode(OR, eLess, nf->CreateNode(AND, eEq, mLess));
  }
  const BBNodeVec msigBig = BBITE(swap, b.msig, a.msig);
  const BBNodeVec msigSmall = BBITE(swap, a.msig, b.msig);
  const BBNodeVec eBig = BBITE(swap, b.eUnb, a.eUnb);
  const BBNodeVec eSmall = BBITE(swap, a.eUnb, b.eUnb);
  const BBNode signBig = knownSameSign
                             ? (knownNegativeSum ? nf->getTrue()
                                                 : nf->getFalse())
                             : nf->CreateNode(ITE, swap, b.sign, a.sign);

  // Alignment distance, clamped into the frame.
  const unsigned dmaxA = sb + 3;
  const unsigned W = sb + dmaxA + 1; // headroom bit for the addition carry
  BBNodeVec dist = eBig;
  BBSub(dist, eSmall, support); // >= 0
  const BBNode distFar = nf->CreateNode(
      NOT, BBBVLE(dist, constVec(dmaxA, E), true /*signed*/));
  const unsigned dwA = [](unsigned x) {
    unsigned bb = 1;
    while ((1u << bb) <= x)
      bb++;
    return bb;
  }(dmaxA);
  BBNodeVec dv(dwA);
  for (unsigned i = 0; i < dwA; i++)
    dv[i] = nf->CreateNode(ITE, distFar,
                           ((dmaxA >> i) & 1) ? nf->getTrue()
                                              : nf->getFalse(),
                           dist[i]);

  // Big at [dmaxA, W-2]; small likewise, then shifted right, everything
  // below the frame ORed into stickyTail.
  BBNodeVec big(W, nf->getFalse());
  BBNodeVec small(W, nf->getFalse());
  for (unsigned i = 0; i < sb; i++)
  {
    big[dmaxA + i] = msigBig[i];
    small[dmaxA + i] = msigSmall[i];
  }
  BBNode stickyTail = nf->getFalse();
  small = BBfpShiftRightSticky(small, dv, stickyTail);

  // One adder for both effective operations. Subtracting also owes the
  // sticky tail: the true small operand is (aligned + fraction), so the
  // true difference is (big - aligned - 1) plus a nonzero fraction; the
  // borrowed carry-in and the kept sticky express exactly that.
  BBNodeVec addend = small;
  BBNode cin = nf->getFalse();
  if (!knownSameSign)
  {
    for (unsigned i = 0; i < W; i++)
      addend[i] = nf->CreateNode(XOR, small[i], effSub);
    cin = nf->CreateNode(AND, effSub,
                         nf->CreateNode(NOT, stickyTail));
  }
  BBNodeVec sum = big;
  BBPlus2(sum, addend, cin);

  BBNodeVec rsig;
  BBNode guard = nf->getFalse();
  BBNode sticky = nf->getFalse();
  BBNodeVec be;
  if (knownSameSign)
  {
    // No cancellation means no arbitrary left normalisation. If the larger
    // scale is normal, the leading bit either stays at W-2 or carries once to
    // W-1. If both operands are subnormal (or one is the minimum normal at
    // the shared exponent), their unshifted sum can be packed directly at
    // biased exponent 1; a missing hidden bit then denotes a subnormal.
    const BBNode carry = sum[W - 1];
    const BBNodeVec rsigNoCarry(sum.begin() + dmaxA,
                                sum.begin() + dmaxA + sb);
    const BBNodeVec rsigCarry(sum.begin() + dmaxA + 1, sum.end());
    rsig = BBITE(carry, rsigCarry, rsigNoCarry);
    guard = nf->CreateNode(ITE, carry, sum[dmaxA], sum[dmaxA - 1]);

    BBNodeVec lowNoCarry(sum.begin(), sum.begin() + dmaxA - 1);
    BBNodeVec lowCarry(sum.begin(), sum.begin() + dmaxA);
    const BBNode stickyNoCarry = nf->CreateNode(
        OR, nf->CreateNode(OR, lowNoCarry), stickyTail);
    const BBNode stickyCarry = nf->CreateNode(
        OR, nf->CreateNode(OR, lowCarry), stickyTail);
    sticky = nf->CreateNode(ITE, carry, stickyCarry, stickyNoCarry);

    // eBig is unbiased. The direct subnormal scale gives 1 here; a normal
    // carry increments the ordinary biased exponent once.
    be = eBig;
    BBPlus2(be, constVec(bias, E), carry);
  }
  else
  {
    // General opposite-sign addition needs a leading-zero count and shift for
    // arbitrary cancellation.
    const unsigned lwA = [](unsigned x) {
      unsigned bb = 1;
      while ((1u << bb) <= x)
        bb++;
      return bb;
    }(W);
    const BBNodeVec ell = BBfpCLZ(sum, lwA);
    const BBNodeVec sn = BBfpShiftLeft(sum, ell);
    rsig.assign(sn.begin() + (W - sb), sn.end());
    guard = sn[W - sb - 1];
    BBNodeVec lowBits(sn.begin(), sn.begin() + (W - sb - 1));
    sticky =
        nf->CreateNode(OR, nf->CreateNode(OR, lowBits), stickyTail);

    // be = eBig + bias + 1 - leading zeros, exactly as the multiplier.
    be = eBig;
    BBPlus2(be, constVec(bias, E), nf->getTrue());
    BBNodeVec ellE = zext(ell, E);
    BBSub(be, ellE, support);
  }

  BBNode bothZero = nf->getFalse();
  BBNode knownSignZeroSign = nf->getFalse();
  BBNode sgn = signBig;
  if (knownSameSign)
  {
    // Nonzero sums round with the proven constant sign. If both magnitudes
    // are zero, equal signs are retained and opposite signs choose -0 only
    // in RTN. The final result-sign mux keeps this exceptional packed sign
    // out of the rounding and overflow circuitry.
    bothZero = nf->CreateNode(AND, a.isZero, b.isZero);
    const BBNode oppositeSigns = nf->CreateNode(XOR, a.sign, b.sign);
    const BBNode bothNegative = nf->CreateNode(AND, a.sign, b.sign);
    knownSignZeroSign = nf->CreateNode(
        OR, bothNegative,
        nf->CreateNode(AND, oppositeSigns, rm[2]));
    sgn = knownNegativeSum ? nf->getTrue() : nf->getFalse();
  }
  else
  {
    // An EXACT zero result (cancellation of equal values -- only possible
    // unshifted, so the sticky tail is clear) is +0 in every mode but RTN.
    const BBNode sumZero = nf->CreateNode(NOR, sum);
    const BBNode exactZero = nf->CreateNode(
        AND, effSub, sumZero, nf->CreateNode(NOT, stickyTail));
    sgn = nf->CreateNode(ITE, exactZero, rm[2], signBig);
  }

  const bool resultFinite = fpNativeKnownFinite(term);
  BBNodeVec res =
      BBfpRoundPack(rm, sgn, rsig, guard, sticky, be, sb, eb, support,
                    resultFinite);

  if (knownSameSign)
    res[w - 1] = nf->CreateNode(ITE, bothZero, knownSignZeroSign, sgn);

  // Specials: NaN operands, or subtracting infinities; otherwise an
  // infinite operand's infinity, keeping that operand's sign.
  auto packSpecial = [&](bool isnan, const BBNode& sign) {
    BBNodeVec s(w, nf->getFalse());
    for (unsigned i = 0; i < eb; i++)
      s[sb - 1 + i] = nf->getTrue();
    if (isnan)
      s[sb - 2] = nf->getTrue(); // canonical quiet NaN, positive
    else
      s[w - 1] = sign;
    return s;
  };
  BBNodeVec nanCases;
  if (!aFinite)
    nanCases.push_back(a.isNaN);
  if (!bFinite)
    nanCases.push_back(b.isNaN);
  if (!aFinite && !bFinite)
    nanCases.push_back(nf->CreateNode(AND, a.isInf, b.isInf, effSub));
  const BBNode anyNaN =
      nanCases.empty() ? nf->getFalse() : nf->CreateNode(OR, nanCases);
  const BBNode anyInf =
      aFinite ? (bFinite ? nf->getFalse() : b.isInf)
              : (bFinite ? a.isInf : nf->CreateNode(OR, a.isInf, b.isInf));

  if (!(aFinite && bFinite))
  {
    const BBNode infSign = aFinite ? b.sign
                                   : (bFinite ? a.sign
                                              : nf->CreateNode(ITE, a.isInf,
                                                               a.sign,
                                                               b.sign));
    res = BBITE(anyInf, packSpecial(false, infSign), res);
    res = BBITE(anyNaN, packSpecial(true, nf->getFalse()), res);
  }
  return res;
}

// Bit-blasted float-to-float conversion (the four-child form of to_fp)
// over a packed operand, under the same flag and gate as BBfpMul/BBfpAdd.
// A conversion is re-rounding: normalise the source significand (one CLZ,
// absorbing subnormals), map it onto the target width -- low zeros when
// widening, guard and sticky when narrowing -- rebias, and let the shared
// rounder/packer handle the rest. Widening (both fields no narrower) is
// exact by construction: no guard, no sticky, and a target exponent range
// covering the source's, so the rounder never fires. The internal
// exponent covers BOTH formats' ranges: a double's subnormal scale is far
// outside a half's eb+2 bits.
BBNodeVec BitBlaster::BBfpToFp(const ASTNode& term, BBNodeSet& support)
{
  assert(term.GetKind() == FP_TOFP);
  assert(term.Degree() == 4);

  const SourceSort tsort = term.GetSourceSort();
  const SourceSort ssort = term[3].GetSourceSort();
  assert(tsort.kind() == SourceSort::Kind::FloatingPoint);
  assert(ssort.kind() == SourceSort::Kind::FloatingPoint);
  const unsigned sb1 = ssort.significandWidth();
  const unsigned eb1 = ssort.exponentWidth();
  const unsigned w1 = eb1 + sb1;
  const unsigned sb2 = tsort.significandWidth();
  const unsigned eb2 = tsort.exponentWidth();
  const unsigned w2 = eb2 + sb2;
  const unsigned bias1 = (1u << (eb1 - 1)) - 1;
  const unsigned bias2 = (1u << (eb2 - 1)) - 1;
  unsigned E = 2;
  while ((1u << (E - 1)) <= bias1 + sb1 + bias2 + 2 * sb2 + 4)
    E++;

  const BBNodeVec rm = BBTerm(term[2], support);
  const BBNodeVec p = BBTerm(term[3], support);
  assert(p.size() == w1);

  const bool sourceKnownZero = fpNativeKnownZeroMagnitude(term[3]);
  if (sourceKnownZero)
  {
    ++fpNativeZeroToFpFastPaths;
    BBNodeVec zero(w2, nf->getFalse());
    zero[w2 - 1] = p[w1 - 1];
    return zero;
  }

  auto constVec = [&](unsigned value, unsigned width) {
    BBNodeVec c(width);
    for (unsigned i = 0; i < width; i++)
      c[i] = ((value >> i) & 1) ? nf->getTrue() : nf->getFalse();
    return c;
  };
  auto zext = [&](const BBNodeVec& v, unsigned width) {
    BBNodeVec c = v;
    while (c.size() < width)
      c.push_back(nf->getFalse());
    return c;
  };

  const bool sourceFinite = fpNativeKnownFinite(term[3]);
  const FpOperand s =
      BBfpUnpack(p, sb1, w1, E, support, sourceFinite, sourceKnownZero);

  // Normalise the source significand; the count also lets a subnormal
  // source become normal in a wider target range.
  const unsigned lw1 = [](unsigned x) {
    unsigned bb = 1;
    while ((1u << bb) <= x)
      bb++;
    return bb;
  }(sb1);
  const BBNodeVec clz = BBfpCLZ(s.msig, lw1);
  const BBNodeVec sn = BBfpShiftLeft(s.msig, clz);

  // Map onto the target significand width.
  BBNodeVec rsig(sb2);
  BBNode guard = nf->getFalse();
  BBNode sticky = nf->getFalse();
  if (sb2 >= sb1)
  {
    for (unsigned i = 0; i < sb2 - sb1; i++)
      rsig[i] = nf->getFalse();
    for (unsigned i = 0; i < sb1; i++)
      rsig[sb2 - sb1 + i] = sn[i];
  }
  else
  {
    const unsigned cut = sb1 - sb2;
    for (unsigned i = 0; i < sb2; i++)
      rsig[i] = sn[cut + i];
    guard = sn[cut - 1];
    BBNodeVec low(sn.begin(), sn.begin() + (cut - 1));
    sticky = low.empty() ? nf->getFalse() : nf->CreateNode(OR, low);
  }

  // Rebias: be = eUnb - leading zeros + bias2.
  BBNodeVec be = s.eUnb;
  BBNodeVec clzE = zext(clz, E);
  BBSub(be, clzE, support);
  BBPlus2(be, constVec(bias2, E), nf->getFalse());

  BBNodeVec res =
      BBfpRoundPack(rm, s.sign, rsig, guard, sticky, be, sb2, eb2, support);

  // Specials map to the target format's; a zero operand must be muxed
  // (its garbage leading-zero count would otherwise wander the exponent).
  auto packSpecial = [&](bool isnan, bool isinf) {
    BBNodeVec sp(w2, nf->getFalse());
    if (isnan || isinf)
      for (unsigned i = 0; i < eb2; i++)
        sp[sb2 - 1 + i] = nf->getTrue();
    if (isnan)
      sp[sb2 - 2] = nf->getTrue(); // canonical quiet NaN, positive
    else
      sp[w2 - 1] = s.sign;
    return sp;
  };
  res = BBITE(s.isZero, packSpecial(false, false), res);
  res = BBITE(s.isInf, packSpecial(false, true), res);
  res = BBITE(s.isNaN, packSpecial(true, false), res);
  return res;
}

// Return bit-blasted form for the overflow predicates BVUADDO, BVSADDO,
// BVUMULO, BVSMULO. Each returns a single boolean.
BBNode BitBlaster::BBOverflow(const ASTNode& form,
                              BBNodeSet& support)
{
  const Kind k = form.GetKind();
  const unsigned w = form[0].GetValueWidth();
  assert(w > 0);

  switch (k)
  {
    case BVUADDO:
    {
      // Overflow == carry-out of the unsigned addition. Zero-extend both
      // operands by one bit, add, and return the top bit of the sum.
      BBNodeVec l = BBTerm(form[0], support);
      BBNodeVec r = BBTerm(form[1], support);
      l.push_back(nf->getFalse());
      r.push_back(nf->getFalse());
      BBPlus2(l, r, nf->getFalse());
      return l[w];
    }
    case BVSADDO:
    {
      // Sign-extend both operands by one bit, add, and check whether the two
      // top bits of the (w+1)-bit sum disagree.
      BBNodeVec l = BBTerm(form[0], support);
      BBNodeVec r = BBTerm(form[1], support);
      l.push_back(l[w - 1]);
      r.push_back(r[w - 1]);
      BBPlus2(l, r, nf->getFalse());
      return nf->CreateNode(XOR, l[w], l[w - 1]);
    }
    case BVUSUBO:
    {
      // Overflow (borrow) of the unsigned subtraction. Zero-extend both
      // operands by one bit, subtract, and return the top bit: it is set iff
      // the true difference is negative, i.e. iff form[0] <u form[1].
      BBNodeVec l = BBTerm(form[0], support);
      BBNodeVec r = BBTerm(form[1], support);
      l.push_back(nf->getFalse());
      r.push_back(nf->getFalse());
      BBSub(l, r, support);
      return l[w];
    }
    case BVSSUBO:
    {
      // Sign-extend both operands by one bit, subtract, and check whether the
      // two top bits of the (w+1)-bit difference disagree.
      BBNodeVec l = BBTerm(form[0], support);
      BBNodeVec r = BBTerm(form[1], support);
      l.push_back(l[w - 1]);
      r.push_back(r[w - 1]);
      BBSub(l, r, support);
      return nf->CreateNode(XOR, l[w], l[w - 1]);
    }
    case BVUMULO:
    case BVSMULO:
    {
      // Build the exact 2w-bit product (via zero/sign-extended operands) and
      // reuse the existing multiplier, then inspect the high bits.
      const Kind ext = (k == BVUMULO) ? BVZX : BVSX;
      const ASTNode widthConst = ASTNF->CreateBVConst(32, 2 * w);
      const ASTNode xE = ASTNF->CreateTerm(ext, 2 * w, form[0], widthConst);
      const ASTNode yE = ASTNF->CreateTerm(ext, 2 * w, form[1], widthConst);
      const ASTNode prod = ASTNF->CreateTerm(BVMULT, 2 * w, xE, yE);
      const BBNodeVec p = BBTerm(prod, support);

      if (k == BVUMULO)
      {
        // Overflow iff any high bit is set.
        BBNodeVec high(p.begin() + w, p.end());
        return nf->CreateNode(OR, high);
      }
      else
      {
        // Overflow iff the product is not the sign-extension of its low w bits,
        // i.e. some bit above w-1 differs from the sign bit p[w-1].
        BBNodeVec diffs;
        diffs.reserve(w);
        for (unsigned i = w; i < 2 * w; i++)
          diffs.push_back(nf->CreateNode(XOR, p[i], p[w - 1]));
        return nf->CreateNode(OR, diffs);
      }
    }
    default:
      cerr << "BBOverflow: Illegal kind" << form << endl;
      FatalError("", form);
  }
}

// return a vector with n copies of fillval
BBNodeVec BitBlaster::BBfill(unsigned int width,
                             BBNode fillval)
{
  BBNodeVec zvec(width, fillval);
  return zvec;
}

BBNode BitBlaster::BBEQ(const BBNodeVec& left,
                        const BBNodeVec& right)
{
  BBNodeVec andvec;
  andvec.reserve(left.size());
  BBNodeVec::const_iterator lit = left.begin();
  const BBNodeVec::const_iterator litend = left.end();
  BBNodeVec::const_iterator rit = right.begin();

  if (left.size() > 1)
  {
    for (; lit != litend; lit++, rit++)
    {
      BBNode biteq = nf->CreateNode(IFF, *lit, *rit);
      // fast path exit
      if (biteq == nf->getFalse())
      {
        return nf->getFalse();
      }
      else
      {
        andvec.push_back(biteq);
      }
    }
    BBNode n = nf->CreateNode(AND, andvec);
    return n;
  }
  else
    return nf->CreateNode(IFF, *lit, *rit);
}

std::ostream& operator<<(std::ostream& output, const BBNodeAIG& /*h*/)
{
  FatalError("This isn't implemented  yet sorry;");
  return output;
}

} // stp namespace
