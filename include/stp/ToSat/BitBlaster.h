/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
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

#ifndef BITBLASTNEW_H
#define BITBLASTNEW_H

#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/constantBitP/MultiplicationStats.h"
#include <cassert>
#include <cmath>
#include <list>
#include <map>

namespace simplifier
{
namespace constantBitP
{
class ConstantBitPropagation;
class FixedBits;
}
}

namespace stp
{

using std::list;
using simplifier::constantBitP::MultiplicationStats;

class Simplifier;
class ASTNode;

using ASTVec = vector<ASTNode>;

template <class BBNode, class BBNodeManagerT> 
class BitBlaster 
{
  using BBNodeVec = vector<BBNode>;
  using BBNodeSet = std::unordered_set<BBNode>;

  BBNode BBTrue, BBFalse;

  // Memo table for bit blasted terms.  If a node has already been
  // bitblasted, it is mapped to a vector of Boolean formulas for
  // the
  std::unordered_map<ASTNode, BBNodeVec, ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual> BBTermMemo;

  // Memo table for bit blasted formulas.  If a node has already
  // been bitblasted, it is mapped to a node representing the
  // bitblasted equivalent
  std::unordered_map<ASTNode, BBNode, ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual> BBFormMemo;

  // Get vector of Boolean formulas for sum of two
  // vectors of Boolean formulas
  void BBPlus2(BBNodeVec& sum, const BBNodeVec& y, BBNode cin);

  // Increment
  BBNodeVec BBInc(const BBNodeVec& x);

  // Add one bit to a vector of bits.
  BBNodeVec BBAddOneBit(const BBNodeVec& x, BBNode cin);

  // Bitwise complement
  BBNodeVec BBNeg(const BBNodeVec& x);

  // Unary minus
  BBNodeVec BBUminus(const BBNodeVec& x);

  // Multiply.
  BBNodeVec BBMult(const BBNodeVec& x, const BBNodeVec& y,
                        BBNodeSet& support, const ASTNode& n);
  void mult_allPairs(const BBNodeVec& x, const BBNodeVec& y,
                     BBNodeSet& support, vector<list<BBNode>>& products);
  void mult_Booth(const BBNodeVec& x_i, const BBNodeVec& y_i,
                  BBNodeSet& support, const stp::ASTNode& xN,
                  const stp::ASTNode& yN, vector<list<BBNode>>& products,
                  const ASTNode& n);
  BBNodeVec mult_normal(const BBNodeVec& x, const BBNodeVec& y,
                             BBNodeSet& support, const ASTNode& n);

  BBNodeVec batcher(const BBNodeVec& in);
  BBNodeVec mergeSorted(const BBNodeVec& in1,
                             const BBNodeVec& in2);
  BBNodeVec compareOddEven(const BBNodeVec& in);

  void setColumnsToZero(vector<list<BBNode>>& products, BBNodeSet& support,
                        const ASTNode& n);

  void sortingNetworkAdd(BBNodeSet& support, list<BBNode>& current,
                         BBNodeVec& currentSorted,
                         BBNodeVec& priorSorted);

  BBNodeVec v6(vector<list<BBNode>>& products, BBNodeSet& support,
                    const ASTNode& n);
  BBNodeVec v7(vector<list<BBNode>>& products, BBNodeSet& support,
                    const ASTNode& n);
  BBNodeVec v8(vector<list<BBNode>>& products, BBNodeSet& support,
                    const ASTNode& n);
  BBNodeVec v9(vector<list<BBNode>>& products, BBNodeSet& support,
                    const ASTNode& n);
  BBNodeVec v13(vector<list<BBNode>>& products, BBNodeSet& support,
                     const ASTNode& n);

  BBNodeVec multWithBounds(const ASTNode& n,
                                vector<list<BBNode>>& products,
                                BBNodeSet& toConjoinToTop);
  bool statsFound(const ASTNode& n);

  void mult_BubbleSorterWithBounds(BBNodeSet& support,
                                   list<BBNode>& currentColumn,
                                   BBNodeVec& currentSorted,
                                   BBNodeVec& priorSorted,
                                   const int minTrue = 0,
                                   const int maxTrue = ((unsigned)~0) >> 1);

  void buildAdditionNetworkResult(list<BBNode>& from, list<BBNode>& to,
                                  BBNodeSet& support, const bool top,
                                  const bool empty);
  BBNodeVec buildAdditionNetworkResult(vector<list<BBNode>>& products,
                                            BBNodeSet& support,
                                            const ASTNode& n);

  BBNodeVec BBAndBit(const BBNodeVec& y, BBNode b);

  MultiplicationStats* getMS(const ASTNode& n, int& highestZero);

  /////////// The end of the multiplication stuff..

  void checkFixed(const BBNodeVec& v, const ASTNode& n);

  // AND each bit of vector y with single bit b and return the result.
  // (used in BBMult)
  // BBNodeVec BBAndBit(const BBNodeVec& y, ASTNode b);

  // Returns BBNodeVec for result - y.  This destroys "result".
  void BBSub(BBNodeVec& result, const BBNodeVec& y,
             BBNodeSet& support);

  // build ITE's (ITE cond then[i] else[i]) for each i.
  BBNodeVec BBITE(const BBNode& cond, const BBNodeVec& thn,
                       const BBNodeVec& els);

  // Build a vector of zeros.
  BBNodeVec BBfill(unsigned int width, BBNode fillval);

  // build an EQ formula
  BBNode BBEQ(const BBNodeVec& left, const BBNodeVec& right);

  // This implements a variant of binary long division.
  // q and r are "out" parameters.  rwidth puts a bound on the
  // recursion depth.   Unsigned only, for now.

  void BBDivMod(const BBNodeVec& y, const BBNodeVec& x,
                BBNodeVec& q, BBNodeVec& r, unsigned int rwidth,
                BBNodeSet& support);

  // Return formula for majority function of three formulas.
  BBNode Majority(const BBNode& a, const BBNode& b, const BBNode& c);

  // Internal bit blasting routines.
  BBNode BBBVLE(const BBNodeVec& x, const BBNodeVec& y,
                bool is_signed, bool is_bvlt = false);
  BBNode BBBVLE_variant1(const BBNodeVec& x, const BBNodeVec& y,
                         bool is_signed, bool is_bvlt = false);
  BBNode BBBVLE_variant2(const BBNodeVec& x, const BBNodeVec& y,
                         bool is_signed, bool is_bvlt = false);

  // Return bit-blasted form for BVLE, BVGE, BVGT, SBLE, etc.
  BBNode BBcompare(const ASTNode& form, BBNodeSet& support);

  void BBLShift(BBNodeVec& x, unsigned int shift);
  void BBRShift(BBNodeVec& x, unsigned int shift);

  // Checks for constants.
  void commonCheck(const ASTNode& n);
  void check(const BBNode& x, const ASTNode& n);
  void check(const BBNodeVec& x, const ASTNode& n);

  bool update(const ASTNode& n, const int i,
              simplifier::constantBitP::FixedBits* b, BBNode& bb,
              BBNodeSet& support);
  void updateTerm(const ASTNode& n, BBNodeVec& bb, BBNodeSet& support);
  void updateForm(const ASTNode& n, BBNode& bb, BBNodeSet& support);

  const BBNode BBForm(const ASTNode& form, BBNodeSet& support);

  bool isConstant(const BBNodeVec& v);
  ASTNode getConstant(const BBNodeVec& v, const ASTNode& n);

  // Nodes in this set can be replaced by their constant values, without being
  // conjoined to the top..
  ASTNodeSet fixedFromBottom;

  UserDefinedFlags* uf;
  NodeFactory* ASTNF;
  Simplifier* simp;
  BBNodeManagerT* nf;

  ASTNodeSet booth_recoded; // Nodes that have been recoded.

public:
  BitBlaster& operator=(const BitBlaster& other) = delete;
  BitBlaster(const BitBlaster& other) = delete;
  ~BitBlaster() { ClearAllTables(); }

  simplifier::constantBitP::ConstantBitPropagation* cb;

  // Bit blast a bitvector term.  The term must have a kind for a
  // bitvector term.  Result is a ref to a vector of formula nodes
  // representing the boolean formula.
  const BBNodeVec BBTerm(const ASTNode& term, BBNodeSet& support);
  
  typename std::unordered_map<ASTNode, BBNodeVec>::iterator
  simplify_during_bb(ASTNode& term, BBNodeSet& support);

  BitBlaster(BBNodeManagerT* bnm, Simplifier* _simp, NodeFactory* astNodeF,
             UserDefinedFlags* _uf,
             simplifier::constantBitP::ConstantBitPropagation* cb_ = NULL)
      : uf(_uf)
  {
    nf = bnm;
    cb = cb_;
    BBTrue = nf->getTrue();
    BBFalse = nf->getFalse();
    simp = _simp;
    ASTNF = astNodeF;
  }

  void ClearAllTables()
  {
    BBTermMemo.clear();
    BBFormMemo.clear();
  }

  // Bitblast a formula
  const BBNode BBForm(const ASTNode& form);

  void getConsts(const ASTNode& n, ASTNodeMap& fromTo, ASTNodeMap& equivs);
};

} // end of namespace

#endif
