// -*- c++ -*-
/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: June, 2010
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


#include "stp/AST/AST.h"
#include "stp/AST/ASTKind.h"
#include <list>
#include "stp/Util/NodeIterator.h"
#include "stp/Simplifier/DifficultyScore.h"

namespace stp
{
// estimate how difficult that input is to solve based on some simple rules.

  static bool isLikeDivision(const Kind& k)
  {
    return k == BVMULT || k == BVDIV || k == BVMOD || k == SBVDIV ||
           k == SBVREM || k == SBVMOD;
  }

  int eval(const ASTNode& b)
  {
    const Kind k = b.GetKind();

    // These scores are approximately the number of AIG nodes created when
    // no input values are known.
    int score = 0;
    if (k == BVMULT)
      score = (5 * b.GetValueWidth() * b.GetValueWidth());
    else if (k == BVMOD)
      score = (15 * b.GetValueWidth() * b.GetValueWidth());
    else if (isLikeDivision(k))
      score = (20 * b.GetValueWidth() * b.GetValueWidth());
    else if (k == BVCONCAT || k == BVEXTRACT || k == NOT)
    {
    } // no harder.
    else if (k == EQ || k == BVGE || k == BVGT || k == BVSGE || k == BVSGT)
    {
      // without getting the width of the child it'd always be 2.
      score = std::max(b[0].GetValueWidth(), 1u) * (b.Degree());
    }
    else if (k == BVSUB)
    {
      // We convert subtract to a + (-b), we want the difficulty scores to be
      // same.
      score = std::max(b[0].GetValueWidth(), 1u) * 3;
    }
    else
    {
      score = std::max(b.GetValueWidth(), 1u) * (b.Degree());
    }
    return score;
  }

  // maps from nodeNumber to the previously calculated difficulty score..
  std::map<int, int> cache;

  int DifficultyScore::score(const ASTNode& top)
  {
    if (cache.find(top.GetNodeNum()) != cache.end())
      return cache.find(top.GetNodeNum())->second;

    NonAtomIterator ni(top, top.GetSTPMgr()->ASTUndefined, *top.GetSTPMgr());
    ASTNode current;
    int result = 0;
    while ((current = ni.next()) != ni.end())
      result += eval(current);

    cache.insert(std::make_pair(top.GetNodeNum(), result));
    return result;
  }
}
