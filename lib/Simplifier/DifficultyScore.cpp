/********************************************************************
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

#include "stp/Simplifier/DifficultyScore.h"
#include "stp/AST/AST.h"
#include "stp/AST/ASTKind.h"
#include "stp/Util/NodeIterator.h"
#include <list>

namespace stp
{
// Estimate the number of clauses that would generated if sent to CNF.

static bool isLikeDivision(const Kind& k)
{
  return k == BVMULT || k == BVDIV || k == BVMOD || k == SBVDIV ||
         k == SBVREM || k == SBVMOD;
}

long eval(const ASTNode& b)
{
  const Kind k = b.GetKind();

  if (b.Degree() == 0)
    return 0; // consts & symbols don't count.

  // These scores are approximately the number of clauses created when
  // no input values are known.
  long score = 0;
  if (k == BVMULT&& b.Degree() == 2 && b[0].GetKind() == BVCONST)
  {
    // because it's going to be booth encoded, it's about the number of runs.
    const auto cbv = b[0].GetBVConst(); // cleanup?
    bool last = CONSTANTBV::BitVector_bit_test(cbv,0);
    int changes = 0;
    for (int i =1; i < b.GetValueWidth();i++)
    {
        if (last != CONSTANTBV::BitVector_bit_test(cbv,i))
          changes++;

        last = CONSTANTBV::BitVector_bit_test(cbv,i);
    }
   //std::cerr << "C" <<changes;
   score = (4 * b.GetValueWidth() * changes); 

  }
  else if (k == BVMULT)
  {
    score = (4 * b.GetValueWidth() * b.GetValueWidth() * b.Degree());
  }
  else if (isLikeDivision(k))
    score = (16 * b.GetValueWidth() * b.GetValueWidth());
  else if (k == BVCONCAT || k == BVEXTRACT || k == NOT || k == BVNOT)
  {
  } // no harder.
  else if (k == EQ || k == BVGE || k == BVGT || k == BVSGE || k == BVSGT)
  {
    score = 6 * std::max(b[0].GetValueWidth(), 1u);
  }
  else if (k == BVSUB)
  {
    // We convert subtract to a + (-b), we want the difficulty scores to be
    // same.
    score = 20 * b.GetValueWidth();
  }
  else if (k == EQ)
  {
    score = 5 * b[0].GetValueWidth();    
  }
  else if (k == BVUMINUS)
  {
    score = 6 * b.GetValueWidth();    
  }  
  else if (k == BVPLUS)
  {
    score = 14 * b.GetValueWidth() * (b.Degree()-1);    
  }
  else if (k == BVRIGHTSHIFT || k == BVLEFTSHIFT)
  {
    score = 29 * b.GetValueWidth();    
  }
  else if (k == BVSRSHIFT)
  {
    score = 30 * b.GetValueWidth();  
  }  
  else if (k == BVZX || k == BVSX)
  {
    score = 0;    
  }
  else 
  {
    //std::cerr << k;
    score = std::max(b.GetValueWidth(), 1u) * (b.Degree());
  }
  return score;
}

long DifficultyScore::score(const ASTNode& top, STPMgr* mgr)
{
  if (cache.find(top.GetNodeNum()) != cache.end())
    return cache.find(top.GetNodeNum())->second;

  NonAtomIterator ni(top, mgr->ASTUndefined, *mgr);
  ASTNode current;
  long result = 0;
  while ((current = ni.next()) != ni.end())
    result += eval(current);

  cache.insert(std::make_pair(top.GetNodeNum(), result));
  return result;
}
}
