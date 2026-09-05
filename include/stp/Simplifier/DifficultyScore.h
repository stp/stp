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

#ifndef DIFFICULTYSCORE_H_
#define DIFFICULTYSCORE_H_

#include "stp/AST/AST.h"
#include <cstdint>

// Estimates how many AIG AND-nodes bit-blasting a formula would build,
// without building them: the per-operation costs are measured, and summed
// over the formula's distinct nodes. Used to decide whether a simplification
// left the problem harder than it found it. See DifficultyScore.cpp for what
// the estimate does and does not model, and tools/difficulty_bench for the
// measurement it is fitted to.
//
// int64_t rather than long: the estimate is a sum of quadratic (and, for
// fp.sqrt, cubic) terms over every node of a formula, so it outgrows 32 bits
// on inputs that are not especially large -- and `long` is 32 bits on Windows
// and on i386.

namespace stp
{
class DifficultyScore // not copyable
{
private:
  // maps from nodeNumber to the previously calculated difficulty score..
  std::map<uint64_t, int64_t> cache;
  int64_t evalCount = 0;

public:
  int64_t score(const ASTNode& top, STPMgr*);
  auto getEvalCount() {return evalCount;}
};
}

#endif /* DIFFICULTYSCORE_H_ */
