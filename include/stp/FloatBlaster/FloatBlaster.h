/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: January 2021
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

#ifndef FLOATBLASTER_H
#define FLOATBLASTER_H

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include <cstdint>

namespace stp
{

// Lowers one floating-point operation to the pure-bitvector circuit symfpu
// builds for it. Stateless: every entry point takes the manager whose nodes
// are being blasted, so independent managers never blast into one another.
class FloatBlaster
{
private:
  static ASTNode BlastNode(STPMgr* bm, const ASTNode& inputterm);

public:
  static ASTNode BlastNode_TopLevel(STPMgr* bm, const ASTNode& b);

  // Return `n` carrying the floating-point format (exp_width, sig_width).
  //
  // A float's format is per-node state, so it is lost whenever a node is
  // rebuilt -- which every constant fold and every simplification does.
  // A plain ASTBVConst has no room for it, so a folded constant is re-made
  // as an interned ASTFPConst. Anywhere that rebuilds a floating-point node
  // has to put the format back through here.
  static ASTNode withFormat(STPMgr* bm, const ASTNode& n,
                            unsigned int exp_width, unsigned int sig_width);

  // The canonical packed bits of a float: pack(unpack(f)). Collapses the NaN
  // payloads, which SMT-LIB equality does not distinguish, while keeping +0
  // and -0 apart. The format-taking form serves callers holding a term that
  // does not carry the format itself.
  static ASTNode canonicalBits(STPMgr* bm, const ASTNode& f);
  static ASTNode canonicalBits(STPMgr* bm, const ASTNode& f,
                               unsigned int exp_width, unsigned int sig_width);

  // fp.rem's circuit unrolls one divide step per representable exponent
  // difference -- 2^eb + sb - 4 steps (symfpu's maximumExponentDifference)
  // -- so its *depth* grows exponentially in the exponent width. Past
  // roughly binary64 scale the circuit outruns both the recursive
  // traversals (a stack overflow) and any hope of solving, so every
  // entrance for fp.rem funnels through remSupported and refuses instead.
  // binary64 needs 2097 steps; the limit leaves headroom for wide
  // significands at eb = 11 while refusing every eb >= 12.
  static const uint64_t REM_UNROLL_LIMIT = 2304;
  static uint64_t remUnrollSteps(unsigned exp_width, unsigned sig_width);
  static bool remSupported(unsigned exp_width, unsigned sig_width);

  // A read of the array supplying an operation's unspecified results. Identity
  // is the name, so every occurrence of an operation at a given signature
  // reads one and the same array -- which is what makes the result a function
  // of the operands rather than an arbitrary value per use.
  static ASTNode unspecifiedValue(STPMgr* bm, const char* tag,
                                  const ASTNode& index,
                                  unsigned int value_width);
};
} // namespace stp
#endif
