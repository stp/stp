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
#include <utility>

namespace stp
{

// Lowers one floating-point operation to the pure-bitvector circuit symfpu
// builds for it. Stateless: every entry point takes the manager whose nodes
// are being blasted, so independent managers never blast into one another.
class FloatBlaster
{
private:
  static ASTNode BlastNode(STPMgr* bm, Kind k, const ASTVec& kids,
                           unsigned int operand_exp, unsigned int operand_sig);

public:
  // The format of an operation's floating-point *operands*, which is what
  // symfpu needs to unpack them, and which is not always the result's format:
  // fp.to_ubv yields a bitvector, and to_fp's four-argument form converts
  // between two formats.
  //
  // Read it off the node the input built, before blasting has replaced its
  // children with bits. Taking it from a blasted operand is what made the
  // blaster depend on the format being stamped onto those bits -- a stamp
  // that lands on a hash-consed node the input may still be using as a plain
  // bitvector, which is a whole family of wrong answers and aborts.
  //
  // Follows the same rule as deriveFPFormat: the first child that carries a
  // format. The others are rounding modes, widths and to_fp's format
  // arguments, none of which do.
  static std::pair<unsigned int, unsigned int> operandFormat(const ASTNode& n);
  static std::pair<unsigned int, unsigned int>
  operandFormat(const ASTVec& children);

  // Lower one floating-point operation to its bitvector circuit. `kids` are
  // its operands already blasted to bits, and operand_exp/operand_sig say
  // what format those bits are in (see operandFormat); both are 0 for an
  // operation with no float operand.
  //
  // The operation is passed as kind-plus-children rather than as a node
  // because there is no well-formed node to pass: an FP_ADD whose children
  // are bitvectors does not type check.
  //
  // What comes back is bits. It carries no floating-point format, and must
  // not be given one -- nodes are hash-consed, so a format stamped on a
  // blasted float lands on whatever else denotes the same bits.
  static ASTNode BlastNode_TopLevel(STPMgr* bm, Kind k, const ASTVec& kids,
                                    unsigned int operand_exp,
                                    unsigned int operand_sig);

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
