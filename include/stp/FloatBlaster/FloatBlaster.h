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
// builds for it. Every entry point takes the manager whose nodes are being
// blasted, and the static-trait backend keeps that context thread-local, so
// independent managers in different threads never blast into one another.
class FloatBlaster
{
public:
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
  // and -0 apart. Takes the format from the caller, for terms that do not
  // carry it themselves.
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
  //
  // The name has to spell the operation's whole SMT-LIB signature, because
  // that is all that separates one of these functions from another. `operands`
  // are the floating-point operands *carrying their formats*, and each one's
  // (exp, sig) goes into the name: a format is not recoverable from a packed
  // width, and two formats of equal packed width -- (_ FloatingPoint 8 24) and
  // (_ FloatingPoint 24 8), say -- are different sorts, so fp.to_ubv at each is
  // a different function and may answer differently. Sharing one array between
  // them equates two independent unspecified choices and loses models.
  //
  // For fp.to_ubv/fp.to_sbv, whose index really is a rounding mode and a whole
  // packed value. An operation whose unspecified choice ranges over a handful
  // of cases wants unspecifiedCells instead.
  static ASTNode unspecifiedValue(STPMgr* bm, const char* tag,
                                  const ASTVec& operands, const ASTNode& index,
                                  unsigned int value_width);

  // The same congruent map, for an operation whose unspecified choice has been
  // shown to depend on only a few bits of its operands: one free bitvector
  // symbol with one bit per case, to be selected between by the caller.
  //
  // An array is the general answer -- a solver without uninterpreted functions
  // has nothing else that is both free and congruent over an unbounded index
  // domain. But it is a heavy one, and its weight is not local: FpTotalise runs
  // before containsArrayOps and numberOfReadsLessThan, so reads it introduces
  // are indistinguishable from the user's. A pure QF_FP problem acquires "array
  // operations" it never had, and a QF_ABVFP problem can stop Ackermannising
  // the user's own arrays because unrelated floating-point operations pushed
  // the read count past a threshold.
  //
  // Over a *finite, small* domain none of that is needed. The cells are free
  // and the selection is a mux, so the result is a function of the operands by
  // construction, and hash-consing supplies the congruence the array's index
  // equalities were supplying. Same freedom, same congruence, no reads, no
  // congruence axioms, and no perturbation of how the user's arrays are solved.
  //
  // Identity is the name here too, and for the same reason: the solve and the
  // two counterexample re-derivations have to mint the same object.
  static ASTNode unspecifiedCells(STPMgr* bm, const char* tag,
                                  const ASTVec& operands,
                                  unsigned int cell_count);
};
} // namespace stp
#endif
