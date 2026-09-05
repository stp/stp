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

#ifndef FLOATBLAST_H
#define FLOATBLAST_H

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"

#include <cstddef>
#include <memory>

namespace stp
{

// Lowers every floating-point operation in a formula to its bitvector
// circuit.
//
// This used to happen inside simplification: SimplifyTerm's floating-point
// arm simplified each float child -- which blasted it -- then rebuilt the
// operation over the resulting bits and blasted that. The intermediate is an
// FP_ADD whose children are bitvectors, which is not a well-formed node, and
// the only thing that made it pass the type checker was stamping a float
// format onto it and onto its blasted children.
//
// That stamp is the defect. Nodes are hash-consed and the format is per-node
// state, so stamping the bits a float blasts to retypes whatever else already
// denotes those bits. A plain bitvector the input also uses starts reporting
// FLOATINGPOINT_TYPE, solver-wide: bitvector operations over it fail to type
// check, and to_fp's four-argument form -- which tells "convert this integer"
// from "reformat this float" by asking its operand's type -- reads an integer
// as a float and answers the wrong thing.
//
// Separating the two passes removes the need for the stamp rather than
// working around it. Simplification now sees floating-point operations as
// floating-point operations, with formats derived from their source sorts;
// this pass then replaces the whole floating-point layer with bits.
//
// The source graph and the bit-vector graph deliberately have different
// views here. A floating-point source node is represented internally by one
// cached SymFPU unpacked value. FP operations and predicates consume that
// value directly, so a chain is not packed after every operation only to be
// unpacked by the next one. Packing is delayed until a real carrier boundary:
// an explicit IEEE-bit conversion, an array element, or a floating-point
// term returned for model evaluation. This preserves one rounding per source
// operation while avoiding representation round-trips between operations.
//
// Runs after FpTotalise -- which supplies the extra child the partial
// operations need -- and before the formula reaches the simplifier, so the
// blasted circuit gets simplified like any other bitvector circuit.
class FloatBlast // not copyable
{
public:
  struct Statistics
  {
    // Actual SymFPU decode/encode constructions (cache misses only).
    size_t unpack_builds = 0;
    size_t pack_builds = 0;

    // Unpacked results built for source FP operations and conversions. Each
    // arithmetic entry is the operation's final, rounded SymFPU result.
    size_t unpacked_operation_builds = 0;
    size_t unpacked_cache_hits = 0;

    // Predicates built directly from two unpacked operands, without
    // constructing the rounded fp.add result they observe.
    size_t add_iszero_builds = 0;
  };

  FloatBlast(STPMgr* bm_);
  ~FloatBlast();

  FloatBlast(const FloatBlast&) = delete;
  FloatBlast& operator=(const FloatBlast&) = delete;

  // Returns `n` with every floating-point operation replaced by the bits it
  // computes. Idempotent: a formula with none left is returned unchanged.
  ASTNode topLevel(const ASTNode& n);

  // Lower one floating-point node on its own, for a caller that holds the
  // node it built and wants the bits -- or the Boolean -- it computes: the
  // constant evaluator folding an all-constant operation, and the model
  // evaluator reducing one over a model.
  //
  // This used to be a second entry point with its own ~30-case switch over
  // the whole floating-point signature (FloatBlaster::BlastNode), taking the
  // operation apart into a kind plus already-blasted children because that
  // was what the packed formulation needed. The two switches agreed on every
  // kind, and had to keep agreeing by hand: an operation added to one and
  // not the other compiles, and fails only on the path that reaches the one
  // that was missed. There is one table now.
  static ASTNode lowerOperation(STPMgr* bm, const ASTNode& n);

  // Cumulative, context-local counters. Besides diagnostics, these make the
  // intended lazy boundary directly testable instead of inferring it from a
  // hash-consed output DAG in which redundant construction can be hidden.
  const Statistics& statistics() const noexcept;

private:
  // SymFPU types stay out of this public header.
  class Impl;
  std::unique_ptr<Impl> impl;
};

} // namespace stp

#endif
