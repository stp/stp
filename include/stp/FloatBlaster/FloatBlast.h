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

namespace stp
{

// Lowers every floating-point operation in a formula to its bitvector
// circuit, in one bottom-up traversal.
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
// floating-point operations, with formats derived from their kinds and
// children as they always were; this pass then replaces the whole
// floating-point layer with bits in one go, taking each operation's operand
// format from the node the input built rather than from the bits it lowered
// to. Nothing downstream of it is floating-point, and no bitvector node
// carries a float's format.
//
// Runs after FpTotalise -- which supplies the extra child the partial
// operations need -- and before the formula reaches the simplifier, so the
// blasted circuit gets simplified like any other bitvector circuit.
class FloatBlast // not copyable
{
public:
  FloatBlast(STPMgr* bm_);

  FloatBlast(const FloatBlast&) = delete;
  FloatBlast& operator=(const FloatBlast&) = delete;

  // Returns `n` with every floating-point operation replaced by the bits it
  // computes. Idempotent: a formula with none left is returned unchanged.
  ASTNode topLevel(const ASTNode& n);

private:
  ASTNode visit(const ASTNode& n);

  // Rebuild `n` around new children, preserving its widths. Unlike
  // FpTotalise's rebuild this does *not* put a floating-point format back:
  // by the time a node is rebuilt here its floating-point children are bits,
  // so it no longer denotes a float.
  ASTNode rebuild(const ASTNode& n, const ASTVec& children);

  STPMgr* bm;
  NodeFactory* nf;
  ASTNodeMap cache;
};

} // namespace stp

#endif
