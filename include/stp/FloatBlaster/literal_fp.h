/********************************************************************
 *
 * BEGIN DATE: August, 2026
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

#ifndef STP_LITERAL_FP_H
#define STP_LITERAL_FP_H

// A *literal* symfpu backend: the same IEEE semantics as the circuit
// backend (symbolic_fp), instantiated over concrete CBV arithmetic instead
// of ASTNode construction. Constant folding through this backend computes
// the answer directly -- microseconds and no node churn -- where the
// circuit backend builds and collapses thousands of interned gates.
//
// The semantics source is shared by construction: both backends
// instantiate the identical symfpu::core templates. The Kind-to-operation
// driver (tryEvaluateFpConstant) is the only per-kind code, and it is
// pinned to the circuit path by an exhaustive per-kind differential in
// FpConstantFold_Test.

#include "stp/AST/AST.h"

namespace stp
{
class STPMgr;

namespace literal_fp
{

// Evaluate one all-constant floating-point operation directly.
//
// `n` is the node the constant evaluator built for the fold: every child
// is a constant (FP constants carry their formats). Returns the folded
// value -- ASTTrue/ASTFalse for predicates, a bare BVCONST for bit-vector
// and float results (the caller re-stamps float formats, as it already
// does for the circuit path) -- or a null ASTNode when this backend does
// not cover the kind or format, in which case the caller falls back to
// building and collapsing the circuit.
//
// Deliberately not covered: fp.min/fp.max/fp.to_ubv/fp.to_sbv (their
// unspecified cases route through FpTotalise's machinery) and
// fp.roundToIntegral (kept on the circuit path so its symfpu guard-bug
// refusals stay identical). Unsupported formats return null for the same
// refusal-parity reason.
ASTNode tryEvaluateFpConstant(STPMgr* bm, const ASTNode& n);

} // namespace literal_fp
} // namespace stp

#endif
