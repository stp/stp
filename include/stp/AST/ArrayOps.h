/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: September, 2026
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

#ifndef STP_ARRAYOPS_H
#define STP_ARRAYOPS_H

#include "stp/AST/ASTNode.h"

class NodeFactory;

namespace stp
{
// Arrays use nonzero-width bit-vector carriers. Boolean source operands are
// represented by one bit, without identifying Bool with (_ BitVec 1).
ASTNode packBoolean(NodeFactory& nf, const ASTNode& value);
ASTNode unpackBoolean(NodeFactory& nf, const ASTNode& bits);
ASTNode createArrayRead(NodeFactory& nf, const ASTNode& array,
                        const ASTNode& index);
ASTNode createArrayWrite(NodeFactory& nf, const ASTNode& array,
                         const ASTNode& index, const ASTNode& value);

// Recognise a source select (or its negation when negated is true), including
// the simplifying factory's !(read == 0) spelling. A plain READ remains a
// bit-vector expression inside the engine.
ASTNode booleanArrayRead(const ASTNode& value, bool negated = false);
} // namespace stp

#endif
