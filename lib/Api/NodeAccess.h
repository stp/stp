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

// NodeAccess.h -- the one friend of ASTNode the 3.x API uses to move between
// an opaque term handle (a retained ASTInternal*) and an engine node.

#ifndef STP_API_NODE_ACCESS_H
#define STP_API_NODE_ACCESS_H

#include "stp/AST/ASTNode.h"

namespace stp
{
namespace api
{
namespace detail
{

class NodeAccess
{
public:
  static ASTNode wrap(ASTInternal* p) { return ASTNode(p); }
  static ASTInternal* raw(const ASTNode& n) { return n._int_node_ptr; }
  static void retain(ASTInternal* p)
  {
    if (p)
      p->IncRef();
  }
  static void release(ASTInternal* p)
  {
    if (p)
      p->DecRef();
  }
};

} // namespace detail
} // namespace api
} // namespace stp

#endif
