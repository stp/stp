/********************************************************************
 * AUTHORS: Andrew V. Jones
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
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/STPManager/STPManager.h"

namespace stp
{

class FloatBlaster // not copyable
{

private:
  // Handy defs
  ASTNode ASTTrue, ASTFalse, ASTUndefined;

  // Ptr to STP Manager
  static FloatBlaster* _instance;

  NodeFactory* nf;

private:
  FloatBlaster();

  ASTNode BlastNode(const ASTNode& inputterm);

  static FloatBlaster* instance();

public:
  virtual ~FloatBlaster() {}

  static ASTNode BlastNode_TopLevel(const ASTNode& b);

  // Return `n` carrying the floating-point format (exp_width, sig_width).
  //
  // A float's format is per-node state, so it is lost whenever a node is
  // rebuilt -- which every constant fold and every simplification does. Worse,
  // it cannot simply be stamped back on: ASTBVConst has no room for it
  // (getExpWidth() is hardwired to 0 and the setter asserts), so a folded
  // constant has to be re-made as an ASTFPConst first. Anywhere that rebuilds
  // a floating-point node has to put the format back through here, or the
  // blaster silently computes against a format of (0, 0).
  static ASTNode withFormat(STPMgr* bm, const ASTNode& n,
                            unsigned int exp_width, unsigned int sig_width);
};
} // namespace stp
#endif
