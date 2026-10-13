/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
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

#ifndef LETMGR_H
#define LETMGR_H

#include "stp/AST/AST.h"
#include "stp/cpp_interface.h"
#include <string_view>

namespace stp
{
using std::string;

// LET Management
class LetMgr
{
private:
  // This maps from bound IDs that occur in LETs to
  // expressions. It's used to replace the IDs
  // with the corresponding expressions.
  // It's complicated because bindings can be shadowed by later bindings.
  // As soon as the brackets that close a let expression is reached it should be popped.

  // Each name maps to the stack of bindings that shadow each other,
  // innermost last, tagged with the index of the frame they belong to.
  // A single hash lookup resolves a name however deeply lets are nested.
  // A dense hash map probed via string_view: the lexer asks about every
  // identifier it sees, so the probe must not copy the name.
  ankerl::unordered_dense::map<string, std::vector<std::pair<size_t, ASTNode>>,
                               TransparentStringHash, std::equal_to<>>
      bindings;

  // One per open frame, innermost last: the names bound in it, so pop() can
  // undo them, and where the bindings of its own list start in pending.
  struct Frame
  {
    std::vector<string> names;
    size_t firstPending;
  };
  std::vector<Frame> frames;

  // The bindings read so far of every binding list still being read,
  // innermost list last. A list's bindings are kept out of resolution until
  // the whole list has been read (commit), so they cannot see each other.
  // That holds inside a let nested in one of the list's right-hand sides
  // too: the nested list commits only its own bindings, off the top.
  std::vector<std::pair<string, ASTNode>> pending;

  // Adds to the current frame. Returns false if the name is already
  // bound in the current frame (leaving the existing binding in place).
  bool insertIntoFrame(const string& name, const ASTNode& letExpr);

public:
  LetMgr([[maybe_unused]] ASTNode undefined)
  {
    assert(!undefined.IsNull());
    push(); // the outermost frame, which no let opens
  }

  ~LetMgr() 
  {  
  }

  // The expression the innermost binding of s maps to, or nullptr.
  // The pointer is invalidated by any change to the bindings.
  const ASTNode* lookupLet(std::string_view s) const;
  size_t depth() const { return frames.size(); }
  bool boundOutside(std::string_view name, size_t depth) const
  {
    const auto found = bindings.find(name);
    return found != bindings.end() && found->second.back().first < depth;
  }

  ASTNode ResolveID(const ASTNode& var);

  // Functions that are used to create LET expressions
  void LetExprMgr(const ASTNode& var, const ASTNode& letExpr);
  void LetExprMgr(string name, const ASTNode& letExpr);

  void commit();
  void push();
  void pop();
  
};
} // end of namespace

#endif
