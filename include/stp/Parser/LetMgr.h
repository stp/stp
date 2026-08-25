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
  typedef ankerl::unordered_dense::map<string, ASTNode, TransparentStringHash,
                                       std::equal_to<>>
      MapType;

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

  // The names bound in each open frame, so pop() can undo them.
  // Initally empty because we expect push() to be called before any bindings are added.
  std::vector<std::vector<string>> frames;

  MapType interim;

  // Adds to the current frame. Returns false if the name is already
  // bound in the current frame (leaving the existing binding in place).
  bool insertIntoFrame(const string& name, const ASTNode& letExpr);

public:
  
  bool frameMode = true;

  LetMgr([[maybe_unused]] ASTNode undefined)
  {
    assert(!undefined.IsNull());
    push(); // CVC format has a global let scope.
  }

  ~LetMgr() 
  {  
  }

  // I think this keeps a reference to symbols so they don't get garbage
  // collected. Used only by the CVC parser.
  ASTNodeSet _parser_symbol_table;
  void cleanupParserSymbolTable();

  void CleanupLetIDMap(void);

  // The expression the innermost binding of s maps to, or nullptr.
  // The pointer is invalidated by any change to the bindings.
  const ASTNode* lookupLet(std::string_view s) const;

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
