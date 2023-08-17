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

namespace stp
{
using std::string;

// LET Management
class LetMgr
{
private:
  const ASTNode ASTUndefined;

  typedef std::unordered_map<string, ASTNode> MapType;

  // This maps from bound IDs that occur in LETs to
  // expressions. It's used to replace the IDs
  // with the corresponding expressions.
  // It's complicated because bindings can be shadowed by later bindings.
  // As soon as the brackets that close a let expression is reached it should be popped.
  
  // Initally empty because we expect push() to be called before any bindings are added.
  std::vector<MapType> stack;

public:
  LetMgr(ASTNode undefined) : ASTUndefined(undefined)
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

  // Has a let with this name has already been declared.
  bool isLetDeclared(string s);

  ASTNode resolveLet(const string s);
  ASTNode ResolveID(const ASTNode& var);

  // Functions that are used to create LET expressions
  void LetExprMgr(const ASTNode& var, const ASTNode& letExpr);
  void LetExprMgr(string name, const ASTNode& letExpr);

  void push();
  void pop();
  
};
} // end of namespace

#endif
