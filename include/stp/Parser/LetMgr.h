// -*- c++ -*-
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

namespace BEEV
{
using std::string;

// LET Management
class LETMgr
{
private:
  const ASTNode ASTUndefined;

  typedef hash_map<string, ASTNode> MapType;

  // MAP: This map is from bound IDs that occur in LETs to
  // expression. The map is useful in checking replacing the IDs
  // with the corresponding expressions. As soon as the brackets
  // that close a let expression is reached, it is emptied by
  // a call to CleanupLetIDMap().
  MapType* _letid_expr_map;

  // Allocate LetID map
  void InitializeLetIDMap(void);

public:
  // I think this keeps a reference to symbols so they don't get garbage
  // collected.
  ASTNodeSet _parser_symbol_table;

  // A let with this name has already been declared.
  bool isLetDeclared(string s)
  {
    return _letid_expr_map->find(s) != _letid_expr_map->end();
  }

  void cleanupParserSymbolTable() { _parser_symbol_table.clear(); }

  LETMgr(ASTNode undefined) : ASTUndefined(undefined)
  {
    assert(!undefined.IsNull());
    InitializeLetIDMap();
  }

  ~LETMgr() { delete _letid_expr_map; }

  // We know for sure that it's a let.
  ASTNode resolveLet(const string s)
  {
    assert(isLetDeclared(s));
    return _letid_expr_map->find(s)->second;
  }

  ASTNode ResolveID(const ASTNode& var);

  // Functions that are used to manage LET expressions
  void LetExprMgr(const ASTNode& var, const ASTNode& letExpr);
  void LetExprMgr(string name, const ASTNode& letExpr);

  // Delete Letid Map. Called when we move onto the expression after (let ... )
  void CleanupLetIDMap(void);

}; // End of class LETMgr
} // end of namespace

#endif
