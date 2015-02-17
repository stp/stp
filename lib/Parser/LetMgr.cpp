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

#include <stdlib.h>
#include "stp/Parser/LetMgr.h"

namespace stp
{
// FUNC: This function builds the map between LET-var names and
// LET-expressions
//
// 1. if the Let-var is already defined in the LET scope, then the
// 1. function returns an error.
//
// 2. if the Let-var is already declared variable in the input, then
// 2. the function returns an error
//
// 3. otherwise add the <var,letExpr> pair to the _letid_expr table.
void LETMgr::LetExprMgr(const ASTNode& var, const ASTNode& letExpr)
{
  string name = var.GetName();
  MapType::iterator it;
  if (((it = _letid_expr_map->find(name)) != _letid_expr_map->end()))
  {
    FatalError("LetExprMgr:The LET-var v has already been defined"
               "in this LET scope: v =",
               var);
  }

  if (_parser_symbol_table.find(var) != _parser_symbol_table.end())
  {
    FatalError("LetExprMgr:This var is already declared. "
               "cannot redeclare as a letvar: v =",
               var);
  }

  LetExprMgr(var.GetName(), letExpr);
} // end of LetExprMgr()

void LETMgr::LetExprMgr(string name, const ASTNode& letExpr)
{
  assert(_letid_expr_map->find(name) == _letid_expr_map->end());
  (*_letid_expr_map)[name] = letExpr;
} // end of LetExprMgr()

// this function looks up the "var to letexpr map" and returns the
// corresponding letexpr. if there is no letexpr, then it simply
// returns the var.
ASTNode LETMgr::ResolveID(const ASTNode& v)
{
  if (v.GetKind() != SYMBOL)
  {
    return v;
  }

  if (_parser_symbol_table.find(v) != _parser_symbol_table.end())
  {
    return v;
  }

  MapType::iterator it;
  if ((it = _letid_expr_map->find(v.GetName())) != _letid_expr_map->end())
  {
    return it->second;
  }

  return v;
} // End of ResolveID()

// This function simply cleans up the LetID -> LetExpr Map.
void LETMgr::CleanupLetIDMap(void)
{
  // ext/hash_map::clear() is very expensive on big empty maps. shortcut.
  if (_letid_expr_map->size() == 0)
    return;

  // May contain lots of buckets, so reset.
  delete _letid_expr_map;
  InitializeLetIDMap();
} // end of CleanupLetIDMap()

void LETMgr::InitializeLetIDMap(void)
{
  _letid_expr_map = new hash_map<string, ASTNode>();
} // end of InitializeLetIDMap()
}
