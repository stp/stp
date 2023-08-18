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

#include "stp/Parser/LetMgr.h"
#include <stdlib.h>

namespace stp
{

//Creates a new binding.  
void LetMgr::LetExprMgr(const ASTNode& var, const ASTNode& letExpr)
{
  if (var.GetKind() != SYMBOL)
  {
    std::cerr << var;
    FatalError("Should be a symbol.");
  }
  LetExprMgr(var.GetName(), letExpr);
}

//Creates a new binding.  
void LetMgr::LetExprMgr(string name, const ASTNode& letExpr)
{
  assert(stack.size() > 0);

  // In CVC they're available to use immediately. In SMTLIB2 it's only when the list of them is done.
  if (frameMode)
    interim.insert(make_pair(name,letExpr));
  else
    stack.back().insert(make_pair(name,letExpr));
}

// We're ready for these bindings to participate. 
void LetMgr::commit()
{
  if (interim.size() == 0)
    return;

  for (const auto& k : interim)
    stack.back().insert(k);
  interim.clear();
}


void LetMgr::push()
{
  commit();
  stack.push_back(MapType());
}

void LetMgr::pop()
{
  if (stack.size() == 0)
    FatalError("Popping from empty let stack");

  stack.erase(stack.end() - 1);
}

// this function looks up the symbols let-binding and returns the
// corresponding letexpr. if there is no letexpr, then it simply
// returns the var.
ASTNode LetMgr::ResolveID(const ASTNode& v)
{
  if (v.GetKind() != SYMBOL)
  {
    return v;
  }

  //Lets shadow other symbols, so check them first.
  if (isLetDeclared(v.GetName()))
    return resolveLet(v.GetName());
  
  return v;
}

ASTNode LetMgr::resolveLet(const string s)
{
  assert(isLetDeclared(s));

  // Searches backwards because they could be shadowed.
  for (auto i = stack.rbegin(); i != stack.rend(); ++i ) 
      if ((*i).find(s) != (*i).end())
        return (*i).find(s)->second;
  FatalError("never here...");
}

bool LetMgr::isLetDeclared(const string s)
{
  for (auto frame : stack )
    if (frame.find(s) != frame.end())
      return true;

  return false;

}

void LetMgr::cleanupParserSymbolTable() 
{
  _parser_symbol_table.clear(); 
}

// Used only by the SMT1 & CVC parsers.
void LetMgr::CleanupLetIDMap(void)
{
  interim.clear();
  stack.clear();
  push();
}

}
