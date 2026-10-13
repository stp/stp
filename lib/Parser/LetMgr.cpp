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
  assert(frames.size() > 0);

  // A binding is visible only once the whole list of them has been read
  // (commit), so the bindings of one let cannot see each other. commit()
  // is also where a name bound twice in the list is caught.
  pending.emplace_back(std::move(name), letExpr);
}

bool LetMgr::insertIntoFrame(const string& name, const ASTNode& letExpr)
{
  auto& shadows = bindings[name];
  if (!shadows.empty() && shadows.back().first == frames.size() - 1)
    return false;

  shadows.emplace_back(frames.size() - 1, letExpr);
  frames.back().names.push_back(name);
  return true;
}

// We're ready for these bindings to participate. Any let nested in the
// list's right-hand sides has been closed by now, so frames.back() is the
// frame this list opened, and its bindings are the top of pending.
void LetMgr::commit()
{
  const size_t first = frames.back().firstPending;
  for (size_t i = first; i < pending.size(); i++)
    if (!insertIntoFrame(pending[i].first, pending[i].second))
    {
      string msg = "Let already created:" + pending[i].first;
      FatalError(msg.c_str());
    }
  pending.erase(pending.begin() + first, pending.end());
}

// Opens the frame of a let whose binding list is about to be read. The
// bindings of any list still being read stay pending: this let may sit in
// one of that list's right-hand sides, where they must not be seen.
void LetMgr::push()
{
  frames.push_back({{}, pending.size()});
}

void LetMgr::pop()
{
  if (frames.size() == 0)
    FatalError("Popping from empty let stack");

  for (const string& name : frames.back().names)
  {
    auto it = bindings.find(name);
    assert(it != bindings.end());
    it->second.pop_back();
    if (it->second.empty())
      bindings.erase(it);
  }
  frames.erase(frames.end() - 1);
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
  const ASTNode* found = lookupLet(v.GetName());
  if (found != nullptr)
    return *found;

  return v;
}

const ASTNode* LetMgr::lookupLet(std::string_view s) const
{
  // The lexer asks about every identifier, including on files with no lets
  // at all; skip the string hash entirely when there is nothing to find.
  if (bindings.empty())
    return nullptr;

  const auto found = bindings.find(s);
  if (found == bindings.end())
    return nullptr;

  // The innermost binding shadows the others.
  return &found->second.back().second;
}

}
