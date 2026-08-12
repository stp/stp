/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: Jan, 2011
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

#include "stp/Simplifier/VariablesInExpression.h"
#include "stp/Util/DagWalk.h"

namespace stp
{

VariablesInExpression::VariablesInExpression()
{
  // TODO Auto-generated constructor stub
}

VariablesInExpression::~VariablesInExpression()
{
  ClearAllTables();
}

void VariablesInExpression::insert(const ASTNode& n, Symbols* s)
{
  assert(s != NULL);
  symbol_graph.insert(std::make_pair(n.GetNodeNum(), s));
}

// This builds a reduced version of a graph, where there
// is only a new node if the number of non-array SYMBOLS
// in the descendents changes. For example (EXTRACT 0 1 n)
// will have the same "Symbols" node as n, because
// no new symbols are introduced.
// Every node below `n` before `n` itself, in the order getSymbol would have
// reached them. It looks at every child of every node it visits, and its one
// early return is for a symbol, which has no children, so nothing is built
// here that it would not have built anyway.
void VariablesInExpression::primeSymbols(const ASTNode& n)
{
  primeMemo(
      n,
      [this](const ASTNode& node)
      {
        if (symbol_graph.find(node.GetNodeNum()) != symbol_graph.end())
          return Walk::Skip; // getSymbol would answer from the graph.
        return node.Degree() == 0 ? Walk::Visit : Walk::Descend;
      },
      [this](const ASTNode& node, PrimeMemoReady) { getSymbol(node, true); });
}

Symbols* VariablesInExpression::getSymbol(const ASTNode& n)
{
  return getSymbol(n, false);
}

Symbols* VariablesInExpression::getSymbol(const ASTNode& n,
                                          const bool knownMissing)
{
  PrimeAudit::Running running(symbolAudit, n);

  // primeSymbols' classifier already made this lookup. Its ready token is a
  // known miss because building a descendant cannot insert an ancestor into
  // this bottom-up graph.
  if (!knownMissing)
  {
    const ASTNodeToNodes::const_iterator it = symbol_graph.find(n.GetNodeNum());
    if (it != symbol_graph.end())
      return it->second;
  }

  if (!priming)
  {
    priming = true;
    primeSymbols(n);
    priming = false;

    const ASTNodeToNodes::const_iterator it = symbol_graph.find(n.GetNodeNum());
    if (it != symbol_graph.end())
      return it->second;
  }

  Symbols* node;

  // Note we skip array variables. We never solve for them so
  // can ignore them.
  if (n.GetKind() == SYMBOL && n.GetIndexWidth() == 0)
  {
    node = new Symbols(n);
    insert(n, node);
    return node;
  }

  vector<Symbols*> children;
  for (size_t i = 0; i < n.Degree(); i++)
  {
    Symbols* v = getSymbol(n[i]);
    if (!v->empty())
      children.push_back(v);
  }

  if (children.size() == 1)
  {
    // If there is only a single child with a symbol. Then jump to it.
    node = children.back();
  }
  else
    node = new Symbols(children);

  insert(n, node);

  return node;
}

// Builds a set of the SYMBOLS that were found under the "term". The symbols are
// the union of "found" and
// all the sets : TermsAlreadySeen(av[0]) union ... TermsAlreadySeen(av[n])".
void VariablesInExpression::VarSeenInTerm(Symbols* term, SymbolPtrSet& visited,
                                          ASTNodeSet& found,
                                          vector<Symbols*>& av)
{
  // Iterative: the Symbols tree is as deep as the expression it was built
  // from, so a call per level exhausts the stack on the inputs that reach
  // here. Children are pushed in reverse, so they are still visited left to
  // right and the walk sees what the recursion saw. See DeepDag_Test.cpp.
  vector<Symbols*> toVisit;
  toVisit.push_back(term);

  while (!toVisit.empty())
  {
    Symbols* const current = toVisit.back();
    toVisit.pop_back();

    if (visited.find(current) != visited.end())
    {
      continue;
    }

    if (current->isLeaf())
    {
      found.insert(current->found);
      continue;
    }

    visited.insert(current);

    SymbolPtrToNode::const_iterator it;
    if ((it = TermsAlreadySeenMap.find(current)) != TermsAlreadySeenMap.end())
    {
      // We've previously built the set of variables below this "symbols".
      // It's not added into "found" because its sometimes 70k variables
      // big, and if there are no other symbols discovered it's a terrible
      // waste to create a copy of the set. Instead we store (in effect)
      // a pointer to the set.
      av.push_back(current);
      continue;
    }

    for (size_t i = current->children.size(); i > 0; i--)
      toVisit.push_back(current->children[i - 1]);
  }
}

ASTNodeSet* VariablesInExpression::SetofVarsSeenInTerm(Symbols* symbol,
                                                       bool& destruct)
{
  assert(symbol != NULL);

  SymbolPtrToNode::iterator it = TermsAlreadySeenMap.find(symbol);

  if (it != TermsAlreadySeenMap.end())
  {
    destruct = false;
    return it->second;
  }

  SymbolPtrSet visited;

  ASTNodeSet* symbols = new ASTNodeSet();
  vector<Symbols*> av;
  VarSeenInTerm(symbol, visited, *symbols, av);

  for (size_t i = 0; i < av.size(); i++)
  {
    const ASTNodeSet& sym = *TermsAlreadySeenMap.find(av[i])->second;
    symbols->insert(sym.begin(), sym.end());
  }

  destruct = true;
  // TermsAlreadySeenMap.insert(make_pair(symbol,symbols));

  return symbols;
}

ASTNodeSet* VariablesInExpression::SetofVarsSeenInTerm(const ASTNode& term,
                                                       bool& destruct)
{
  getSymbol(term);
  return SetofVarsSeenInTerm(symbol_graph[term.GetNodeNum()], destruct);
}

bool VariablesInExpression::VarSeenInTerm(const ASTNode& var,
                                          const ASTNode& term)
{
  // This only returns true if we are searching for variables that aren't
  // arrays.
  assert(var.GetKind() == SYMBOL && var.GetIndexWidth() == 0);
  if (term.isConstant())
    return false;

  getSymbol(term);

  SymbolPtrSet visited;
  ASTNodeSet* symbols = new ASTNodeSet();
  vector<Symbols*> av;
  VarSeenInTerm(symbol_graph[term.GetNodeNum()], visited, *symbols, av);

  bool result = (symbols->count(var) != 0);

  // cerr << "visited:" << visited.size() << endl;
  // cerr << "av:" << av.size() << endl;
  // cerr << "Term is const" << term.isConstant() << endl;

  if (visited.size() > 250) // No use caching it, unless we've done some work.
  {
    sort(av.begin(), av.end());

    // cout << "===" << endl;
    for (size_t i = 0; i < av.size(); i++)
    {
      if (i != 0 && av[i] == av[i - 1])
        continue;

      const ASTNodeSet& sym = *TermsAlreadySeenMap.find(av[i])->second;
      // cout << "set: " << i << " " << sym.size() << endl;
      symbols->insert(sym.begin(), sym.end());
    }
    TermsAlreadySeenMap.insert(
        make_pair(symbol_graph[term.GetNodeNum()], symbols));
    // cout << "finish" << symbols->size() << endl;
    // cout << "===" << endl;
    result = (symbols->count(var) != 0);
  }
  else
  {
    const int size = av.size();
    for (int i = 0; i < size; i++)
    {
      if (result)
        break;
      const ASTNodeSet& sym = *TermsAlreadySeenMap.find(av[i])->second;
      result |= (sym.find(var) != sym.end());
    }
    delete symbols;
  }
  return result;
}

void VariablesInExpression::ClearAllTables()
{
  std::set<Symbols*> deleted;
  for (ASTNodeToNodes::iterator it = symbol_graph.begin();
       it != symbol_graph.end(); it++)
  {
    if (deleted.find(it->second) == deleted.end())
    {
      deleted.insert(it->second);
      delete it->second;
    }
  }

  for (SymbolPtrToNode::iterator it = TermsAlreadySeenMap.begin();
       it != TermsAlreadySeenMap.end(); it++)
    delete (it->second);

  symbol_graph.clear();
  TermsAlreadySeenMap.clear();
}
}
