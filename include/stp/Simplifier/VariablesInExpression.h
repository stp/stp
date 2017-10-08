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

#ifndef VARIABLESINEXPRESSION_H_
#define VARIABLESINEXPRESSION_H_

#include "Symbols.h"
#include "stp/AST/AST.h"
#include "stp/Util/Attributes.h"

namespace stp
{

class VariablesInExpression // not copyable
{
private:
  void insert(const ASTNode& n, Symbols* s);

  typedef std::unordered_map<int, Symbols*> ASTNodeToNodes;
  ASTNodeToNodes symbol_graph;

public:
  DLL_PUBLIC VariablesInExpression();
  DLL_PUBLIC virtual ~VariablesInExpression();

  // When solving, we're interested in whether variables appear multiple times.
  typedef std::unordered_set<Symbols*, SymbolPtrHasher> SymbolPtrSet;

  Symbols* getSymbol(const ASTNode& n);

  // this map is useful while traversing terms and uniquely
  // identifying variables in the those terms. Prevents double
  // counting.

  typedef std::unordered_map<Symbols*, ASTNodeSet*, SymbolPtrHasher>
      SymbolPtrToNode;
  SymbolPtrToNode TermsAlreadySeenMap;

  // this function return true if the var occurs in term, else the
  // function returns false
  bool VarSeenInTerm(const ASTNode& var, const ASTNode& term);
  ASTNodeSet* SetofVarsSeenInTerm(const ASTNode& term, bool& destruct);
  ASTNodeSet* SetofVarsSeenInTerm(Symbols* symbol, bool& destruct);
  void VarSeenInTerm(Symbols* term, SymbolPtrSet& visited, ASTNodeSet& found,
                     vector<Symbols*>& av);

  void ClearAllTables();
};
}

#endif /* VARIABLESINEXPRESSION_H_ */
