/*
 * VariablesInExpression.cpp
 */

#include "VariablesInExpression.h"

namespace BEEV {

VariablesInExpression::VariablesInExpression() {
	// TODO Auto-generated constructor stub

}

VariablesInExpression::~VariablesInExpression() {
	  set<Symbols*> deleted;
	  for (ASTNodeToNodes::iterator it = symbol_graph.begin(); it != symbol_graph.end(); it++)
	  {
		  if (deleted.find(it->second) == deleted.end())
		  {
			  deleted.insert(it->second);
			  delete it->second;
		  }
	  }

	  for (SymbolPtrToNode::iterator it = TermsAlreadySeenMap.begin(); it != TermsAlreadySeenMap.end() ; it++)
		  delete (it->second);

	symbol_graph.clear();

}

// This builds a reduced version of a graph, where there
// is only a new node if the number of non-array SYMBOLS
// in the descendents changes. For example (EXTRACT 0 1 n)
// will have the same "Symbols" node as n, because
// no new symbols are introduced.
Symbols* VariablesInExpression::BuildSymbolGraph(const ASTNode& n) {
	if (symbol_graph.find(n) != symbol_graph.end()) {
		return symbol_graph[n];
	}

	Symbols* node;

	// Note we skip array variables. We never solve for them so
	// can ignore them.
	if (n.GetKind() == SYMBOL && n.GetIndexWidth() == 0) {
		node = new Symbols(n);
		symbol_graph.insert(make_pair(n, node));
		return node;
	}

	vector<Symbols*> children;
	for (int i = 0; i < n.Degree(); i++) {
		Symbols* v = BuildSymbolGraph(n[i]);
		if (!v->empty())
			children.push_back(v);
	}

	if (children.size() == 1) {
		// If there is only a single child with a symbol. Then jump to it.
		node = children.back();
	} else
		node = new Symbols(children);

	symbol_graph.insert(make_pair(n, node));

	return node;
}

// Builds a set of the SYMBOLS that were found under the "term". The symbols are the union of "found" and
// all the sets : TermsAlreadySeen(av[0]) union ... TermsAlreadySeen(av[n])".
void VariablesInExpression::VarSeenInTerm(Symbols* term, SymbolPtrSet& visited,
		ASTNodeSet& found, vector<Symbols*>& av) {
	if (visited.find(term) != visited.end()) {
		return;
	}
	SymbolPtrToNode::const_iterator it;
	if ((it = TermsAlreadySeenMap.find(term)) != TermsAlreadySeenMap.end()) {
		// We've previously built the set of variables below this "symbols".
		// It's not added into "found" because its sometimes 70k variables
		// big, and if there are no other symbols discovered it's a terrible
		// waste to create a copy of the set. Instead we store (in effect)
		// a pointer to the set.
		av.push_back(term);
		return;
	}

	if (term->isLeaf()) {
		found.insert(term->found);
		return;
	}

	for (vector<Symbols*>::const_iterator it = term->children.begin(), itend =
			term->children.end(); it != itend; it++) {
		VarSeenInTerm(*it, visited, found, av);
	}

	visited.insert(term);
	return;
}//End of VarSeenInTerm

#if 0
void VariablesInExpression::SetofVarsSeenInTerm(const ASTNode& term, ASTNodeSet& symbols)
{
	assert(symbols.size() ==0);

	BuildSymbolGraph(term);

	SymbolPtrSet visited;

	vector<Symbols*> av;
	VarSeenInTerm(symbol_graph[term],visited,symbols,av);

	for (int i =0; i < av.size();i++)
	{
		const ASTNodeSet& sym = *TermsAlreadySeenMap.find(av[i])->second;
		symbols.insert(sym.begin(), sym.end());
	}

	if (visited.size() > 50) // No use caching it, unless we've done some work.
	{
		TermsAlreadySeenMap.insert(make_pair(symbol_graph[term],symbols));
	}
}
#endif

bool VariablesInExpression::VarSeenInTerm(const ASTNode& var,
		const ASTNode& term) {
	// This only returns true if we are searching for variables that aren't arrays.
	assert(var.GetKind() == SYMBOL && var.GetIndexWidth() == 0);
	if (term.isConstant())
		return false;

	BuildSymbolGraph(term);

	SymbolPtrSet visited;
	ASTNodeSet *symbols = new ASTNodeSet();
	vector<Symbols*> av;
	VarSeenInTerm(symbol_graph[term], visited, *symbols, av);

	bool result = (symbols->count(var) != 0);

	//cerr << "visited:" << visited.size() << endl;
	//cerr << "av:" << av.size() << endl;
	//cerr << "Term is const" << term.isConstant() << endl;

	if (visited.size() > 50) // No use caching it, unless we've done some work.
	{
		for (int i = 0; i < av.size(); i++) {
			const ASTNodeSet& sym = *TermsAlreadySeenMap.find(av[i])->second;
			symbols->insert(sym.begin(), sym.end());
		}
		TermsAlreadySeenMap.insert(make_pair(symbol_graph[term], symbols));
		result = (symbols->count(var) != 0);
	} else {
		const int size = av.size();
		for (int i = 0; i < size; i++) {
			if (result)
				break;
			const ASTNodeSet& sym = *TermsAlreadySeenMap.find(av[i])->second;
			result |= (sym.find(var) != sym.end());
		}
		delete symbols;
	}
	return result;
}

};
