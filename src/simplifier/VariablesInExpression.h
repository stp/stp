/*
 * VariablesInExpression.h
 *
 *  Created on: 27/01/2011
 *      Author: thansen
 */

#ifndef VARIABLESINEXPRESSION_H_
#define VARIABLESINEXPRESSION_H_

#include "../AST/AST.h"
#include "Symbols.h"

//#include "../STPManager/STPManager.h"
//#include "../AST/NodeFactory/SimplifyingNodeFactory.h"
//#include "SubstitutionMap.h"


namespace BEEV
{

class VariablesInExpression {
public:
	VariablesInExpression();
	virtual ~VariablesInExpression();


    // When solving, we're interested in whether variables appear multiple times.
    typedef HASHSET<Symbols*,SymbolPtrHasher> SymbolPtrSet;

	typedef HASHMAP<
	  ASTNode,
	  Symbols*,
	  ASTNode::ASTNodeHasher,
	  ASTNode::ASTNodeEqual> ASTNodeToNodes;
	  ASTNodeToNodes symbol_graph;

	  Symbols* BuildSymbolGraph(const ASTNode& n);

	    //this map is useful while traversing terms and uniquely
	    //identifying variables in the those terms. Prevents double
	    //counting.

	    typedef HASHMAP<
		  Symbols*,
		  ASTNodeSet*,
		  SymbolPtrHasher
		  > SymbolPtrToNode;
		SymbolPtrToNode TermsAlreadySeenMap;

    //this function return true if the var occurs in term, else the
    //function returns false
    bool VarSeenInTerm(const ASTNode& var, const ASTNode& term);
    void SetofVarsSeenInTerm(const ASTNode& term, ASTNodeSet& symbols);
    void VarSeenInTerm(Symbols* term, SymbolPtrSet& visited, ASTNodeSet& found, vector<Symbols*>& av);

	};
};



#endif /* VARIABLESINEXPRESSION_H_ */
