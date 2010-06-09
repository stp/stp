#ifndef COUNTOFSYMBOLS_H_
#define COUNTOFSYMBOLS_H_

#include "../AST/AST.h"
#include <cassert>

// Count the number of times each symbol appears in the input term.
// This can be expensive to build for large terms, so it's built lazily.

namespace BEEV
{
class CountOfSymbols {

	typedef hash_map<ASTNode, int, ASTNode::ASTNodeHasher,
			ASTNode::ASTNodeEqual> ASTNodeToIntMap;

	ASTNodeToIntMap Vars;
	const ASTNode& top;
	bool loaded;

	ASTNodeSet visited;

	void VarsInTheTerm(const ASTNode& term) {

		if (visited.find(term) != visited.end())
			return;

		switch (term.GetKind()) {
		case BVCONST:
			return;
		case SYMBOL:
			//cerr << "debugging: symbol added: " << term << endl;
			Vars[term]++;
			return;
		case READ:
			//skip the arrayname, provided the arrayname is a SYMBOL
			//But we don't skip it if it's a WRITE function??
			if (SYMBOL == term[0].GetKind()) {
				VarsInTheTerm(term[1]);
			} else {
				VarsInTheTerm(term[0]);
				VarsInTheTerm(term[1]);
			}
			break;
		default: {
			const ASTVec& c = term.GetChildren();
			for (ASTVec::const_iterator it = c.begin(), itend = c.end(); it
					!= itend; it++) {
				VarsInTheTerm(*it);
			}
			break;
		}
		}

		visited.insert(term);
		return;
	} //end of VarsInTheTerm()

public:

	CountOfSymbols(const ASTNode& top_v) :
		top(top_v) {
		loaded = false;
	}

	bool single(const ASTNode &m) {
		if (!loaded)
		{
			VarsInTheTerm(top);
			loaded = true;
			visited.clear();
		}

		ASTNodeToIntMap::const_iterator it = Vars.find(m);
		if (it == Vars.end())
			return false;
		else
			return (it->second == 1);
	}
};
}
#endif /* COUNTOFSYMBOLS_H_ */
