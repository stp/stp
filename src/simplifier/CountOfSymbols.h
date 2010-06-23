#ifndef COUNTOFSYMBOLS_H_
#define COUNTOFSYMBOLS_H_

#include "../AST/AST.h"
#include <cassert>
#include "Symbols.h"

// Count the number of times each symbol appears in the input term.
// This can be expensive to build for large terms, so it's built lazily.

namespace BEEV
{
class CountOfSymbols {

	typedef hash_map<ASTNode, int, ASTNode::ASTNodeHasher,
			ASTNode::ASTNodeEqual> ASTNodeToIntMap;

	ASTNodeToIntMap Vars;
	const Symbols* top;
	bool loaded;

	// If no variables are found in "term", then it's cached---we don't need to visit there
	// again. However, if it's true, we need to revisit (and hence recount), the next time it's
	// encountered.

	void VarsInTheTerm(const Symbols* term) {
		assert(!term->empty());

		if (!term->found.IsNull())
		{
			Vars[term->found]++;
		}
		else
		{
			const vector<Symbols*>& c = term->children;
			for (vector<Symbols*>::const_iterator it = c.begin(), itend = c.end(); it
					!= itend; it++)
			{
				VarsInTheTerm(*it);
			}
		}
	} //end of VarsInTheTerm()

public:

	CountOfSymbols(const Symbols* top_v) :
		top(top_v) {
		loaded = false;
	}

	bool single(const ASTNode &m) {
		if (!loaded)
		{
			VarsInTheTerm(top);
			loaded = true;
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
