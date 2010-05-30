#ifndef COUNTOFSYMBOLS_H_
#define COUNTOFSYMBOLS_H_

#include "../AST/AST.h"
#include <cassert>
#include "simplifier.h"

namespace BEEV
{
class CountOfSymbols {


	//collect all the vars in the lhs and rhs
	//Build this only if it's needed.

	typedef hash_map<ASTNode, int, ASTNode::ASTNodeHasher,
			ASTNode::ASTNodeEqual> ASTNodeToIntMap;

	ASTNodeToIntMap Vars;
	const ASTNode& top;
	bool loaded;

	ASTNodeSet TermsAlreadySeenMap;

	//collects the vars in the term 'lhs' into the multiset Vars
	void VarsInTheTerm_TopLevel(const ASTNode& lhs) {
		TermsAlreadySeenMap.clear();
		VarsInTheTerm(lhs);
	}

	//collects the vars in the term 'lhs' into the multiset Vars
	void VarsInTheTerm(const ASTNode& term) {
		ASTNodeSet::const_iterator it;
		bool inserted = (TermsAlreadySeenMap.insert(term).second);

		if (!inserted)
			return;

		switch (term.GetKind()) {
		case BVCONST:
			return;
		case SYMBOL:
			//cerr << "debugging: symbol added: " << term << endl;
			Vars[term]++;
			break;
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

		//ensures that you don't double count. if you have seen the term
		//once, then memoize
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
			VarsInTheTerm_TopLevel(top);
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
