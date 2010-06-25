#ifndef DIFFICULTYSCORE_H_
#define DIFFICULTYSCORE_H_

#include "../AST/AST.h"
#include "../AST/AST.h"
#include "../AST/ASTKind.h"

// estimate how difficult that input is to solve based on some simple rules.

namespace BEEV
{
struct DifficultyScore
{
	typedef map<ASTNode,int> Cache;

	static bool isLikeMultiplication(const Kind& k)
	{
		return k == BVMULT || k == BVDIV || k == BVMOD || k == SBVDIV || k == SBVREM || k == SBVMOD;
	}

	static int visit(const ASTNode& b, Cache& cache)
	{
		Cache::iterator it;

		if ((it = cache.find(b)) != cache.end())
			return 0; // already included.

		int score= 0;
		if (isLikeMultiplication(b.GetKind()))
			score += (b.GetValueWidth() * b.GetValueWidth() );
		else
			score += b.GetValueWidth();

		const ASTVec& c = b.GetChildren();
		ASTVec::const_iterator itC = c.begin();
		ASTVec::const_iterator itendC = c.end();
		for (; itC != itendC; itC++)
		{
			score += visit(*itC, cache);
		}

		cache[b] = score;
		return score;
	}

	static int score(const ASTNode& top)
	{
		Cache cache;
		int result = visit(top,cache);
		return result;
	}
};
};

#endif /* DIFFICULTYSCORE_H_ */



