/*
 * substitutionMap.h
 *
 */

#ifndef SUBSTITUTIONMAP_H_
#define SUBSTITUTIONMAP_H_

#include "../AST/AST.h"
#include "../STPManager/STPManager.h"
#include "../AST/NodeFactory/SimplifyingNodeFactory.h"

namespace BEEV {

class Simplifier;
class ArrayTransformer;

class SubstitutionMap {

	ASTNodeMap * SolverMap;
	Simplifier *simp;
	STPMgr* bm;
	ASTNode ASTTrue, ASTFalse, ASTUndefined;

public:
	SubstitutionMap(Simplifier *_simp, STPMgr* _bm) {
		simp = _simp;
		bm = _bm;

		ASTTrue  = bm->CreateNode(TRUE);
	      ASTFalse = bm->CreateNode(FALSE);
	      ASTUndefined = bm->CreateNode(UNDEFINED);

		SolverMap = new ASTNodeMap(INITIAL_TABLE_SIZE);

	}

	void clear() {
		SolverMap->clear();
	}

	virtual ~SubstitutionMap();

	//check the solver map for 'key'. If key is present, then return the
	//value by reference in the argument 'output'
	bool CheckSubstitutionMap(const ASTNode& key, ASTNode& output) {
		ASTNodeMap::iterator it = SolverMap->find(key);
		if (it != SolverMap->end()) {
			output = it->second;
			return true;
		}
		return false;
	}

	//update solvermap with (key,value) pair
	bool UpdateSolverMap(const ASTNode& key, const ASTNode& value) {
		ASTNode var = (BVEXTRACT == key.GetKind()) ? key[0] : key;
		if (!CheckSubstitutionMap(var) && key != value) {
			(*SolverMap)[key] = value;
			return true;
		}
		return false;
	} //end of UpdateSolverMap()

	const ASTNodeMap * Return_SolverMap() {
		return SolverMap;
	} // End of SolverMap()



	bool CheckSubstitutionMap(const ASTNode& key) {
		if (SolverMap->find(key) != SolverMap->end())
			return true;
		else
			return false;
	}

	bool UpdateSubstitutionMap(const ASTNode& e0, const ASTNode& e1) {
		int i = TermOrder(e0, e1);
		if (0 == i)
			return false;

		assert(e0 != e1); // One side should be a variable, the other a constant.
		assert(e0.GetValueWidth() == e1.GetValueWidth());
		assert(e0.GetIndexWidth() == e1.GetIndexWidth());

		if (SYMBOL == e1.GetKind() && CheckSubstitutionMap(e1))
		{
			// if we didn't check this, scenarios like:
			// a <-> b
			// b <-> a
			// would cause a loop.
			return false;
		}

		//e0 is of the form READ(Arr,const), and e1 is const, or
		//e0 is of the form var, and e1 is const
		if (1 == i && !CheckSubstitutionMap(e0)) {
			assert((e1.GetKind() == TRUE) ||
					(e1.GetKind() == FALSE) ||
					(e1.GetKind() == SYMBOL) ||
					(e1.GetKind() == BVCONST));
			(*SolverMap)[e0] = e1;
			return true;
		}

		//e1 is of the form READ(Arr,const), and e0 is const, or
		//e1 is of the form var, and e0 is const
		if (-1 == i && !CheckSubstitutionMap(e1)) {
			assert((e0.GetKind() == TRUE) ||
					(e0.GetKind() == FALSE) ||
					(e0.GetKind() == SYMBOL) ||
					(e0.GetKind() == BVCONST));
			(*SolverMap)[e1] = e0;
			return true;
		}

		return false;
	}

	ASTNode CreateSubstitutionMap(const ASTNode& a,   ArrayTransformer*at);

	ASTNode applySubstitutionMap(const ASTNode& n);

	// Replace any nodes in "n" that exist in the fromTo map.
	// NB the fromTo map is changed.
	ASTNode replace(const ASTNode& n, ASTNodeMap& fromTo, ASTNodeMap& cache);
};

}
;
#endif /* SUBSTITUTIONMAP_H_ */
