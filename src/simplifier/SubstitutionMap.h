/*
 * substitutionMap.h
 *
 */

#ifndef SUBSTITUTIONMAP_H_
#define SUBSTITUTIONMAP_H_

#include "../AST/AST.h"
#include "../STPManager/STPManager.h"
#include "../AST/NodeFactory/SimplifyingNodeFactory.h"
#include "VariablesInExpression.h"

namespace BEEV {

class Simplifier;
class ArrayTransformer;

const bool debug_substn = false;

class SubstitutionMap {

	ASTNodeMap * SolverMap;
	Simplifier *simp;
	STPMgr* bm;
	ASTNode ASTTrue, ASTFalse, ASTUndefined;

	// These are used to avoid substituting {x = f(y,z), z = f(x)}
	typedef hash_map<ASTNode, Symbols*,ASTNode::ASTNodeHasher> DependsType;
	DependsType dependsOn; // The lhs depends on the variables in the rhs.
	ASTNodeSet rhs; // All the rhs that have been seeen.
	VariablesInExpression::SymbolPtrSet rhs_visited; // the rhs contains all the variables in here already.

	int loopCount;

public:

	// When the substitutionMap has been applied globally, then,
	// these are no longer needed.
	void haveAppliedSubstitutionMap()
	{
		dependsOn.clear();
		rhs.clear();
		rhs_visited.clear();
	}


	VariablesInExpression vars;

	SubstitutionMap(Simplifier *_simp, STPMgr* _bm) {
		simp = _simp;
		bm = _bm;

		ASTTrue  = bm->CreateNode(TRUE);
	      ASTFalse = bm->CreateNode(FALSE);
	      ASTUndefined = bm->CreateNode(UNDEFINED);

		SolverMap = new ASTNodeMap(INITIAL_TABLE_SIZE);
		loopCount = 0;
	}

	void clear()
	{
		SolverMap->clear();
		haveAppliedSubstitutionMap();
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

	// Adds to the dependency graph that n0 depends on the variables in n1.
	// It's not the transitive closure of the dependencies. Just the variables in the expression "n1".
	// This is only needed as long as all the substitution rules haven't been written through.
	void buildDepends(const ASTNode& n0, const ASTNode& n1)
	{
		if (n0.GetKind() != SYMBOL)
			return;

		if (n1.isConstant())
			return;

		vector<Symbols*> av;
		vars.VarSeenInTerm(vars.getSymbol(n1), rhs_visited, rhs, av);

		sort(av.begin(), av.end());
		for (int i =0; i < av.size();i++)
		{
			if (i!=0 && av[i] == av[i-1])
				continue; // Treat it like a set of Symbol* in effect.
			const ASTNodeSet& sym = *(vars.TermsAlreadySeenMap.find(av[i])->second);
			rhs.insert(sym.begin(), sym.end());
		}

		assert (dependsOn.find(n0) == dependsOn.end());
		dependsOn.insert(make_pair(n0,vars.getSymbol(n1)));
	}

	// Take the transitive closure of the varsToCheck. Storing the result in visited.
	void loops_helper(const set<ASTNode>& varsToCheck, set<ASTNode>& visited)
	{
		set<ASTNode>::const_iterator visitedIt = visited.begin();

		set<ASTNode> toVisit;
		vector<ASTNode> visitedN;

		// for each variable.
		for (set<ASTNode>::const_iterator varIt = varsToCheck.begin(); varIt != varsToCheck.end(); varIt++)
		{
			while (*visitedIt < *varIt && visitedIt != visited.end())
				visitedIt++;

			if (*visitedIt == *varIt)
				continue;

			visitedN.push_back(*varIt);
			DependsType::iterator it;
			if ((it = dependsOn.find(*varIt)) != dependsOn.end())
			{
				Symbols* s= it->second;
				bool destruct;
				ASTNodeSet* varsSeen = vars.SetofVarsSeenInTerm(s,destruct);
				toVisit.insert(varsSeen->begin(), varsSeen->end());

				if (destruct)
					delete varsSeen;
			}
		}

		visited.insert(visitedN.begin(), visitedN.end());

		visitedN.clear();

		if (toVisit.size() !=0)
			loops_helper(toVisit, visited);
	}

	// If n0 is replaced by n1 in the substitution map. Will it cause a loop?
	// i.e. will the dependency graph be an acyclic graph still.
	// For example, if we have x = F(y,z,w), it would make the substitutionMap loop
	// if there's already z = F(x).
	bool loops(const ASTNode& n0, const ASTNode& n1)
		{
		if (n0.GetKind() != SYMBOL)
			return false; // sometimes this function is called with constants on the lhs.

		if (n1.isConstant())
			return false; // constants contain no variables. Can't loop.

		// We are adding an edge FROM n0, so unless there is already an edge TO n0,
		// there is no change it can loop. Unless adding this would add a TO and FROM edge.
		if (rhs.find(n0) == rhs.end())
		{
			return vars.VarSeenInTerm(n0,n1);
		}

		if (n1.GetKind() == SYMBOL && dependsOn.find(n1) == dependsOn.end() )
			return false; // The rhs is a symbol and doesn't appear.

		if (debug_substn)
			cout << loopCount++  << endl;

		bool destruct = true;
		ASTNodeSet* dependN = vars.SetofVarsSeenInTerm(n1,destruct);

		if (debug_substn)
		{
			cout << n0 << " " <<  n1.GetNodeNum(); //<< " Expression size:" << bm->NodeSize(n1,true);
			cout << "Variables in expression: "<< dependN->size() << endl;
		}

		set<ASTNode> depend(dependN->begin(), dependN->end());

		if (destruct)
			delete dependN;

		set<ASTNode> visited;
		loops_helper(depend,visited);

		bool loops = visited.find(n0) != visited.end();

		if (debug_substn)
			cout << "Visited:" << visited.size() << "Loops:" << loops << endl;

		return (loops);
		}

	//update solvermap with (key,value) pair
	bool UpdateSolverMap(const ASTNode& key, const ASTNode& value) {
		ASTNode var = (BVEXTRACT == key.GetKind()) ? key[0] : key;

		if (var.GetKind() == SYMBOL && loops(var,value))
			return false;


		if (!CheckSubstitutionMap(var) && key != value) {
			//cerr << "from" << key << "to" <<value;
			buildDepends(key,value);
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

	// The substitutionMap will be updated, given x <-> f(w,z,y), iff,
	// 1) x doesn't appear in the rhs.
	// 2) x hasn't already been stored in the substitution map.
	// 3) none of the variables in the transitive closure of the rhs depend on x.
	bool UpdateSubstitutionMap(const ASTNode& e0, const ASTNode& e1) {
		int i = TermOrder(e0, e1);
		if (0 == i)
			return false;

		assert(e0 != e1);
		assert(e0.GetValueWidth() == e1.GetValueWidth());
		assert(e0.GetIndexWidth() == e1.GetIndexWidth());

		if (e0.GetKind() == SYMBOL)
		{
			if (CheckSubstitutionMap(e0))
				return false; // already in the map.

			if (loops(e0,e1))
				return false; // loops.
		}

		if (e1.GetKind() == SYMBOL)
		{
			if (CheckSubstitutionMap(e1))
				return false; // already in the map.


			if (loops(e1,e0))
				return false; // loops
		}

		//e0 is of the form READ(Arr,const), and e1 is const, or
		//e0 is of the form var, and e1 is a function.
		if (1 == i && !CheckSubstitutionMap(e0)) {
			buildDepends(e0,e1);
			(*SolverMap)[e0] = e1;
			return true;
		}

		//e1 is of the form READ(Arr,const), and e0 is const, or
		//e1 is of the form var, and e0 is const
		if (-1 == i && !CheckSubstitutionMap(e1)) {
			buildDepends(e1,e0);
			(*SolverMap)[e1] = e0;
			return true;
		}

		return false;
	}

	ASTNode CreateSubstitutionMap(const ASTNode& a,   ArrayTransformer*at);

	ASTNode applySubstitutionMap(const ASTNode& n);

	ASTNode applySubstitutionMapUntilArrays(const ASTNode& n);

	// Replace any nodes in "n" that exist in the fromTo map.
	// NB the fromTo map is changed.
	static ASTNode replace(const ASTNode& n, ASTNodeMap& fromTo, ASTNodeMap& cache, NodeFactory *nf);
    static ASTNode replace(const ASTNode& n, ASTNodeMap& fromTo, ASTNodeMap& cache, NodeFactory *nf, bool stopAtArrays);

};

}
;
#endif /* SUBSTITUTIONMAP_H_ */
