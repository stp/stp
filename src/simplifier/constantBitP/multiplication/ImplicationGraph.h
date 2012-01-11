/*
 * ImplicationGraph.h
 *
 *  Created on: 24/03/2010
 *      Author: thansen
 */

#ifndef IMPLICATIONGRAPH_H_
#define IMPLICATIONGRAPH_H_

#include "../../../AST/UsefulDefs.h"
#include "../ConstantBitP_TransferFunctions.h"
#include "../ConstantBitP_Utility.h"
#include "Edge.h"
#include "ColumnCounts.h"
#include "ColumnStats.h"
#include <list>

namespace simplifier
{
namespace constantBitP
{

extern const bool debug_multiply;

// Relationship between bits. One bit may imply another bit.
class ImplicationGraph
{
	typedef hash_set<Edge, EdgeHasher, eqEdge> Edges;
	Edges edges;

	struct Target
	{
		EdgeType type;
		bool isLeft;
		int index;
	};

	// Contains the relevants parts of the implication graph.
	struct RelevantImplicationGraph
	{
		vector<list<Target> > left;
		vector<list<Target> > right;
		const FixedBits& l;
		const FixedBits& r;

		RelevantImplicationGraph(const FixedBits& leftFB,
				const FixedBits& rightFB, const Edges edges) :
			left(leftFB.getWidth()), right(leftFB.getWidth()), l(leftFB), r(
					rightFB)
		{
			assert(l <= r);

			Edges::iterator it = edges.begin();

			// Get all the relevant implications.
			while (it != edges.end())
			{
				if (!(it->left == leftFB && it->right == rightFB))
				{
					it++;
					continue;
				}
				EdgeType et = (EdgeType) it->type;

				{
					Target t;
					t.type = et;
					t.isLeft = false;
					t.index = it->rightIndex;
					left[it->leftIndex].push_front(t);
				}

				// The other way.
				{
					char newEdgeType = 0;
					if ((et & STRAIGHT_IMPLIES) != 0)
					{
						newEdgeType |= NOT_IMPLIES_NOT;
					}
					if ((et & NOT_IMPLIES) != 0)
					{
						newEdgeType |= NOT_IMPLIES;
					}
					if ((et & IMPLIES_NOT) != 0)
					{
						newEdgeType |= IMPLIES_NOT;
					}
					if ((et & NOT_IMPLIES_NOT) != 0)
					{
						newEdgeType |= STRAIGHT_IMPLIES;
					}

					Target t;
					t.type = (EdgeType) newEdgeType;
					t.isLeft = true;
					t.index = it->leftIndex;
					right[it->rightIndex].push_front(t);
				}

				it++;
			}

			assert(left.size() == ((unsigned) leftFB.getWidth()));
			assert(left.size() == ((unsigned) rightFB.getWidth()));

			if (debug_multiply)
			{
				cout << "left";
				for (int i = 0; i < left.size(); i++)
				{

					cout << "[" << i << ":" << left[i].size() << "] ";
				}
				cout << "right";
				for (int i = 0; i < right.size(); i++)
				{

					cout << "[" << i << ":" << right[i].size() << "] ";
				}

			}
		}
	};

	void outputArray(string msg, vector<char> copy)
	{
		const int width = copy.size();
		cout << msg;
		for (int i = width - 1; i >= 0; i--)
			if (copy[i] == (char) 3)
				cout << "-";
			else
				cout << (int) copy[i];
		cout << endl;
	}


	// return true if changed
	bool addEdge(FixedBits& left, const int leftIndex, FixedBits& right,
			const int rightIndex, const EdgeType eT)
	{
		Edge e = Edge(left, leftIndex, right, rightIndex);
		Edges::iterator it = edges.find(e);

		if (it != edges.end())
		{
			// already present.
			// But the new type might by new.
			char oldType = it->type;
			if (((~oldType) & eT) == 0)
				return false; // not changed.

			e.type = oldType | eT;

			edges.erase(e);
			edges.insert(e);
		}
		else
		{
			// not present already.
			e.type = eT;
			edges.insert(e);
		}

		if (debug_multiply)
			cout << "inserting" << e;

		return true;
	}

	bool writeIn(vector<char> left_assigned, FixedBits& left)
	{
		assert(((int)left_assigned.size()) == left.getWidth());
		unsigned bitWidth = left.getWidth();
		bool changed = false;
		for (unsigned i = 0; i < bitWidth; i++)
		{
			if (left_assigned[i] == 1)
			{
				if (left.isFixedToOne(i))
					continue;
				changed = true;
				assert(!left.isFixedToZero(i));
				left.setFixed(i, true);
				left.setValue(i, true);
			}
			else if (left_assigned[i] == 0)
			{
				if (left.isFixedToZero(i))
					continue;
				changed = true;
				assert(!left.isFixedToOne(i));
				left.setFixed(i, true);
				left.setValue(i, false);
			}
			else if (left_assigned[i] == 3)
			{
				assert(!left.isFixed(i));
			}
			else
			{
				throw new std::runtime_error("sdafas`3");
			}
		}
		return changed;
	}

	// return true if consistent.
	bool propagate(vector<char>& left_assigned, vector<char>& right_assigned,
			const int index, const bool isLeft,
			const RelevantImplicationGraph& relevant)
	{

		list<Target>::const_iterator it = isLeft ? relevant.left[index].begin()
				: relevant.right[index].begin();
		const list<Target>::const_iterator end =
				isLeft ? relevant.left[index].end()
						: relevant.right[index].end();

		vector<int> leftToRun;
		vector<int> rightToRun;

		while (it != end)
		{
			const char type = (*it).type;
			const int leftIndex = isLeft ? index : it->index;
			const int rightIndex = isLeft ? it->index : index;

			assert(isLeft != it->isLeft);

			assert( 0 == ((type & ~IMPLIES_NOT) & ~NOT_IMPLIES)); // others not implemented.

			// can only do something if xor set to unknown.
			char leftValue = left_assigned[leftIndex];
			char rightValue = right_assigned[rightIndex];

			if (debug_multiply)
			{
				cout << "checking" << endl;
				cout << "left[" << leftIndex << "] = " << (int) leftValue
						<< " ";
				cout << (int) type;
				cout << "right[" << rightIndex << "] = " << (int) rightValue
						<< endl;
			}

			if ((leftValue == 3) != (rightValue == 3))
			{
				if ((type & IMPLIES_NOT) != 0)
				{
					if (leftValue == 3 && rightValue == 1)
					{
						left_assigned[leftIndex] = 0;
						leftToRun.push_back(leftIndex);
					}

					if (leftValue == 1 && rightValue == 3)
					{
						right_assigned[rightIndex] = 0;
						rightToRun.push_back(rightIndex);
					}
				}

				if ((type & NOT_IMPLIES) != 0)
				{
					if (leftValue == 3 && rightValue == 0)
					{
						left_assigned[leftIndex] = 1;
						leftToRun.push_back(leftIndex);
					}

					if (leftValue == 0 && rightValue == 3)
					{
						right_assigned[rightIndex] = 1;
						rightToRun.push_back(rightIndex);
					}
				}
			}

			if ((type & IMPLIES_NOT) != 0)
			{
				if (leftValue == 1 && rightValue == 1)
				{
					return false;
				}
			}

			if ((type & NOT_IMPLIES) != 0)
			{
				if (leftValue == 0 && rightValue == 0)
				{
					return false;
				}

			}

			it++;
		}

		for (vector<int>::iterator it = leftToRun.begin(); it
				!= leftToRun.end(); it++)
		{
			if (!propagate(left_assigned, right_assigned, *it, true, relevant))
				return false;
		}

		for (vector<int>::iterator it = rightToRun.begin(); it
				!= rightToRun.end(); it++)
		{
			if (!propagate(left_assigned, right_assigned, *it, false, relevant))
				return false;
		}

		return true;
	}

	// If there are no implications containing a particular bit, then set the value to "setTo"
	void setIfUnconstrained(vector<char>&left_assigned,
			vector<char>&right_assigned, const char setTo,
			const RelevantImplicationGraph& relevant)
	{
		const int bitWidth = left_assigned.size();
		bool left_specified[bitWidth];
		bool right_specified[bitWidth];

		// get everything that's already set to one.
		for (int i = 0; i < bitWidth; i++)
		{
			if (left_assigned[i] != 3)
				left_specified[i] = true;
			else
				left_specified[i] = false;

			if (right_assigned[i] != 3)
				right_specified[i] = true;
			else
				right_specified[i] = false;
		}

		for (int i = 0; i < bitWidth; i++)
		{
			if (relevant.left[i].size() != 0)
				left_specified[i] = true;
			if (relevant.right[i].size() != 0)
				right_specified[i] = true;
		}

		for (int i = 0; i < bitWidth; i++)
			if (!left_specified[i])
				left_assigned[i] = setTo;

		for (int i = 0; i < bitWidth; i++)
			if (!right_specified[i])
				right_assigned[i] = setTo;

	}

	// note the assigned vectors are passed by value.
	void fill(vector<char>& left_assigned, vector<char>& right_assigned,
			vector<int>& min, vector<int>& max,
			const RelevantImplicationGraph& relevant)
	{
		const int width = left_assigned.size();
		bool done = false;

		if (debug_multiply)
		{
			outputArray("calling with left", left_assigned);
			outputArray("calling with right", right_assigned);
		}

		// Lookahead to check that something intersting may comeout. i.e. a higher max, or lower min is possible.
		{
			bool shouldContinue = false;
			for (int k = 0; ((k < width) && !shouldContinue); k++)
			{
				int ones = 0;
				int zeroes = 0;
				int unfixed = 0;

				for (int j = 0; j <= k; j++)
				{
					if (left_assigned[j] == 1 && right_assigned[k - j] == 1)
					{
						ones++;
					}
					else if (left_assigned[j] == 0 || right_assigned[k - j]
							== 0)
					{
						zeroes++;
					}
					else
						unfixed++;
				}

				if (ones + unfixed > max[k] || ones < min[k])
					shouldContinue = true;
			}
			if (!shouldContinue)
				return;
		}


		for (int i = 0; i < width && !done; i++)
		{
			if (left_assigned[i] == 3)
			{
				vector<char> left_assigned_copy(left_assigned);
				vector<char> right_assigned_copy(right_assigned);

				left_assigned[i] = 0;
				if (propagate(left_assigned, right_assigned, i, true, relevant))
					fill(left_assigned, right_assigned, min, max, relevant);

				left_assigned_copy[i] = 1;
				if (propagate(left_assigned_copy, right_assigned_copy, i, true,
						relevant))
					fill(left_assigned_copy, right_assigned_copy, min, max,
							relevant);
				done = true;
			}
			else if (right_assigned[i] == 3)
			{
				vector<char> left_assigned_copy(left_assigned);
				vector<char> right_assigned_copy(right_assigned);

				right_assigned[i] = 0;
				if (propagate(left_assigned, right_assigned, i, false, relevant))
					fill(left_assigned, right_assigned, min, max, relevant);

				right_assigned_copy[i] = 1;
				if (propagate(left_assigned_copy, right_assigned_copy, i,
						false, relevant))
					fill(left_assigned_copy, right_assigned_copy, min, max,
							relevant);
				done = true;
			}
		}

		if (debug_multiply)
		{
			outputArray("left", left_assigned);
			outputArray("right", right_assigned);
		}

		if (!done)
		{
			for (int i = 0; i < width; i++)
			{
				assert(left_assigned[i]!=3);
				assert(right_assigned[i]!=3);
			}

			for (int k = 0; k < width; k++)
			{
				int oneCount = 0;

				for (int j = 0; j <= k; j++)
				{
					oneCount+= (int)(left_assigned[j] * right_assigned[k - j]);
				}

				if (oneCount < min[k])
				{
					min[k] = oneCount;
					if (debug_multiply)
						cout << "columnL[" << k << "]=" << oneCount << endl;
				}
				if (oneCount > max[k])
				{
					max[k] = oneCount;
					if (debug_multiply)
						cout << "columnH[" << k << "]=" << oneCount << endl;
				}
			}
		}
	}

public:

	// Go through all of the edges. Fix if it can be fixed.
	Result fixUsingImplications(FixedBits& x, FixedBits& y)
	{
		const unsigned bitWidth = x.getWidth();
		vector<char> left_assigned(bitWidth, 3);
		vector<char> right_assigned(bitWidth, 3);

		FixedBits& left = x <= y ? x : y;
		FixedBits& right = x <= y ? y : x;

		for (unsigned i = 0; i < bitWidth; i++)
		{
			if (left.isFixed(i))
			{
				left_assigned[i] = left.getValue(i) ? 1 : 0;
			}
			if (right.isFixed(i))
			{
				right_assigned[i] = right.getValue(i) ? 1 : 0;
			}
		}

		RelevantImplicationGraph graph(left, right, edges);
		bool ok = true;

		for (unsigned i = 0; i < bitWidth; i++)
		{
			ok &= propagate(left_assigned, right_assigned, i, true, graph);
			ok &= propagate(left_assigned, right_assigned, i, false, graph);
		}

		if (!ok)
			return CONFLICT;

		Result r;

		bool changed = writeIn(left_assigned, left);
		changed = writeIn(right_assigned, right) | changed;

		if (changed)
			return CHANGED;

		return NO_CHANGE;
	}

	// Update the sums using the Implication Graph
	Result updateSums(const FixedBits& x, const FixedBits& y, ColumnCounts& cc)
	{
		const unsigned int bitWidth = (unsigned) x.getWidth();

		if (bitWidth > 8)
			return NO_CHANGE; // this is currently toooo slow for larger bitwidths.

		const FixedBits& left = x <= y ? x : y;
		const FixedBits& right = x <= y ? y : x;

		RelevantImplicationGraph relevant(left, right, edges);

		vector<char> left_assigned(bitWidth, 3);
		vector<char> right_assigned(bitWidth, 3);

		for (unsigned i = 0; i < bitWidth; i++)
		{
			if (left.isFixed(i))
			{
				left_assigned[i] = left.getValue(i) ? 1 : 0;
			}
			if (right.isFixed(i))
			{
				right_assigned[i] = right.getValue(i) ? 1 : 0;
			}
		}

		if (debug_multiply)
		{
			outputArray("initial left:", left_assigned);
			outputArray("initial right:", right_assigned);
		}

		vector<int> min(bitWidth, bitWidth);
		vector<int> max(bitWidth, 0);

		// maximum.
		{
			vector<char> left_assigned_copy(left_assigned);
			vector<char> right_assigned_copy(right_assigned);

			setIfUnconstrained(left_assigned_copy, right_assigned_copy, 1,
					relevant);

			if (debug_multiply)
			{
				outputArray("max left", left_assigned_copy);
				outputArray("max right", right_assigned_copy);
			}

			fill(left_assigned_copy, right_assigned_copy, min, max, relevant);
		}

		bool allAlreadyMin = true;
		for (int i = 0; i < bitWidth; i++)
			if (min[i] != 0)
				allAlreadyMin = false;

		// if they're already zero don't look.
		if (!allAlreadyMin)
		{
			// minimum.
			setIfUnconstrained(left_assigned, right_assigned, 0, relevant);
			if (debug_multiply)
			{
				outputArray("min left", left_assigned);
				outputArray("min right", right_assigned);
			}

			fill(left_assigned, right_assigned, min, max, relevant);
		}

		bool changed = false;
		for (unsigned i = 0; i < bitWidth; i++)
		{

			if (min[i] > cc.columnL[i])
			{
				cc.columnL[i] = min[i];
				changed = true;
			}

			if (max[i] < cc.columnH[i])
			{
				cc.columnH[i] = max[i];
				changed = true;
			}

			if (min[i] > max[i])
			{
				cerr << min[i] << " " << max[i] << endl;
				return CONFLICT;
			}

		}
		if (!changed)
			return NO_CHANGE;
		else
			return CHANGED;
	}

	Result discoverNewXORs(FixedBits& x, FixedBits& y, const int index,
			const int aspirationalSum)
	{
		ColumnStats cs(x, y, index);

		int columnUnfixed = cs.columnUnfixed; // both unfixed.
		int columnOneFixed = cs.columnOneFixed; // one of the values is fixed to one.
		int columnOnes = cs.columnOnes; // both are ones.

		int calcSum = aspirationalSum - columnOnes;

		if (calcSum < 0)
			return CONFLICT;

		if (columnUnfixed > 0)
			return NO_CHANGE;

		//  There are two oneFixed values. They must sum to one. So the values must be opposites.
		int a = -1, b = -1;
		bool aY = -1, bY = -1; // quieten compiler
		if (!(calcSum == 1 && columnOneFixed == 2))
			return NO_CHANGE;

		for (int i = 0; i <= index; i++)
		{
			if ((x.isFixedToOne(index - i) && !y.isFixed(i)) || (!x.isFixed(
					index - i) && y.isFixedToOne(i)))
			{
				if (a == -1)
				{
					a = i;
					if (y.isFixed(i))
						aY = false;
					else
						aY = true;
				}
				else if (b == -1)
				{
					b = i;
					if (y.isFixed(i))
						bY = false;
					else
						bY = true;

				}
				else
					throw std::runtime_error("bad");
			}
		}

		// a and b now contain the y-indexes.
		assert(a!=-1 && b!=-1);

		FixedBits& fb1 = aY ? y : x;
		FixedBits& fb2 = bY ? y : x;

		if (fb1 == fb2)
		{
		  if (debug_multiply)
		    cerr << "Not handled yet implications between the same elemtn.";
			return NO_CHANGE;
		}

		int index1 = aY ? a : index - a;
		int index2 = bY ? b : index - b;

		if (fb1 <= fb2)
		{
			bool changed = addEdge(fb1, index1, fb2, index2, NOT_IMPLIES);
			changed |= addEdge(fb1, index1, fb2, index2, IMPLIES_NOT);

			if (changed)
				return CHANGED;
		}
		else
		{
			bool changed = addEdge(fb2, index2, fb1, index1, NOT_IMPLIES);
			changed |= addEdge(fb2, index2, fb1, index1, IMPLIES_NOT);

			if (changed)
				return CHANGED;
		}
		return NO_CHANGE;
	}

	Result discoverNewNANDs(FixedBits& x, FixedBits& y, const int index,
			const int aspirationalSum)
	{
		Result result = NO_CHANGE;

		ColumnStats cs(x, y, index);

		int columnUnfixed = cs.columnUnfixed; // both unfixed.
		//int columnOneFixed = cs.columnOneFixed; // one of the values is fixed to one.
		int columnOnes = cs.columnOnes; // both are ones.
		//int columnZeroes = cs.columnZeroes; // either are zero.


		if (aspirationalSum == columnOnes && (columnUnfixed > 0))
		{
			for (int i = 0; i <= index; i++)
			{
				if (!y.isFixed(i) && !(x.isFixed(index - i)))
				{
					if (x <= y)
					{
						if (addEdge(x, index - i, y, i, IMPLIES_NOT))
							result = CHANGED;
					}
					else if (addEdge(y, i, x, index - i, IMPLIES_NOT))
						result = CHANGED;
				}
			}
		}
		return result;
	}
};

}
}

#endif /* IMPLICATIONGRAPH_H_ */
