#ifndef EDGE_H_
#define EDGE_H_

namespace simplifier
{
namespace constantBitP
{


typedef enum EdgeTypeRec
{
	STRAIGHT_IMPLIES = 1, NOT_IMPLIES = 2, IMPLIES_NOT = 4, NOT_IMPLIES_NOT = 8
} EdgeType;

struct Edge
{
private:
	Edge& operator=(const Edge&);
	//Edge(const Edge& copy);

public:
	FixedBits& left;
	const int leftIndex;
	FixedBits& right;
	const int rightIndex;
	char type;

	Edge(FixedBits& _left, int _leftIndex, FixedBits& _right, int _rightIndex) :
		left(_left), leftIndex(_leftIndex), right(_right), rightIndex(
				_rightIndex)

	{
		type = 0;
		assert(left <= right);
		assert(leftIndex < left.getWidth());
		assert(rightIndex < right.getWidth());
		assert(leftIndex >=0);
		assert(rightIndex >=0);
	}
};

std::ostream& operator<<(std::ostream& output, struct Edge e)
{
	output << e.left << "[";
	output << e.leftIndex << "]";
	output << " " << ((int) e.type) << " ";
	output << e.right << "[";
	output << e.rightIndex << "]" << endl;

	return output;
}

struct EdgeHasher
{
	size_t operator()(const Edge& e1) const
	{
		return ((size_t) &(e1.left)) + ((size_t) &(e1.right)) + e1.leftIndex
				+ e1.rightIndex;
	}
};

struct eqEdge
{
	bool operator()(const Edge& e1, const Edge& e2) const
	{
		return (e1.left) == (e2.left) && e1.leftIndex == e2.leftIndex
				&& (e1.right == e2.right) && e1.rightIndex == e2.rightIndex;
	}
};

}
}

#endif /* EDGE_H_ */
