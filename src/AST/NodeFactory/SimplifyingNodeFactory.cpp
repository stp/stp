/* A node factory that:
 * 	    * Sorts children to increases sharing,
 *	    * Performs constant evaluation,
 *	    * performs simplify boolean simplifications,
 *	    * converts less thans to greater thans.
 *
 * NOTE: CreateNode doesn't necessary return a node with the same Kind as what it was called
 * with. For example: (AND TRUE FALSE) will return FALSE. Which isn't an AND node.
 *
 * The intention is to never create nodes that will later be simplified by single level
 * re-write rules. So we will never create the node (NOT(NOT x)). This is and example of
 * a multi-level rule that never increases the global number of nodes.
 *
 * These rules never increase the total number of nodes.  They are complimented by
 * multi-level re-write rules that consider the global reference count when simplifying.
 *
 */

#include "../../AST/AST.h"
#include <cassert>
#include "SimplifyingNodeFactory.h"
#include "../../simplifier/simplifier.h"

using BEEV::Kind;

static bool debug_simplifyingNodeFactory = false;

ASTNode SimplifyingNodeFactory::CreateNode(Kind kind, const ASTVec & children)
{

	assert(kind != BEEV::SYMBOL); // These are created specially.

	// If all the parameters are constant, return the constant value.
	// The bitblaster calls CreateNode with a boolean vector. We don't try to simplify those.
	if (kind != BEEV::UNDEFINED)
	{
		bool allConstant = true;

		for (unsigned i = 0; i < children.size(); i++)
			if (!children[i].isConstant())
			{
				allConstant = false;
				break;
			}

		if (allConstant)
		{
			const ASTNode& hash = hashing.CreateNode(kind, children);
			const ASTNode& c = NonMemberBVConstEvaluator(hash);
			assert(c.isConstant());
			return c;
		}
	}
	ASTNode result;

	switch (kind)
	{

	case BEEV::BVLT:
		assert(children.size() ==2);
		result = NodeFactory::CreateNode(BEEV::BVGT, children[1], children[0]);
		break;

	case BEEV::BVLE:
		assert(children.size() ==2);
		result = NodeFactory::CreateNode(BEEV::BVGE, children[1], children[0]);
		break;

	case BEEV::BVSLT:
		assert(children.size() ==2);
		result = NodeFactory::CreateNode(BEEV::BVSGT, children[1], children[0]);
		break;

	case BEEV::BVSLE:
		assert(children.size() ==2);
		result = NodeFactory::CreateNode(BEEV::BVSGE, children[1], children[0]);
		break;

	case BEEV::NOT:
		result = CreateSimpleNot(children);
		break;
	case BEEV::AND:
		result = CreateSimpleAndOr(1, children);
		break;
	case BEEV::OR:
		result = CreateSimpleAndOr(0, children);
		break;
	case BEEV::NAND:
		result = CreateSimpleNot(CreateSimpleAndOr(1, children));
		break;
	case BEEV::NOR:
		result = CreateSimpleNot(CreateSimpleAndOr(0, children));
		break;
	case BEEV::XOR:
		result = CreateSimpleXor(children);
		break;
	case BEEV::ITE:
		result = CreateSimpleFormITE(children);
		break;
	case BEEV::EQ:
		result = CreateSimpleEQ(children);
		break;
	default:
		result = hashing.CreateNode(kind, children);
	}

	return result;
}

ASTNode SimplifyingNodeFactory::CreateSimpleNot(const ASTNode& form)
{
	const Kind k = form.GetKind();
	switch (k)
	{
	case BEEV::FALSE:
	{
		return form.GetSTPMgr()->ASTTrue;
	}
	case BEEV::TRUE:
	{
		return form.GetSTPMgr()->ASTFalse;
	}
	case BEEV::NOT:
	{
		return form[0];
	} // NOT NOT cancellation
	default:
	{
		ASTVec children;
		children.push_back(form);
		return hashing.CreateNode(BEEV::NOT, children);
	}
	}
}

ASTNode SimplifyingNodeFactory::CreateSimpleNot(const ASTVec& children)
{
	const Kind k = children[0].GetKind();
	switch (k)
	{
	case BEEV::FALSE:
	{
		return children[0].GetSTPMgr()->ASTTrue;
	}
	case BEEV::TRUE:
	{
		return children[0].GetSTPMgr()->ASTFalse;
	}
	case BEEV::NOT:
	{
		return children[0][0];
	} // NOT NOT cancellation
	default:
	{
		return hashing.CreateNode(BEEV::NOT, children);
	}
	}
}

ASTNode SimplifyingNodeFactory::CreateSimpleAndOr(bool IsAnd,
		const ASTNode& form1, const ASTNode& form2)
{
	ASTVec children;
	children.push_back(form1);
	children.push_back(form2);
	return CreateSimpleAndOr(IsAnd, children);
}

ASTNode SimplifyingNodeFactory::CreateSimpleAndOr(bool IsAnd,
		const ASTVec &children)
{
	const Kind k = IsAnd ? BEEV::AND : BEEV::OR;

	if (debug_simplifyingNodeFactory)
	{
		cout << "========" << endl << "CreateSimpAndOr " << k << " ";
		lpvec(children);
		cout << endl;
	}

	const ASTNode& annihilator = (IsAnd ? ASTFalse : ASTTrue);
	const ASTNode& identity = (IsAnd ? ASTTrue : ASTFalse);

	ASTNode retval;

	const ASTVec::const_iterator it_end = children.end();
	for (ASTVec::const_iterator it = children.begin(); it != it_end; it++)
	{
		ASTVec::const_iterator next_it;

		bool nextexists = (it + 1 < it_end);
		if (nextexists)
			next_it = it + 1;
		else
			next_it = it_end;

		if (*it == annihilator)
		{
			retval = annihilator;
			if (debug_simplifyingNodeFactory)
			{
				cout << "Annihilator" << endl;
			}
			return retval;
		}
		else if (*it == identity || (nextexists && (*next_it == *it)))
		{
			// just drop it
		}
	}

	// If we get here, we saw no annihilators, and children should
	// be only the non-True nodes.
	if (children.size() < 2)
	{
		if (0 == children.size())
		{
			retval = identity;
		}
		else
		{
			// there is just one child
			retval = children[0];
		}
	}
	else
	{
		// 2 or more children.  Create a new node.
		retval = hashing.CreateNode(IsAnd ? BEEV::AND : BEEV::OR, children);
	}
	if (debug_simplifyingNodeFactory)
	{
		cout << "returns " << retval << endl;
	}
	return retval;
}


//Tries to simplify the input to TRUE/FALSE. if it fails, then
//return the constructed equality
ASTNode SimplifyingNodeFactory::CreateSimpleEQ(const ASTVec& children)
{
	const ASTNode& in1 = children[0];
	const ASTNode& in2 = children[1];
	const Kind k1 = in1.GetKind();
	const Kind k2 = in2.GetKind();

	if (in1 == in2)
		//terms are syntactically the same
		return in1.GetSTPMgr()->ASTTrue;

	//here the terms are definitely not syntactically equal but may be
	//semantically equal.
	if (BEEV::BVCONST == k1 && BEEV::BVCONST == k2)
		return in1.GetSTPMgr()->ASTFalse;

	//last resort is to CreateNode
	return hashing.CreateNode(BEEV::EQ, children);
}

// Constant children are accumulated in "accumconst".
ASTNode SimplifyingNodeFactory::CreateSimpleXor(const ASTVec &children)
{
	if (debug_simplifyingNodeFactory)
	{
		cout << "========" << endl << "CreateSimpXor ";
		lpvec(children);
		cout << endl;
	}

	ASTVec flat_children; // empty vector
	flat_children = children;

	// sort so that identical nodes occur in sequential runs, followed by
	// their negations.
	SortByExprNum(flat_children);

	// This is the C Boolean value of all constant args seen.  It is initially
	// 0.  TRUE children cause it to change value.
	bool accumconst = 0;

	ASTVec new_children;
	new_children.reserve(children.size());

	const ASTVec::const_iterator it_end = flat_children.end();
	ASTVec::iterator next_it;
	for (ASTVec::iterator it = flat_children.begin(); it != it_end; it++)
	{
		next_it = it + 1;
		bool nextexists = (next_it < it_end);

		if (ASTTrue == *it)
		{
			accumconst = !accumconst;
		}
		else if (ASTFalse == *it)
		{
			// Ignore it
		}
		else if (nextexists && (*next_it == *it))
		{
			// x XOR x = FALSE.  Skip current, write "false" into next_it
			// so that it gets tossed, too.
			*next_it = ASTFalse;
		}
		else if (nextexists && (next_it->GetKind() == BEEV::NOT)
				&& ((*next_it)[0] == *it))
		{
			// x XOR NOT x = TRUE.  Skip current, write "true" into next_it
			// so that it gets tossed, too.
			*next_it = ASTTrue;
		}
		else if (BEEV::NOT == it->GetKind())
		{
			// If child is (NOT alpha), we can flip accumconst and use alpha.
			// This is ok because (NOT alpha) == TRUE XOR alpha
			accumconst = !accumconst;
			// CreateSimpNot just takes child of not.
			new_children.push_back(CreateSimpleNot(*it));
		}
		else
		{
			new_children.push_back(*it);
		}
	}

	ASTNode retval;

	// Children should be non-constant.
	if (new_children.size() < 2)
	{
		if (0 == new_children.size())
		{
			// XOR(TRUE, FALSE) -- accumconst will be 1.
			if (accumconst)
			{
				retval = ASTTrue;
			}
			else
			{
				retval = ASTFalse;
			}
		}
		else
		{
			// there is just one child
			// XOR(x, TRUE) -- accumconst will be 1.
			if (accumconst)
			{
				retval = CreateSimpleNot(new_children[0]);
			}
			else
			{
				retval = new_children[0];
			}
		}
	}
	else
	{
		// negate first child if accumconst == 1
		if (accumconst)
		{
			new_children[0] = CreateSimpleNot(new_children[0]);
		}
		retval = hashing.CreateNode(BEEV::XOR, new_children);
	}

	if (debug_simplifyingNodeFactory)
	{
		cout << "returns " << retval << endl;
	}
	return retval;
}

// FIXME:  How do I know whether ITE is a formula or not?
ASTNode SimplifyingNodeFactory::CreateSimpleFormITE(const ASTVec& children)
{

	const ASTNode& child0 = children[0];
	const ASTNode& child1 = children[1];
	const ASTNode& child2 = children[2];

	ASTNode retval;

	if (debug_simplifyingNodeFactory)
	{
		cout << "========" << endl << "CreateSimpleFormITE " << child0
				<< child1 << child2 << endl;
	}

	if (ASTTrue == child0)
	{
		retval = child1;
	}
	else if (ASTFalse == child0)
	{
		retval = child2;
	}
	else if (child1 == child2)
	{
		retval = child1;
	}
	// ITE(x, TRUE, y ) == x OR y
	else if (ASTTrue == child1)
	{
		retval = CreateSimpleAndOr(0, child0, child2);
	}
	// ITE(x, FALSE, y ) == (!x AND y)
	else if (ASTFalse == child1)
	{
		retval = CreateSimpleAndOr(1, CreateSimpleNot(child0), child2);
	}
	// ITE(x, y, TRUE ) == (!x OR y)
	else if (ASTTrue == child2)
	{
		retval = CreateSimpleAndOr(0, CreateSimpleNot(child0), child1);
	}
	// ITE(x, y, FALSE ) == (x AND y)
	else if (ASTFalse == child2)
	{
		retval = CreateSimpleAndOr(1, child0, child1);
	}
	else
	{
		retval = hashing.CreateNode(BEEV::ITE, children);
	}

	if (debug_simplifyingNodeFactory)
	{
		cout << "returns " << retval << endl;
	}

	return retval;
}

// Move reads down through writes until, either we hit a write to an identical (syntactically) index,
// or we hit a write to an index that might be the same. This is intended to simplify things like:
// read(write(write(A,1,2),2,3),4) cheaply.
// The "children" that are passed should be the children of a READ.
ASTNode SimplifyingNodeFactory::chaseRead(const ASTVec& children, unsigned int width)
{
	assert(children[0].GetKind() == BEEV::WRITE);
	const ASTNode& readIndex = children[1];
	ASTNode write = children[0];

	const bool read_is_const = (BEEV::BVCONST == readIndex.GetKind());

	while (write.GetKind() == BEEV::WRITE)
	{
		const ASTNode& write_index = write[1];

		if (readIndex == write_index)
		{
			// The are definately the same.
			//cerr << "-";
			return write[2];
		}
		else if (read_is_const && BEEV::BVCONST == write_index.GetKind())
		{
			// They are definately different. Ignore this.
			//cerr << "+";
		}else
		{
			// They may be the same. Exit.
			//cerr << "#";
			break;
		}
		write = write[0];
	}
	return hashing.CreateTerm(BEEV::READ, width, write,readIndex);
}


ASTNode SimplifyingNodeFactory::CreateTerm(Kind kind, unsigned int width,
		const ASTVec &children)
{
	if (!is_Term_kind(kind))
		FatalError("CreateTerm:  Illegal kind to CreateTerm:", ASTUndefined,
				kind);

	assert(kind != BEEV::BVCONST); // These are created specially.
	assert(kind != BEEV::SYMBOL); // so are these.

	// If all the parameters are constant, return the constant value.
	bool allConstant = true;
	for (unsigned i = 0; i < children.size(); i++)
		if (!children[i].isConstant())
		{
			allConstant = false;
			break;
		}

	assert(bm.hashingNodeFactory == &hashing);

	if (allConstant)
	{
		const ASTNode& hash = hashing.CreateTerm(kind, width, children);
		const ASTNode& c = NonMemberBVConstEvaluator(hash);
		assert(c.isConstant());
		return c;
	}

	ASTNode result;

	switch (kind)
	{
	case BEEV::ITE:
	{
		if (children[0]== ASTTrue)
			result = children[1];
		else if (children[0]== ASTFalse)
			result = children[2];
		else if (children[1] == children[2])
			result = children[1];
		break;
	}

	case BEEV::BVNEG:
	{
		switch (children[0].GetKind())
		{

		case BEEV::BVNEG:
			result = children[0][0];
			break;
		default: // quieten compiler.
			break;
		}
	}
	break;

	case BEEV::READ:
	if (children[0].GetKind() == BEEV::WRITE)
	{
		result = chaseRead(children,width);
	}
	break;

	default: // quieten compiler.
		break;
	}

	if (result.IsNull())
		result = hashing.CreateTerm(kind, width, children);

	return result;
}
