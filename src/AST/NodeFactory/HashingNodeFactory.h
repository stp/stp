// A Node factory that only does structural hashing.
#ifndef HASHINGNODEFACTORY_H_
#define HASHINGNODEFACTORY_H_

#include "NodeFactory.h"
#include "ASTKind.h"
namespace BEEV
{
	class STPMgr;
}

class HashingNodeFactory : public NodeFactory
{
	BEEV::STPMgr& bm;
public:
	HashingNodeFactory(BEEV::STPMgr& bm_)
	: bm(bm_)
	{
	}

	virtual ~HashingNodeFactory();
	BEEV::ASTNode CreateNode(const BEEV::Kind kind,	const BEEV::ASTVec & back_children);
	BEEV::ASTNode CreateTerm(BEEV::Kind kind, unsigned int width,const BEEV::ASTVec &children);

};

#endif /* HASHINGNODEFACTORY_H_ */
