// Wrapper around the main beevmgr class given to the parsers.
// Over time I hope the parsers will interact entirely through this class.

#ifndef PARSERINTERFACE_H_
#define PARSERINTERFACE_H_

#include "../AST/AST.h"
#include "../AST/NodeFactory/NodeFactory.h"
#include <cassert>
#include "LetMgr.h"
#include "../STPManager/STPManager.h"

namespace BEEV
{
using BEEV::STPMgr;


// There's no BVTypeCheck() function. Use a typechecking node factory instead.

class ParserInterface
{
	STPMgr& bm;

public:
	LETMgr letMgr;
	NodeFactory* nf;

	ParserInterface(STPMgr &bm_, NodeFactory* factory)
	: bm(bm_),
	  nf(factory),
	  letMgr(bm.ASTUndefined)
	{
		assert(nf != NULL);
	}

	const ASTVec GetAsserts(void)
	{
		return bm.GetAsserts();
	}

	UserDefinedFlags& getUserFlags()
	{
		return bm.UserFlags;
	}

	void AddAssert(const ASTNode& assert)
	{
		bm.AddAssert(assert);
	}

    void AddQuery(const ASTNode& q)
    {
    	bm.AddQuery(q);
    }

	//NODES//
    ASTNode CreateNode(BEEV::Kind kind, const BEEV::ASTVec& children = _empty_ASTVec)
    {
   	 return nf->CreateNode(kind,children);
    }

    //	These belong in the node factory..

    //TERMS//
    ASTNode CreateZeroConst(unsigned int width)
    {
    	return bm.CreateZeroConst(width);
    }

    ASTNode CreateOneConst(unsigned int width)
    {
    	 return bm.CreateOneConst(width);
    }

    ASTNode CreateBVConst(string*& strval, int base, int bit_width)
    {
    	return bm.CreateBVConst(strval, base, bit_width);
    }

    ASTNode CreateBVConst(const char* const strval, int base)
    {
    	return bm.CreateBVConst(strval, base);
    }

    ASTNode CreateBVConst(unsigned int width, unsigned long long int bvconst)
    {
    	return bm.CreateBVConst(width, bvconst);
    }

    ASTNode CreateSymbol(const char * const name)
    {
    	return bm.CreateSymbol(name);
    }
};
}

#endif /* PARSERINTERFACE_H_ */
