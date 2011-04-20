// Wrapper around the main beevmgr class given to the parsers.
// Over time I hope the parsers will interact entirely through this class.

#ifndef PARSERINTERFACE_H_
#define PARSERINTERFACE_H_

#include "../AST/AST.h"
#include "../AST/NodeFactory/NodeFactory.h"
#include <cassert>
#include "LetMgr.h"
#include "../STPManager/STPManager.h"
//#include "../boost/pool/object_pool.hpp"

namespace BEEV
{
using BEEV::STPMgr;


// There's no BVTypeCheck() function. Use a typechecking node factory instead.

class ParserInterface
{
	STPMgr& bm;
	//boost::object_pool<ASTNode> node_pool;
	bool alreadyWarned;

public:
	LETMgr letMgr;
	NodeFactory* nf;

	ParserInterface(STPMgr &bm_, NodeFactory* factory)
	: bm(bm_),
	  nf(factory),
	  letMgr(bm.ASTUndefined)
	{
		assert(nf != NULL);
		alreadyWarned = false;
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

    ASTNode CreateNode(BEEV::Kind kind, const BEEV::ASTNode n0, const BEEV::ASTNode n1)
    {
        if (n0.GetIndexWidth() > 0 && !alreadyWarned)
          {
            cerr << "Warning: Parsing a term that uses array extensionality. STP doesn't handle array extensionality." << endl;
            alreadyWarned = true;
          }
        return nf->CreateNode(kind,n0,n1);
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

    ASTNode CreateBVConst(string& strval, int base, int bit_width)
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

    ASTNode LookupOrCreateSymbol(const char * const name)
    {
    	return bm.LookupOrCreateSymbol(name);
    }

    ASTNode LookupOrCreateSymbol(string name)
    {
    	return bm.LookupOrCreateSymbol(name.c_str());
    }

    bool LookupSymbol(const char * const name, ASTNode& output)
    {
      return bm.LookupSymbol(name,output);
    }

    bool isSymbolAlreadyDeclared(char* name)
    {
           return bm.LookupSymbol(name);
    }


    bool isSymbolAlreadyDeclared(string name)
	{
	   return bm.LookupSymbol(name.c_str());
	}

    // On testcase20 it took about 4.2 seconds to parse using the standard allocator and the pool allocator.
	ASTNode * newNode(const ASTNode& copyIn)
	{
		return new ASTNode(copyIn);
		//return node_pool.construct(copyIn);
	}

	void deleteNode(ASTNode *n)
	{
		delete n;
		//node_pool.destroy(n);
	}
};
}

#endif /* PARSERINTERFACE_H_ */
