// Wrapper around the main beevmgr class given to the parsers.
// Over time I hope the parsers will interact entirely through this class.

#ifndef PARSERINTERFACE_H_
#define PARSERINTERFACE_H_

#include "../AST/AST.h"
#include "../AST/NodeFactory/NodeFactory.h"
#include <cassert>
#include "LetMgr.h"
#include "../STPManager/STPManager.h"
#include "../STPManager/STP.h"
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
	bool print_success;
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
		cache.push_back(Entry(SOLVER_UNDECIDED));
		symbols.push_back(ASTVec());
		print_success=false;
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

    void setPrintSuccess(bool ps)
    {
      print_success= ps;
    }


    bool isSymbolAlreadyDeclared(string name)
	{
	   return bm.LookupSymbol(name.c_str());
	}

    // Create the node, then "new" it.
    ASTNode * newNode(const Kind k, const ASTNode& n0, const ASTNode& n1)
    {
      return newNode(CreateNode(k,n0,n1));
    }

    // Create the node, then "new" it.
    ASTNode * newNode(const Kind k, const int width, const ASTNode& n0, const ASTNode& n1)
    {
      return newNode(nf->CreateTerm(k,width,n0,n1));
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

	struct Entry
	{
	  explicit Entry( SOLVER_RETURN_TYPE result_)
	  {
	    result = result_;
	  }

	  SOLVER_RETURN_TYPE result;
	  ASTNode node;

	  void print()
	  {
            if (result == SOLVER_UNSATISFIABLE)
              cerr << "u";
            else if (result ==  SOLVER_SATISFIABLE)
              cerr << "s";
            else if (result ==  SOLVER_UNDECIDED)
              cerr << "?";
	  }
	};
	vector<Entry> cache;
	vector<vector<ASTNode> > symbols;

	void
	addSymbol(ASTNode &s)
	{
	  symbols.back().push_back(s);
	  letMgr._parser_symbol_table.insert(s);
	}

	void
        success()
        {
          if (print_success)
            {
              cout << "success" << endl;
              flush(cout);
            }
        }

        void
        pop()
        {
          if (symbols.size() ==0)
            FatalError("Popping from an empty stack.");
          if (symbols.size() ==1)
             FatalError("Can't pop away the default base element.");

          assert(symbols.size() == cache.size());
          cache.erase(cache.end()-1);
          ASTVec & current = symbols.back();
          for (int i=0; i < current.size() ;i++)
              letMgr._parser_symbol_table.erase(current[i]);
          symbols.erase(symbols.end()-1);
        }

        void
        push()
        {
          // If the prior one is unsatisiable then the new one will be too.
          if (cache.size() > 1 && cache.back().result == SOLVER_UNSATISFIABLE)
            cache.push_back(Entry(SOLVER_UNSATISFIABLE));
          else
            cache.push_back(Entry(SOLVER_UNDECIDED));

          symbols.push_back(ASTVec());
          assert(symbols.size() == cache.size());
        }

     void printStatus()
     {
      for (int i=0; i < cache.size();i++)
        {
          cache[i].print();
        }
      cerr<< endl;
     }

     // Does some simple caching of prior results.
    void
    checkSat(vector<ASTVec> & assertionsSMT2)
    {
      bm.GetRunTimes()->stop(RunTimes::Parsing);
      assert(assertionsSMT2.size() == cache.size());

      Entry& cacheEntry = cache.back();

      //cerr << "------------" << endl;
      //printStatus();

      if ((cacheEntry.result ==  SOLVER_SATISFIABLE || cacheEntry.result == SOLVER_UNSATISFIABLE)
          && (assertionsSMT2.back().size() ==1 && assertionsSMT2.back()[0] == cacheEntry.node))
        { // If we already know the answer then return.
          if (bm.UserFlags.quick_statistics_flag)
            {
              bm.GetRunTimes()->print();
            }

          (GlobalSTP->tosat)->PrintOutput(cache.back().result);
          bm.GetRunTimes()->start(RunTimes::Parsing);
          return;
        }

      bm.ClearAllTables();
      GlobalSTP->ClearAllTables();

      // Loop through the set of assertions converting them to single nodes..
      ASTVec v;
      for (int i = 0; i < assertionsSMT2.size(); i++)
        {
          if (assertionsSMT2[i].size() == 1)
            {}
          else if (assertionsSMT2[i].size() == 0)
            assertionsSMT2[i].push_back(bm.ASTTrue);
          else
            {
              ASTNode v = parserInterface->CreateNode(AND, assertionsSMT2[i]);
              assertionsSMT2[i].clear();
              assertionsSMT2[i].push_back(v);
            }
          assert(assertionsSMT2[i].size() ==1);
          v.push_back(assertionsSMT2[i][0]);
        }

      ASTNode query;

      if (v.size() > 1)
        query = parserInterface->CreateNode(AND, v);
      else if (v.size() > 0)
        query = v[0];
      else
        query = bm.ASTTrue;

      SOLVER_RETURN_TYPE last_result = GlobalSTP->TopLevelSTP(query, bm.ASTFalse);

      // Write in the answer to the current slot.
      if (last_result ==SOLVER_SATISFIABLE || last_result ==SOLVER_UNSATISFIABLE)
          {
            Entry e(last_result);
            e.node = assertionsSMT2.back()[0];
            cacheEntry = e;
            assert (!cacheEntry.node.IsNull());
          }

      // It's satisfiable, so everything beneath it is satisfiable too.
      if (last_result ==SOLVER_SATISFIABLE)
        {
          for (int i=0; i < cache.size(); i++)
              {
              assert(cache[i].result != SOLVER_UNSATISFIABLE);
              cache[i].result = SOLVER_SATISFIABLE;
              }
        }

      if (bm.UserFlags.quick_statistics_flag)
        {
          bm.GetRunTimes()->print();
        }

      (GlobalSTP->tosat)->PrintOutput(last_result);
      //printStatus();
      bm.GetRunTimes()->start(RunTimes::Parsing);
    }

    void cleanUp()
    {
      letMgr.cleanupParserSymbolTable();
      cache.clear();
      symbols.clear();
    }
};
}

#endif /* PARSERINTERFACE_H_ */
