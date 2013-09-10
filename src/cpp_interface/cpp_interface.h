#ifndef CPP_INTERFACE_H_
#define CPP_INTERFACE_H_

#include "../AST/AST.h"
#include "../AST/NodeFactory/NodeFactory.h"
#include "../parser/LetMgr.h"
#include "../STPManager/STPManager.h"
#include "../STPManager/STP.h"
#include <cassert>

namespace BEEV
{
  using BEEV::STPMgr;
  using std::cerr;
  using std::cout;
  using std::endl;

// There's no BVTypeCheck() function. Use a typechecking node factory instead.

  class Cpp_interface
  {
    STPMgr& bm;
    //boost::object_pool<ASTNode> node_pool;
    bool alreadyWarned;
    bool print_success;
    bool ignoreCheckSatRequest;

    // Used to cache prior queries.
    struct Entry
    {
      explicit
      Entry(SOLVER_RETURN_TYPE result_)
      {
        result = result_;
        node_number = -1;
      }

      SOLVER_RETURN_TYPE result;
      int node_number; // a weak pointer.

      void
      print()
      {
        if (result == SOLVER_UNSATISFIABLE)
          cerr << "u";
        else if (result == SOLVER_SATISFIABLE)
          cerr << "s";
        else if (result == SOLVER_UNDECIDED)
          cerr << "?";
      }
    };
    vector<Entry> cache;
    vector<vector<ASTNode> > symbols;

    struct Function
    {
      ASTVec params;
      ASTNode function;
      string name;
    };

    hash_map<string, Function> functions;

    void checkInvariant()
    {
      assert(bm.getAssertLevel() == cache.size());
      assert(bm.getAssertLevel() == symbols.size());
    }

    void init()
    {
      assert(nf != NULL);
      alreadyWarned = false;

      cache.push_back(Entry(SOLVER_UNDECIDED));
      symbols.push_back(ASTVec());

      if (bm.getVectorOfAsserts().size() ==0)
        bm.Push();

      print_success = false;
      ignoreCheckSatRequest=false;

    }

  public:
    LETMgr letMgr;
    NodeFactory* nf;

    Cpp_interface(STPMgr &bm_);


    Cpp_interface(STPMgr &bm_, NodeFactory* factory) :
        bm(bm_), nf(factory), letMgr(bm.ASTUndefined)
    {
      init();
    }

    void
    startup()
    {
      CONSTANTBV::ErrCode c = CONSTANTBV::BitVector_Boot();
      if(0 != c) {
        cout << CONSTANTBV::BitVector_Error(c) << endl;
        FatalError("Bad startup");
      }
    }

    const ASTVec
    GetAsserts(void)
    {
      return bm.GetAsserts();
    }

    const ASTVec
    getAssertVector(void)
    {
      return bm.getVectorOfAsserts();
    }

    UserDefinedFlags&
    getUserFlags()
    {
      return bm.UserFlags;
    }

    void
    AddAssert(const ASTNode& assert)
    {
      bm.AddAssert(assert);
    }

    void
    AddQuery(const ASTNode& q)
    {
      bm.AddQuery(q);
    }

    //NODES//
    ASTNode
    CreateNode(BEEV::Kind kind, const BEEV::ASTVec& children = _empty_ASTVec)
    {
      return nf->CreateNode(kind, children);
    }

    ASTNode
    CreateNode(BEEV::Kind kind, const BEEV::ASTNode n0, const BEEV::ASTNode n1)
    {
      if (n0.GetIndexWidth() > 0 && !alreadyWarned)
        {
          cerr << "Warning: Parsing a term that uses array extensionality. STP doesn't handle array extensionality."
              << endl;
          alreadyWarned = true;
        }
      return nf->CreateNode(kind, n0, n1);
    }

    //	These belong in the node factory..

    //TERMS//
    ASTNode
    CreateZeroConst(unsigned int width)
    {
      return bm.CreateZeroConst(width);
    }

    ASTNode
    CreateOneConst(unsigned int width)
    {
      return bm.CreateOneConst(width);
    }

    ASTNode
    CreateBVConst(string& strval, int base, int bit_width)
    {
      return bm.CreateBVConst(strval, base, bit_width);
    }

    ASTNode
    CreateBVConst(const char* const strval, int base)
    {
      return bm.CreateBVConst(strval, base);
    }

    ASTNode
    CreateBVConst(unsigned int width, unsigned long long int bvconst)
    {
      return bm.CreateBVConst(width, bvconst);
    }

    ASTNode
    LookupOrCreateSymbol(const char * const name)
    {
      return bm.LookupOrCreateSymbol(name);
    }

    void
    removeSymbol(ASTNode s)
    {
      bool removed=false;

     for (size_t i = 0; i < symbols.back().size(); i++)
       if (symbols.back()[i] == s)
         {
         symbols.back().erase(symbols.back().begin() + i);
         removed = true;
         }

     if (!removed)
       FatalError("Should have been removed...");

     letMgr._parser_symbol_table.erase(s);
    }

    // Declare a function. We can't keep references to the declared variables though. So rename them..
    void
    storeFunction(const string name, const ASTVec& params, const ASTNode& function)
    {
      Function f;
      f.name = name;

      ASTNodeMap fromTo;
      for (size_t i = 0, size = params.size(); i < size; ++i)
        {
          ASTNode p = bm.CreateFreshVariable(params[i].GetIndexWidth(), params[i].GetValueWidth(), "STP_INTERNAL_FUNCTION_NAME");
          fromTo.insert(std::make_pair(params[i], p));
          f.params.push_back(p);
        }
      ASTNodeMap cache;
      f.function = SubstitutionMap::replace(function,fromTo,cache, nf);
      functions.insert(std::make_pair(f.name,f));
    }

    ASTNode
    applyFunction(const string name, const ASTVec& params)
    {
      if (functions.find(name) == functions.end())
        FatalError("Trying to apply function which has not been defined.");

      Function f;
      f = functions[string(name)];

      ASTNodeMap fromTo;
      for (size_t i = 0, size = f.params.size(); i < size; ++i)
        {
          if (f.params[i].GetValueWidth() != params[i].GetValueWidth())
            FatalError("Actual parameters differ from formal");

          if (f.params[i].GetIndexWidth() != params[i].GetIndexWidth())
            FatalError("Actual parameters differ from formal");

          fromTo.insert(std::make_pair(f.params[i], params[i]));
        }

      ASTNodeMap cache;
      return SubstitutionMap::replace(f.function,fromTo,cache, nf);
    }

    bool isFunction(const string name)
    {
      return (functions.find(name) != functions.end());
    }


    ASTNode
    LookupOrCreateSymbol(string name)
    {
      return bm.LookupOrCreateSymbol(name.c_str());
    }

    bool
    LookupSymbol(const char * const name, ASTNode& output)
    {
      return bm.LookupSymbol(name, output);
    }

    bool
    isSymbolAlreadyDeclared(char* name)
    {
      return bm.LookupSymbol(name);
    }

    void
    setPrintSuccess(bool ps)
    {
      print_success = ps;
    }

    bool
    isSymbolAlreadyDeclared(string name)
    {
      return bm.LookupSymbol(name.c_str());
    }

    // Create the node, then "new" it.
    ASTNode *
    newNode(const Kind k, const ASTNode& n0, const ASTNode& n1)
    {
      return newNode(CreateNode(k, n0, n1));
    }

    // Create the node, then "new" it.
    ASTNode *
    newNode(const Kind k, const int width, const ASTNode& n0, const ASTNode& n1)
    {
      return newNode(nf->CreateTerm(k, width, n0, n1));
    }

    // On testcase20 it took about 4.2 seconds to parse using the standard allocator and the pool allocator.
    ASTNode *
    newNode(const ASTNode& copyIn)
    {
      return new ASTNode(copyIn);
      //return node_pool.construct(copyIn);
    }

    void
    deleteNode(ASTNode *n)
    {
      delete n;
      //node_pool.destroy(n);
    }

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

    // Resets the tables used by STP, but keeps all the nodes that have been created.
    void
    resetSolver()
    {
      bm.ClearAllTables();
      GlobalSTP->ClearAllTables();
    }

    // We can't pop off the zeroeth level.
    void popToFirstLevel()
    {
      while (symbols.size() > 1)
        pop();

      // I don't understand why this is required.
      while(bm.getAssertLevel() > 0)
       bm.Pop();
    }

    void
    pop()
    {
      if (symbols.size() == 0)
        FatalError("Popping from an empty stack.");
      if (symbols.size() == 1)
        FatalError("Can't pop away the default base element.");

      bm.Pop();

      // These tables might hold references to symbols that have been
      // removed.
      resetSolver();

      cache.erase(cache.end() - 1);
      ASTVec & current = symbols.back();
      for (size_t i = 0, size = current.size(); i < size; ++i)
        letMgr._parser_symbol_table.erase(current[i]);

      symbols.erase(symbols.end() - 1);
      checkInvariant();
    }

    void
    push()
    {
      // If the prior one is unsatisiable then the new one will be too.
      if (cache.size() > 1 && cache.back().result == SOLVER_UNSATISFIABLE)
        cache.push_back(Entry(SOLVER_UNSATISFIABLE));
      else
        cache.push_back(Entry(SOLVER_UNDECIDED));

      bm.Push();
      symbols.push_back(ASTVec());

      checkInvariant();
    }

    // Useful when printing back, so that you can parse, but ignore the request.
    void
    ignoreCheckSat()
    {
      ignoreCheckSatRequest=  true;
    }

    void
    printStatus()
    {
      for (size_t i = 0, size = cache.size(); i < size; ++i)
        {
          cache[i].print();
        }
      cerr << endl;
    }

    void
    checkSat(const ASTVec & assertionsSMT2);

    void
    deleteGlobal()
    {
      delete GlobalSTP;
    }

    void
    cleanUp()
    {
      letMgr.cleanupParserSymbolTable();
      cache.clear();
      symbols.clear();
    }
  };
}

#endif
