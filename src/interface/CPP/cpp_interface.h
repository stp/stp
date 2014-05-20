// vim: set sw=2 ts=2 softtabstop=2 expandtab:
#ifndef CPP_INTERFACE_H_
#define CPP_INTERFACE_H_

#include "../AST/AST.h"
#include "../AST/NodeFactory/NodeFactory.h"
#include <memory>
#include <string>
#include <vector>

namespace BEEV
{

// There's no BVTypeCheck() function. Use a typechecking node factory instead.

  // Foward declarations
  struct UserDefinedFlags;
  class STPMgr;
  class LETMgr;

  class Cpp_interface
  {
    STPMgr& bm;
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
          std::cerr << "u";
        else if (result == SOLVER_SATISFIABLE)
          std::cerr << "s";
        else if (result == SOLVER_UNDECIDED)
          std::cerr << "?";
      }
    };
    vector<Entry> cache;
    vector<vector<ASTNode> > symbols;

    struct Function
    {
      ASTVec params;
      ASTNode function;
      std::string name;
    };

    hash_map<std::string, Function> functions;

    void checkInvariant();
    void init();

  public:
    std::unique_ptr<LETMgr> letMgr;
    NodeFactory* nf;

    Cpp_interface(STPMgr &bm_);
    Cpp_interface(STPMgr &bm_, NodeFactory* factory);

    void startup();

    // FIXME: What is the difference between these two methods?
    const ASTVec GetAsserts(void);
    const ASTVec getAssertVector(void);

    UserDefinedFlags& getUserFlags();

    void AddAssert(const ASTNode& assert);
    void AddQuery(const ASTNode& q);

    //NODES//
    ASTNode CreateNode(BEEV::Kind kind,
                       const BEEV::ASTVec& children = _empty_ASTVec);

    ASTNode CreateNode(BEEV::Kind kind,
                       const BEEV::ASTNode n0,
                       const BEEV::ASTNode n1);

    //	These belong in the node factory..

    //TERMS//
    ASTNode CreateZeroConst(unsigned int width);
    ASTNode CreateOneConst(unsigned int width);
    ASTNode CreateBVConst(std::string& strval, int base, int bit_width);
    ASTNode CreateBVConst(const char* const strval, int base);
    ASTNode CreateBVConst(unsigned int width, unsigned long long int bvconst);
    ASTNode LookupOrCreateSymbol(const char * const name);

    void removeSymbol(ASTNode s);

    // Declare a function. We can't keep references to the declared variables
    // though. So rename them..
    void storeFunction(const std::string name,
                       const ASTVec& params,
                       const ASTNode& function);

    ASTNode applyFunction(const std::string name, const ASTVec& params);

    bool isFunction(const std::string name);


    ASTNode LookupOrCreateSymbol(std::string name);
    bool LookupSymbol(const char * const name, ASTNode& output);
    bool isSymbolAlreadyDeclared(char* name);
    void setPrintSuccess(bool ps);
    bool isSymbolAlreadyDeclared(std::string name);

    // Create the node, then "new" it.
    ASTNode* newNode(const Kind k,
                     const ASTNode& n0,
                     const ASTNode& n1);

    // Create the node, then "new" it.
    ASTNode* newNode(const Kind k,
                     const int width,
                     const ASTNode& n0,
                     const ASTNode& n1);

    // On testcase20 it took about 4.2 seconds to parse using the standard
    // allocator and the pool allocator.
    ASTNode* newNode(const ASTNode& copyIn);

    void deleteNode(ASTNode *n);
    void addSymbol(ASTNode &s);
    void success();

    // Resets the tables used by STP, but keeps all the nodes that have been created.
    void resetSolver();

    // We can't pop off the zeroeth level.
    void popToFirstLevel();

    void pop();

    void push();

    // Useful when printing back, so that you can parse, but ignore the request.
    void ignoreCheckSat();

    void printStatus();

    void checkSat(const ASTVec & assertionsSMT2);

    void deleteGlobal();

    void cleanUp();
  };
}

#endif
