/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: Apr, 2010
 *
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
********************************************************************/

#ifndef CPP_INTERFACE_H_
#define CPP_INTERFACE_H_

#include "stp/AST/AST.h"
#include "stp/AST/NodeFactory/NodeFactory.h"
#include <memory>
#include <string>
#include <vector>

namespace stp
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
    explicit Entry(SOLVER_RETURN_TYPE result_)
    {
      result = result_;
      node_number = -1;
    }

    SOLVER_RETURN_TYPE result;
    int node_number; // a weak pointer.

    void print()
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
  vector<vector<ASTNode>> symbols;

  struct Function
  {
    ASTVec params;
    ASTNode function;
    std::string name;
  };

  hash_map<std::string, Function> functions;

  void checkInvariant();
  void init();

  bool produce_models;

public:
  std::unique_ptr<LETMgr> letMgr;
  NodeFactory* nf;

  Cpp_interface(STPMgr& bm_);
  Cpp_interface(STPMgr& bm_, NodeFactory* factory);

  void startup();

  // FIXME: What is the difference between these two methods?
  const ASTVec GetAsserts(void);
  const ASTVec getAssertVector(void);

  UserDefinedFlags& getUserFlags();

  void AddAssert(const ASTNode& assert);
  void AddQuery(const ASTNode& q);

  // NODES//
  ASTNode CreateNode(stp::Kind kind,
                     const stp::ASTVec& children = _empty_ASTVec);

  ASTNode CreateNode(stp::Kind kind, const stp::ASTNode n0,
                     const stp::ASTNode n1);

  //	These belong in the node factory..

  // TERMS//
  ASTNode CreateZeroConst(unsigned int width);
  ASTNode CreateOneConst(unsigned int width);
  ASTNode CreateBVConst(std::string& strval, int base, int bit_width);
  ASTNode CreateBVConst(const char* const strval, int base);
  ASTNode CreateBVConst(unsigned int width, unsigned long long int bvconst);
  ASTNode LookupOrCreateSymbol(const char* const name);

  void removeSymbol(ASTNode s);

  // Declare a function. We can't keep references to the declared variables
  // though. So rename them..
  void storeFunction(const std::string name, const ASTVec& params,
                     const ASTNode& function);

  ASTNode applyFunction(const std::string name, const ASTVec& params);

  bool isBitVectorFunction(const std::string name);
  bool isBooleanFunction(const std::string name);

  ASTNode LookupOrCreateSymbol(std::string name);
  bool LookupSymbol(const char* const name, ASTNode& output);
  bool isSymbolAlreadyDeclared(char* name);
  void setPrintSuccess(bool ps);
  bool isSymbolAlreadyDeclared(std::string name);

  // Create the node, then "new" it.
  ASTNode* newNode(const Kind k, const ASTNode& n0, const ASTNode& n1);

  // Create the node, then "new" it.
  ASTNode* newNode(const Kind k, const int width, const ASTNode& n0,
                   const ASTNode& n1);

  // On testcase20 it took about 4.2 seconds to parse using the standard
  // allocator and the pool allocator.
  ASTNode* newNode(const ASTNode& copyIn);

  void deleteNode(ASTNode* n);
  void addSymbol(ASTNode& s);
  
  void success();
  void error(std::string msg);
  void unsupported();


  // Resets the tables used by STP, but keeps all the nodes that have been
  // created.
  void resetSolver();

  // We can't pop off the zeroeth level.
  void popToFirstLevel();

  // Reset STP back to "just started up" state.
  void reset();

  void pop();

  void push();

  // Useful when printing back, so that you can parse, but ignore the request.
  void ignoreCheckSat();

  void printStatus();

  void checkSat(const ASTVec& assertionsSMT2);

  void deleteGlobal();

  void cleanUp();

  void setOption(std::string , std::string);
  void getOption(std::string );

  void getModel();

  void getValue(const ASTVec &v);
};
}

#endif
