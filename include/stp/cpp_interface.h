/********************************************************************
 * AUTHORS: Trevor Hansen, Andrew V. Jones
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
#include "stp/NodeFactory/NodeFactory.h"
#include "stp/Util/Attributes.h"
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

  struct Function
  {
    ASTVec params;
    ASTNode function;
    std::string name;
  };
  std::unordered_map<std::string, Function> functions;

  // Nested helper class to encapsulate a frame (i.e., between push a pop)
  class SolverFrame
  {
  public:
    // Functions are (currently) managed at global scope; we need a pointer to
    // the global functions to be able to remove functions when we pop
    SolverFrame(
        std::unordered_map<std::string, Function>* global_function_context);
    virtual ~SolverFrame();

    // Obtain the functions for the current frame
    vector<std::string>& getFunctions();

    // Obtain the symbols for the current frame
    ASTVec& getSymbols();

  private:
    vector<std::string> _scoped_functions;
    ASTVec _scoped_symbols;
    std::unordered_map<std::string, Function>* _global_function_context;
  };

  // The vector of all frames that have been created by calling push
  std::vector<SolverFrame> frames;

  // Obtain the symbols/functions for the current frame
  ASTVec& getCurrentSymbols();
  vector<std::string>& getCurrentFunctions();

  void checkInvariant();
  void init();

  bool produce_models;
  bool changed_model_status;

public:
  std::unique_ptr<LETMgr> letMgr;
  NodeFactory* nf;

  DLL_PUBLIC Cpp_interface(STPMgr& bm_);
  DLL_PUBLIC Cpp_interface(STPMgr& bm_, NodeFactory* factory);

  DLL_PUBLIC void startup();

  // FIXME: What is the difference between these two methods?
  DLL_PUBLIC const ASTVec GetAsserts(void);
  DLL_PUBLIC const ASTVec getAssertVector(void);

  DLL_PUBLIC UserDefinedFlags& getUserFlags();

  DLL_PUBLIC void AddAssert(const ASTNode& assert);
  DLL_PUBLIC void SetQuery(const ASTNode& q);

  // NODES//
  DLL_PUBLIC ASTNode CreateNode(stp::Kind kind,
                                const stp::ASTVec& children = _empty_ASTVec);

  DLL_PUBLIC ASTNode CreateNode(stp::Kind kind, const stp::ASTNode n0,
                                const stp::ASTNode n1);

  //	These belong in the node factory..

  // TERMS//
  DLL_PUBLIC ASTNode CreateZeroConst(unsigned int width);
  DLL_PUBLIC ASTNode CreateOneConst(unsigned int width);
  DLL_PUBLIC ASTNode CreateBVConst(std::string& strval, int base,
                                   int bit_width);
  DLL_PUBLIC ASTNode CreateBVConst(const char* const strval, int base);
  DLL_PUBLIC ASTNode CreateBVConst(unsigned int width,
                                   unsigned long long int bvconst);
  DLL_PUBLIC ASTNode LookupOrCreateSymbol(const char* const name);

  void removeSymbol(ASTNode to_remove);

  // Declare a function. We can't keep references to the declared variables
  // though. So rename them..
  DLL_PUBLIC void storeFunction(const std::string name, const ASTVec& params,
                                const ASTNode& function);

  DLL_PUBLIC ASTNode applyFunction(const std::string name,
                                   const ASTVec& params);

  DLL_PUBLIC bool isBitVectorFunction(const std::string name);
  DLL_PUBLIC bool isBooleanFunction(const std::string name);

  DLL_PUBLIC ASTNode LookupOrCreateSymbol(std::string name);
  DLL_PUBLIC bool LookupSymbol(const char* const name, ASTNode& output);
  DLL_PUBLIC bool isSymbolAlreadyDeclared(char* name);
  DLL_PUBLIC void setPrintSuccess(bool ps);
  DLL_PUBLIC bool isSymbolAlreadyDeclared(std::string name);

  // Create the node, then "new" it.
  DLL_PUBLIC ASTNode* newNode(const Kind k, const ASTNode& n0,
                              const ASTNode& n1);

  // Create the node, then "new" it.
  DLL_PUBLIC ASTNode* newNode(const Kind k, const int width, const ASTNode& n0,
                              const ASTNode& n1);

  // Create the node, then "new" it.
  DLL_PUBLIC ASTNode* newNode(const Kind k, const int width, const ASTVec& v);

  // On testcase20 it took about 4.2 seconds to parse using the standard
  // allocator and the pool allocator.
  DLL_PUBLIC ASTNode* newNode(const ASTNode& copyIn);

  DLL_PUBLIC void deleteNode(ASTNode* n);
  DLL_PUBLIC void addSymbol(ASTNode& s);

  DLL_PUBLIC void success();
  DLL_PUBLIC void error(std::string msg);
  DLL_PUBLIC void unsupported();

  // Resets the tables used by STP, but keeps all the nodes that have been
  // created.
  DLL_PUBLIC void resetSolver();

  // Reset STP back to "just started up" state.
  DLL_PUBLIC void reset();
  DLL_PUBLIC void pop();
  DLL_PUBLIC void push();
  DLL_PUBLIC void popToFirstLevel(); // We can't pop off the zeroeth level

  // Useful when printing back, so that you can parse, but ignore the request.
  DLL_PUBLIC void ignoreCheckSat();
  DLL_PUBLIC void printStatus();
  DLL_PUBLIC void checkSat(const ASTVec& assertionsSMT2);

  DLL_PUBLIC void deleteGlobal();
  DLL_PUBLIC void cleanUp();

  DLL_PUBLIC void setOption(std::string, std::string);
  DLL_PUBLIC void getOption(std::string);

  DLL_PUBLIC void getModel();
  DLL_PUBLIC void getValue(const ASTVec& v);
};

// Functions used by C++ clients of STP. TODO: either export abc cleanly or don't use this in clients.

/// Export version of Cnf_ClearMemory.
DLL_PUBLIC void CNFClearMemory();
}

#endif
