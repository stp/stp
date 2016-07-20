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

#include "stp/cpp_interface.h"
#include "stp/ToSat/AIG/ToSATAIG.h"
#include "stp/STPManager/STPManager.h"
#include "stp/STPManager/STP.h"
#include "stp/Parser/LetMgr.h"
#include <cassert>

using std::cerr;
using std::cout;
using std::endl;

namespace stp
{

void Cpp_interface::checkInvariant()
{
  assert(bm.getAssertLevel() == cache.size());
  assert(bm.getAssertLevel() == symbols.size());
}

void Cpp_interface::init()
{
  assert(nf != NULL);
  alreadyWarned = false;

  cache.push_back(Entry(SOLVER_UNDECIDED));
  symbols.push_back(ASTVec());

  if (bm.getVectorOfAsserts().size() == 0)
    bm.Push();

  print_success = false;
  ignoreCheckSatRequest = false;
  produce_models = false;
}

Cpp_interface::Cpp_interface(STPMgr& bm_, NodeFactory* factory)
    : bm(bm_), letMgr(new LETMgr(bm.ASTUndefined)), nf(factory)
{
  init();
}

void Cpp_interface::startup()
{
  CONSTANTBV::ErrCode c = CONSTANTBV::BitVector_Boot();
  if (0 != c)
  {
    cout << CONSTANTBV::BitVector_Error(c) << endl;
    FatalError("Bad startup");
  }
}

const ASTVec Cpp_interface::GetAsserts(void)
{
  return bm.GetAsserts();
}

const ASTVec Cpp_interface::getAssertVector(void)
{
  return bm.getVectorOfAsserts();
}

UserDefinedFlags& Cpp_interface::getUserFlags()
{
  return bm.UserFlags;
}

void Cpp_interface::AddAssert(const ASTNode& assert)
{
  bm.AddAssert(assert);
}

void Cpp_interface::AddQuery(const ASTNode& q)
{
  bm.AddQuery(q);
}

ASTNode Cpp_interface::CreateNode(stp::Kind kind, const stp::ASTVec& children)
{
  return nf->CreateNode(kind, children);
}

ASTNode Cpp_interface::CreateNode(stp::Kind kind, const stp::ASTNode n0,
                                  const stp::ASTNode n1)
{
  if (n0.GetIndexWidth() > 0 && !alreadyWarned)
  {
    cerr << "Warning: Parsing a term that uses array extensionality. "
            "STP doesn't handle array extensionality." << endl;
    alreadyWarned = true;
  }
  return nf->CreateNode(kind, n0, n1);
}

ASTNode Cpp_interface::CreateZeroConst(unsigned int width)
{
  return bm.CreateZeroConst(width);
}

ASTNode Cpp_interface::CreateOneConst(unsigned int width)
{
  return bm.CreateOneConst(width);
}

ASTNode Cpp_interface::CreateBVConst(string& strval, int base, int bit_width)
{
  return bm.CreateBVConst(strval, base, bit_width);
}

ASTNode Cpp_interface::CreateBVConst(const char* const strval, int base)
{
  return bm.CreateBVConst(strval, base);
}

// FIXME: unsigned long long int is disgusting! use intN_t from cstdint.h
ASTNode Cpp_interface::CreateBVConst(unsigned int width,
                                     unsigned long long int bvconst)
{
  return bm.CreateBVConst(width, bvconst);
}

ASTNode Cpp_interface::LookupOrCreateSymbol(const char* const name)
{
  return bm.LookupOrCreateSymbol(name);
}

void Cpp_interface::removeSymbol(ASTNode s)
{
  bool removed = false;

  for (size_t i = 0; i < symbols.back().size(); i++)
    if (symbols.back()[i] == s)
    {
      symbols.back().erase(symbols.back().begin() + i);
      removed = true;
    }

  if (!removed)
    FatalError("Should have been removed...");

}

void Cpp_interface::storeFunction(const string name, const ASTVec& params,
                                  const ASTNode& function)
{
  Function f;
  f.name = name;

  ASTNodeMap fromTo;
  for (size_t i = 0, size = params.size(); i < size; ++i)
  {
    ASTNode p = bm.CreateFreshVariable(params[i].GetIndexWidth(),
                                       params[i].GetValueWidth(),
                                       "STP_INTERNAL_FUNCTION_NAME");
    fromTo.insert(std::make_pair(params[i], p));
    f.params.push_back(p);
  }

  ASTNodeMap cache;
  f.function = SubstitutionMap::replace(function, fromTo, cache, nf);
  functions.insert(std::make_pair(f.name, f));
}

ASTNode Cpp_interface::applyFunction(const string name, const ASTVec& params)
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
  return SubstitutionMap::replace(f.function, fromTo, cache, nf);
}

bool Cpp_interface::isBitVectorFunction(const string name)
{
  return ((functions.find(name) != functions.end()) &&
          functions.find(name)->second.function.GetType() == BITVECTOR_TYPE);
}

bool Cpp_interface::isBooleanFunction(const string name)
{
  return ((functions.find(name) != functions.end()) &&
          functions.find(name)->second.function.GetType() == BOOLEAN_TYPE);
}

ASTNode Cpp_interface::LookupOrCreateSymbol(string name)
{
  return bm.LookupOrCreateSymbol(name.c_str());
}

bool Cpp_interface::LookupSymbol(const char* const name, ASTNode& output)
{
  return bm.LookupSymbol(name, output);
}

bool Cpp_interface::isSymbolAlreadyDeclared(char* name)
{
  return bm.LookupSymbol(name);
}

void Cpp_interface::setPrintSuccess(bool ps)
{
  print_success = ps;
  success();
}

bool Cpp_interface::isSymbolAlreadyDeclared(string name)
{
  return bm.LookupSymbol(name.c_str());
}

ASTNode* Cpp_interface::newNode(const Kind k, const ASTNode& n0,
                                const ASTNode& n1)
{
  return newNode(CreateNode(k, n0, n1));
}

ASTNode* Cpp_interface::newNode(const Kind k, const int width,
                                const ASTNode& n0, const ASTNode& n1)
{
  return newNode(nf->CreateTerm(k, width, n0, n1));
}

ASTNode* Cpp_interface::newNode(const ASTNode& copyIn)
{
  return new ASTNode(copyIn);
}

void Cpp_interface::deleteNode(ASTNode* n)
{
  delete n;
}

void Cpp_interface::addSymbol(ASTNode& s)
{
  symbols.back().push_back(s);
}

void Cpp_interface::success()
{
  if (print_success)
  {
    cout << "success" << endl;
    flush(cout);
  }
}

//TODO escape string.
void Cpp_interface::error(std::string msg)
{
  cout << "error(\"" << msg << "\")" << endl;
  flush(cout);
}

void Cpp_interface::unsupported()
{
  cout << "unsupported" << endl;
  flush(cout);
}


void Cpp_interface::resetSolver()
{
  bm.ClearAllTables();
  GlobalSTP->ClearAllTables();
}

// Can clear away the base frame..
void Cpp_interface::reset()
{
  popToFirstLevel();

  if (symbols.size() > 0)
  {
    // used just by cvc parser. 
    assert(letMgr->_parser_symbol_table.size() == 0); 

    symbols.erase(symbols.end() - 1);
  }

  assert(symbols.size() ==0);
  
  // These tables might hold references to symbols that have been
  // removed.
  resetSolver();

  cleanUp();
  
  checkInvariant();

  init();
}


void Cpp_interface::popToFirstLevel()
{
  while (symbols.size() > 1)
    pop();

  // I don't understand why this is required.
  while (bm.getAssertLevel() > 0)
    bm.Pop();
}

void Cpp_interface::pop()
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

  assert(letMgr->_parser_symbol_table.size() == 0); 
  
  symbols.erase(symbols.end() - 1);
  checkInvariant();
}

void Cpp_interface::push()
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

void Cpp_interface::ignoreCheckSat()
{
  ignoreCheckSatRequest = true;
}

void Cpp_interface::printStatus()
{
  for (size_t i = 0, size = cache.size(); i < size; ++i)
  {
    cache[i].print();
  }
  cerr << endl;
}

// Does some simple caching of prior results.
void Cpp_interface::checkSat(const ASTVec& assertionsSMT2)
{
  if (ignoreCheckSatRequest)
    return;

  bm.GetRunTimes()->stop(RunTimes::Parsing);

  checkInvariant();
  assert(assertionsSMT2.size() == cache.size());

  Entry& last_run = cache.back();
  if ((last_run.node_number != assertionsSMT2.back().GetNodeNum()) &&
      (last_run.result == SOLVER_SATISFIABLE))
  {
    // extra asserts might have been added to it,
    // flipping from sat to unsat. But never from unsat to sat.
    last_run.result = SOLVER_UNDECIDED;
  }

  // We might have run this query before, or it might already be shown to be
  // unsat. If it was sat,
  // we've stored the result (but not the model), so we can shortcut and return
  // what we know.
  if (!((last_run.result == SOLVER_SATISFIABLE) ||
        last_run.result == SOLVER_UNSATISFIABLE))
  {
    resetSolver();

    ASTNode query;

    if (assertionsSMT2.size() > 1)
      query = nf->CreateNode(AND, assertionsSMT2);
    else if (assertionsSMT2.size() == 1)
      query = assertionsSMT2[0];
    else
      query = bm.ASTTrue;

    SOLVER_RETURN_TYPE last_result = GlobalSTP->TopLevelSTP(query, bm.ASTFalse);

    // Store away the answer. Might be timeout, or error though..
    last_run = Entry(last_result);
    last_run.node_number = assertionsSMT2.back().GetNodeNum();

    // It's satisfiable, so everything beneath it is satisfiable too.
    if (last_result == SOLVER_SATISFIABLE)
    {
      for (size_t i = 0; i < cache.size(); i++)
      {
        assert(cache[i].result != SOLVER_UNSATISFIABLE);
        cache[i].result = SOLVER_SATISFIABLE;
      }
    }
  }

  if (bm.UserFlags.quick_statistics_flag)
  {
    bm.GetRunTimes()->print();
  }

  (GlobalSTP->tosat)->PrintOutput(last_run.result);
  bm.GetRunTimes()->start(RunTimes::Parsing);
}

// This method sets up some of the globally required data.
Cpp_interface::Cpp_interface(STPMgr& bm_)
    : bm(bm_), letMgr(new LETMgr(bm.ASTUndefined)), nf(bm_.defaultNodeFactory)
{
  nf = bm.defaultNodeFactory;
  startup();
  stp::GlobalParserInterface = this;

  Simplifier* simp = new Simplifier(&bm);
  ArrayTransformer* at = new ArrayTransformer(&bm, simp);
  AbsRefine_CounterExample* abs = new AbsRefine_CounterExample(&bm, simp, at);
  ToSATAIG* tosat = new ToSATAIG(&bm, at);

  stp::GlobalParserBM = &bm_;

  GlobalSTP = new STP(&bm, simp, at, tosat, abs);
  init();
}

void Cpp_interface::deleteGlobal()
{
  GlobalSTP->deleteObjects();
  delete GlobalSTP;
}

void Cpp_interface::cleanUp()
{
  letMgr->cleanupParserSymbolTable();
  cache.clear();
  symbols.clear();
}

  void Cpp_interface::setOption(std::string option, std::string value)
  {
      /*
      :diagnostic-output-channel
      :global-declarations
      :interactive-mode
      :produce-assertions
      :produce-assignments
      :produce-proofs
      :produce-unsat-assumptions
      :produce-unsat-cores
      :random-seed
      :regular-output-channel
      :reproducible-resource-limit
      :verbosity
      */

     if(option == "print-success")
      {
        if (value =="true")
          setPrintSuccess(true);
        else if (value =="false")
          setPrintSuccess(false);
        else
          unsupported();
      }
     else if(option == "produce-models")
      {
        if (value =="true")
          {
            produce_models = true;
            success();
          }
        else if (value =="false")
          {
            produce_models = false;
            success();
          }
        else
          unsupported();
      }
      else
        unsupported();
  }
  
  void Cpp_interface::getOption(std::string )
  {
      unsupported();
  }

  void Cpp_interface::getValue(const ASTVec &v)
  {
    std::ostringstream os;

    os << "("<< std::endl;
    
    for (ASTNode n: v)
      {
        if (n.GetKind() != SYMBOL)
        {
          unsupported();
          return;
        }
        GlobalSTP->Ctr_Example->PrintSMTLIB2(os,n);
        os << std::endl;        
      }
    os << ")" << std::endl;

    cout << os.str();
  }

  void Cpp_interface::getModel()
  {
    //TODO check that produce-models is turned on.
    //Check that check-sat was just called.
    cout << "("<< std::endl;

    std::ostringstream os;
    GlobalSTP->Ctr_Example->PrintCounterExampleSMTLIB2(os);
    cout << os.str();
    cout << ")" << std::endl;
  }
}
