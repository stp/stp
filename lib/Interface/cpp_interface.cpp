/********************************************************************
 * AUTHORS: Trevor Hansen, Andrew Teylu
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
#include "stp/Parser/LetMgr.h"
#include "stp/Printer/printers.h"
#include "stp/Util/GitSHA1.h"
#include "stp/STPManager/STP.h"
#include "stp/STPManager/STPManager.h"
#include "stp/ToSat/ToSATAIG.h"
#include <cassert>

using std::cerr;
using std::cout;
using std::endl;

namespace stp
{

void Cpp_interface::checkInvariant()
{
  assert(bm.getAssertLevel() == cache.size());
  assert(bm.getAssertLevel() == frames.size());
}

void Cpp_interface::init()
{
  assert(nf != NULL);
  alreadyWarned = false;

  cache.push_back(Entry(SOLVER_UNDECIDED));

  addFrame();

  // Ask the stack how deep it is rather than for its contents:
  // getVectorOfAsserts() fills empty levels with TRUE as a side effect, and
  // two interfaces are constructed over the one STPMgr, so using it as an
  // emptiness test left a stray TRUE asserted at the base level forever.
  if (bm.getAssertLevel() == 0)
    bm.Push();

  print_success = false;
  ignoreCheckSatRequest = false;
  produce_models = false;
  changed_model_status = false;
}

void Cpp_interface::addFrame()
{
  // create a new frame
  SolverFrame* new_frame = new SolverFrame(&functions);

  // store the new frame
  frames.push_back(new_frame);
}

void Cpp_interface::removeFrame()
{
    // obtain the last frame
    SolverFrame* last = frames.back();

    // The frame's symbols go out of scope with it: drop any rounding-mode
    // markers so the model printers and reset-assertions don't outlive
    // them, and any array-sort registrations so a later same-name,
    // same-widths declaration doesn't inherit this frame's index or
    // element sorts (the symbol node would be the very same one).
    for (const ASTNode& s : last->getSymbols())
    {
      bm.rounding_mode_symbols.erase(s);
      bm.fp_index_arrays.erase(s);
      bm.rm_index_arrays.erase(s);
      bm.rm_element_arrays.erase(s);
    }

    // delete it
    delete last;

    // remove it from the vector of frames
    frames.pop_back();
}

Cpp_interface::Cpp_interface(STPMgr& bm_, NodeFactory* factory)
    : bm(bm_), letMgr(new LetMgr(bm.ASTUndefined)), nf(factory)
{
  init();
}

ASTVec& Cpp_interface::getCurrentSymbols()
{
  return frames.back()->getSymbols();
}

vector<std::string>& Cpp_interface::getCurrentFunctions()
{
  return frames.back()->getFunctions();
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

void Cpp_interface::SetQuery(const ASTNode& q)
{
  bm.SetQuery(q);
}

ASTNode Cpp_interface::CreateNode(stp::Kind kind, const stp::ASTVec& children)
{
  if (kind == EQ && children.size() > 0 && children[0].GetIndexWidth() > 0 && !alreadyWarned)
  {
    cerr << "Warning: Parsing a term that uses array extensionality. "
            "STP doesn't handle array extensionality."
         << endl;
    alreadyWarned = true;
  }

  return nf->CreateNode(kind, children);
}

ASTNode Cpp_interface::CreateNode(stp::Kind kind, const stp::ASTNode n0,
                                  const stp::ASTNode n1)
{
  if (n0.GetIndexWidth() > 0 && !alreadyWarned)
  {
    cerr << "Warning: Parsing a term that uses array extensionality. "
            "STP doesn't handle array extensionality."
         << endl;
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

ASTNode Cpp_interface::CreateFPSpecialConst(stp::FPSpecial which,
                                            unsigned exp_width,
                                            unsigned sig_width)
{
  return bm.CreateFPSpecialConst(which, exp_width, sig_width);
}

void Cpp_interface::addSortAlias(const std::string& name, unsigned exp_width,
                                 unsigned sig_width)
{
  // SMT-LIB does not allow redefining a sort name.
  if (sort_aliases.find(name) != sort_aliases.end())
    FatalError("define-sort: the sort name is already defined");
  sort_aliases[name] = std::make_pair(exp_width, sig_width);
}

bool Cpp_interface::lookupSortAlias(const std::string& name,
                                    unsigned& exp_width,
                                    unsigned& sig_width) const
{
  const auto found = sort_aliases.find(name);
  if (found == sort_aliases.end())
    return false;
  exp_width = found->second.first;
  sig_width = found->second.second;
  return true;
}

ASTNode Cpp_interface::CreateBVConst(string& strval, int base, int bit_width)
{
  return bm.CreateBVConst(strval, base, bit_width);
}

ASTNode Cpp_interface::CreateBVConst(const char* const strval, int base)
{
  return bm.CreateBVConst(strval, base);
}

// FIXME: unsigned long long int is wong. Use intN_t from cstdint
ASTNode Cpp_interface::CreateBVConst(unsigned int width,
                                     unsigned long long int bvconst)
{
  return bm.CreateBVConst(width, bvconst);
}

ASTNode Cpp_interface::LookupOrCreateSymbol(const char* const name)
{
  return bm.LookupOrCreateSymbol(name);
}

ASTNode Cpp_interface::CreateParameterisedBooleanVar(const ASTNode& var,
                                                     const ASTNode& constant)
{
  return bm.NewParameterized_BooleanVar(var, constant);
}

void Cpp_interface::removeSymbol(ASTNode to_remove)
{
  bool removed = false;

  // Get the symbols for the current frame
  ASTVec& curr_symbols = getCurrentSymbols();

  for (ASTVec::iterator iter = curr_symbols.begin(); iter != curr_symbols.end();
       ++iter)
  {
    if ((*iter) == to_remove)
    {
      curr_symbols.erase(iter);
      removed = true;
      break;
    }
  }

  if (!removed)
    FatalError("Should have been removed...");
}

void Cpp_interface::storeFunction(const string& name, const ASTVec& params,
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
    // A floating-point parameter carries its format in the exponent and
    // significand widths, which CreateFreshVariable does not copy. Without
    // this the placeholder is a formatless (in fact zero-width) symbol, and
    // the function body -- e.g. (fp.isNormal f) -- fails to type-check when
    // it is stored.
    p.SetExpWidth(params[i].GetExpWidth());
    p.SetSigWidth(params[i].GetSigWidth());
    fromTo.insert(std::make_pair(params[i], p));
    f.params.push_back(p);
  }

  ASTNodeMap cache;
  f.function = SubstitutionMap::replace(function, fromTo, cache, nf);

  // store the function in the global function store
  functions.insert(std::make_pair(f.name, f));

  // record which frame this function was created in, such that it can be
  // removed later (e.g., via pop)
  getCurrentFunctions().push_back(f.name);
}

ASTNode Cpp_interface::applyFunction(const string& name, const ASTVec& params)
{
  const auto found = functions.find(name);
  if (found == functions.end())
    FatalError("Trying to apply function which has not been defined.");

  const Function& f = found->second;

  if (f.params.size() != params.size())
    FatalError("Actual parameters differ in number from formal");

  // A nullary function application is just its body: there is nothing to
  // substitute, so skip building the (always empty) fromTo and cache maps
  // and the replace() traversal. Files built from define-funs with no
  // parameters (e.g. bit-blasted circuits) apply such functions millions
  // of times, once each, so the per-call map churn dominated.
  if (f.params.empty())
    return f.function;

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

bool Cpp_interface::isBitVectorFunction(const string& name)
{
  const auto found = functions.find(name);
  if (found == functions.end())
    return false;

  return found->second.function.GetType() == BITVECTOR_TYPE;
}

bool Cpp_interface::isBooleanFunction(const string& name)
{
  const auto found = functions.find(name);
  if (found == functions.end())
    return false;

  return found->second.function.GetType() == BOOLEAN_TYPE;
}

types Cpp_interface::functionReturnType(const string& name)
{
  const auto found = functions.find(name);
  if (found == functions.end())
    return UNKNOWN_TYPE;

  return found->second.function.GetType();
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

ASTNode* Cpp_interface::newNode(const Kind k, const int width, const ASTVec& v)
{
  return newNode(nf->CreateTerm(k, width, v));
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
  getCurrentSymbols().push_back(s);
}

void Cpp_interface::addRoundingModeSymbol(ASTNode& s)
{
  addSymbol(s);
  bm.rounding_mode_symbols.insert(s);
  assertRoundingModeValid(s);
}

// SMT-LIB's RoundingMode sort has exactly five values; the 5-bit carrier has
// 32. Pin a declared RoundingMode symbol to the five one-hot encodings.
// Asserted (rather than built into the blaster) so that every route to a
// query -- check-sat here, or a C-API query over a parsed file -- sees it.
void Cpp_interface::assertRoundingModeValid(const ASTNode& s)
{
  AddAssert(bm.roundingModeValidConstraint(s));
}

void Cpp_interface::addArraySymbol(ASTNode& s, const array_sort& sort)
{
  addSymbol(s);

  s.SetIndexWidth(sort.index.width);
  s.SetValueWidth(sort.elem.width);

  // A float element's format rides on the array node itself, in the same
  // exponent/significand widths a float term uses; a read off the array
  // inherits it (see deriveFPFormat). Everything the node cannot say --
  // a float *index* format, and RoundingMode on either side -- goes into
  // the manager's registries instead.
  if (sort.elem.kind == array_sort_component::FLOATINGPOINT)
  {
    s.SetExpWidth(sort.elem.exp_bits);
    s.SetSigWidth(sort.elem.sig_bits);
  }
  if (sort.elem.kind == array_sort_component::ROUNDINGMODE)
    bm.rm_element_arrays.insert(s);
  if (sort.index.kind == array_sort_component::FLOATINGPOINT)
    bm.fp_index_arrays[s] =
        std::make_pair(sort.index.exp_bits, sort.index.sig_bits);
  if (sort.index.kind == array_sort_component::ROUNDINGMODE)
    bm.rm_index_arrays.insert(s);
}

bool Cpp_interface::arraySortsAgree(const ASTNode& arr, const array_sort& sort)
{
  unsigned eb = 0;
  unsigned sb = 0;
  const bool fp_index = bm.arrayHasFpIndex(arr, eb, sb);

  if (sort.index.kind == array_sort_component::FLOATINGPOINT)
  {
    if (!fp_index || eb != sort.index.exp_bits || sb != sort.index.sig_bits)
      return false;
  }
  else if (fp_index)
    return false;

  if ((sort.index.kind == array_sort_component::ROUNDINGMODE) !=
      bm.arrayHasRmIndex(arr))
    return false;

  if (sort.elem.kind == array_sort_component::FLOATINGPOINT)
  {
    if (arr.GetExpWidth() != sort.elem.exp_bits ||
        arr.GetSigWidth() != sort.elem.sig_bits)
      return false;
  }
  else if (arr.GetExpWidth() != 0)
    return false;

  if ((sort.elem.kind == array_sort_component::ROUNDINGMODE) !=
      bm.arrayHasRmElement(arr))
    return false;

  return true;
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
  cout << "(error \"" << msg << "\")" << endl;
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

  if (frames.size() > 0)
  {
    // used just by cvc parser.
    assert(letMgr->_parser_symbol_table.size() == 0);

    removeFrame();
  }

  assert(frames.size() == 0);

  // These tables might hold references to symbols that have been
  // removed.
  resetSolver();

  cleanUp();

  checkInvariant();

  init();
}

void Cpp_interface::popToFirstLevel()
{
  while (frames.size() > 1)
    pop();

  // I don't understand why this is required.
  while (bm.getAssertLevel() > 0)
    bm.Pop();
}

// Weaker than reset(): the base level's declarations and the current options
// survive, only the assertions go. Deliberately avoids popToFirstLevel(),
// which leaves bm's assert level at zero and so breaks checkInvariant().
void Cpp_interface::resetAssertions()
{
  // Discard every level above the base one, which also removes the symbols
  // declared inside them.
  while (frames.size() > 1)
    pop();

  // Empty the base level without removing it, so that the assertion stack,
  // the result cache and the frame stack stay in step.
  bm.Pop();
  bm.Push();

  // The base level's declarations survive reset-assertions, so the validity
  // constraint attached to each RoundingMode declaration must survive too;
  // the assertion carrying it was just discarded.
  for (const ASTNode& s : bm.rounding_mode_symbols)
    assertRoundingModeValid(s);

  // Whatever we last concluded no longer refers to these assertions.
  cache.back() = Entry(SOLVER_UNDECIDED);

  // These tables might hold references to the assertions just discarded.
  resetSolver();

  checkInvariant();
}

void Cpp_interface::pop()
{
  if (frames.size() == 0)
    FatalError("Popping from an empty stack.");
  if (frames.size() == 1)
    FatalError("Can't pop away the default base element.");

  bm.Pop();

  // These tables might hold references to symbols that have been
  // removed.
  resetSolver();

  cache.erase(cache.end() - 1);

  assert(letMgr->_parser_symbol_table.size() == 0);

  removeFrame();
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

  addFrame();
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

  // If there are no model commands in the STMLIB2 (say) file, then the command line
  // argument might set that asks for the model to be checked.
  if (changed_model_status)
  {
    bm.UserFlags.check_counterexample_flag = produce_models;
  }

  Entry& last_run = cache.back();
  if (((unsigned)last_run.node_number != assertionsSMT2.back().GetNodeNum()) &&
      (last_run.result == SOLVER_SATISFIABLE))
  {
    // extra asserts might have been added to it,
    // flipping from sat to unsat. But never from unsat to sat.
    last_run.result = SOLVER_UNDECIDED;
  }

  // We might have run this query before, or it might already be shown to be
  // unsat. If it was sat, we've stored the result (but not the model), so we 
  // can shortcut and return what we know - if we don't need the model.
  if ( (!((last_run.result == SOLVER_SATISFIABLE) || last_run.result == SOLVER_UNSATISFIABLE)) ||
        (last_run.result == SOLVER_SATISFIABLE && bm.UserFlags.construct_counterexample_flag)
     )
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

  ToSATBase::PrintOutput(&bm, last_run.result);

  // User has specified -p option to print model.
   if (bm.UserFlags.print_counterexample_flag)
   {
      getModel();
   }


  bm.GetRunTimes()->start(RunTimes::Parsing);
}

// This method sets up some of the globally required data.
Cpp_interface::Cpp_interface(STPMgr& bm_)
    : bm(bm_), letMgr(new LetMgr(bm.ASTUndefined)), nf(bm_.defaultNodeFactory)
{
  nf = bm.defaultNodeFactory;
  startup();
  stp::GlobalParserInterface = this;
  stp::GlobalParserBM = &bm_;
  GlobalSTP = new STP(&bm);
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

  // Every frame is going away, so don't erase the functions from the
  // map one at a time (files can define millions of functions).
  functions.clear();
  for (SolverFrame* frame : frames)
    frame->getFunctions().clear();

  while (frames.size() > 0)
  {
    removeFrame();
  }
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

  if (option == "print-success")
  {
    if (value == "true")
      setPrintSuccess(true);
    else if (value == "false")
      setPrintSuccess(false);
    else
      unsupported();
  }
  else if (option == "produce-models")
  {
    changed_model_status = true;

    if (value == "true")
    {
      produce_models = true;
      success();
    }
    else if (value == "false")
    {
      produce_models = false;
      success();
    }
    else
      unsupported();
  }
  else if (option == "diagnostic-output-channel")
  {
    if (value == "stdout")
      success();
    else
      unsupported();
  }	  
  else
    unsupported();
}

// The options we report are exactly the ones setOption() honours; everything
// else must answer "unsupported" rather than invent a value (SMT-LIB 2.6
// 4.1.7).
void Cpp_interface::getOption(std::string option)
{
  if (option == "print-success")
    cout << (print_success ? "true" : "false") << endl;
  else if (option == "produce-models")
    cout << (produce_models ? "true" : "false") << endl;
  else if (option == "diagnostic-output-channel")
    cout << "\"stdout\"" << endl;
  else
  {
    unsupported();
    return;
  }

  flush(cout);
}

void Cpp_interface::getInfo(std::string flag)
{
  if (flag == "name")
    cout << "(:name \"STP\")" << endl;
  else if (flag == "version")
    cout << "(:version \"" << get_git_version_tag() << "\")" << endl;
  else if (flag == "error-behavior")
  {
    // FatalError() exits rather than unwinding to the next command.
    cout << "(:error-behavior immediate-exit)" << endl;
  }
  else if (flag == "assertion-stack-levels")
  {
    // The base level is not an assertion level.
    cout << "(:assertion-stack-levels "
         << (frames.size() > 0 ? frames.size() - 1 : 0) << ")" << endl;
  }
  else
  {
    // :all-statistics, :authors and :reason-unknown are not reported.
    unsupported();
    return;
  }

  flush(cout);
}

void Cpp_interface::getAssertions()
{
  // GetAsserts() flattens the stack into the individual asserted formulas,
  // unlike getAssertVector(), which conjoins each level.
  const ASTVec v = GetAsserts();

  cout << "(" << endl;
  for (const ASTNode& n : v)
  {
    printer::SMTLIB2_Print1(cout, n, 0, false);
    cout << endl;
  }
  cout << ")" << endl;
  flush(cout);
}

void Cpp_interface::getValue(const ASTVec& v)
{
  std::ostringstream os;

  os << "(" << std::endl;

  for (ASTNode n : v)
  {
    if (n.GetKind() != SYMBOL)
    {
      unsupported();
      return;
    }
    GlobalSTP->Ctr_Example->PrintSMTLIB2(os, n);
    os << std::endl;
  }
  os << ")";

  cout << os.str() << std::endl;
}

// Note, doesn't consider that extra assertions might have been applied?
void Cpp_interface::getModel()
{
  if (!bm.UserFlags.construct_counterexample_flag)
  {
    // Perhaps this is confusing and instead it whould return "()"?
    unsupported();
    return;
  }

  if (cache.size() ==0 || (cache.back().result != SOLVER_SATISFIABLE))
  {
    return;
  }

  cout << "(" << std::endl;
  std::ostringstream os;
  GlobalSTP->Ctr_Example->PrintFullCounterExampleSMTLIB2(os);
  cout << os.str();
  cout << ")" << std::endl;
}

void CNFClearMemory()
{
  Cnf_ManFree();
}

Cpp_interface::SolverFrame::SolverFrame(
    ankerl::unordered_dense::map<std::string, Function>*
        global_function_context)
    : _global_function_context(global_function_context)
{
}

// When we destroy a solver frame, we need to make sure that all of the scoped
// functions in the global function context are also correctly removed.
//
// This ensures that the reference counting for any symbols used in the
// function declarations are correctly decremented.
Cpp_interface::SolverFrame::~SolverFrame()
{
  // Iterate on the function names in our current scope
  for (const auto& scoped_function_name : getFunctions())
  {
    // Find this function in the global context
    const auto& function_to_erase =
        _global_function_context->find(scoped_function_name);

    // Hard-error if we cannot find it!
    if (function_to_erase == _global_function_context->end())
    {
      FatalError("Trying to erase function which has not been defined.");
    }

    // Remove our scope function from the global function context
    _global_function_context->erase(function_to_erase);
  }
}

vector<std::string>& Cpp_interface::SolverFrame::getFunctions()
{
  return _scoped_functions;
}

ASTVec& Cpp_interface::SolverFrame::getSymbols()
{
  return _scoped_symbols;
}
}
