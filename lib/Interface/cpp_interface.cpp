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
#include "stp/Extensionality/ExtensionalityContext.h"
#include "stp/Incremental/IncrementalSolver.h"
#include "stp/Parser/LetMgr.h"
#include "stp/Parser/parser.h"
#include "stp/Printer/printers.h"
#include "stp/STPManager/STP.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Sat/SATSolverFactory.h"
#include "stp/Simplifier/DistinctOrdering.h"
#include "stp/ToSat/ToSATAIG.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/UninterpretedFunctions/UFModel.h"
#include "stp/UninterpretedFunctions/UFRefinement.h"
#include "stp/Util/GitSHA1.h"
#include <cassert>
#include <limits>

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
  session_touched = false;
  model_valid = false;
  current_command_rejected = false;
  current_command_active = false;
  incremental_from_start =
      bm.UserFlags.incremental_mode == UserDefinedFlags::IncrementalMode::ON;
  session_incremental = incremental_from_start;
  delayed_bv_auto_engagement = false;
  solves_run = 0;
}

void Cpp_interface::addFrame()
{
  // create a new frame
  SolverFrame* new_frame = new SolverFrame(&functions, &sort_aliases, &bm);

  // store the new frame
  frames.push_back(new_frame);
}

void Cpp_interface::removeFrame()
{
    // obtain the last frame
    SolverFrame* last = frames.back();

    // delete it
    delete last;

    // remove it from the vector of frames
    frames.pop_back();
}

Cpp_interface::Cpp_interface(STPMgr& bm_, NodeFactory* factory)
    : bm(bm_), set_global_parser_bm(false),
      letMgr(new LetMgr(bm.ASTUndefined)), nf(factory)
{
  init();
}

// Every writer of the parser globals borrows: whoever sets one clears it
// again. GlobalParserInterface is cleared whichever constructor ran, because
// the callers that assign it directly (the C interface's parse entry points)
// point it at a stack local of theirs, which is this object. The guard keeps
// an interface that has since been superseded from clearing a pointer that
// now belongs to a live one.
Cpp_interface::~Cpp_interface()
{
  cleanUp();

  if (GlobalParserInterface == this)
    GlobalParserInterface = NULL;

  if (set_global_parser_bm && GlobalParserBM == &bm)
    GlobalParserBM = NULL;
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

bool Cpp_interface::declaredSortsEnabled() const
{
  return bm.UserFlags.enable_uninterpreted_functions || ax_enabled_by_logic;
}

void Cpp_interface::setLogic(const std::string& logic)
{
  const bool selectsUF =
      logic.compare(0, 5, "QF_UF") == 0 ||
      logic.compare(0, 6, "QF_AUF") == 0;
  if (selectsUF)
  {
    if (!uf_enabled_by_logic)
    {
      uf_option_before_logic = bm.UserFlags.enable_uninterpreted_functions;
      uf_enabled_by_logic = true;
    }
    bm.UserFlags.enable_uninterpreted_functions = true;
  }
  else
    restoreUFOptionAfterLogic();

  const bool selectsAX = logic == "QF_AX";
  if (selectsAX)
  {
    if (!ax_enabled_by_logic)
    {
      array_equality_option_before_logic =
          bm.UserFlags.enable_array_equality;
      ax_enabled_by_logic = true;
    }
    bm.UserFlags.enable_array_equality = true;
  }
  else
    restoreArrayEqualityOptionAfterLogic();

  // This policy is intentionally limited to the two fragments measured in
  // the threshold sweep. QF_AUFBV, the FP logics, legacy parsers, and native
  // API clients retain the established solve-3 policy until separately
  // measured. An explicit --incremental-auto-engage-at still wins below.
  delayed_bv_auto_engagement = logic == "QF_BV" || logic == "QF_ABV";
}

void Cpp_interface::restoreUFOptionAfterLogic()
{
  if (!uf_enabled_by_logic)
    return;
  bm.UserFlags.enable_uninterpreted_functions = uf_option_before_logic;
  uf_enabled_by_logic = false;
}

void Cpp_interface::restoreArrayEqualityOptionAfterLogic()
{
  if (!ax_enabled_by_logic)
    return;
  bm.UserFlags.enable_array_equality = array_equality_option_before_logic;
  ax_enabled_by_logic = false;
}

void Cpp_interface::AddAssert(const ASTNode& assert)
{
  if (current_command_rejected)
    return;
  bm.AddAssert(assert);
  session_touched = true;

  // SMT-LIB: an assertion invalidates the most recent model, and the last
  // check-sat-assuming round with it.
  model_valid = false;
  lastCheckWasAssuming = false;
}

void Cpp_interface::SetQuery(const ASTNode& q)
{
  bm.SetQuery(q);
}

ASTNode Cpp_interface::CreateNode(stp::Kind kind, const stp::ASTVec& children)
{
  return nf->CreateNode(kind, children);
}

ASTNode Cpp_interface::CreateNode(stp::Kind kind, const stp::ASTNode n0,
                                  const stp::ASTNode n1)
{
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

void Cpp_interface::addSortAlias(const std::string& name,
                                 const SourceSort& sort)
{
  // SMT-LIB does not allow redefining a sort name.
  if (sort_aliases.find(name) != sort_aliases.end())
    FatalError("the sort name is already defined");
  sort_aliases[name] = sort;
  frames.back()->addSortAlias(name);
  session_touched = true;
}

bool Cpp_interface::lookupSortAlias(const std::string& name,
                                    SourceSort& sort) const
{
  const auto found = sort_aliases.find(name);
  if (found == sort_aliases.end())
    return false;
  sort = found->second;
  return true;
}

void Cpp_interface::addSortAlias(const std::string& name, unsigned exp_width,
                                 unsigned sig_width)
{
  addSortAlias(name, SourceSort::floatingPoint(exp_width, sig_width));
}

bool Cpp_interface::lookupSortAlias(const std::string& name,
                                    unsigned& exp_width,
                                    unsigned& sig_width) const
{
  SourceSort sort;
  if (!lookupSortAlias(name, sort) ||
      sort.kind() != SourceSort::Kind::FloatingPoint)
    return false;
  exp_width = sort.exponentWidth();
  sig_width = sort.significandWidth();
  return true;
}

ASTNode Cpp_interface::CreateBVConst(string& strval, int base, int bit_width)
{
  return bm.CreateBVConst(strval, base, bit_width);
}

// FIXME: unsigned long long int is wong. Use intN_t from cstdint
ASTNode Cpp_interface::CreateBVConst(unsigned int width,
                                     uint64_t bvconst)
{
  return bm.CreateBVConst(width, bvconst);
}

ASTNode Cpp_interface::CreateRMConst(unsigned mode)
{
  return bm.CreateRMConst(mode);
}

ASTNode Cpp_interface::CreateSourceSymbol(const char* name,
                                          const SourceSort& source_sort)
{
  // SMT-LIB 2 reserves an initial '@' or '.' for the solver, and STP does not
  // merely respect that reservation, it relies on it: CreateFreshVariable
  // mints '@' names, and so do the objects supplying the unspecified results
  // of the partial floating-point operations, whose identity *is* their name.
  // An input free to declare one of those names could be handed the solver's
  // own object -- which is a wrong answer, not just a confusing model.
  //
  // Every declaration the parser makes comes through here, so this is the one
  // place it has to be said. Symbols STP mints for itself go to the manager
  // directly and are unaffected.
  if (STPMgr::isReservedSymbolName(name))
    FatalError("a symbol name beginning with '@' or '.' is reserved for "
               "solver use and cannot be declared");

  return bm.CreateSourceSymbol(name, source_sort);
}

ASTNode Cpp_interface::LookupOrCreateSymbol(const char* const name)
{
  ASTNode found;
  if (LookupSymbol(name, found))
    return found;
  return bm.LookupOrCreateSymbol(name);
}

ASTNode Cpp_interface::CreateParameterisedBooleanVar(const ASTNode& var,
                                                     const ASTNode& constant)
{
  return bm.NewParameterized_BooleanVar(var, constant);
}

void Cpp_interface::removeSymbol(ASTNode to_remove)
{
  if (!frames.back()->removeSymbol(to_remove))
    FatalError("Should have been removed...");
}

void Cpp_interface::storeFunction(const string& name, const ASTVec& params,
                                  const ASTNode& function)
{
  if (current_command_rejected)
    return;
  Function f;
  f.name = name;

  ASTNodeMap fromTo;
  for (size_t i = 0, size = params.size(); i < size; ++i)
  {
    ASTNode p = bm.CreateFreshSourceVariable(
        params[i].GetSourceSort(), "STP_INTERNAL_FUNCTION_NAME");
    fromTo.insert(std::make_pair(params[i], p));
    f.params.push_back(p);
  }

  ASTNodeMap cache;
  f.function = SubstitutionMap::replace(function, fromTo, cache, nf);

  // store the function in the global function store
  functions.insert(std::make_pair(f.name, f));
  session_touched = true;

  // record which frame this function was created in, such that it can be
  // removed later (e.g., via pop)
  getCurrentFunctions().push_back(f.name);
}

ASTNode Cpp_interface::applyFunction(const string& name, const ASTVec& params)
{
  const Function* f = lookupFunction(name);
  if (f == NULL)
    FatalError("Trying to apply function which has not been defined.");
  return applyFunction(*f, params);
}

const Cpp_interface::Function*
Cpp_interface::lookupFunction(const string& name) const
{
  const auto found = functions.find(name);
  return found == functions.end() ? NULL : &found->second;
}

ASTNode Cpp_interface::applyFunction(const Function& f, const ASTVec& params)
{
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
    if (f.params[i].GetSourceSort() != params[i].GetSourceSort())
      FatalError("Actual parameter sort differs from formal");

    fromTo.insert(std::make_pair(f.params[i], params[i]));
  }

  ASTNodeMap cache;
  return SubstitutionMap::replace(f.function, fromTo, cache, nf);
}

const UFDecl* Cpp_interface::declareUninterpretedFunction(
    const std::string& name, const std::vector<SourceSort>& domain,
    const SourceSort& codomain, std::string* diagnostic)
{
  if (lookupFunction(name) != NULL)
  {
    if (diagnostic != NULL)
      *diagnostic = "name '" + name + "' already denotes a define-fun";
    return NULL;
  }
  ASTNode symbol;
  if (LookupSymbol(name.c_str(), symbol))
  {
    if (diagnostic != NULL)
      *diagnostic = "name '" + name + "' already denotes an ordinary symbol";
    return NULL;
  }
  const UFDecl* result =
      bm.getUFContext()->declareFunction(name, domain, codomain, diagnostic);
  if (result != NULL)
  {
    session_touched = true;
    model_valid = false;
    if (GlobalSTP != NULL &&
        GlobalSTP->Ctr_Example->getUFTheoryAdapter() != NULL)
      GlobalSTP->Ctr_Example->getUFTheoryAdapter()
          ->invalidateCertifiedModel();
  }
  return result;
}

const UFDecl* Cpp_interface::declareScopedUninterpretedFunction(
    const std::string& name, const std::vector<SourceSort>& domain,
    const SourceSort& codomain, std::string* diagnostic)
{
  const UFDecl* result =
      declareUninterpretedFunction(name, domain, codomain, diagnostic);
  if (result != NULL)
    frames.back()->addUFDeclaration(result);
  return result;
}

const UFDecl*
Cpp_interface::lookupUninterpretedFunction(const std::string& name) const
{
  const UFContext* context = bm.getUFContextIfAny();
  return context == NULL ? NULL : context->lookup(name);
}

ASTNode Cpp_interface::applyUninterpretedFunction(
    const UFDecl* declaration, const ASTVec& actuals,
    std::string* diagnostic)
{
  UFContext* context = bm.getUFContextIfAny();
  if (context == NULL)
  {
    if (diagnostic != NULL)
      *diagnostic = "uninterpreted-function declaration is not owned by this "
                    "context";
    return bm.ASTUndefined;
  }
  return context->apply(declaration, actuals, diagnostic);
}

ASTNode Cpp_interface::getUninterpretedApplicationValue(
    const ASTNode& application, std::string* diagnostic)
{
  if (!model_valid || GlobalSTP == NULL)
  {
    if (diagnostic != NULL)
      *diagnostic = "no current certified model is available";
    return bm.ASTUndefined;
  }
  if (GlobalSTP->hasIncrementalSolver())
    GlobalSTP->getIncrementalSolver()->materializePendingModel();
  ASTNode value;
  std::string localDiagnostic;
  if (!UFModel::evaluateApplication(
          &bm, GlobalSTP->Ctr_Example->getUFTheoryAdapter(), application,
          value, localDiagnostic))
  {
    if (diagnostic != NULL)
      *diagnostic = localDiagnostic;
    return bm.ASTUndefined;
  }
  return value;
}

bool Cpp_interface::hasUninterpretedFunctions() const
{
  const UFContext* context = bm.getUFContextIfAny();
  return context != NULL && context->activeDeclarationCount() != 0;
}

ASTNode Cpp_interface::LookupOrCreateSymbol(string name)
{
  return LookupOrCreateSymbol(name.c_str());
}

bool Cpp_interface::LookupSymbol(const char* const name, ASTNode& output)
{
  // One strlen for the whole search, not one per frame.
  const std::string_view sv(name);
  for (auto it = frames.rbegin(); it != frames.rend(); ++it)
  {
    if ((*it)->lookupSymbol(sv, output))
      return true;
  }
  return false;
}

bool Cpp_interface::LookupTemporarySymbol(const char* const name,
                                          ASTNode& output)
{
  const std::string_view sv(name);
  for (auto it = frames.rbegin(); it != frames.rend(); ++it)
  {
    if ((*it)->lookupTemporarySymbol(sv, output))
      return true;
  }
  return false;
}

void Cpp_interface::setPrintSuccess(bool ps)
{
  print_success = ps;
  success();
}

bool Cpp_interface::isSymbolAlreadyDeclared(string name)
{
  ASTNode ignored;
  return LookupSymbol(name.c_str(), ignored);
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
  if (current_command_rejected)
    return;
  frames.back()->addSymbol(s);
  session_touched = true;
}

void Cpp_interface::addTemporarySymbol(ASTNode& s)
{
  // A formal is parser-local scratch, not a declaration. The successful
  // storeFunction call is what makes the command observable and marks the
  // session touched; a rejected define-fun leaves neither behind.
  frames.back()->addTemporarySymbol(s);
}

bool Cpp_interface::validateTopLevelDeclarationName(
    const std::string& name, std::string* diagnostic)
{
  std::string message;
  if (lookupFunction(name) != NULL)
    message = "name '" + name + "' already denotes a define-fun";
  else if (lookupUninterpretedFunction(name) != NULL)
    message = "name '" + name +
              "' already denotes an uninterpreted function";
  else
  {
    ASTNode symbol;
    if (LookupSymbol(name.c_str(), symbol))
      message = "name '" + name + "' already denotes an ordinary symbol";
  }
  if (message.empty())
    return true;
  if (diagnostic != NULL)
    *diagnostic = message;
  return false;
}

void Cpp_interface::addRoundingModeSymbol(ASTNode& s)
{
  addSymbol(s);
  assertRoundingModeValid(s);
}

// SMT-LIB's RoundingMode sort has exactly five values; the 5-bit carrier has
// 32. Pin a declared RoundingMode symbol to the five one-hot encodings.
// Asserted (rather than built into the blaster) so that every route to a
// query -- check-sat here, or a C-API query over a parsed file -- sees it.
//
// This is the pin for the level the symbol is declared at, not the guarantee:
// an assertion belongs to a level and the symbol node does not, so FpTotalise
// re-pins every mode the formula names at solve time. See its class comment.
void Cpp_interface::assertRoundingModeValid(const ASTNode& s)
{
  AddAssert(bm.roundingModeValidConstraint(s));
}

void Cpp_interface::addArraySymbol(ASTNode& s, const array_sort& sort)
{
  addSymbol(s);
  (void)sort;
}

bool Cpp_interface::arraySortsAgree(const ASTNode& arr, const array_sort& sort)
{
  return arr.GetSourceSort() == sort.sourceSort();
}

void Cpp_interface::success()
{
  if (current_command_rejected)
    return;
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

void Cpp_interface::beginCurrentCommand()
{
  // A prior parse may have aborted while reducing a formal declaration. Its
  // command and lexer state are not part of this new top-level command.
  if (current_command_active)
    abortCurrentCommand();
  SMT2ResetCommandLexerState();
  current_command_active = true;
  current_command_rejected = false;
  if (UFContext* context = bm.getUFContextIfAny())
    context->beginParserCommand();
}

void Cpp_interface::abortCurrentCommand()
{
  if (current_command_active)
  {
    if (UFContext* context = bm.getUFContextIfAny())
      context->finishParserCommand(false);
    frames.back()->clearTemporarySymbols();
  }
  current_command_rejected = false;
  current_command_active = false;
  SMT2ResetCommandLexerState();
}

void Cpp_interface::rejectCurrentCommand(const std::string& diagnostic)
{
  // One command has one rejection response. Continue reducing with typed
  // carriers, but do not emit a diagnostic for every malformed descendant.
  if (current_command_rejected)
    return;
  current_command_rejected = true;
  error(diagnostic);
}

void Cpp_interface::refuseCurrentCommand(const std::string& diagnostic)
{
  rejectCurrentCommand(diagnostic);
  // Reducing the rest of the command first would only build carriers for a
  // session that is over, so the report above is the last thing printed on
  // stdout and FatalError takes it from here.
  FatalError(diagnostic.c_str());
}

void Cpp_interface::finishCurrentCommand()
{
  if (current_command_active)
  {
    if (UFContext* context = bm.getUFContextIfAny())
      context->finishParserCommand(!current_command_rejected);
    // Function formals are command-local even if error recovery skipped a
    // define-fun production's ordinary removal loop.
    frames.back()->clearTemporarySymbols();
  }
  current_command_rejected = false;
  current_command_active = false;
  SMT2ResetCommandLexerState();
}

void Cpp_interface::resetSolver()
{
  bm.ClearAllTables();
  GlobalSTP->ClearAllTables();
}

// The incremental driver's base-level units are permanent, so anything that
// empties the base level must destroy the driver; a fresh one is created on
// demand. resetSolver() deliberately does not do this -- it runs before
// every solve, where the driver's persistence is the whole point.
void Cpp_interface::resetIncrementalSolver()
{
  if (GlobalSTP != NULL)
    GlobalSTP->resetIncrementalSolver();
}

// Public and define-fun handles retain opaque ARRAY_EQ nodes, never generated
// proxies. Scope mutation can therefore discard the complete last-solve table
// without inspecting which handles remain live; future assertions lower their
// durable structural handles afresh.
void Cpp_interface::discardExtensionalitySolveState()
{
  ExtensionalityContext* ext = bm.getExtensionalityIfAny();
  if (ext != NULL)
    ext->beginSolve();
}

// Can clear away the base frame..
void Cpp_interface::reset()
{
  // reset destroys the current frame and UF context itself, so close its
  // accepted command transaction while both are still alive. The grammar's
  // outer finish becomes a harmless no-op after init().
  if (current_command_active)
    finishCurrentCommand();

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
  discardExtensionalitySolveState();
  resetIncrementalSolver();

  // A reason-unknown belongs to the session that produced it.
  bm.clearUnknown();

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

// Weaker than reset(): retain options and the selected logic, but empty the
// assertion stack. With :global-declarations false SMT-LIB requires this to
// discard declarations and definitions too; with it true they are kept, which
// is the point of the option for a driver that streams large terms once and
// re-queries them.
void Cpp_interface::resetAssertions()
{
  // Pop the ordinary levels through the ordinary path so the assertion stack,
  // result cache, declarations and solver tables stay in lockstep.
  while (frames.size() > 1)
    pop();

  assert(frames.size() == 1);
  assert(cache.size() == 1);
  assert(bm.getAssertLevel() == 1);

  // The base is an assertion level too for declaration lifetime. Rebuild it
  // rather than merely replacing its assertions: destroying the frame drops
  // its symbols, functions, and sort aliases together. Global declarations
  // are exactly the case where that must not happen -- the pops above have
  // already moved every level's declarations into this frame -- so there the
  // frame stays and only its assertions go.
  model_valid = false;
  bm.Pop();
  if (!global_declarations)
    removeFrame();
  cache.clear();
  bm.clearUnknown();

  // These tables may retain the discarded assertions or declarations.
  resetSolver();
  discardExtensionalitySolveState();
  resetIncrementalSolver();

  cache.push_back(Entry(SOLVER_UNDECIDED));
  if (!global_declarations)
    addFrame();
  bm.Push();

  checkInvariant();
}

void Cpp_interface::pop()
{
  if (frames.size() == 0)
    FatalError("Popping from an empty stack.");
  if (frames.size() == 1)
    FatalError("Can't pop away the default base element.");

  model_valid = false;
  lastCheckWasAssuming = false;

  bm.Pop();

  // These tables might hold references to symbols that have been
  // removed.
  resetSolver();
  discardExtensionalitySolveState();

  cache.erase(cache.end() - 1);

  assert(letMgr->_parser_symbol_table.size() == 0);

  // Popping a level undoes the assertions made in it either way; what it does
  // to the declarations made in it is what :global-declarations selects
  // (SMT-LIB 2.6, 4.1.5). When they are global, the level's declarations move
  // down to the base frame -- which only reset destroys -- instead of dying
  // with the frame.
  if (global_declarations)
    frames.front()->adoptDeclarations(*frames.back());

  removeFrame();
  checkInvariant();
}

void Cpp_interface::push()
{
  // The session is incremental from the first push on (the same trigger z3
  // uses): later check-sats go through the incremental driver where they
  // can. Sessions that never push are untouched by this. This is session
  // state, not the user's request, so it does not travel through UserFlags --
  // but --incremental=off is a request that no session become incremental,
  // pushing ones included, so it is the one thing that stops this.
  if (bm.UserFlags.incremental_mode != UserDefinedFlags::IncrementalMode::OFF)
    session_incremental = true;

  // If the prior one is unsatisiable then the new one will be too. The
  // core provenance rides along, so a shortcut taken above a core-recorded
  // level still reports itself under --stats.
  if (cache.size() > 1 && cache.back().result == SOLVER_UNSATISFIABLE)
  {
    Entry inherited(SOLVER_UNSATISFIABLE);
    inherited.fromCore = cache.back().fromCore;
    cache.push_back(inherited);
  }
  else
    cache.push_back(Entry(SOLVER_UNDECIDED));

  model_valid = false;
  lastCheckWasAssuming = false;
  session_touched = true;

  bm.Push();

  addFrame();
  checkInvariant();
}

void Cpp_interface::popAssumptionFrame()
{
  // The assumption frame cannot contain declarations -- nothing runs
  // between the internal push and this pop -- so unlike pop() there is no
  // danger of derived tables referencing removed symbols, and the tables
  // are kept so the model remains readable. The next real solve clears
  // them first (checkSat calls resetSolver before solving).
  bm.Pop();
  cache.erase(cache.end() - 1);
  removeFrame();
  checkInvariant();
}

void Cpp_interface::checkSatAssuming(const ASTVec& assumptions)
{
  // The parser reduces a malformed UF subexpression to a typed carrier so it
  // can reach this outer boundary. Rejection is transactional: in particular
  // do not push, invalidate a model, solve the base stack, or print a verdict.
  if (current_command_rejected)
    return;

  // An internal assertion level holding exactly the assumptions. push()
  // inherits a known-UNSAT verdict from the level below, and a SAT answer
  // propagates to the levels beneath, so the verdict cache keeps working
  // across this the same way it does for user levels.
  push();

  for (const ASTNode& a : assumptions)
    AddAssert(a);

  // The assumptions ride as the last level, assumed one conjunct each so
  // an unsat answer can name exactly the assumptions it used.
  checkSat(getAssertVector(), true);

  // Remember the round for get-unsat-assumptions; the verdict is read
  // before the frame pop erases its cache entry.
  lastAssumptionTerms = assumptions;
  lastAssumingResult = cache.back().result;
  lastCheckWasAssuming = true;

  // checkSat set model_valid from this solve's outcome; the frame pop
  // below deliberately leaves both it and the model alone, so get-value
  // and get-model answer under the assumptions, per SMT-LIB.
  popAssumptionFrame();
}

void Cpp_interface::ignoreCheckSat()
{
  ignoreCheckSatRequest = true;
}

// Does some simple caching of prior results.
void Cpp_interface::checkSat(const ASTVec& assertionsSMT2,
                             bool fromCheckSatAssuming)
{
  if (ignoreCheckSatRequest)
    return;

  // Any ordinary check supersedes the last check-sat-assuming round;
  // checkSatAssuming re-records after this returns.
  lastCheckWasAssuming = false;
  session_touched = true;

  bm.GetRunTimes()->stop(RunTimes::Parsing);
  bm.clearUnknown();
  // Element names belong to one model. Cleared here rather than in getModel so
  // that get-value and get-model agree within a solve whichever is asked first.
  bm.clearUninterpretedElements();

  // Bracket the solve so (get-info :all-statistics) can report on this check
  // alone. Taken here rather than at entry so the parse that preceded the
  // check is not charged to it.
  const std::vector<CategoryWork> work_before = currentWork();

  checkInvariant();
  assert(assertionsSMT2.size() == cache.size());

  // A sort declared by declare-sort is unbounded and its carrier is not, so a
  // query needing more elements of one sort than the carrier can tell apart may
  // be unsatisfiable in the encoding while being satisfiable in the theory.
  // Which way that can go wrong is not symmetric: every carrier pattern denotes
  // an element and bit equality on the carrier is the sort's equality, so any
  // satisfying carrier assignment is a genuine model and `sat` is always sound.
  // Only `unsat` can be an artefact, and it is also the one answer a caller
  // cannot tell from a real refutation.
  //
  // So the query is SOLVED and only an `unsat` is withheld -- see the
  // conversion after the solve below. Refusing before solving would have
  // thrown away sound `sat` answers too, which is a plain loss for the users
  // who narrowed the carrier deliberately.
  //
  // Decided here rather than in either engine because both are reachable from
  // this one funnel and the question is about the input, not about how it was
  // solved. Conservative: it counts terms that could need an element of their
  // own, not elements actually forced apart, so an over-capacity query that is
  // unsatisfiable for unrelated reasons is withheld too. At the default width
  // that takes 65537 terms of one sort -- reachable by a generated query, and
  // measured at 0.27 s, so it is no hand-written query that gets there rather
  // than none at all.
  std::string carrierExhausted;
  const bool carrierMayBeShort =
      sortCarrierExhausted(assertionsSMT2, carrierExhausted);

  Entry& last_run = cache.back();
  if ((last_run.node_number != assertionsSMT2.back().GetNodeNum()) &&
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

    // The policy itself lives on the driver, so this frontend and the C API
    // cannot drift apart again; --incremental=on overrides it, and
    // --incremental=off has already kept session_incremental false.
    const bool autoEngaged = IncrementalSolver::automaticEngagementReady(
        bm.UserFlags.incremental_auto_engage_at, delayed_bv_auto_engagement,
        solves_run);
    const bool use_incremental =
        session_incremental &&
        (incremental_from_start || autoEngaged) &&
        GlobalSTP->getIncrementalSolver()->canHandle(assertionsSMT2);
    // The `use_incremental &&` this used to carry was dead: the value is read
    // only inside the `if (use_incremental)` branch below.
    const bool firstForcedIncrementalSolve =
        IncrementalSolver::forcedFirstSolve(incremental_from_start, solves_run);
    solves_run++;

    SOLVER_RETURN_TYPE last_result;
    if (use_incremental)
    {
      // The incremental driver keeps its SAT solver and encoding across
      // check-sats; resetSolver() above cleared only batch-pipeline tables.
      IncrementalSolver* inc = GlobalSTP->getIncrementalSolver();
      last_result = inc->checkSat(assertionsSMT2, fromCheckSatAssuming,
                                  firstForcedIncrementalSolve);

      // Core-aware caching: when the refutation's failed assumptions all
      // lie at or below some level D beneath the top, the stack truncated
      // at D is already unsatisfiable -- the failed levels' formulas
      // force their assumed literals (an activation variable occurs only
      // in its implication clauses, so any model of the content extends
      // to it), and the base only ever grows. Recording unsat on level
      // D's entry lets every later check that pops back to (or re-pushes
      // above) D answer from the cache without solving; a pop past D
      // erases the entry, which is exactly its validity condition.
      if (last_result == SOLVER_UNSATISFIABLE && inc->lastSolveWasUnsat())
      {
        const std::vector<size_t> core = inc->lastUnsatCoreLevels();
        const size_t deepest = core.empty() ? 0 : core.back();
        if (deepest + 1 < cache.size())
        {
          cache[deepest].result = SOLVER_UNSATISFIABLE;
          cache[deepest].fromCore = true;
        }
      }
    }
    else
    {
      ASTNode query;

      if (assertionsSMT2.size() > 1)
        query = nf->CreateNode(AND, assertionsSMT2);
      else if (assertionsSMT2.size() == 1)
        query = assertionsSMT2[0];
      else
        query = bm.ASTTrue;

      last_result = GlobalSTP->TopLevelSTP(query, bm.ASTFalse);
    }

    // Store away the answer. It may also be unknown or an error.
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
  else if (bm.UserFlags.stats_flag &&
           last_run.result == SOLVER_UNSATISFIABLE && last_run.fromCore)
  {
    std::cerr << "Incremental: unsat answered from a cached core, no solve"
              << std::endl;
  }

  // An `unsat` reached over a carrier too narrow for the query may be an
  // artefact of the encoding rather than a refutation, and nothing in the
  // output would distinguish the two. Withhold it. `sat` is kept: every
  // carrier assignment denotes a real assignment of elements, so a model found
  // this way is a genuine one whatever the carrier's width.
  if (carrierMayBeShort && last_run.result == SOLVER_UNSATISFIABLE)
  {
    bm.noteUnknown(UnknownReason::CarrierExhausted, carrierExhausted);
    last_run.result = bm.unknownResult();
  }

  // A model exists exactly when this check concluded SAT and the solve
  // constructed a counterexample. On the shortcut paths (verdict reused,
  // no model wanted) nothing was constructed, so nothing may be read.
  model_valid = (last_run.result == SOLVER_SATISFIABLE) &&
                bm.UserFlags.construct_counterexample_flag;

  recordCheckWork(work_before);

  if (bm.UserFlags.quick_statistics_flag)
  {
    bm.GetRunTimes()->print();
    {
      // What the bit-blaster was handed and what the abstraction took, per
      // kind, and what the refinement then spent.
      //
      // The counters have always been kept; they had no route out but the C
      // API, so the numbers that say how much wide arithmetic actually
      // reached the blaster, and how many rounds were spent on it, could not
      // be read off a run. That made them the numbers a comparison against
      // another solver most wanted and least had: reading them off the query
      // text instead over-counts, because it counts occurrences the
      // simplifier has already retired.
      const UserDefinedFlags::EncodingCoverage& c = bm.UserFlags.coverage;
      // In AbstractionKind order; a kind added there needs a name here.
      static const char* kindNames[] = {"eq",   "compare", "ite",
                                        "plus", "mult",    "divmod"};
      static_assert(sizeof(kindNames) / sizeof(kindNames[0]) ==
                        UserDefinedFlags::EncodingCoverage::KINDS,
                    "abstraction kind names are out of step with the counters");
      std::cerr << "Abstraction coverage (candidates -> abstracted):";
      for (unsigned i = 0; i < UserDefinedFlags::EncodingCoverage::KINDS; i++)
        std::cerr << " " << kindNames[i] << "=" << c.bv_candidates[i] << "->"
                  << c.bv_abstracted[i];
      std::cerr << std::endl
                << "Abstraction refinement: rounds=" << c.bv_refinement_rounds
                << " blocking=" << c.bv_blocking_lemmas
                << " schema=" << c.bv_schema_lemmas << std::endl;
    }
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
//
// NB it does not create the STP that GlobalSTP points at. Every writer of
// GlobalSTP borrows: whoever allocates the STP frees it, and the pointer is
// only ever a non-owning view. Callers that need one (because they reach
// something which dereferences GlobalSTP, such as BBAsProp) construct the STP
// themselves and assign it before that point.
Cpp_interface::Cpp_interface(STPMgr& bm_)
    : bm(bm_), set_global_parser_bm(true),
      letMgr(new LetMgr(bm.ASTUndefined)), nf(bm_.defaultNodeFactory)
{
  nf = bm.defaultNodeFactory;
  startup();
  stp::GlobalParserInterface = this;
  stp::GlobalParserBM = &bm_;
  init();
}

void Cpp_interface::cleanUp()
{
  // exit and reset perform cleanup from inside their command action and do
  // not return through the ordinary closing-parenthesis reduction.
  if (current_command_active)
    finishCurrentCommand();

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

  restoreUFOptionAfterLogic();
  restoreArrayEqualityOptionAfterLogic();
}

// SMT-LIB gives these options a <b_value> argument (2.6, figure 3.9), so a
// value that is not true or false does not describe a command the solver
// could have carried out: it is malformed input, and "unsupported" -- the
// answer for what the solver cannot do (3.9.1) -- would misreport it as a
// capability it lacks. Report it the way the parser reports its own
// malformed input, with an error response and then a stop.
void Cpp_interface::badBooleanOptionValue(const std::string& option,
                                          const std::string& value)
{
  const std::string msg = "set-option :" + option +
                          " takes true or false, but was given: " + value;
  error(msg);
  FatalError(msg.c_str());
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
      badBooleanOptionValue(option, value);
  }
  else if (option == "produce-models")
  {
    // An input to the counterexample-construction derivations (batch and
    // driver), NOT the self-check flag: asking for models is not asking
    // for them to be verified, and the driver defers construction to the
    // first read.
    if (value == "true")
    {
      produce_models = true;
      bm.UserFlags.produce_models = true;
      success();
    }
    else if (value == "false")
    {
      produce_models = false;
      bm.UserFlags.produce_models = false;
      success();
    }
    else
      badBooleanOptionValue(option, value);
  }
  else if (option == "global-declarations")
  {
    // SMT-LIB gives this option mode "start" (2.6, 4.1.7), and this is the
    // one option where a late change is not merely untidy: pop reads the flag
    // as it stands then, not the value that was in force when the declaration
    // was made, so setting it with declarations already in hand would decide
    // their scope after the fact. Refuse instead of answering that
    // retroactively. Nothing is at stake before the first declaration or
    // assertion, so set-logic, set-info and the other options may all precede
    // it, and reset makes it settable again.
    if (session_touched)
    {
      const std::string msg = "set-option :global-declarations must come "
                              "before anything is declared or asserted";
      error(msg);
      FatalError(msg.c_str());
    }

    if (value == "true")
    {
      global_declarations = true;
      success();
    }
    else if (value == "false")
    {
      global_declarations = false;
      success();
    }
    else
      badBooleanOptionValue(option, value);
  }
  else if (option == "produce-unsat-assumptions")
  {
    // get-unsat-assumptions is always answered; the option is accepted so
    // conforming drivers can request it.
    if (value == "true" || value == "false")
      success();
    else
      badBooleanOptionValue(option, value);
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
  else if (option == "global-declarations")
    cout << (global_declarations ? "true" : "false") << endl;
  else if (option == "diagnostic-output-channel")
    cout << "\"stdout\"" << endl;
  else
  {
    unsupported();
    return;
  }

  flush(cout);
}

std::vector<Cpp_interface::CategoryWork> Cpp_interface::currentWork() const
{
  std::vector<CategoryWork> result;
  for (const RunTimes::CategoryTotal& total : bm.GetRunTimes()->totals())
  {
    CategoryWork work;
    work.category = static_cast<int>(total.category);
    work.count = total.count;
    work.time_ms = total.time_ms;
    result.push_back(work);
  }
  return result;
}

void Cpp_interface::recordCheckWork(const std::vector<CategoryWork>& before)
{
  last_check_work.clear();
  for (const CategoryWork& now : currentWork())
  {
    CategoryWork charged = now;
    for (const CategoryWork& then : before)
    {
      if (then.category == now.category)
      {
        charged.count -= then.count;
        charged.time_ms -= then.time_ms;
        break;
      }
    }

    // --print-quickstat clears the run times as it prints, so a later
    // reading can be smaller than the one taken before the solve. Report
    // nothing rather than a negative count when that happens.
    if (charged.count > 0 && charged.time_ms >= 0)
      last_check_work.push_back(charged);
  }
}

// The keywords (get-info :all-statistics) answers with, one per run-time
// category. Deliberately a table of its own rather than RunTimes' display
// names: those are prose, they are what --print-quickstat prints, and one of
// them is misspelled -- reusing them would make an output contract out of
// text that exists to be read, where tidying a name later would break
// whoever parses it.
static const char* categoryKeyword(RunTimes::Category c)
{
  switch (c)
  {
    case RunTimes::Transforming: return "transforming";
    case RunTimes::SimplifyTopLevel: return "simplifying";
    case RunTimes::Parsing: return "parsing";
    case RunTimes::CNFConversion: return "cnf-conversion";
    case RunTimes::BitBlasting: return "bit-blasting";
    case RunTimes::Solving: return "sat-solving";
    case RunTimes::BVSolver: return "bitvector-solving";
    case RunTimes::PropagateEqualities: return "variable-elimination";
    case RunTimes::SendingToSAT: return "sending-to-sat-solver";
    case RunTimes::CounterExampleGeneration:
      return "counter-example-generation";
    case RunTimes::SATSimplifying: return "sat-simplification";
    case RunTimes::ConstantBitPropagation: return "constant-bit-propagation";
    case RunTimes::ArrayReadRefinement: return "array-read-refinement";
    case RunTimes::ApplyingSubstitutions: return "applying-substitutions";
    case RunTimes::RemoveUnconstrained: return "removing-unconstrained";
    case RunTimes::PureLiterals: return "pure-literals";
    case RunTimes::UseITEContext: return "ite-contexts";
    case RunTimes::AIGSimplifyCore: return "aig-core-simplification";
    case RunTimes::IntervalPropagation: return "interval-propagation";
    case RunTimes::Flatten: return "sharing-aware-flattening";
    case RunTimes::NodeDomainAnalysis: return "node-domain-analysis";
    case RunTimes::StrengthReduction: return "strength-reduction";
    case RunTimes::SplitExtracts: return "split-extracts";
    case RunTimes::Rewriting: return "sharing-aware-rewriting";
    case RunTimes::MergeSame: return "merge-same";
    case RunTimes::CommonSubSum: return "common-sub-sum-extraction";
  }
  return "unknown";
}

void Cpp_interface::getInfo(std::string flag)
{
  if (flag == "name")
    cout << "(:name \"STP\")" << endl;
  else if (flag == "version")
  {
    // The SAT backend behind the build decides both the answers and the
    // timings, and a session driving STP through SMT-LIB has no --version to
    // ask; so the version string carries the same backend list --version
    // prints. The standard's response here is a single string, which is why
    // the list rides inside it rather than as info values of its own.
    cout << "(:version \"" << get_git_version_tag() << " (SAT solvers";
    const std::vector<std::string> solvers = compiledSolverVersions();
    for (size_t i = 0; i < solvers.size(); i++)
      cout << (i == 0 ? " " : ", ") << solvers[i];
    if (solvers.empty())
      cout << " none";
    cout << ")\")" << endl;
  }
  else if (flag == "authors")
  {
    // Required, like :name and :version (SMT-LIB 2.6, 4.1.8), and answered
    // collectively: the response is a fixed string, while the people it
    // stands for are in AUTHORS, where they can be credited properly and
    // kept current without touching the solver's output.
    cout << "(:authors \"the STP team\")" << endl;
  }
  else if (flag == "error-behavior")
  {
    // FatalError() exits rather than unwinding to the next command.
    cout << "(:error-behavior immediate-exit)" << endl;
  }
  else if (flag == "all-statistics")
  {
    // No standard statistics are defined (SMT-LIB 2.6, 4.1.8), so what is in
    // here is STP's own; the response shape is the standard's, a sequence of
    // info_response values. The per-stage numbers are the most recent check's,
    // as the standard asks; the process ones are what they say, process-wide,
    // and :check-sat-calls counts the session. Stages the check did no work in
    // are left out, so a small query does not answer with a screen of zeroes.
    //
    // The standard permits this only in sat or unsat mode. STP answers it
    // whenever it is asked, since the alternative under an immediate-exit
    // error behaviour is killing a session over a diagnostic query.
    std::ios_base::fmtflags saved(cout.flags());
    const std::streamsize saved_precision = cout.precision();
    cout << std::fixed;
    cout.precision(2);

    cout << "(:check-sat-calls " << solves_run << endl;
    cout << " :cpu-time " << processCpuTime() << endl;
    cout << " :peak-memory-mb " << peakMemoryMB();

    cout.flags(saved);
    cout.precision(saved_precision);

    for (const CategoryWork& work : last_check_work)
    {
      const char* keyword =
          categoryKeyword(static_cast<RunTimes::Category>(work.category));
      cout << endl << " :" << keyword << " " << work.count;
      cout << endl << " :" << keyword << "-time-ms " << work.time_ms;
    }
    cout << ")" << endl;
  }
  else if (flag == "assertion-stack-levels")
  {
    // The base level is not an assertion level.
    cout << "(:assertion-stack-levels "
         << (frames.size() > 0 ? frames.size() - 1 : 0) << ")" << endl;
  }
  else if (flag == "reason-unknown")
  {
    // Only meaningful after an answer of `unknown`, which is the one case
    // SMT-LIB defines it for. Asked at any other time the honest answer is
    // that there is no unknown to explain, and saying so beats inventing a
    // reason or reporting the flag as unsupported when it is implemented.
    // That answer is carried inside the info response rather than raised as
    // an error response, for the reason :all-statistics gives above: under an
    // immediate-exit error behaviour, raising one would kill the session over
    // a diagnostic query.
    switch (bm.getUnknownReason())
    {
      case UnknownReason::Timeout:
        cout << "(:reason-unknown timeout)" << endl;
        break;
      case UnknownReason::ConflictBudget:
        // Not `timeout`: this one is deterministic and re-running with more
        // time will reproduce it exactly. SMT-LIB admits an s-expression here,
        // and naming the flag is what a caller can act on.
        cout << "(:reason-unknown (incomplete \"the conflict budget set by "
                "--max-num-confl ran out\"))" << endl;
        break;
      case UnknownReason::CarrierExhausted:
      case UnknownReason::AssumedInjectivity:
      case UnknownReason::AIGBudget:
      case UnknownReason::Incomplete:
        // The predefined SMT-LIB spelling, followed by what was incomplete:
        // the flag admits an s-expression, and a bare "incomplete" tells a
        // caller nothing they can act on. All four share it because the
        // sentence is what says which, and SMT-LIB2 has no spelling that
        // would say it better.
        cout << "(:reason-unknown (incomplete \""
             << bm.getUnknownReasonDetail()
             << "\"))" << endl;
        break;
      case UnknownReason::None:
        // SOLVER_UNKNOWN cannot reach the frontend without a reason: both
        // output boundaries enforce that invariant. None therefore means
        // there was no unknown result to explain.
        cout << "(:reason-unknown (error \"the last answer was not "
                "unknown\"))" << endl;
        break;
    }
  }
  else
  {
    unsupported();
    return;
  }

  flush(cout);
}

// How many elements of one declared sort the query could need at once, counted
// per sort, against what its carrier can hold. See the caller for what is done
// with the answer.
bool Cpp_interface::sortCarrierExhausted(const ASTVec& assertions,
                                         std::string& detail) const
{
  // Nothing to count when no sort was ever declared, which is almost every
  // query. Checked before the walk rather than inside it: this runs on every
  // check-sat ahead of the result cache, and an O(DAG) sweep that always
  // answers no cost 6.7x on a session of repeated check-sats over a 60k-node
  // formula with no declare-sort in it at all.
  if (sort_aliases.empty())
    return false;
  bool anyDeclared = false;
  for (const std::pair<const std::string, SourceSort>& alias : sort_aliases)
    anyDeclared = anyDeclared ||
                  alias.second.kind() == SourceSort::Kind::Uninterpreted;
  if (!anyDeclared)
    return false;

  // What counts is a term that could need an element of its own, so two node
  // shapes carrying the sort are excluded and neither is an edge case:
  //
  //  - a declaration's identity symbol. It carries the codomain sort so that an
  //    application can derive its own, but it denotes the function, not an
  //    element, and counting it refused a query with one constant and one
  //    application at width 1 -- where one element suffices.
  //  - an if-then-else. Its value is always one of its branches, which are
  //    counted already, so it can never require a fresh element. Four
  //    constants and one ite over them read as five terms against a capacity
  //    of four.
  std::map<unsigned, uint64_t> named;
  std::map<unsigned, unsigned> widths;
  const auto reserve = [&named, &widths](const SourceSort& sort,
                                         uint64_t count) {
    if (sort.kind() != SourceSort::Kind::Uninterpreted || count == 0)
      return;
    uint64_t& total = named[sort.uninterpretedId()];
    if (std::numeric_limits<uint64_t>::max() - total < count)
      total = std::numeric_limits<uint64_t>::max();
    else
      total += count;
    widths[sort.uninterpretedId()] = sort.packedWidth();
  };
  ASTNodeSet visited;
  ASTNodeSet identities;
  const UFContext* const context = bm.getUFContextIfAny();
  if (context != NULL)
    context->collectIdentitySymbols(identities);
  std::vector<ASTNode> pending(assertions.begin(), assertions.end());
  while (!pending.empty())
  {
    const ASTNode current = pending.back();
    pending.pop_back();
    if (current.IsNull() || !visited.insert(current).second)
      continue;
    const SourceSort sort = current.GetSourceSort();
    if (sort.kind() == SourceSort::Kind::Uninterpreted &&
        current.GetKind() != ITE && identities.count(current) == 0)
      reserve(sort, 1);

    // Array extensionality introduces one witness index and two witness
    // reads for each distinct equality record. Those nodes deliberately use
    // raw bit-vector sorts because they live below the source boundary, so
    // the ordinary term count above cannot see their demand on a declared
    // component sort. Reserve their source-level elements here before the
    // lowering happens. This matters only for deliberately tiny
    // --uf-sort-width values; at the default width the bound is remote.
    if (current.GetKind() == ARRAY_EQ && current.Degree() == 2)
    {
      const SourceSort array = current[0].GetSourceSort();
      if (array.kind() == SourceSort::Kind::Array)
      {
        reserve(array.index(), 1);
        reserve(array.element(), 2);
      }
    }
    else if (current.GetKind() == DISTINCT && current.Degree() >= 2 &&
             current[0].GetSourceSort().kind() == SourceSort::Kind::Array)
    {
      // lowerDistinct creates one equality record for every operand pair.
      const uint64_t count = current.Degree();
      const uint64_t pairs =
          count > std::numeric_limits<uint64_t>::max() / (count - 1)
              ? std::numeric_limits<uint64_t>::max()
              : count * (count - 1) / 2;
      const SourceSort array = current[0].GetSourceSort();
      reserve(array.index(), pairs);
      reserve(array.element(),
              pairs > std::numeric_limits<uint64_t>::max() / 2
                  ? std::numeric_limits<uint64_t>::max()
                  : pairs * 2);
    }
    for (size_t i = 0; i < current.Degree(); ++i)
      pending.push_back(current[i]);
  }

  for (const std::pair<const unsigned, uint64_t>& entry : named)
  {
    const unsigned width = widths[entry.first];
    if (width >= 64)
      continue; // a carrier that wide holds more elements than can be named
    const uint64_t capacity = (uint64_t)1 << width;
    if (entry.second <= capacity)
      continue;
    // The remedy is a WIDTH, not a term count. Saying "raise it to at least 5"
    // for five terms named a value four times larger than needed, and above
    // 1024 named one the flag's own range check refuses -- so the advice was
    // unfollowable exactly where it was most needed.
    unsigned needed = width;
    while (needed < 64 && ((uint64_t)1 << needed) < entry.second)
      needed++;
    std::ostringstream message;
    message << "the query needs up to " << entry.second
            << " elements of sort " << uninterpretedSortName(entry.first)
            << ", and --uf-sort-width=" << width << " tells only " << capacity
            << " apart; raise --uf-sort-width to at least " << needed;
    detail = message.str();
    return true;
  }
  return false;
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
  if (current_command_rejected)
    return;
  if (!bm.UserFlags.construct_counterexample_flag || !model_valid)
  {
    unsupported();
    return;
  }

  // The driver defers counterexample construction to the first reader.
  // hasIncrementalSolver, not getIncrementalSolver: the latter constructs one
  // on demand, so asking it whether a driver exists built a driver -- and a
  // SAT backend with it -- in every batch session that printed a model.
  if (GlobalSTP != NULL && GlobalSTP->hasIncrementalSolver())
    GlobalSTP->getIncrementalSolver()->materializePendingModel();

  std::ostringstream os;

  os << "(" << std::endl;

  for (ASTNode n : v)
  {
    if (n.GetKind() == UF_APPLY)
    {
      std::string diagnostic;
      const ASTNode value =
          getUninterpretedApplicationValue(n, &diagnostic);
      if (value.GetKind() == UNDEFINED)
      {
        // The solve never reached this application, so there is no certified
        // value to hand back -- but there is still an answer, and the same
        // command list was already giving it: an application nested inside a
        // term goes through the model evaluator, which completes it against
        // the published interpretation, so (bvadd (f #x07) #x01) answered
        // while the bare (f #x07) was refused. The printed model is total and
        // says what (f #x07) is; refusing to repeat it here was the one place
        // the two disagreed.
        //
        // Fall through to the ordinary term path, which is that evaluator.
        // Anything genuinely unanswerable -- no model at all, an application
        // from another context, one whose model has been invalidated -- fails
        // there too, and the diagnostic computed above is what it reports.
        if (!model_valid || GlobalSTP == NULL)
        {
          if (diagnostic.empty())
            diagnostic = "uninterpreted-function application has no certified "
                         "value";
          refuseCurrentCommand(diagnostic);
        }
        GlobalSTP->Ctr_Example->PrintSMTLIB2(os, n);
        os << std::endl;
        continue;
      }
      os << "( ";
      // Through the letizing entry point, for the reason the note above
      // AbsRefine_CounterExample::PrintSMTLIB2 gives: an application's
      // arguments may be a shared DAG a caller built out of very little
      // input text.
      printer::SMTLIB2_PrintTerm(os, &bm, n);
      os << " ";
      // The value is printed at the application's own sort, not by handing the
      // node to the term printer -- which prints a node and would print an
      // element of a declared sort as the carrier pattern it is represented
      // by. The sort is recoverable here: a UF_APPLY's source sort is its
      // declaration's codomain.
      if (bm.isUninterpretedSortedTerm(n))
        os << "|"
           << bm.uninterpretedElementName(n.GetSourceSort(), value) << "|";
      else
        printer::SMTLIB2_Print1(os, value, 0, false);
      os << " )" << std::endl;
      continue;
    }
    // (get-value ...) asks for the value of arbitrary well-sorted terms and
    // not just of variables, and the model evaluator already decides all of
    // them -- including terms built over uninterpreted applications. The one
    // shape with no value to print is an array: (get-model) prints the
    // completed array interpretations instead. That refusal is
    // unconditional, because reaching the printer with an array aborted the
    // process rather than answering when array equality was disabled -- and
    // disabled is the default.
    if (n.GetType() == ARRAY_TYPE)
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

namespace
{
// Whether any top-level conjunct of `a` is in `failed`. The driver reports
// failed conjuncts of the assumptions LEVEL, and an assumption that is
// itself a conjunction was split before it was assumed, so membership is
// judged against its flattened conjuncts.
bool assumptionFailed(const ASTNode& a, const ASTNodeSet& failed,
                      const ASTNode& trueNode)
{
  std::vector<ASTNode> pending(1, a);
  while (!pending.empty())
  {
    const ASTNode n = pending.back();
    pending.pop_back();
    if (n == trueNode)
      continue;
    if (n.GetKind() == AND)
    {
      for (const ASTNode& c : n)
        pending.push_back(c);
      continue;
    }
    if (failed.count(n))
      return true;
  }
  return false;
}
} // namespace

void Cpp_interface::getUnsatAssumptions()
{
  // Meaningful right after a check-sat-assuming that answered unsat;
  // anything else gets the empty list, which is the correct core whenever
  // the command is legal at all.
  if (!lastCheckWasAssuming || lastAssumingResult != SOLVER_UNSATISFIABLE)
  {
    cout << "()" << endl;
    return;
  }

  // Per-assumption granularity from the driver when it ran the solve; the
  // full assumption set is always a correct core, and covers the batch
  // first solve and the extensionality rounds.
  std::vector<ASTNode> failed;
  bool granular = false;
  if (GlobalSTP != NULL && GlobalSTP->hasIncrementalSolver())
  {
    IncrementalSolver* inc = GlobalSTP->getIncrementalSolver();
    if (inc->lastSolveWasUnsat() &&
        inc->lastUnsatHasAssumptionGranularity())
    {
      failed = inc->lastUnsatAssumptionConjuncts();
      granular = true;
    }
  }
  const ASTNodeSet failedSet(failed.begin(), failed.end());

  ASTVec semanticAssumptions;
  const ASTVec* assumptionsForMatching = &lastAssumptionTerms;
  if (granular && bm.has_distinct)
  {
    semanticAssumptions.reserve(lastAssumptionTerms.size());
    for (const ASTNode& a : lastAssumptionTerms)
      semanticAssumptions.push_back(lowerDistinct(&bm, a));
    assumptionsForMatching = &semanticAssumptions;
  }

  // Ordinarily each failed driver conjunct is exactly one flattened conjunct
  // of a lowered source assumption. The simplifying factory may instead
  // collapse the assumptions level as a whole (for example, p and (not p))
  // before the driver assigns its per-conjunct literals. If a reported
  // conjunct cannot be mapped back, falling back to the full source set is a
  // correct core; silently dropping it can produce an empty, invalid one.
  bool completeMapping = true;
  if (granular)
  {
    for (const ASTNode& failedConjunct : failedSet)
    {
      const ASTNodeSet singleton{failedConjunct};
      bool found = false;
      for (const ASTNode& a : *assumptionsForMatching)
      {
        if (assumptionFailed(a, singleton, bm.ASTTrue))
        {
          found = true;
          break;
        }
      }
      if (!found)
      {
        completeMapping = false;
        break;
      }
    }
  }

  std::ostringstream os;
  os << "(";
  bool first = true;
  for (size_t i = 0; i < lastAssumptionTerms.size(); ++i)
  {
    if (granular && completeMapping &&
        !assumptionFailed((*assumptionsForMatching)[i], failedSet, bm.ASTTrue))
      continue;
    if (!first)
      os << " ";
    first = false;
    printer::SMTLIB2_Print1(os, lastAssumptionTerms[i], 0, false);
  }
  os << ")";
  cout << os.str() << endl;
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

  if (cache.size() == 0 || (cache.back().result != SOLVER_SATISFIABLE) ||
      !model_valid)
  {
    return;
  }

  // The driver defers counterexample construction to the first reader.
  // hasIncrementalSolver, not getIncrementalSolver: the latter constructs one
  // on demand, so asking it whether a driver exists built a driver -- and a
  // SAT backend with it -- in every batch session that printed a model.
  if (GlobalSTP != NULL && GlobalSTP->hasIncrementalSolver())
    GlobalSTP->getIncrementalSolver()->materializePendingModel();

  // The body is rendered first because rendering it is what names the
  // elements of any declared sort, and the preamble that declares them has to
  // come before the definitions that use them.
  std::ostringstream os;
  GlobalSTP->Ctr_Example->PrintFullCounterExampleSMTLIB2(os);

  cout << "(" << std::endl;

  // A model that mentions a sort declared by declare-sort has to say so, or it
  // cannot be read back: the sort has no elements anyone else knows about. So
  // it declares the sort, then one constant per element the model mentions,
  // and the definitions refer to those. Distinct names denote distinct
  // elements -- the convention every solver's models rest on, and the only
  // thing this format cannot state outright.
  // Every sort the body mentioned, not only those that named an element. A
  // sort can reach the text through a function signature alone -- a predicate
  // over an opaque sort, which is the commonest shape of all -- and a model
  // that used a sort it never declared cannot be read back at all.
  for (const SourceSort& sort : bm.uninterpretedSortsPrinted())
    cout << "(declare-sort " << sourceSortToSMTLib(sort) << " 0)" << std::endl;
  for (const STPMgr::UninterpretedElement& element : bm.uninterpretedElements())
    cout << "(declare-fun |" << element.name << "| () "
         << sourceSortToSMTLib(element.sort) << ")" << std::endl;

  cout << os.str();
  cout << ")" << std::endl;
}

void CNFClearMemory()
{
  Cnf_ManFree();
}

Cpp_interface::SolverFrame::SolverFrame(
    ankerl::unordered_dense::map<std::string, Function>*
        global_function_context,
    std::map<std::string, SourceSort>*
        global_sort_alias_context,
    STPMgr* manager)
    : _global_function_context(global_function_context),
      _global_sort_alias_context(global_sort_alias_context), _manager(manager)
{
}

// When we destroy a solver frame, we need to make sure that all of the scoped
// functions in the global function context are also correctly removed.
//
// This ensures that the reference counting for any symbols used in the
// function declarations are correctly decremented.
Cpp_interface::SolverFrame::~SolverFrame()
{
  UFContext* uf = _manager->getUFContextIfAny();
  if (uf != NULL)
  {
    for (const UFDecl* declaration : _scoped_uf_declarations)
    {
      std::string ignored;
      const bool removed = uf->deactivate(declaration, &ignored);
      assert(removed);
      (void)removed;
    }
  }

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

  // Sort declarations have the same SMT-LIB scope as symbols and functions:
  // pop drops declarations made in that frame, while reset and
  // reset-assertions drop every non-global declaration.
  for (const auto& scoped_alias_name : _scoped_sort_aliases)
  {
    const auto alias_to_erase =
        _global_sort_alias_context->find(scoped_alias_name);
    if (alias_to_erase == _global_sort_alias_context->end())
      FatalError("Trying to erase a sort alias which has not been defined.");
    _global_sort_alias_context->erase(alias_to_erase);
  }
}

vector<std::string>& Cpp_interface::SolverFrame::getFunctions()
{
  return _scoped_functions;
}

void Cpp_interface::SolverFrame::addSortAlias(const std::string& name)
{
  _scoped_sort_aliases.push_back(name);
}

void Cpp_interface::SolverFrame::addUFDeclaration(const UFDecl* declaration)
{
  assert(declaration != NULL);
  _scoped_uf_declarations.push_back(declaration);
}

void Cpp_interface::SolverFrame::addSymbol(const ASTNode& symbol)
{
  _scoped_symbols.push_back(symbol);
  _symbol_bindings[std::string(symbol.GetName())].push_back(symbol);
}

void Cpp_interface::SolverFrame::addTemporarySymbol(const ASTNode& symbol)
{
  addSymbol(symbol);
  _temporary_symbol_bindings[std::string(symbol.GetName())].push_back(symbol);
}

void Cpp_interface::SolverFrame::clearTemporarySymbols()
{
  while (!_temporary_symbol_bindings.empty())
  {
    const ASTNode symbol = _temporary_symbol_bindings.begin()->second.back();
    const bool removed = removeSymbol(symbol);
    assert(removed);
    (void)removed;
  }
}

bool Cpp_interface::SolverFrame::removeSymbol(const ASTNode& symbol)
{
  const auto temporary =
      _temporary_symbol_bindings.find(std::string_view(symbol.GetName()));
  if (temporary != _temporary_symbol_bindings.end() &&
      !temporary->second.empty() && temporary->second.back() == symbol)
  {
    temporary->second.pop_back();
    if (temporary->second.empty())
      _temporary_symbol_bindings.erase(temporary);
  }

  const auto binding = _symbol_bindings.find(std::string_view(symbol.GetName()));
  if (binding == _symbol_bindings.end() || binding->second.empty() ||
      binding->second.back() != symbol)
    return false;
  binding->second.pop_back();
  if (binding->second.empty())
    _symbol_bindings.erase(binding);

  for (auto it = _scoped_symbols.end(); it != _scoped_symbols.begin();)
  {
    --it;
    if (*it == symbol)
    {
      _scoped_symbols.erase(it);
      return true;
    }
  }
  return false;
}

void Cpp_interface::SolverFrame::adoptDeclarations(SolverFrame& donor)
{
  // Re-add rather than splice: this frame's own bindings index has to end up
  // knowing about the adopted symbols, and adding them in declaration order
  // keeps the most recent declaration of a name the one lookupSymbol finds.
  for (const ASTNode& symbol : donor._scoped_symbols)
    addSymbol(symbol);
  donor._scoped_symbols.clear();
  donor._symbol_bindings.clear();

  // Functions and sort aliases live in contexts shared by every frame; a
  // frame only records the names it is responsible for erasing, so moving
  // the names is what moves the responsibility.
  _scoped_functions.insert(_scoped_functions.end(),
                           donor._scoped_functions.begin(),
                           donor._scoped_functions.end());
  donor._scoped_functions.clear();

  _scoped_sort_aliases.insert(_scoped_sort_aliases.end(),
                              donor._scoped_sort_aliases.begin(),
                              donor._scoped_sort_aliases.end());
  donor._scoped_sort_aliases.clear();

  _scoped_uf_declarations.insert(_scoped_uf_declarations.end(),
                                 donor._scoped_uf_declarations.begin(),
                                 donor._scoped_uf_declarations.end());
  donor._scoped_uf_declarations.clear();
}

bool Cpp_interface::SolverFrame::lookupSymbol(std::string_view name,
                                              ASTNode& output) const
{
  const auto found = _symbol_bindings.find(name);
  if (found == _symbol_bindings.end() || found->second.empty())
    return false;
  output = found->second.back();
  return true;
}

bool Cpp_interface::SolverFrame::lookupTemporarySymbol(
    const std::string_view name, ASTNode& output) const
{
  const auto found = _temporary_symbol_bindings.find(name);
  if (found == _temporary_symbol_bindings.end() || found->second.empty())
    return false;
  output = found->second.back();
  return true;
}
}
