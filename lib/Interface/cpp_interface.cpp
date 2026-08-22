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
#include "stp/Parser/LetMgr.h"
#include "stp/Printer/printers.h"
#include "stp/Sat/SATSolverFactory.h"
#include "stp/Util/GitSHA1.h"
#include "stp/Incremental/IncrementalSolver.h"
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
  incremental_from_start =
      bm.UserFlags.incremental_mode == UserDefinedFlags::IncrementalMode::ON;
  session_incremental = incremental_from_start;
  delayed_bv_auto_engagement = false;
  solves_run = 0;
}

void Cpp_interface::addFrame()
{
  // create a new frame
  SolverFrame* new_frame = new SolverFrame(&functions, &sort_aliases);

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

void Cpp_interface::setLogic(const std::string& logic)
{
  // This policy is intentionally limited to the two fragments measured in
  // the threshold sweep. QF_AUFBV, the FP logics, legacy parsers, and native
  // API clients retain the established solve-3 policy until separately
  // measured. An explicit --incremental-auto-engage-at still wins below.
  delayed_bv_auto_engagement = logic == "QF_BV" || logic == "QF_ABV";
}

void Cpp_interface::AddAssert(const ASTNode& assert)
{
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

ASTNode Cpp_interface::CreateBVConst(const char* const strval, int base)
{
  return bm.CreateBVConst(strval, base);
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

types Cpp_interface::functionReturnType(const string& name)
{
  const auto found = functions.find(name);
  if (found == functions.end())
    return UNKNOWN_TYPE;

  return found->second.function.GetType();
}

SourceSort Cpp_interface::functionReturnSourceSort(const string& name)
{
  const auto found = functions.find(name);
  return found == functions.end() ? SourceSort::unknown()
                                  : found->second.function.GetSourceSort();
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

bool Cpp_interface::isSymbolAlreadyDeclared(char* name)
{
  ASTNode ignored;
  return LookupSymbol(name, ignored);
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
  frames.back()->addSymbol(s);
  session_touched = true;
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

  // Recorded distinct groups name nodes from assertions that no longer
  // exist. The ordering pass ignores a group its walk cannot reach, so
  // keeping them would be harmless; dropping them keeps a long session's
  // registry proportional to what is asserted rather than to what has ever
  // been asserted.
  bm.distinctGroups.clear();

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
  bm.distinctGroups.clear();
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

  // Bracket the solve so (get-info :all-statistics) can report on this check
  // alone. Taken here rather than at entry so the parse that preceded the
  // check is not charged to it.
  const std::vector<CategoryWork> work_before = currentWork();

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
  else if (bm.UserFlags.stats_flag &&
           last_run.result == SOLVER_UNSATISFIABLE && last_run.fromCore)
  {
    std::cerr << "Incremental: unsat answered from a cached core, no solve"
              << std::endl;
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
    switch (bm.unknown_reason)
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
      case UnknownReason::Incomplete:
        // The predefined SMT-LIB spelling, followed by what was incomplete:
        // the flag admits an s-expression, and a bare "incomplete" tells a
        // caller nothing they can act on.
        cout << "(:reason-unknown (incomplete \"" << bm.unknown_detail
             << "\"))" << endl;
        break;
      case UnknownReason::None:
        // Two shapes reach here: no unknown to explain, and an unknown whose
        // producer recorded no reason. Told apart by the verdict, because
        // answering "not unknown" after an unknown would be a plain lie.
        //
        // SOLVER_TIMEOUT is the verdict every no-answer carries, whichever
        // budget ran out, and PrintOutput answers `unknown` for all of them --
        // so a check-sat that gave up and recorded nothing lands here holding
        // exactly that, and saying "not unknown" would contradict the line
        // above it. Every producer of that verdict does record a reason today;
        // this arm is what keeps a future one that forgets from turning a
        // missing explanation into a false statement. SOLVER_UNDECIDED is
        // deliberately not here: it is what the cache holds before a level has
        // been solved and what a stale entry is reset to, so admitting it
        // would answer for a check-sat that never ran.
        if (cache.size() > 0 && cache.back().result == SOLVER_TIMEOUT)
          cout << "(:reason-unknown unknown)" << endl;
        else
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
    // (get-value ...) asks for the value of arbitrary well-sorted terms and
    // not just of variables, and the model evaluator already decides all of
    // them. The one shape with no value to print is an array: (get-model)
    // prints the completed array interpretations instead. That refusal is
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

  std::ostringstream os;
  os << "(";
  bool first = true;
  for (const ASTNode& a : lastAssumptionTerms)
  {
    if (granular && !assumptionFailed(a, failedSet, bm.ASTTrue))
      continue;
    if (!first)
      os << " ";
    first = false;
    printer::SMTLIB2_Print1(os, a, 0, false);
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
        global_function_context,
    std::map<std::string, SourceSort>*
        global_sort_alias_context)
    : _global_function_context(global_function_context),
      _global_sort_alias_context(global_sort_alias_context)
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

ASTVec& Cpp_interface::SolverFrame::getSymbols()
{
  return _scoped_symbols;
}

void Cpp_interface::SolverFrame::addSortAlias(const std::string& name)
{
  _scoped_sort_aliases.push_back(name);
}

void Cpp_interface::SolverFrame::addSymbol(const ASTNode& symbol)
{
  _scoped_symbols.push_back(symbol);
  _symbol_bindings[std::string(symbol.GetName())].push_back(symbol);
}

bool Cpp_interface::SolverFrame::removeSymbol(const ASTNode& symbol)
{
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
}
