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
#include "stp/Parser/SMT2Output.h"
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
#include "stp/Util/SMTLibString.h"
#include "Lra/LraFrontend.h"
#include <cassert>
#include <charconv>
#include <exception>
#include <limits>

using std::cerr;
using std::cout;
using std::endl;

namespace stp
{

namespace
{
// Opens the engine's own work in a command -- a check, a model read, a push
// -- and records in engine_work_failed that an exception left it. Only an
// EngineFatal is ever classified by the record (see engine_work_failed); a
// ParseAbandon or ScriptEnded unwinding through ends the parse on its own
// terms, before any EngineFatal could be asked about.
class EngineWork
{
public:
  explicit EngineWork(bool& failed) noexcept
      : failed_(failed), uncaught_(std::uncaught_exceptions())
  {
  }
  ~EngineWork()
  {
    if (std::uncaught_exceptions() > uncaught_)
      failed_ = true;
  }
  EngineWork(const EngineWork&) = delete;
  EngineWork& operator=(const EngineWork&) = delete;

private:
  bool& failed_;
  const int uncaught_;
};
} // namespace

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
  output_channels->reset();
  produce_models = initial_produce_models;
  bm.UserFlags.produce_models = initial_produce_models;
  bm.UserFlags.random_seed = initial_random_seed;
  solver_random_seed = initial_random_seed;
  produce_assertions = false;
  produce_assignments = false;
  produce_unsat_assumptions = false;
  produce_unsat_cores = false;
  core_solver_layout = false;
  last_core_available = false;
  last_assumption_core_available = false;
  last_unsat_core.clear();
  last_core_assumption_indices.clear();
  current_assertion_name.reset();
  global_declarations = false;
  mode = Mode::Start;
  current_command_name.clear();
  current_command_supported = true;
  session_touched = false;
  model_valid = false;
  current_command_rejected = false;
  current_command_active = false;
  incremental_from_start =
      bm.UserFlags.incremental_mode == UserDefinedFlags::IncrementalMode::ON;
  session_incremental = incremental_from_start;
  pushed_in_session = false;
  delayed_bv_auto_engagement = false;
  lra_logic = false;
  last_check_work.clear();
}

void Cpp_interface::addFrame()
{
  // create a new frame
  SolverFrame* new_frame = new SolverFrame(&functions, &sort_aliases, &bm);

  // store the new frame
  frames.push_back(new_frame);
  assertion_names.emplace_back();
}

void Cpp_interface::removeFrame()
{
    // obtain the last frame
    SolverFrame* last = frames.back();

    // delete it
    delete last;

    // remove it from the vector of frames
    frames.pop_back();
    assertion_names.pop_back();
}

Cpp_interface::Cpp_interface(STPMgr& bm_, NodeFactory* factory)
    : bm(bm_), initial_produce_models(bm_.UserFlags.callerRequestedModel()),
      model_option_before_parse(bm_.UserFlags.produce_models),
      initial_random_seed(bm_.UserFlags.random_seed),
      output_channels(new SMT2Output), set_global_parser_bm(false),
      letMgr(new LetMgr(bm.ASTUndefined)), nf(factory)
{
  init();
}

// Every writer of the parser globals borrows: whoever sets one clears it
// again. GlobalParserInterface is cleared whichever constructor ran, because
// the callers that assign it directly (the API's parse entries) point it at
// a stack local of theirs, which is this object. The guard keeps
// an interface that has since been superseded from clearing a pointer that
// now belongs to a live one.
Cpp_interface::~Cpp_interface()
{
  cleanUp();
  bm.UserFlags.produce_models = model_option_before_parse;

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
  // Keep assertion occurrences intact: labels and get-assertions refer to
  // the original assertions, even after a check has conjoined a level.
  ASTVec result;
  for (const ASTVec* level : bm.AssertLevels())
    result.push_back(level->empty() ? bm.ASTTrue
                     : level->size() == 1 ? level->front()
                     : nf->CreateNode(AND, *level));
  return result;
}

void Cpp_interface::adoptAssertionNames(const AssertionNames& names)
{
  assert(names.size() <= frames.size());
  assertion_names = names;
  assertion_names.resize(frames.size());
}

void Cpp_interface::nameCurrentAssertion(const std::string& name)
{
  if (current_command_name == "assert")
    current_assertion_name = name;
}

void Cpp_interface::addParsedAssertion(const ASTNode& assertion)
{
  AddAssert(assertion);
  if (!current_command_rejected && current_assertion_name)
    assertion_names.back().emplace(bm.AssertLevels().back()->size() - 1,
                                   *current_assertion_name);
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
  mode = Mode::Assert;
  const bool selectsUF =
      logic == "ALL" || logic.compare(0, 5, "QF_UF") == 0 ||
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

  ax_enabled_by_logic = logic == "QF_AX";
  const bool selectsArrays = logic == "ALL" || logic.compare(0, 4, "QF_A") == 0;
  if (selectsArrays)
  {
    if (!arrays_enabled_by_logic)
    {
      array_equality_option_before_logic =
          bm.UserFlags.enable_array_equality;
      arrays_enabled_by_logic = true;
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
  lra_logic = logic == "QF_LRA";
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
  ax_enabled_by_logic = false;
  if (!arrays_enabled_by_logic)
    return;
  bm.UserFlags.enable_array_equality = array_equality_option_before_logic;
  arrays_enabled_by_logic = false;
}

void Cpp_interface::AddAssert(const ASTNode& assert)
{
  if (current_command_rejected)
    return;
  try
  {
    bm.AddAssert(assert);
  }
  catch (const lra::FrontendFailure& failure)
  {
    // Registering an assertion preregisters its Real atoms, and that walk
    // does exact arithmetic, so it can refuse the same way a Real term
    // constructor can -- a chain of products outgrows the number budget
    // before any solving starts. registerFormula, one line further on,
    // translates every frontend failure it sees; preregister's escaped
    // instead, and nothing above here catches it, so a budget refusal on
    // an assert reached terminate. Decline the command with the refusal's
    // own diagnostic, which is what every other refused Real command does.
    refuseCurrentCommand(std::string("assertion could not be registered: ") +
                         failure.what());
    return;
  }
  session_touched = true;

  // SMT-LIB: an assertion invalidates the most recent model, and the last
  // check-sat-assuming round with it.
  model_valid = false;
  lastCheckWasAssuming = false;
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
  {
    const std::string msg = "the sort name is already defined: " + name;
    rejectCurrentCommand(msg);
    endParseWithDiagnostic(msg);
  }
  if (accept_sort_declaration && !accept_sort_declaration(name, sort))
    refuseCurrentCommand("the sort name '" + name +
                         "' conflicts with a declaration retained by the term manager");
  sort_aliases.emplace(name, SMT2SortDefinition{0, SMT2Sort(sort)});
  frames.back()->addSortAlias(name);
  session_touched = true;
}

bool Cpp_interface::lookupSortAlias(const std::string& name,
                                    SourceSort& sort) const
{
  const auto found = sort_aliases.find(name);
  if (found == sort_aliases.end())
    return false;
  if (found->second.arity != 0)
    return false;
  sort = found->second.body.sourceSort();
  return true;
}

void Cpp_interface::addSortParameter(const std::string& name)
{
  const unsigned slot = sort_parameters.size();
  if (!sort_parameters.emplace(name, slot).second)
    refuseCurrentCommand("duplicate sort parameter: " + name);
}

SMT2Sort Cpp_interface::sortAtom(const std::string& name, const SourceSort& builtin) const
{
  const auto parameter = sort_parameters.find(name);
  return parameter == sort_parameters.end() ? SMT2Sort(builtin)
                                            : SMT2Sort::param(parameter->second);
}

SMT2Sort Cpp_interface::sortExpression(const std::string& name,
                                      const std::vector<SMT2Sort>& arguments) const
{
  const auto parameter = sort_parameters.find(name);
  if (parameter != sort_parameters.end())
  {
    if (!arguments.empty())
      throw std::invalid_argument("sort parameter cannot take arguments: " + name);
    return SMT2Sort::param(parameter->second);
  }
  const auto definition = sort_aliases.find(name);
  if (definition == sort_aliases.end())
    throw std::invalid_argument("unknown sort (not built in, and not a declared sort): " + name);
  if (arguments.size() != definition->second.arity)
    throw std::invalid_argument("wrong number of arguments to sort: " + name);
  return definition->second.body.substitute(arguments);
}

SourceSort Cpp_interface::resolveSort(const SMT2Sort& expression)
{
  try
  {
    return expression.sourceSort();
  }
  catch (const std::invalid_argument& error)
  {
    refuseCurrentCommand(error.what());
  }
}

void Cpp_interface::defineSort(const std::string& name, const SMT2Sort& body)
{
  if (sort_parameters.empty())
    addSortAlias(name, resolveSort(body));
  else
  {
    if (sort_aliases.count(name))
      refuseCurrentCommand("the sort name is already defined: " + name);
    if (accept_sort_declaration && !accept_sort_declaration(name, SourceSort::unknown()))
      refuseCurrentCommand("the sort name conflicts with a declaration retained by the term manager: " + name);
    sort_aliases.emplace(name, SMT2SortDefinition{static_cast<unsigned>(sort_parameters.size()), body});
    frames.back()->addSortAlias(name);
    session_touched = true;
  }
  sort_parameters.clear();
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

ASTNode Cpp_interface::CreateRealConst(const std::string& exact_text)
{
  return bm.CreateRealConst(exact_text);
}

ASTNode Cpp_interface::CreateRealTerm(Kind kind, const ASTVec& children)
{
  return bm.CreateRealTerm(kind, children);
}

ASTNode Cpp_interface::CreateRealPredicate(Kind kind, const ASTNode& lhs,
                                           const ASTNode& rhs)
{
  return bm.CreateRealPredicate(kind, lhs, rhs);
}

ASTNode Cpp_interface::CreateFpToReal(const ASTNode& x)
{
  return bm.CreateFpToReal(x);
}


void Cpp_interface::checkReservedSymbolName(const char* name)
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
  {
    const std::string msg = std::string("a symbol name beginning with '@' or '.' is reserved for "
                                        "solver use and cannot be declared: ") +
                            name;
    rejectCurrentCommand(msg);
    endParseWithDiagnostic(msg);
  }
}

ASTNode Cpp_interface::CreateSourceSymbol(const char* name,
                                          const SourceSort& source_sort)
{
  checkReservedSymbolName(name);
  return bm.CreateSourceSymbol(name, source_sort);
}

ASTNode Cpp_interface::CreateParameterSymbol(const char* name,
                                             const SourceSort& source_sort)
{
  checkReservedSymbolName(name);
  // A formal is local to its definition. Registering it as a public Real
  // symbol both requests an unnecessary model value and invalidates the
  // current exact model, even though the assertion context has not changed.
  return bm.CreateInternalSourceSymbol(name, source_sort);
}

ASTNode Cpp_interface::LookupOrCreateSymbol(const char* const name)
{
  ASTNode found;
  if (LookupSymbol(name, found))
    return found;
  return bm.LookupOrCreateSymbol(name);
}

void Cpp_interface::removeSymbol(ASTNode to_remove)
{
  if (!frames.back()->removeSymbol(to_remove))
    FatalError("Should have been removed...");
}

void Cpp_interface::storeFunction(const string& name, const ASTVec& params,
                                  const ASTNode& function, bool named)
{
  if (current_command_rejected)
    return;
  if (accept_function_definition && !accept_function_definition(name))
    refuseCurrentCommand("the name '" + name +
                         "' conflicts with a name retained by the term manager");
  Function f;
  f.name = name;
  f.named = named;

  ASTNodeMap fromTo;
  for (size_t i = 0, size = params.size(); i < size; ++i)
  {
    ASTNode p = bm.CreateFreshInternalSourceVariable(
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

void Cpp_interface::addFunction(const Function& function)
{
  const auto inserted = functions.emplace(function.name, function);
  if (inserted.second)
    getCurrentFunctions().push_back(function.name);
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
  {
    frames.back()->addUFDeclaration(result);
    // The frame owns the declaration before validation, so a refusal also
    // deactivates it when the failed parse tears the frame down.
    checkSymbolDeclaration(name, result->identityNode());
  }
  return result;
}

const UFDecl*
Cpp_interface::lookupUninterpretedFunction(const std::string& name) const
{
  const UFContext* context = bm.getUFContextIfAny();
  if (context == NULL)
    return NULL;
  if (const UFDecl* declaration = context->lookup(name))
    return declaration;
  const auto alias = uninterpreted_function_aliases.find(name);
  return alias != uninterpreted_function_aliases.end() &&
                 context->isActive(alias->second)
             ? alias->second
             : NULL;
}

void Cpp_interface::addUninterpretedFunctionAlias(
    const std::string& name, const UFDecl* declaration)
{
  assert(bm.getUFContextIfAny() != NULL &&
         bm.getUFContextIfAny()->isActive(declaration));
  uninterpreted_function_aliases.emplace(name, declaration);
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

void Cpp_interface::deleteNode(ASTNode*& n)
{
  delete n;
  n = nullptr;
}

void Cpp_interface::checkSymbolDeclaration(const std::string& name,
                                            const ASTNode& symbol)
{
  if (accept_symbol_declaration && !accept_symbol_declaration(name, symbol))
    refuseCurrentCommand("the symbol name '" + name +
                         "' conflicts with a declaration retained by the term manager");
}

void Cpp_interface::addSymbol(ASTNode& s)
{
  if (current_command_rejected)
    return;
  checkSymbolDeclaration(s.GetName(), s);
  // A public declaration changes the context whose combined model is being
  // described, even when the new symbol belongs to a disjoint theory.
  bm.InvalidateRealModel();
  frames.back()->addSymbol(s);
  session_touched = true;
}

void Cpp_interface::addSymbolAlias(const std::string& name, const ASTNode& s)
{
  frames.back()->addSymbolAs(name, s);
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
// query -- check-sat here, or an API check over a parsed script -- sees it.
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

void Cpp_interface::beginOutputRouting() { output_channels->begin(); }
void Cpp_interface::endOutputRouting() { output_channels->end(); }

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

void Cpp_interface::echo(const std::string& value)
{
  cout << quoteSMTLibString(value) << endl;
}

void Cpp_interface::error(std::string msg)
{
  last_error_message = msg;
  cout << "(error " << quoteSMTLibString(msg) << ")" << endl;
  flush(cout);
}

void Cpp_interface::unsupported()
{
  current_command_supported = false;
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
  SMT2ExpectCommand();
  current_command_active = true;
  current_command_rejected = false;
  current_command_supported = true;
  current_command_name.clear();
  sort_parameters.clear();
  current_assertion_name.reset();
  if (UFContext* context = bm.getUFContextIfAny())
    context->beginParserCommand();
}

void Cpp_interface::requireCommand(const std::string& command)
{
  current_command_name = command;
  if (!protocol_checks)
    return;
  bool allowed = true;
  if (command == "set-logic")
    allowed = mode == Mode::Start;
  else if (command == "get-model" || command == "get-value" ||
           command == "get-assignment")
    allowed = mode == Mode::Sat;
  else if (command == "get-proof" || command == "get-unsat-core" ||
           command == "get-unsat-assumptions")
    allowed = mode == Mode::Unsat;
  else if (mode == Mode::Start &&
           (command == "assert" || command == "check-sat" ||
            command == "check-sat-assuming" ||
            command.compare(0, 8, "declare-") == 0 ||
            command.compare(0, 7, "define-") == 0))
  {
    // Like cvc5 and Bitwuzla, accept scripts that omit set-logic. Select
    // the supported theories before the lexer reads this command's terms.
    // Metadata and stack operations alone do not choose a logic.
    setLogic("ALL");
    SMT2SetFloatTokens(true);
    SMT2SetRealTokens(true);
    SMT2SetBitVectorTokens(true);
  }
  if (!allowed)
    refuseCurrentCommand(command + " is not permitted in the current solver mode");
}

void Cpp_interface::unavailableQuery(const std::string& command,
                                     const std::string& option)
{
  refuseCurrentCommand(command + " requires :" + option + " true");
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
  // stdout, and the parse ends here as a whole. Inside a command that means
  // unwinding to SMT2Parse(), which answers failure -- the command line
  // exits with the diagnostic, a library caller gets a parse error with its
  // assertion stack put back. Outside one there is no parse to abandon, and
  // FatalError takes it as before.
  endParseWithDiagnostic(diagnostic);
}

void Cpp_interface::endParseWithDiagnostic(const std::string& diagnostic)
{
  if (!current_command_active)
    FatalError(diagnostic.c_str());
  // The other channels ("Fatal Error:" on stderr and the observer) keep
  // their report; under the 3.x API the diagnostic is also the parse error's
  // own text.
  ReportFatalError(diagnostic.c_str());
  throw ParseAbandon();
}

void Cpp_interface::finishCurrentCommand()
{
  const std::string& command = current_command_name;
  if (!current_command_rejected && current_command_supported &&
      (command == "assert" || command == "reset-assertions" ||
       command.compare(0, 8, "declare-") == 0))
  {
    if (mode != Mode::Start)
      mode = Mode::Assert;
    model_valid = false;
    lastCheckWasAssuming = false;
  }
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
  {
    GlobalSTP->resetIncrementalSolver();
    GlobalSTP->discardRealSession();
  }
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
  const EngineWork work(engine_work_failed);
  // reset destroys the current frame and UF context itself, so close its
  // accepted command transaction while both are still alive. The grammar's
  // outer finish becomes a harmless no-op after init().
  if (current_command_active)
    finishCurrentCommand();

  popToFirstLevel();

  if (frames.size() > 0)
    removeFrame();

  assert(frames.size() == 0);

  // These tables might hold references to symbols that have been
  // removed.
  resetSolver();
  discardExtensionalitySolveState();
  resetIncrementalSolver();
  // The new session's first solve is the new driver's first.
  if (GlobalSTP != NULL)
    GlobalSTP->incrementalSolvesRun = 0;

  // A reason-unknown belongs to the session that produced it.
  bm.clearUnknown();

  cleanUp();

  // reset is stronger than reset-assertions: old declarations and both LRA
  // identity registries cease to be current before the new base frame is
  // created.  Any retained low-level AST handle remains safely owned by the
  // manager but cannot leak an old model or registry identity into this
  // fresh public context.
  bm.ResetLraStateForPublicReset();
  if (after_public_reset)
    after_public_reset();

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
  const EngineWork work(engine_work_failed);
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
  else
    assertion_names.front().clear();
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
  const EngineWork work(engine_work_failed);
  if (frames.size() == 0)
    FatalError("Popping from an empty stack.");
  if (frames.size() == 1)
  {
    // a (pop) with nothing pushed: the script's error, not the process's end
    const std::string msg = "Can't pop away the default base element.";
    rejectCurrentCommand(msg);
    endParseWithDiagnostic(msg);
  }

  if (mode != Mode::Start)
    mode = Mode::Assert;
  model_valid = false;
  lastCheckWasAssuming = false;

  bm.Pop();

  // These tables might hold references to symbols that have been
  // removed.
  resetSolver();
  discardExtensionalitySolveState();

  cache.erase(cache.end() - 1);

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
  const EngineWork work(engine_work_failed);
  pushed_in_session = true;
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

  if (mode != Mode::Start)
    mode = Mode::Assert;
  model_valid = false;
  lastCheckWasAssuming = false;
  session_touched = true;

  bm.Push();

  addFrame();
  checkInvariant();
}

void Cpp_interface::adoptAssertLevels()
{
  while (frames.size() < bm.getAssertLevel())
  {
    cache.push_back(Entry(SOLVER_UNDECIDED));
    addFrame();
  }
  checkInvariant();
}

void Cpp_interface::retainUFDeclarations(bool retain)
{
  retain_uf_declarations = retain;
}

void Cpp_interface::popAssumptionFrame()
{
  // The assumption frame cannot contain declarations -- nothing runs
  // between the internal push and this pop -- so unlike pop() there is no
  // danger of derived tables referencing removed symbols, and the tables
  // are kept so the model remains readable. The next real solve clears
  // them first (checkSat calls resetSolver before solving).
  bm.PopPreservingRealModel();
  cache.erase(cache.end() - 1);
  removeFrame();
  checkInvariant();
}

void Cpp_interface::checkSatAssuming(const ASTVec& assumptions)
{
  const EngineWork work(engine_work_failed);
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
  // The frame is the assumptions' own, and comes off however the check ends:
  // a run that ends at the check's first CNF (ScriptEnded) used to leave the
  // assumptions asserted on a level of their own.
  struct PopOnUnwind
  {
    Cpp_interface* self;
    bool armed;
    ~PopOnUnwind()
    {
      if (!armed)
        return;
      try
      {
        self->popAssumptionFrame();
      }
      catch (...)
      {
      }
    }
  } pop_on_unwind{this, true};

  for (const ASTNode& a : assumptions)
    AddAssert(a);

  // The assumptions ride as the last level, assumed one conjunct each so
  // an unsat answer can name exactly the assumptions it used.
  checkSat(getAssertVector(), true);
  pop_on_unwind.armed = false;

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
  const EngineWork work(engine_work_failed);
  if (ignoreCheckSatRequest)
    return;
  // Before anything is solved, and before any of this check's state is
  // cleared: a setting the engine cannot honour is this command's to refuse,
  // not something for the engine to discover and report as its own failure.
  if (validate_check_options)
  {
    std::string diagnostic;
    validate_check_options(diagnostic);
    if (!diagnostic.empty())
      refuseCurrentCommand(diagnostic);
  }
  last_core_available = false;
  last_assumption_core_available = false;
  last_unsat_core.clear();
  last_core_assumption_indices.clear();
  if (before_check && before_check())
  {
    mode = Mode::Sat;
    // An interrupt pending as the check begins answers it at once, as the
    // API answers its own checks: unknown, nothing solved, no model. (An
    // interrupted search reports its budget gone, as this does.)
    model_valid = false;
    session_touched = true;
    lastCheckWasAssuming = false;
    bm.clearUnknown();
    bm.noteUnknown(UnknownReason::Timeout, "the check was interrupted before it began");
    ToSATBase::PrintOutput(&bm, bm.unknownResult());
    return;
  }

  // Upstream post-solve accounting can allocate after the coordinator has
  // installed an exact model.  A public check that unwinds at any later
  // boundary did not complete, so it must not leave that model readable.
  struct ExactModelFailureGuard final
  {
    STPMgr& manager;
    bool& public_model_valid;
    bool armed = true;

    ~ExactModelFailureGuard() noexcept
    {
      if (!armed)
        return;
      manager.InvalidateRealModel();
      public_model_valid = false;
    }

    void release() noexcept { armed = false; }
  } exact_model_failure_guard{bm, model_valid};

  bm.InvalidateRealModel();
  bool active_real = lra_logic || !bm.AllRealSymbols().empty();
  for (const ASTNode& assertion : assertionsSMT2)
    active_real = active_real || lra::Frontend::containsRealSyntax(assertion);
  // A new public check invalidates the previous exact model until this call
  // reaches a fresh all-checkers-consistent candidate.

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

  ASTVec coreTerms;
  std::vector<std::string> coreNames;
  ASTVec coreLevels;
  std::vector<size_t> coreIndices;
  // Snapshot every assumption answer, including batch/cached answers, rather
  // than interpreting a previous driver's occurrence IDs against a new query.
  if (fromCheckSatAssuming && !produce_unsat_cores)
    for (size_t i = 0; i < bm.AssertLevels().back()->size(); ++i)
      coreIndices.push_back(i);
  if (produce_unsat_cores)
  {
    ASTVec background;
    const auto& levels = bm.AssertLevels();
    const size_t assertionLevels = levels.size() - (fromCheckSatAssuming ? 1 : 0);
    for (size_t level = 0; level < assertionLevels; ++level)
      for (size_t i = 0; i < levels[level]->size(); ++i)
      {
        const ASTNode& assertion = (*levels[level])[i];
        const auto name = assertion_names[level].find(i);
        if (name == assertion_names[level].end())
          background.push_back(assertion);
        else
        {
          coreTerms.push_back(assertion);
          coreNames.push_back(name->second);
        }
      }
    if (fromCheckSatAssuming)
      coreTerms.insert(coreTerms.end(), levels.back()->begin(), levels.back()->end());

    // The permanent base is empty: even unnamed assertions can be popped.
    // Keep their conjunction in a retractable background level, and track
    // named assertions and user assumptions together at the final level.
    // Do not simplify that conjunction: p AND (NOT p) must retain both
    // source assertions for the driver's failed-assumption projection.
    coreLevels = {bm.ASTTrue,
                  background.empty() ? bm.ASTTrue
                    : background.size() == 1 ? background.front()
                    : nf->CreateNode(AND, background),
                  coreTerms.empty() ? bm.ASTTrue
                    : coreTerms.size() == 1 ? coreTerms.front()
                    : bm.hashingNodeFactory->CreateNode(AND, coreTerms)};
    // Batch and untracked whole-stack encodings have no finer provenance. The same
    // fallback as get-unsat-assumptions keeps their full input core valid.
    for (size_t i = 0; i < coreTerms.size(); ++i)
      coreIndices.push_back(i);
  }

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
  if (produce_unsat_cores || active_real ||
       (!((last_run.result == SOLVER_SATISFIABLE) || last_run.result == SOLVER_UNSATISFIABLE)) ||
        (last_run.result == SOLVER_SATISFIABLE && bm.UserFlags.construct_counterexample_flag)
     )
  {
    resetSolver();
    // Ordinary checks may have made named assertions permanent base units.
    // Changing layouts must retire that encoding before extracting a core.
    // A new seed also needs a fresh backend: existing persistent solvers
    // keep their original random state. Defer this until solving so that
    // set-option alone preserves the previous model and core.
    if (core_solver_layout != produce_unsat_cores ||
        solver_random_seed != bm.UserFlags.random_seed)
    {
      resetIncrementalSolver();
      core_solver_layout = produce_unsat_cores;
      solver_random_seed = bm.UserFlags.random_seed;
    }

    // The policy itself lives on the driver, so this frontend and the API
    // cannot drift apart again; --incremental=on overrides it, and
    // --incremental=off has already kept session_incremental false.
    //
    // The count is the session's, on GlobalSTP, not this interface's: the
    // API makes a new interface for every parse, and its own checks solve on
    // the same driver, so a count of this interface's solves would claim a
    // forced first solve of a driver the API had already solved on.
    size_t& solves_run = GlobalSTP->incrementalSolvesRun;
    const bool autoEngaged = IncrementalSolver::automaticEngagementReady(
        bm.UserFlags.incremental_auto_engage_at, delayed_bv_auto_engagement,
        solves_run);
    const bool use_incremental =
        !active_real &&
        ((produce_unsat_cores && bm.UserFlags.incremental_mode !=
                                    UserDefinedFlags::IncrementalMode::OFF) ||
         (session_incremental && (incremental_from_start || autoEngaged))) &&
        GlobalSTP->getIncrementalSolver()->canHandle(assertionsSMT2);
    // The `use_incremental &&` this used to carry was dead: the value is read
    // only inside the `if (use_incremental)` branch below.
    const bool firstForcedIncrementalSolve =
        IncrementalSolver::forcedFirstSolve(incremental_from_start, solves_run);
    solves_run++;

    SOLVER_RETURN_TYPE last_result = SOLVER_ERROR;
    if (use_incremental)
    {
      // The incremental driver keeps its SAT solver and encoding across
      // check-sats; resetSolver() above cleared only batch-pipeline tables.
      IncrementalSolver* inc = GlobalSTP->getIncrementalSolver();
      last_result = inc->checkSat(produce_unsat_cores ? coreLevels : assertionsSMT2,
                                  produce_unsat_cores || fromCheckSatAssuming,
                                  !produce_unsat_cores && firstForcedIncrementalSolve,
                                  produce_unsat_cores ? &coreTerms
                                    : fromCheckSatAssuming ? bm.AssertLevels().back()
                                                          : nullptr);
      if (bm.UserFlags.quick_statistics_flag)
        inc->reportBVAbstractionRecords(std::cerr);

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
        if (produce_unsat_cores || fromCheckSatAssuming)
          coreIndices = inc->lastUnsatAssumptionIndices();
        if (!produce_unsat_cores)
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
    }
    else
    {
      bool sessionHandled = false;
      if ((bm.UserFlags.lra_incremental_session || bm.UserFlags.lra_persistent_state) &&
          active_real &&
          !fromCheckSatAssuming && session_incremental &&
          bm.UserFlags.incremental_mode !=
              UserDefinedFlags::IncrementalMode::OFF &&
          GlobalSTP->realSessionCanHandle(assertionsSMT2))
        last_result =
            GlobalSTP->checkSatRealSession(bm.AssertLevels(), sessionHandled);
      if (!sessionHandled)
      {
        if (active_real)
          GlobalSTP->discardRealSession();
        ASTNode query;
        if (assertionsSMT2.size() > 1)
          query = nf->CreateNode(AND, assertionsSMT2);
        else if (assertionsSMT2.size() == 1)
          query = assertionsSMT2[0];
        else
          query = bm.ASTTrue;
        last_result = GlobalSTP->TopLevelSTP(query, bm.ASTFalse);
      }
    }

    // The run ended at this check's first CNF: so does the script, with no
    // answer and nothing else said (see ScriptEnded). The Parsing bracket is
    // put back as the end of this function puts it back.
    if (bm.run_ended_after_cnf)
    {
      bm.GetRunTimes()->start(RunTimes::Parsing);
      throw ScriptEnded();
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

  if ((produce_unsat_cores || fromCheckSatAssuming) &&
      last_run.result == SOLVER_UNSATISFIABLE)
  {
    // Both SMT-LIB queries must project the SAME core: the returned names
    // plus unnamed assertions plus returned assumptions must still be unsat.
    for (size_t i : coreIndices)
      if (i < coreNames.size())
        last_unsat_core.push_back(coreNames[i]);
      else
        last_core_assumption_indices.push_back(i - coreNames.size());
    last_core_available = produce_unsat_cores;
    last_assumption_core_available = true;
  }

  // A model exists exactly when this check concluded SAT and the solve
  // constructed a counterexample. On the shortcut paths (verdict reused,
  // no model wanted) nothing was constructed, so nothing may be read.
  model_valid = (last_run.result == SOLVER_SATISFIABLE) &&
                (bm.UserFlags.construct_counterexample_flag || active_real);

  recordCheckWork(work_before);

  if (bm.UserFlags.quick_statistics_flag)
  {
    bm.GetRunTimes()->print();
    // What reached the bit-blaster, what abstraction accepted, and what the
    // refinement spent. Shared with the early-CNF path so population
    // screening need not solve every query merely to read these counters.
    printAbstractionCoverage(bm.UserFlags, std::cerr);
  }

  if (after_check)
    after_check();
  mode = last_run.result == SOLVER_UNSATISFIABLE ? Mode::Unsat : Mode::Sat;
  ToSATBase::PrintOutput(&bm, last_run.result);

  // User has specified -p option to print model.
   if (bm.UserFlags.print_counterexample_flag && model_valid)
   {
      getModel();
   }


  bm.GetRunTimes()->start(RunTimes::Parsing);
  exact_model_failure_guard.release();
}

// This method sets up some of the globally required data.
//
// NB it does not create the STP that GlobalSTP points at. Every writer of
// GlobalSTP borrows: whoever allocates the STP frees it, and the pointer is
// only ever a non-owning view. Callers that need one (because they reach
// something which dereferences GlobalSTP, such as BBAsProp) construct the STP
// themselves and assign it before that point.
Cpp_interface::Cpp_interface(STPMgr& bm_)
    : bm(bm_), initial_produce_models(bm_.UserFlags.callerRequestedModel()),
      model_option_before_parse(bm_.UserFlags.produce_models),
      initial_random_seed(bm_.UserFlags.random_seed),
      output_channels(new SMT2Output), set_global_parser_bm(true),
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

  cache.clear();

  if (assertion_names_at_cleanup != nullptr)
    *assertion_names_at_cleanup = assertion_names;
  // An API caller resumes with its own options after this frontend is
  // destroyed. Retire a script's core layout or seeded solver before
  // restoring those options. No query in the completed script needs it now.
  if (core_solver_layout || solver_random_seed != initial_random_seed)
  {
    resetIncrementalSolver();
    core_solver_layout = false;
    solver_random_seed = initial_random_seed;
  }
  bm.UserFlags.random_seed = initial_random_seed;

  // Every frame is going away, so don't erase the functions from the
  // map one at a time (files can define millions of functions).
  if (functions_at_cleanup != nullptr)
    *functions_at_cleanup = std::move(functions);
  functions.clear();
  for (SolverFrame* frame : frames)
    frame->getFunctions().clear();

  // The manager outlives this interface and keeps the functions the script
  // declared (retainUFDeclarations): the frames must not deactivate them.
  if (retain_uf_declarations)
    for (SolverFrame* frame : frames)
      frame->releaseUFDeclarations();

  // What the frames declare is what the script left in scope, which a caller
  // may have asked to keep (keepDeclaredSymbolsAtCleanup).
  if (symbols_at_cleanup != nullptr)
    *symbols_at_cleanup = getDeclaredSymbols();
  if (sorts_at_cleanup != nullptr)
    *sorts_at_cleanup = sort_aliases;

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
  rejectCurrentCommand(msg);
  endParseWithDiagnostic(msg);
}

void Cpp_interface::setOption(std::string option, std::string value)
{
  const bool boolean_option = option == "print-success" ||
      option == "global-declarations" || option == "interactive-mode" ||
      option == "produce-assertions" || option == "produce-assignments" ||
      option == "produce-models" || option == "produce-proofs" ||
      option == "produce-unsat-assumptions" || option == "produce-unsat-cores";
  if (boolean_option && value != "true" && value != "false")
    badBooleanOptionValue(option, value);
  // Accept production options on either side of set-logic, as cvc5 and
  // Bitwuzla do. Restrictions needed by an option's implementation belong
  // in its handler (for example, global-declarations below).
  /*
      :diagnostic-output-channel
      :global-declarations
      :interactive-mode
      :produce-assertions
      :produce-assignments
      :produce-proofs
      :produce-unsat-assumptions
      :produce-unsat-cores
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
  else if (option == "random-seed")
  {
    uint64_t seed = 0;
    const auto parsed = std::from_chars(value.data(), value.data() + value.size(), seed);
    if (parsed.ec != std::errc() || parsed.ptr != value.data() + value.size())
      refuseCurrentCommand("set-option :random-seed requires a numeral in the range "
                           "0 to 18446744073709551615");
    bm.UserFlags.random_seed = seed;
    success();
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
      bm.UserFlags.produce_models = produce_assignments;
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
      rejectCurrentCommand(msg);
      endParseWithDiagnostic(msg);
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
  else if (option == "produce-assignments")
  {
    produce_assignments = value == "true";
    bm.UserFlags.produce_models = produce_models || produce_assignments;
    success();
  }
  else if (option == "produce-unsat-assumptions")
  {
    produce_unsat_assumptions = value == "true";
    success();
  }
  else if (option == "produce-unsat-cores")
  {
    produce_unsat_cores = value == "true";
    success();
  }
  else if (option == "produce-assertions" || option == "interactive-mode")
  {
    produce_assertions = value == "true";
    success();
  }
  else if (option == "diagnostic-output-channel" ||
           option == "regular-output-channel")
  {
    if (!output_channels->set(option == "diagnostic-output-channel", value))
      refuseCurrentCommand("cannot open output channel: " + value);
    success();
  }
  else if (set_registry_option)
  {
    std::string diagnostic;
    if (!set_registry_option(option, value, diagnostic))
      unsupported();
    else if (!diagnostic.empty())
      refuseCurrentCommand("set-option :" + option + ": " + diagnostic);
    else
    {
      // The frontend keeps the driver's session policy as well as the
      // registry's engine flag. A setting before the first check must update
      // both, including a push that preceded set-option.
      if (option == "incremental")
      {
        const auto mode = bm.UserFlags.incremental_mode;
        incremental_from_start = mode == UserDefinedFlags::IncrementalMode::ON;
        session_incremental = incremental_from_start ||
            (mode != UserDefinedFlags::IncrementalMode::OFF && pushed_in_session);
      }
      else if (option == "logic")
        setLogic(value);
      success();
    }
  }
  else
    unsupported();
}

// Unsupported predefined options retain their defaults (2.7 section 4.2.8).
void Cpp_interface::getOption(std::string option)
{
  if (option == "print-success")
    cout << (print_success ? "true" : "false") << endl;
  else if (option == "produce-models")
    cout << (produce_models ? "true" : "false") << endl;
  else if (option == "global-declarations")
    cout << (global_declarations ? "true" : "false") << endl;
  else if (option == "produce-assertions" || option == "interactive-mode")
    cout << (produce_assertions ? "true" : "false") << endl;
  else if (option == "produce-unsat-assumptions")
    cout << (produce_unsat_assumptions ? "true" : "false") << endl;
  else if (option == "produce-assignments")
    cout << (produce_assignments ? "true" : "false") << endl;
  else if (option == "produce-unsat-cores")
    cout << (produce_unsat_cores ? "true" : "false") << endl;
  else if (option == "produce-proofs")
    cout << "false" << endl;
  else if (option == "random-seed")
    cout << bm.UserFlags.random_seed << endl;
  else if (option == "reproducible-resource-limit" || option == "verbosity")
    cout << "0" << endl;
  else if (option == "diagnostic-output-channel" ||
           option == "regular-output-channel")
    cout << quoteSMTLibString(output_channels->name(
                option == "diagnostic-output-channel")) << endl;
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
    case RunTimes::CommonFactor: return "common-factor-extraction";
    case RunTimes::LinearForm: return "linear-canonical-form";
    case RunTimes::CongruenceCandidates: return "congruence-candidates";
  }
  return "unknown";
}

void Cpp_interface::getInfo(std::string flag)
{
  if (protocol_checks && flag == "reason-unknown" &&
      (mode != Mode::Sat || bm.getUnknownReason() == UnknownReason::None))
    refuseCurrentCommand("get-info :reason-unknown requires a preceding unknown result");
  const EngineWork work(engine_work_failed);
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
    std::ios_base::fmtflags saved(cout.flags());
    const std::streamsize saved_precision = cout.precision();
    cout << std::fixed;
    cout.precision(2);

    cout << "(:check-sat-calls "
         << (GlobalSTP != NULL ? GlobalSTP->incrementalSolvesRun : 0) << endl;
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
    // Protocol checks above restrict this to the most recent unknown result.
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
      case UnknownReason::StoppedAfterCnf:
      case UnknownReason::Incomplete:
        // The predefined SMT-LIB spelling, followed by what was incomplete:
        // the flag admits an s-expression, and a bare "incomplete" tells a
        // caller nothing they can act on. All four share it because the
        // sentence is what says which, and SMT-LIB2 has no spelling that
        // would say it better.
        cout << "(:reason-unknown (incomplete "
             << quoteSMTLibString(bm.getUnknownReasonDetail())
             << "))" << endl;
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
  for (const auto& alias : sort_aliases)
    anyDeclared = anyDeclared ||
                  (alias.second.arity == 0 &&
                   alias.second.body.sourceSort().kind() == SourceSort::Kind::Uninterpreted);
  if (!anyDeclared)
    return false;
  return declaredSortCarrierMayBeShort(bm, assertions, "--uf-sort-width",
                                       detail);
}

// See cpp_interface.h.
bool declaredSortCarrierMayBeShort(const STPMgr& bm, const ASTVec& assertions,
                                   const char* option, std::string& detail)
{
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
            << ", and " << option << "=" << width << " tells only " << capacity
            << " apart; raise " << option << " to at least " << needed;
    detail = message.str();
    return true;
  }
  return false;
}

void Cpp_interface::getAssertions()
{
  // Assertions are always retained. Like cvc5, allow inspection regardless
  // of :produce-assertions rather than reject information already available.
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
  const EngineWork work(engine_work_failed);
  if (current_command_rejected)
    return;
  if (!produce_models)
    unavailableQuery("get-value", "produce-models");
  bool readable_model = bm.UserFlags.construct_counterexample_flag;
  // Exact Real solving constructs and certifies a combined model even when
  // the caller did not request the ordinary counterexample product. The
  // solve restores that request flag after each query, so use the actual
  // published model instead of latching the flag.
  readable_model = readable_model || bm.HasRealModel();
  if (!readable_model || !model_valid)
  {
    refuseCurrentCommand("get-value: no model is available for the current context");
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
    if (n.GetSourceSort().kind() == SourceSort::Kind::Real)
    {
      if (!bm.HasRealModelValue(n))
      {
        unsupported();
        return;
      }
      os << "(";
      printer::SMTLIB2_Print1(os, n, 0, false);
      os << " " << bm.GetRealModelSMTLIB(n) << ")" << std::endl;
      continue;
    }

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
        bm.printUninterpretedElement(os, n.GetSourceSort(), value);
      else
        printer::SMTLIB2_Print1(os, value, 0, false);
      os << " )" << std::endl;
      continue;
    }
    GlobalSTP->Ctr_Example->PrintSMTLIB2(os, n);
    os << std::endl;
  }
  os << ")";

  cout << os.str() << std::endl;
}

void Cpp_interface::getAssignment()
{
  if (!produce_assignments)
    unavailableQuery("get-assignment", "produce-assignments");
  const EngineWork work(engine_work_failed);
  if (!model_valid)
    refuseCurrentCommand("get-assignment: no model is available for the current context");
  if (GlobalSTP->hasIncrementalSolver())
    GlobalSTP->getIncrementalSolver()->materializePendingModel();
  std::map<std::string, ASTNode> labels;
  for (const auto& definition : functions)
    if (definition.second.named &&
        definition.second.function.GetSourceSort().kind() == SourceSort::Kind::Bool)
      labels.emplace(definition.first, definition.second.function);
  std::ostringstream response;
  response << "(";
  bool first = true;
  for (const auto& label : labels)
  {
    if (!first) response << " ";
    first = false;
    const ASTNode value = GlobalSTP->Ctr_Example->ModelValueOfFormula(label.second);
    response << "(|" << label.first << "| "
             << (value == bm.ASTTrue ? "true" : "false") << ")";
  }
  response << ")";
  cout << response.str() << endl;
}

void Cpp_interface::getUnsatCore()
{
  if (!produce_unsat_cores)
    unavailableQuery("get-unsat-core", "produce-unsat-cores");
  if (mode != Mode::Unsat || !last_core_available)
    refuseCurrentCommand("get-unsat-core requires an unsat check with :produce-unsat-cores true");
  std::ostringstream response;
  response << "(";
  for (size_t i = 0; i < last_unsat_core.size(); ++i)
  {
    if (i != 0) response << " ";
    response << "|" << last_unsat_core[i] << "|";
  }
  response << ")";
  cout << response.str() << endl;
}

void Cpp_interface::getUnsatAssumptions()
{
  if (!produce_unsat_assumptions)
    unavailableQuery("get-unsat-assumptions", "produce-unsat-assumptions");
  const EngineWork work(engine_work_failed);
  // Meaningful right after a check-sat-assuming that answered unsat;
  // anything else gets the empty list, which is the correct core whenever
  // the command is legal at all.
  if (!lastCheckWasAssuming || lastAssumingResult != SOLVER_UNSATISFIABLE)
  {
    cout << "()" << endl;
    return;
  }

  // Per-assumption granularity from the driver when it ran the solve
  // (IncrementalSolver::lastUnsatAssumptionIndices); the full assumption set
  // is always a correct core, and covers the batch first solve and the
  // untracked whole-stack rounds.
  std::vector<size_t> used = last_core_assumption_indices;
  if (!last_assumption_core_available)
    for (size_t i = 0; i < lastAssumptionTerms.size(); ++i)
      used.push_back(i);

  std::ostringstream os;
  os << "(";
  bool first = true;
  for (size_t i : used)
  {
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
  const EngineWork work(engine_work_failed);
  if (!produce_models)
    unavailableQuery("get-model", "produce-models");
  bool readable_model = bm.UserFlags.construct_counterexample_flag;
  readable_model = readable_model || bm.HasRealModel();
  if (!readable_model || !model_valid)
  {
    refuseCurrentCommand("get-model: no model is available for the current context");
  }

  // The driver defers counterexample construction to the first reader.
  // hasIncrementalSolver, not getIncrementalSolver: the latter constructs one
  // on demand, so asking it whether a driver exists built a driver -- and a
  // SAT backend with it -- in every batch session that printed a model.
  if (GlobalSTP != NULL && GlobalSTP->hasIncrementalSolver())
    GlobalSTP->getIncrementalSolver()->materializePendingModel();

  // Current frames keep their declaration vectors private. Resolve every
  // manager-known name through the frame lookup instead: only the innermost
  // live binding compares equal, while popped and shadowed nodes, and the
  // solver's own symbols, which were never declared, remain excluded.
  const auto in_scope = [this](const ASTNode& symbol) {
    if (symbol.GetKind() != SYMBOL)
      return true; // nothing to look up, and GetName would be fatal
    ASTNode visible;
    return LookupSymbol(symbol.GetName(), visible) && visible == symbol;
  };

  std::ostringstream os;
  GlobalSTP->Ctr_Example->PrintFullCounterExampleSMTLIB2(os, in_scope);
  if (bm.HasRealModel())
  {
    ASTVec visible_real_symbols;
    // The same rule; the RealModel applies its own deterministic ordering.
    for (const ASTNode& symbol : bm.AllRealSymbols())
      if (in_scope(symbol))
        visible_real_symbols.push_back(symbol);
    bm.PrintRealModelSMTLIB2(os, visible_real_symbols);
  }

  cout << "(" << std::endl;

  // SMT-LIB models contain only definitions. Abstract values carry their
  // sorts locally, and user-declared sorts are already in the signature.
  cout << os.str();
  cout << ")" << std::endl;
}

ASTNode Cpp_interface::abstractValue(const std::string& name,
                                     const SourceSort& sort)
{
  if (current_command_name != "get-value" || !model_valid)
    refuseCurrentCommand("abstract values may only occur in get-value for the current model");
  for (const auto& value : bm.uninterpretedElements())
    if (value.name == name && value.sort == sort)
      return bm.CreateUninterpretedConst(value.carrier, sort);
  refuseCurrentCommand("unknown abstract value for the current model: " + name);
  return ASTNode();
}

Cpp_interface::SolverFrame::SolverFrame(
    FunctionMap*
        global_function_context,
    SortMap* global_sort_alias_context,
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

void Cpp_interface::SolverFrame::releaseUFDeclarations()
{
  _scoped_uf_declarations.clear();
}

void Cpp_interface::SolverFrame::addSymbol(const ASTNode& symbol)
{
  _scoped_symbols.push_back(symbol);
  _symbol_bindings[std::string(symbol.GetName())].push_back(symbol);
}

void Cpp_interface::SolverFrame::addSymbolAs(const std::string& name, const ASTNode& symbol)
{
  _symbol_bindings[name].push_back(symbol);
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

ASTVec Cpp_interface::getDeclaredSymbols() const
{
  ASTVec out;
  for (const SolverFrame* frame : frames)
    out.insert(out.end(), frame->getSymbols().begin(), frame->getSymbols().end());
  return out;
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
