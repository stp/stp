/********************************************************************
 * AUTHORS: Vijay Ganesh, Andrew Teylu
 *
 * BEGIN DATE: November, 2005
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
#include "stp/c_interface.h"

#include <cassert>
#include <cinttypes>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <mutex>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "stp/FloatBlaster/FloatBlaster.h"
#include "stp/FloatBlaster/FpTotalise.h"
#include "stp/Incremental/IncrementalSolver.h"
#include "stp/Interface/FdOStream.h"
#include "stp/Parser/parser.h"
#include "stp/Printer/printers.h"
#include "stp/Simplifier/DistinctOrdering.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/UninterpretedFunctions/UFModel.h"
#include "stp/UninterpretedFunctions/UFRefinement.h"
#include "stp/Util/GitSHA1.h"
#include "stp/cpp_interface.h"

// From ABC
#include "sat/cnf/cnf.h"

#include "stp/ToSat/ToSATAIG.h"

using std::cout;
using std::ostream;
using std::stringstream;
using std::string;
using std::endl;

// Defined further down, but used by the boolean expression builders above it.
Expr createBinaryNode(VC vc, Kind k, Expr left, Expr right);

namespace /* anonymous namespace for static */
{

// The legacy VC and Expr types remain raw pointers. UF declarations are new
// API, however, so give them monotonic integer identities instead of allocator
// addresses. A context owns the live id -> declaration mapping; destroying the
// context drops the mapping, and no later declaration can reuse the id.
struct CContextRecord
{
  uint64_t generation = 0;
  stp::STPMgr* manager = NULL;
  bool tracksExpressions = false;
  std::unordered_set<Expr> expressions;
  std::unordered_map<UFDeclHandle, const stp::UFDecl*> declarations;
};

struct CExpressionRecord
{
  uint64_t contextGeneration = 0;
  VC owner = NULL;
};

std::mutex cHandleMutex;
uint64_t nextCContextGeneration = 0;
uint64_t nextCUFDeclarationId = 0;
std::unordered_map<VC, CContextRecord> liveCContexts;
std::unordered_map<stp::STPMgr*, VC> contextByManager;
std::unordered_map<Expr, CExpressionRecord> cExpressions;

void registerCContext(VC vc, stp::STPMgr* manager)
{
  assert(vc != NULL && manager != NULL);
  std::lock_guard<std::mutex> lock(cHandleMutex);
  CContextRecord record;
  record.generation = ++nextCContextGeneration;
  record.manager = manager;
  liveCContexts[vc] = record;
  contextByManager[manager] = vc;
}

bool liveCContext(VC vc, CContextRecord& record)
{
  std::lock_guard<std::mutex> lock(cHandleMutex);
  const std::unordered_map<VC, CContextRecord>::const_iterator found =
      liveCContexts.find(vc);
  if (found == liveCContexts.end())
    return false;
  // Callers need identity/ownership metadata, not a copy of the potentially
  // large per-context retirement indexes.
  record.generation = found->second.generation;
  record.manager = found->second.manager;
  return true;
}

void enableCExpressionTracking(VC vc)
{
  std::lock_guard<std::mutex> lock(cHandleMutex);
  const std::unordered_map<VC, CContextRecord>::iterator context =
      liveCContexts.find(vc);
  if (context == liveCContexts.end() || context->second.tracksExpressions)
    return;
  context->second.tracksExpressions = true;

  // The public contract requires enabling UF before declaring a function and
  // before constructing its argument handles. Recover the context-managed
  // handles which predate the flag as a convenience; caller-owned wrappers
  // created before the flag deliberately remain outside the safe UF registry.
  for (stp::ASTNode* expression : context->second.manager->persist)
  {
    if (expression == NULL || expression->IsNull())
      continue;
    CExpressionRecord record;
    record.contextGeneration = context->second.generation;
    record.owner = vc;
    cExpressions[expression] = record;
    context->second.expressions.insert(expression);
  }
}

void retireCContext(VC vc)
{
  std::vector<stp::ASTNode*> toDelete;
  {
    std::lock_guard<std::mutex> lock(cHandleMutex);
    const std::unordered_map<VC, CContextRecord>::iterator context =
        liveCContexts.find(vc);
    if (context == liveCContexts.end())
      return;
    contextByManager.erase(context->second.manager);
    if (context->second.tracksExpressions)
    {
      toDelete.reserve(context->second.expressions.size());
      for (const Expr expression : context->second.expressions)
      {
        cExpressions.erase(expression);
        toDelete.push_back(static_cast<stp::ASTNode*>(expression));
      }
    }
    liveCContexts.erase(context);
  }
  // AST references must be released while their owning manager is alive.
  for (stp::ASTNode* expression : toDelete)
    delete expression;
}

Expr registerCExpression(stp::ASTNode* node)
{
  if (node == NULL || node->IsNull())
    return node;
  // UF-disabled C clients pay no registry or lock cost. This is the common
  // legacy path and is also what keeps expression churn bounded and fast.
  if (!node->GetNodeManager()->UserFlags.enable_uninterpreted_functions)
    return node;
  std::lock_guard<std::mutex> lock(cHandleMutex);
  const std::unordered_map<stp::STPMgr*, VC>::const_iterator owner =
      contextByManager.find(node->GetNodeManager());
  if (owner != contextByManager.end())
  {
    const std::unordered_map<VC, CContextRecord>::iterator context =
        liveCContexts.find(owner->second);
    if (context != liveCContexts.end())
    {
      if (!context->second.tracksExpressions)
        return node;
      CExpressionRecord record;
      record.contextGeneration = context->second.generation;
      record.owner = owner->second;
      cExpressions[node] = record;
      context->second.expressions.insert(node);
    }
  }
  return node;
}

bool liveCExpression(VC vc, Expr expression, stp::ASTNode*& node,
                     std::string& diagnostic)
{
  node = NULL;
  if (expression == NULL)
  {
    diagnostic = "null expression handle";
    return false;
  }
  std::lock_guard<std::mutex> lock(cHandleMutex);
  const std::unordered_map<VC, CContextRecord>::const_iterator context =
      liveCContexts.find(vc);
  if (context == liveCContexts.end())
  {
    diagnostic = "invalid or destroyed validity-checker handle";
    return false;
  }
  const std::unordered_map<Expr, CExpressionRecord>::const_iterator found =
      cExpressions.find(expression);
  if (found == cExpressions.end())
  {
    diagnostic = "invalid or destroyed expression handle";
    return false;
  }
  if (found->second.owner != vc ||
      found->second.contextGeneration != context->second.generation)
  {
    diagnostic = "expression belongs to another context";
    return false;
  }
  node = static_cast<stp::ASTNode*>(expression);
  return true;
}

UFDeclHandle registerCUFDecl(VC vc, const stp::UFDecl* declaration)
{
  assert(vc != NULL && declaration != NULL);
  std::lock_guard<std::mutex> lock(cHandleMutex);
  const std::unordered_map<VC, CContextRecord>::iterator context =
      liveCContexts.find(vc);
  if (context == liveCContexts.end())
    return 0;
  const UFDeclHandle handle = ++nextCUFDeclarationId;
  context->second.declarations.insert(std::make_pair(handle, declaration));
  return handle;
}

bool liveCUFDecl(VC vc, UFDeclHandle handle, const stp::UFDecl*& declaration,
                 std::string& diagnostic)
{
  declaration = NULL;
  if (handle == 0)
  {
    diagnostic = "null uninterpreted-function declaration handle";
    return false;
  }
  std::lock_guard<std::mutex> lock(cHandleMutex);
  const std::unordered_map<VC, CContextRecord>::const_iterator context =
      liveCContexts.find(vc);
  if (context == liveCContexts.end())
  {
    diagnostic = "invalid or destroyed validity-checker handle";
    return false;
  }
  const std::unordered_map<UFDeclHandle, const stp::UFDecl*>::const_iterator
      found = context->second.declarations.find(handle);
  if (found == context->second.declarations.end() || found->second == NULL)
  {
    diagnostic = "invalid, stale, destroyed, or cross-context "
                 "uninterpreted-function declaration handle";
    return false;
  }
  declaration = found->second;
  return true;
}

void requireBooleanOperand(const char* operation, const stp::ASTNode& n)
{
  if (n.GetSourceSort().kind() == stp::SourceSort::Kind::Bool)
    return;
  std::string message("CInterface: ");
  message += operation;
  message += " requires Boolean operands: ";
  stp::FatalError(message.c_str(), n);
}

stp::ASTNode createPublicSourceSymbol(stp::STPMgr* bm, const char* name,
                                      const stp::SourceSort& source_sort)
{
  // The same reservation the parser enforces, for the entry point that has no
  // parser in front of it. STP mints '@' names for its own objects and takes
  // their uniqueness on trust, so a caller able to declare one could be handed
  // the solver's own -- see Cpp_interface::CreateSourceSymbol.
  if (stp::STPMgr::isReservedSymbolName(name))
  {
    stp::FatalError("CInterface: a symbol name beginning with '@' or '.' is "
                    "reserved for solver use and cannot be declared");
  }

  const auto found = bm->c_api_source_sorts.find(name);
  if (found != bm->c_api_source_sorts.end() && found->second != source_sort)
  {
    stp::FatalError("CInterface: a symbol cannot be redeclared with a "
                    "different source sort");
  }
  bm->c_api_source_sorts[name] = source_sort;
  return bm->CreateSourceSymbol(name, source_sort);
}

void requireBitVectorOperand(const char* operation, const stp::ASTNode& n)
{
  if (n.GetSourceSort().kind() == stp::SourceSort::Kind::BitVector)
    return;

  std::string message("CInterface: ");
  message += operation;
  message += " requires bitvector operands";
  if (n.GetType() == stp::FLOATINGPOINT_TYPE)
    message += "; use vc_fpToIEEEBV to expose a float's packed bits";
  message += ": ";
  stp::FatalError(message.c_str(), n);
}

void requireSamePublicSort(const char* operation, stp::STPMgr* bm,
                           const stp::ASTNode& left,
                           const stp::ASTNode& right)
{
  (void)bm;
  const stp::SourceSort left_sort = left.GetSourceSort();
  if (left_sort.isKnown() && left_sort == right.GetSourceSort())
    return;

  std::string message("CInterface: ");
  message += operation;
  message += " requires operands of the same sort: ";
  stp::FatalError(message.c_str(), left);
}

// The packed bit width laid under a scalar type node: the declared width of
// a BITVECTOR, the packed width of a FLOATINGPOINT, five for ROUNDINGMODE.
unsigned int scalarTypeNodeWidth(const stp::ASTNode& t)
{
  switch (t.GetKind())
  {
    case stp::BITVECTOR:
      return t[0].GetUnsignedConst();
    case stp::FLOATINGPOINT:
      return t[0].GetUnsignedConst() + t[1].GetUnsignedConst();
    case stp::ROUNDINGMODE:
      return 5;
    default:
      stp::FatalError("CInterface: expected a bitvector, floating-point or "
                      "RoundingMode type node: ",
                      t);
      return 0;
  }
}

/* The two steps almost every entry point below repeats: unwrapping the
 * opaque VC handle to reach the node manager, and handing a node that has
 * just been built back to the caller as an opaque, caller-owned Expr. */
stp::STPMgr* mgr(VC vc)
{
  return ((stp::STP*)vc)->bm;
}

Expr wrap(const stp::ASTNode& n)
{
  return registerCExpression(new stp::ASTNode(n));
}

// Whether the query that just returned this leaves anything to read. VALID
// counts: there is no counterexample to a valid query, but that is the
// decided answer to the question rather than an absence of one, and
// GetCounterExample has its own arm for saying so. An unknown or an error
// decided nothing and cleared the tables on the way in.
static int recordQueryOutcome(stp::STP* stp_i, int outcome)
{
  if (outcome == stp::SOLVER_UNKNOWN)
    outcome = stp_i->bm->unknownResult();
  stp_i->queryAnswered = (outcome == stp::SOLVER_INVALID ||
                          outcome == stp::SOLVER_VALID);
  return outcome;
}

// Nonfatal diagnostic through the handler vc_registerErrorHandler installs,
// falling back to stderr when there is none. Deliberately not both, which is
// what FatalError does: that one is on its way to abort() and has to be seen,
// whereas a caller that registered a handler for this has already said where
// it wants to be told, and the call returns for it to act on.
static void reportCAPIError(const std::string& message)
{
  if (stp::vc_error_hdlr != NULL)
    stp::vc_error_hdlr(message.c_str());
  else
    std::cerr << "CInterface: " << message << std::endl;
}

// The interface passes an int for fields that are unsigned in UserFlags.
// Answering whether this one may be stored, and saying so through the same
// nonfatal path the rest of this interface uses when it may not.
bool nonNegativeFlag(int param_value, const char* flag)
{
  if (param_value >= 0)
    return true;
  reportCAPIError(std::string(flag) + " must not be negative");
  return false;
}

/* this method is purposefully not public! */
std::pair<unsigned int, unsigned int> getTypeSizes(Type type)
{
  unsigned int indexWidth = 0;
  unsigned int valueWidth = 0;

  stp::ASTNode* a = (stp::ASTNode*)type;

  switch (a->GetKind())
  {
    case stp::BITVECTOR:
      indexWidth = 0;
      valueWidth = (*a)[0].GetUnsignedConst();
      break;
    case stp::ARRAY:
      // The children are the index and element type nodes themselves (see
      // vc_arrayType), each BITVECTOR, FLOATINGPOINT or ROUNDINGMODE.
      indexWidth = scalarTypeNodeWidth((*a)[0]);
      valueWidth = scalarTypeNodeWidth((*a)[1]);
      break;
    case stp::BOOLEAN:
      indexWidth = 0;
      valueWidth = 0;
      break;
    case stp::FLOATINGPOINT:
      // A floating-point type node carries its exponent and significand widths
      // as its two children (see vc_fpType). The packed value width is their
      // sum; exp/sig are stamped onto the symbol separately, in vc_varExpr.
      indexWidth = 0;
      valueWidth = (*a)[0].GetUnsignedConst() + (*a)[1].GetUnsignedConst();
      break;
    case stp::ROUNDINGMODE:
      // A rounding mode is carried as a 5-bit bitvector; vc_varExpr
      // additionally pins the symbol to the five legal encodings.
      indexWidth = 0;
      valueWidth = 5;
      break;
    default:
      stp::FatalError("CInterface: vc_varExpr: Unsupported type", *a);
  }
  return std::make_pair(valueWidth, indexWidth);
}
} // namespace

// GLOBAL FUNCTION: parser
extern int cvcparse(void*);
extern int smtparse(void*);

/* wraps get_git_version_sha in stp namespace */
const char* get_git_version_sha(void)
{
  return stp::get_git_version_sha();
}

/* wraps get_git_version_tag in stp namespace */
const char* get_git_version_tag(void)
{
  return stp::get_git_version_tag();
}

/* wraps get_compilation_env in stp namespace */
const char* get_compilation_env(void)
{
  return stp::get_compilation_env();
}

// TODO remove this, it's really ugly
void vc_setFlags(VC vc, char c, int /*param_value*/)
{
  process_argument(c, vc);
}

// TODO remove this, it's really ugly
void vc_setFlag(VC vc, char c)
{
  process_argument(c, vc);
}

// A profile is an atomic mask/round pair, but a ceiling the caller named is
// theirs. Without this the two halves of the pair would resolve differently
// depending on call order: ROUNDS then PROFILE lost the ceiling, PROFILE then
// ROUNDS kept it. The command line cannot reach that -- the two options
// exclude each other there -- so this is the C interface holding to the same
// answer the command line gives.
static void applyProfileRounds(stp::STPMgr* b, unsigned rounds)
{
  if (!b->UserFlags.bv_term_abstraction_rounds_explicit)
    b->UserFlags.bv_term_abstraction_rounds = rounds;
}

// ... and the mask half by the same rule, which it was not. Left
// last-writer-wins, the two halves of one atomic pair resolved by opposite
// rules: a ceiling named before a profile survived it, a group list named
// before a profile did not.
static void applyProfileGroups(stp::STPMgr* b, uint32_t groups)
{
  if (!b->UserFlags.bv_term_abstraction_schema_groups_explicit)
    b->UserFlags.bv_term_abstraction_schema_groups = groups;
}

void vc_setInterfaceFlags(VC vc, enum ifaceflag_t f, int param_value)
{
  stp::STPMgr* b = mgr(vc);
  switch (f)
  {
    case EXPRDELETE:
      b->UserFlags.cinterface_exprdelete_on_flag = param_value != 0;
      break;
    case MS:
      b->UserFlags.solver_to_use = stp::UserDefinedFlags::MINISAT_SOLVER;
      break;
    case SMS:
      b->UserFlags.solver_to_use =
          stp::UserDefinedFlags::SIMPLIFYING_MINISAT_SOLVER;
      break;
    case CMS4:
      b->UserFlags.solver_to_use = stp::UserDefinedFlags::CRYPTOMINISAT5_SOLVER;
      break;
    case MSP:
      //Array-based Minisat has been replaced with normal MiniSat
      b->UserFlags.solver_to_use = stp::UserDefinedFlags::MINISAT_SOLVER;
      break;
    case INCREMENTAL_AUTO_ENGAGE_AT:
      // Same policy object the SMT-LIB2 reader drives with
      // --incremental-auto-engage-at; this is the C API's way to reach it.
      b->UserFlags.incremental_auto_engage_at = param_value;
      break;
    case CADICAL:
      b->UserFlags.solver_to_use = stp::UserDefinedFlags::CADICAL_SOLVER;
      break;
    // The refinement knobs the CLI exposes. Each sets the same UserFlags
    // field the CLI parser writes, so a C API client reaches the encodings
    // that until now only a query read from a file could.
    case UF_NARROW_RESULTS:
      b->UserFlags.uf_narrow_results = param_value != 0;
      break;
    case UF_EQUALITY_INJECTIVITY:
      b->UserFlags.uf_inject_args = param_value != 0;
      break;
    case UF_PHASE_HINTS:
      b->UserFlags.uf_phase_hints = param_value != 0;
      break;
    case DISTINCT_ORDERING:
      b->UserFlags.distinct_ordering = param_value != 0;
      break;
    case BV_EQ_ABSTRACTION:
      b->UserFlags.bv_eq_abstraction = param_value != 0;
      break;
    case BV_TERM_ABSTRACTION:
      b->UserFlags.bv_term_abstraction = param_value != 0;
      break;
    case BV_TERM_ABSTRACTION_MULT:
      b->UserFlags.bv_term_abstraction_mult = param_value != 0;
      // This flag covered MULT, DIV and MOD before the DIVMOD switch existed,
      // and still does unless the caller has named DIV/MOD itself. Order does
      // not matter: an explicit DIVMOD wins whether it came first or second.
      if (!b->UserFlags.bv_term_abstraction_divmod_explicit)
        b->UserFlags.bv_term_abstraction_divmod = param_value != 0;
      break;
    case BV_TERM_ABSTRACTION_DIVMOD:
      b->UserFlags.bv_term_abstraction_divmod = param_value != 0;
      b->UserFlags.bv_term_abstraction_divmod_explicit = true;
      break;
    case BV_TERM_ABSTRACTION_PROFILE:
      if (param_value == STP_BV_TERM_ABSTRACTION_PROFILE_QUALIFIED)
      {
        applyProfileGroups(b, stp::BV_SCHEMA_GROUP_QUALIFIED);
        applyProfileRounds(b, stp::BV_TERM_ABSTRACTION_QUALIFIED_ROUNDS);
      }
      else if (param_value == STP_BV_TERM_ABSTRACTION_PROFILE_AGGRESSIVE)
      {
        applyProfileGroups(b, stp::BV_SCHEMA_GROUP_AGGRESSIVE);
        applyProfileRounds(b, stp::BV_TERM_ABSTRACTION_AGGRESSIVE_ROUNDS);
      }
      else if (param_value == STP_BV_TERM_ABSTRACTION_PROFILE_BROAD)
      {
        applyProfileGroups(b, stp::BV_SCHEMA_GROUP_BROAD);
        applyProfileRounds(b, stp::BV_TERM_ABSTRACTION_BROAD_ROUNDS);
      }
      else
        reportCAPIError("BV_TERM_ABSTRACTION_PROFILE takes a "
                        "bv_term_abstraction_profile_t ordinal");
      break;
    case BV_TERM_ABSTRACTION_SCHEMAS:
      b->UserFlags.bv_term_abstraction_schemas = param_value != 0;
      break;
    case BV_TERM_ABSTRACTION_INC_BITBLAST:
      b->UserFlags.bv_term_abstraction_inc_bitblast = param_value != 0;
      break;
    case INCREMENTAL_PIECE_REWRITING:
      b->UserFlags.incremental_piece_rewriting = param_value != 0;
      break;
    case INCREMENTAL_SCOPED_PREPROCESSING:
      b->UserFlags.incremental_scoped_preprocessing = param_value != 0;
      break;
    case CNF_GENERATION_EFFORT:
      if (param_value < 0 ||
          param_value > stp::UserDefinedFlags::CNF_EFFORT_VERY_HIGH)
        reportCAPIError("CNF_GENERATION_EFFORT takes an effort ordinal from "
                        "0 (very low) to 4 (very high)");
      else
        b->UserFlags.cnf_effort =
            static_cast<stp::UserDefinedFlags::CNFEffort>(param_value);
      break;
    // Every field below is unsigned in UserFlags, so a negative value would
    // wrap to something enormous: for a width, a threshold no term can reach;
    // for a budget, no limit at all. Refuse it and leave the field as it was.
    case BV_ABSTRACTION_WIDTH:
      if (nonNegativeFlag(param_value, "BV_ABSTRACTION_WIDTH"))
        b->UserFlags.bv_abstraction_width =
            static_cast<unsigned>(param_value);
      break;
    case CNF_AUTO_THRESHOLD:
      if (nonNegativeFlag(param_value, "CNF_AUTO_THRESHOLD"))
        b->UserFlags.cnf_auto_threshold = static_cast<unsigned>(param_value);
      break;
    case BV_EQ_REFINE_WIDTH:
      if (nonNegativeFlag(param_value, "BV_EQ_REFINE_WIDTH"))
        b->UserFlags.bv_eq_refine_width = static_cast<unsigned>(param_value);
      break;
    case BV_TERM_ABSTRACTION_ROUNDS:
      if (nonNegativeFlag(param_value, "BV_TERM_ABSTRACTION_ROUNDS"))
      {
        b->UserFlags.bv_term_abstraction_rounds =
            static_cast<unsigned>(param_value);
        b->UserFlags.bv_term_abstraction_rounds_explicit = true;
      }
      break;
    case BV_TERM_ABSTRACTION_VALUE_DIVISOR:
      if (nonNegativeFlag(param_value, "BV_TERM_ABSTRACTION_VALUE_DIVISOR"))
        b->UserFlags.bv_term_abstraction_value_divisor =
            static_cast<unsigned>(param_value);
      break;
    case BV_TERM_ABSTRACTION_DIVMOD_VALUE_LIMIT:
      if (nonNegativeFlag(param_value,
                          "BV_TERM_ABSTRACTION_DIVMOD_VALUE_LIMIT"))
        b->UserFlags.bv_term_abstraction_divmod_value_limit =
            static_cast<unsigned>(param_value);
      break;
    case UF_LEMMAS_PER_ROUND:
      if (nonNegativeFlag(param_value, "UF_LEMMAS_PER_ROUND"))
        b->UserFlags.uf_lemmas_per_round = static_cast<unsigned>(param_value);
      break;
    case UF_ACKERMANN_BUDGET:
      if (nonNegativeFlag(param_value, "UF_ACKERMANN_BUDGET"))
        b->UserFlags.uf_eager_budget = static_cast<unsigned>(param_value);
      break;
    // Signed in UserFlags, and -1 is a value of its own there: no limit,
    // which is the default. 0 is a budget of no gates at all. So only a
    // value below -1 names nothing, and that is what is refused.
    case AIG_NODE_BUDGET:
      if (param_value < -1)
      {
        reportCAPIError("AIG_NODE_BUDGET must be -1 (no limit) or a count");
        break;
      }
      b->UserFlags.aig_node_budget = static_cast<int64_t>(param_value);
      break;
    // Bounded at both ends rather than merely at zero, because both ends were
    // reachable and neither failed cleanly: a zero-width element is read as a
    // Boolean by the legacy width checks, and a width past the ceiling
    // overflows the word arithmetic underneath and answers unsat for two
    // elements of an unbounded sort. The CLI refuses the same range.
    case UF_SORT_WIDTH:
      if (param_value < 1 || param_value > 1024)
      {
        reportCAPIError("UF_SORT_WIDTH must be between 1 and 1024");
        break;
      }
      b->UserFlags.uf_sort_width = static_cast<unsigned>(param_value);
      break;
    // An enumeration, so a value outside it names no mode; taking it would
    // leave the field holding something no arm of the lowering tests for.
    case UF_ACKERMANN:
      switch (param_value)
      {
        case 0:
          b->UserFlags.uf_eager_mode =
              stp::UserDefinedFlags::UFEagerMode::AUTO;
          break;
        case 1:
          b->UserFlags.uf_eager_mode = stp::UserDefinedFlags::UFEagerMode::ON;
          break;
        case 2:
          b->UserFlags.uf_eager_mode = stp::UserDefinedFlags::UFEagerMode::OFF;
          break;
        default:
          reportCAPIError("UF_ACKERMANN must be 0 (auto), 1 (on) or 2 (off)");
          break;
      }
      break;
    default:
      stp::FatalError("C_interface: vc_setInterfaceFlags: Unrecognized flag\n");
      break;
  }
}

// Division is now always total
void make_division_total(VC /*vc*/)
{
}

// Create a validity Checker.
VC vc_createValidityChecker(void)
{
  // Boot the bitvector library before allocating anything, so the failure
  // path leaks nothing.
  CONSTANTBV::ErrCode c = CONSTANTBV::BitVector_Boot();
  if (0 != c)
  {
    cout << CONSTANTBV::BitVector_Error(c) << endl;
    return 0;
  }

  return vc_createValidityCheckerReuse(new stp::STPMgr());
}

// Create a validity checker over an existing manager (an stp::STPMgr*), so a
// client mixing the C API with the C++ objects can solve over nodes it built
// directly.
VC vc_createValidityCheckerReuse(void* _bm)
{
  stp::STPMgr* bm = (stp::STPMgr*)_bm;

  CONSTANTBV::ErrCode c = CONSTANTBV::BitVector_Boot();
  if (0 != c)
  {
    cout << CONSTANTBV::BitVector_Error(c) << endl;
    return 0;
  }

  // A fresh manager starts out with its plain hashing factory; upgrade it to
  // the simplifying one. A reused manager that was already given a factory
  // keeps it (this used to replace -- and leak -- whatever was installed).
  if (bm->defaultNodeFactory == bm->hashingNodeFactory)
    bm->defaultNodeFactory =
        new SimplifyingNodeFactory(*(bm->hashingNodeFactory), *bm);

  // The parser-facing helpers read GlobalParserBM; point it at this manager
  // so a C-API client that never parses still has it aimed at a live one.
  // (Floating-point blasting itself takes the manager explicitly and does
  // not consult this.)
  stp::GlobalParserBM = bm;

  stp::STP* stpObj =
      new stp::STP(bm);

  registerCContext(static_cast<VC>(stpObj), bm);

  // created_exprs.clear();
  vc_setFlags(stpObj, 'd');
  return (VC)stpObj;
}

// Expr I/O
void vc_printExpr(VC vc, Expr e)
{
  // do not print in lisp mode
  stp::ASTNode q = (*(stp::ASTNode*)e);
  stp::STPMgr* b = mgr(vc);
  q.PL_Print(cout, b);
}

char* vc_printSMTLIB2(VC vc, Expr e)
{
  stp::STPMgr* b = mgr(vc);

  stringstream ss;
  printer::SMTLIB2_PrintBack(ss, *((stp::ASTNode*)e), b, false);
  string s = ss.str();
  char* copy = strdup(s.c_str());
  return copy;
}

void vc_printExprFile(VC vc, Expr e, int fd)
{
  stp::STPMgr* b = mgr(vc);

  stp::FdOStream os(fd);

  ((stp::ASTNode*)e)->PL_Print(os, b);
  // os.flush();
}

// The incremental driver defers counterexample construction to the first
// reader; every C-API entry that reads the counterexample tables calls
// this first. Cheap and idempotent when nothing is pending.
static void materializePendingModel(VC vc)
{
  stp::STP* stp_i = (stp::STP*)vc;
  if (stp_i->hasIncrementalSolver())
    stp_i->getIncrementalSolver()->materializePendingModel();
}

static void vc_printVarDeclsToStream(VC vc, ostream& os)
{
  stp::STPMgr* b = mgr(vc);

  for (stp::ASTVec::iterator i = b->decls.begin(), iend = b->decls.end();
       i != iend; i++)
  {
    stp::ASTNode a = *i;
    switch (a.GetType())
    {
      case stp::BITVECTOR_TYPE:
        a.PL_Print(os, b);
        os << " : BITVECTOR(" << a.GetValueWidth() << ");" << endl;
        break;
      case stp::ARRAY_TYPE:
        a.PL_Print(os, b);
        os << " : ARRAY "
           << "BITVECTOR(" << a.GetIndexWidth() << ") OF ";
        os << "BITVECTOR(" << a.GetValueWidth() << ");" << endl;
        break;
      case stp::BOOLEAN_TYPE:
        a.PL_Print(os, b);
        os << " : BOOLEAN;" << endl;
        break;
      default:
        stp::FatalError("vc_printDeclsToStream: Unsupported type", a);
        break;
    }
  }
}

void vc_printVarDecls(VC vc)
{
  vc_printVarDeclsToStream(vc, cout);
}

void vc_clearDecls(VC vc)
{
  stp::STPMgr* b = mgr(vc);
  b->decls.clear();
}

static void vc_printAssertsToStream(VC vc, ostream& os, int simplify_print)
{
  stp::STPMgr* b = mgr(vc);
  stp::ASTVec v = b->GetAsserts();

  stp::SubstitutionMap sm (b);
  stp::Simplifier simp(b, &sm );
  for (stp::ASTVec::iterator i = v.begin(), iend = v.end(); i != iend; i++)
  {
    stp::ASTNode q = *i;
    if (simplify_print == 1 && b->has_distinct)
      q = stp::lowerDistinct(b, q);
    q = (simplify_print == 1) ? simp.SimplifyFormula_TopLevel(q, false) : q;
    q = (simplify_print == 1) ? simp.SimplifyFormula_TopLevel(q, false) : q;
    os << "ASSERT( ";
    q.PL_Print(os, b);
    os << ");" << endl;
  }
}

void vc_printAsserts(VC vc, int simplify_print)
{
  vc_printAssertsToStream(vc, cout, simplify_print);
}

void vc_printQueryStateToBuffer(VC vc, Expr e, char** buf, size_t* len,
                                int simplify_print)
{
  stp::STPMgr* b = mgr(vc);
  assert(vc);
  assert(e);
  assert(buf);
  assert(len);

  stp::SubstitutionMap sm (b);
  stp::Simplifier simp(b, &sm );

  // formate the state of the query
  stringstream os;
  vc_printVarDeclsToStream(vc, os);
  os << "%----------------------------------------------------" << endl;
  vc_printAssertsToStream(vc, os, simplify_print);
  os << "%----------------------------------------------------" << endl;
  os << "QUERY( ";
  stp::ASTNode q = *(stp::ASTNode*)e;
  if (simplify_print == 1 && b->has_distinct)
    q = stp::lowerDistinct(b, q);
  if (simplify_print == 1)
    q = simp.SimplifyFormula_TopLevel(q, false);
  q.PL_Print(os, b);
  os << " );" << endl;

  // convert to a c buffer
  string s = os.str();
  const char* cstr = s.c_str();
  size_t size = s.size() + 1; // number of chars + terminating null
  *buf = (char*)malloc(size);
  if (!(*buf))
  {
    fprintf(stderr, "malloc(%zu) failed.", size);
    assert(*buf);
  }
  *len = size;
  memcpy(*buf, cstr, size);
}

void vc_printCounterExampleToBuffer(VC vc, char** buf, size_t* len)
{
  materializePendingModel(vc);
  assert(vc);
  assert(buf);
  assert(len);

  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::AbsRefine_CounterExample* ce =
      (stp::AbsRefine_CounterExample*)(stp_i->Ctr_Example);

  // formate the state of the query
  std::ostringstream os;
  bool currentPrint = b->UserFlags.print_counterexample_flag;
  b->UserFlags.print_counterexample_flag = true;
  os << "COUNTEREXAMPLE BEGIN: \n";
  ce->PrintCounterExample(true, os);
  os << "COUNTEREXAMPLE END: \n";
  b->UserFlags.print_counterexample_flag = currentPrint;

  // convert to a c buffer
  string s = os.str();
  const char* cstr = s.c_str();
  size_t size = s.size() + 1; // number of chars + terminating null
  *buf = (char*)malloc(size);
  if (!(*buf))
  {
    fprintf(stderr, "malloc(%zu) failed.", size);
    assert(*buf);
  }
  *len = size;
  memcpy(*buf, cstr, size);
}

unsigned long long vc_getCounter(VC vc, enum stp_counter_t counter)
{
  const stp::UserDefinedFlags::EncodingCoverage& c =
      mgr(vc)->UserFlags.coverage;
  typedef stp::UserDefinedFlags UF;
  switch (counter)
  {
    case STP_COUNTER_QUERIES_BITBLASTED: return c.queries_bitblasted;

    case STP_COUNTER_BV_CANDIDATES_EQ:
      return c.bv_candidates[UF::ABSTRACT_EQ];
    case STP_COUNTER_BV_CANDIDATES_COMPARE:
      return c.bv_candidates[UF::ABSTRACT_COMPARE];
    case STP_COUNTER_BV_CANDIDATES_ITE:
      return c.bv_candidates[UF::ABSTRACT_ITE];
    case STP_COUNTER_BV_CANDIDATES_PLUS:
      return c.bv_candidates[UF::ABSTRACT_PLUS];
    case STP_COUNTER_BV_CANDIDATES_MULT:
      return c.bv_candidates[UF::ABSTRACT_MULT];
    case STP_COUNTER_BV_CANDIDATES_DIVMOD:
      return c.bv_candidates[UF::ABSTRACT_DIVMOD];

    case STP_COUNTER_BV_ABSTRACTED_EQ:
      return c.bv_abstracted[UF::ABSTRACT_EQ];
    case STP_COUNTER_BV_ABSTRACTED_COMPARE:
      return c.bv_abstracted[UF::ABSTRACT_COMPARE];
    case STP_COUNTER_BV_ABSTRACTED_ITE:
      return c.bv_abstracted[UF::ABSTRACT_ITE];
    case STP_COUNTER_BV_ABSTRACTED_PLUS:
      return c.bv_abstracted[UF::ABSTRACT_PLUS];
    case STP_COUNTER_BV_ABSTRACTED_MULT:
      return c.bv_abstracted[UF::ABSTRACT_MULT];
    case STP_COUNTER_BV_ABSTRACTED_DIVMOD:
      return c.bv_abstracted[UF::ABSTRACT_DIVMOD];

    case STP_COUNTER_BV_REFINEMENT_ROUNDS: return c.bv_refinement_rounds;
    case STP_COUNTER_BV_BLOCKING_LEMMAS: return c.bv_blocking_lemmas;
    case STP_COUNTER_BV_SCHEMA_LEMMAS: return c.bv_schema_lemmas;
    case STP_COUNTER_UF_APPLICATIONS_LOWERED:
      return c.uf_applications_lowered;
    case STP_COUNTER_UF_CONSTRAINTS_INSTALLED:
      return c.uf_constraints_installed;
    case STP_COUNTER_BV_EXACT_ESCALATIONS:
      return c.bv_exact_escalations;
    case STP_COUNTER_BV_EXACT_ESCALATIONS_MULT:
      return c.bv_exact_escalations_mult;
    case STP_COUNTER_BV_EXACT_ESCALATIONS_DIVMOD:
      return c.bv_exact_escalations_divmod;
    case STP_COUNTER_BV_EXACT_CLAUSES: return c.bv_exact_clauses;
    case STP_COUNTER_BV_EXACT_VARIABLES: return c.bv_exact_variables;
    case STP_COUNTER_BV_EXACT_MICROSECONDS:
      return c.bv_exact_microseconds;
    case STP_COUNTER_BV_SCHEMA_CLAUSES: return c.bv_schema_clauses;
    case STP_COUNTER_BV_SCHEMA_VARIABLES: return c.bv_schema_variables;
    case STP_COUNTER_BV_SCHEMA_MICROSECONDS:
      return c.bv_schema_microseconds;
  }
  reportCAPIError("vc_getCounter: unrecognised counter");
  return 0;
}

// The C header spells the group count as a macro so a C caller can size an
// array with it; this is the only thing keeping the two in step.
static_assert(STP_BV_SCHEMA_GROUP_COUNT == stp::BV_SCHEMA_GROUP_COUNT,
              "the C schema-group count is out of step with BVSchemaGroup");

int vc_setSchemaGroups(VC vc, const char* groups)
{
  if (groups == NULL)
  {
    reportCAPIError("vc_setSchemaGroups: no group list");
    return 0;
  }

  // The same parser --bv-term-abstraction-schema-groups uses, so the two
  // doors accept one vocabulary rather than two that can drift.
  uint32_t mask = 0;
  std::string error;
  if (!stp::parseBVSchemaGroups(groups, mask, error))
  {
    reportCAPIError(("vc_setSchemaGroups: " + error).c_str());
    return 0;
  }

  // Only on success: a caller that mistypes one group in a list should not
  // end up running with a narrower catalogue than it asked for.
  stp::STP* b = (stp::STP*)vc;
  b->bm->UserFlags.bv_term_abstraction_schema_groups = mask;
  b->bm->UserFlags.bv_term_abstraction_schema_groups_explicit = true;
  return 1;
}

unsigned long long vc_getSchemaGroupCounter(VC vc, unsigned group)
{
  if (group >= stp::BV_SCHEMA_GROUP_COUNT)
  {
    reportCAPIError("vc_getSchemaGroupCounter: schema group index out of "
                    "range");
    return 0;
  }
  stp::STP* b = (stp::STP*)vc;
  return b->bm->UserFlags.coverage.bv_schema_group_lemmas[group];
}

const char* vc_schemaGroupName(unsigned group)
{
  if (group >= stp::BV_SCHEMA_GROUP_COUNT)
  {
    reportCAPIError("vc_schemaGroupName: schema group index out of range");
    return NULL;
  }
  return stp::bvSchemaGroupName(static_cast<stp::BVSchemaGroup>(group));
}

enum reason_unknown_t vc_getReasonUnknown(VC vc)
{
  switch (mgr(vc)->getUnknownReason())
  {
    case stp::UnknownReason::Timeout:
      return REASON_UNKNOWN_TIMEOUT;
    case stp::UnknownReason::ConflictBudget:
      return REASON_UNKNOWN_CONFLICT_BUDGET;
    case stp::UnknownReason::Incomplete:
      return REASON_UNKNOWN_INCOMPLETE;
    case stp::UnknownReason::CarrierExhausted:
      return REASON_UNKNOWN_CARRIER_EXHAUSTED;
    case stp::UnknownReason::AssumedInjectivity:
      return REASON_UNKNOWN_ASSUMED_INJECTIVITY;
    case stp::UnknownReason::AIGBudget:
      return REASON_UNKNOWN_AIG_BUDGET;
    case stp::UnknownReason::None:
      break;
  }
  return REASON_UNKNOWN_NONE;
}

void vc_getReasonUnknownToBuffer(VC vc, char** buf, size_t* len)
{
  // Empty rather than absent when there is nothing to say, so that a caller
  // has one shape to handle and always something to free.
  const std::string& detail = mgr(vc)->getUnknownReasonDetail();
  const size_t size = detail.size() + 1; // chars plus the terminating null
  *buf = (char*)malloc(size);
  *len = size;
  memcpy(*buf, detail.c_str(), size);
}

void vc_printExprToBuffer(VC vc, Expr e, char** buf, size_t* len)
{
  stp::STPMgr* b = mgr(vc);
  stp::ASTNode q = *((stp::ASTNode*)e);

  stringstream os;
  q.PL_Print(os, b);
  string s = os.str();
  const char* cstr = s.c_str();
  size_t size = s.size() + 1; // number of chars + terminating null
  *buf = (char*)malloc(size);
  *len = size;
  memcpy(*buf, cstr, size);
}

void vc_printQuery(VC vc)
{
  stp::STPMgr* b = mgr(vc);

  ostream& os = std::cout;
  os << "QUERY(";
  stp::ASTNode q = b->GetQuery();
  q.PL_Print(os, b);
  os << ");" << endl;
}

stp::ASTNode* persistNode(VC vc, stp::ASTNode n)
{
  stp::STPMgr* b = mgr(vc);

  stp::ASTNode* np = new stp::ASTNode(n);
  registerCExpression(np);
  if (b->UserFlags.cinterface_exprdelete_on_flag)
    b->persist.push_back(np);
  return np;
}

/////////////////////////////////////////////////////////////////////////////
// Array-related methods                                                   //
/////////////////////////////////////////////////////////////////////////////
//! Create an array type
Type vc_arrayType(VC vc, Type typeIndex, Type typeData)
{
  stp::STPMgr* b = mgr(vc);
  stp::ASTNode* ti = (stp::ASTNode*)typeIndex;
  stp::ASTNode* td = (stp::ASTNode*)typeData;

  // Index and element may each be a bitvector, a floating-point format, or
  // RoundingMode. The type node keeps the child type nodes whole, so
  // vc_varExpr can lay the right widths and formats onto the symbol.
  const auto scalar = [](const stp::ASTNode& t) {
    return t.GetKind() == stp::BITVECTOR ||
           t.GetKind() == stp::FLOATINGPOINT ||
           t.GetKind() == stp::ROUNDINGMODE;
  };
  if (!scalar(*ti))
  {
    stp::FatalError("CInterface: vc_arrayType: the index type must be a "
                    "bitvector, floating-point or RoundingMode type: ",
                    *ti);
  }
  if (!scalar(*td))
  {
    stp::FatalError("CInterface: vc_arrayType: the element type must be a "
                    "bitvector, floating-point or RoundingMode type: ",
                    *td);
  }
  stp::ASTNode output = b->CreateNode(stp::ARRAY, *ti, *td);

  return persistNode(vc, output);
}

// A rounding-mode-sorted term. Was a copy here; it is STPMgr's now, because
// the operations that take a rounding mode need the same test and were making
// do with the carrier's width.
// The rounding-mode argument of a floating-point operation. SMT-LIB's
// RoundingMode has five values; the carrier has thirty-two, and symfpu
// computes under a sixth, non-IEEE mode if handed one of the other
// twenty-seven.
static void checkRoundingMode(const char* who, stp::STPMgr* b,
                              const stp::ASTNode& rm)
{
  if (!b->isRoundingModeSortedTerm(rm))
  {
    stp::FatalError((std::string("CInterface: ") + who +
                     ": expected a rounding mode: ")
                        .c_str(),
                    rm);
  }
}

// The index of an array access must have the array's declared index sort:
// a float of the right format for a float-indexed array, a rounding mode
// for a RoundingMode-indexed one, and a plain bitvector otherwise. Mixing
// sorts of one width is not merely ill-sorted -- a raw index alongside
// canonicalised ones would break the array's congruence (see FpTotalise).
static void checkArrayIndexSort(const char* who, stp::STPMgr* b,
                                const stp::ASTNode& arr,
                                const stp::ASTNode& index)
{
  (void)b;
  const stp::SourceSort array_sort = arr.GetSourceSort();
  if (array_sort.kind() != stp::SourceSort::Kind::Array)
    stp::FatalError("CInterface: select/store expects an array: ", arr);
  const stp::SourceSort expected = array_sort.index();
  if (index.GetSourceSort() == expected)
    return;

  if (expected.kind() == stp::SourceSort::Kind::FloatingPoint)
  {
    stp::FatalError((std::string("CInterface: ") + who +
                     ": the array is indexed by a floating-point sort, but "
                     "the index is not a float of that format: ")
                        .c_str(),
                    index);
  }
  if (expected.kind() == stp::SourceSort::Kind::RoundingMode)
  {
    stp::FatalError((std::string("CInterface: ") + who +
                     ": the array is indexed by RoundingMode, but the index "
                     "is not a rounding mode: ")
                        .c_str(),
                    index);
  }
  stp::FatalError((std::string("CInterface: ") + who +
                   ": index sort differs from the array's bitvector index "
                   "sort: ")
                      .c_str(),
                  index);
}

// The value stored by vc_writeExpr must have the array's element sort, by
// the same reasoning.
static void checkArrayValueSort(stp::STPMgr* b, const stp::ASTNode& arr,
                                const stp::ASTNode& value)
{
  (void)b;
  const stp::SourceSort array_sort = arr.GetSourceSort();
  if (array_sort.kind() != stp::SourceSort::Kind::Array)
    stp::FatalError("CInterface: vc_writeExpr expects an array: ", arr);
  const stp::SourceSort expected = array_sort.element();
  if (value.GetSourceSort() == expected)
    return;

  if (expected.kind() == stp::SourceSort::Kind::FloatingPoint)
  {
    stp::FatalError("CInterface: vc_writeExpr: the array's elements are "
                    "floats, but the stored value is not a float of that "
                    "format: ",
                    value);
  }
  if (expected.kind() == stp::SourceSort::Kind::RoundingMode)
  {
    stp::FatalError("CInterface: vc_writeExpr: the array's elements are "
                    "rounding modes, but the stored value is not one: ",
                    value);
  }
  stp::FatalError("CInterface: vc_writeExpr: stored value sort differs from "
                  "the array's bitvector element sort: ",
                  value);
}

//! Create an expression for the value of array at the given index
Expr vc_readExpr(VC vc, Expr array, Expr index)
{
  stp::STPMgr* b = mgr(vc);
  stp::ASTNode* a = (stp::ASTNode*)array;
  stp::ASTNode* i = (stp::ASTNode*)index;

  assert(BVTypeCheck(*a));
  assert(BVTypeCheck(*i));
  checkArrayIndexSort("vc_readExpr", b, *a, *i);
  stp::ASTNode o = b->CreateTerm(stp::READ, a->GetValueWidth(), *a, *i);
  assert(BVTypeCheck(o));

  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return wrap(o);
}

// //! Array update; equivalent to "array WITH [index] := newValue"
Expr vc_writeExpr(VC vc, Expr array, Expr index, Expr newValue)
{
  stp::STPMgr* b = mgr(vc);
  stp::ASTNode* a = (stp::ASTNode*)array;
  stp::ASTNode* i = (stp::ASTNode*)index;
  stp::ASTNode* n = (stp::ASTNode*)newValue;

  assert(BVTypeCheck(*a));
  assert(BVTypeCheck(*i));
  assert(BVTypeCheck(*n));
  checkArrayIndexSort("vc_writeExpr", b, *a, *i);
  checkArrayValueSort(b, *a, *n);
  stp::ASTNode o = b->CreateTerm(stp::WRITE, a->GetValueWidth(), *a, *i, *n);
  o.SetIndexWidth(a->GetIndexWidth());
  assert(BVTypeCheck(o));

  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return wrap(o);
}

/////////////////////////////////////////////////////////////////////////////
// Context-related methods                                                 //
/////////////////////////////////////////////////////////////////////////////
//! Assert a new formula in the current context.
/*! The formula must have Boolean type. */
void vc_assertFormula(VC vc, Expr e)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = mgr(vc);
  stp::ASTNode* a = (stp::ASTNode*)e;

  if (a->GetSourceSort().kind() != stp::SourceSort::Kind::Bool ||
      !stp::is_Form_kind(a->GetKind()))
    stp::FatalError("Trying to assert a NON formula: ", *a);

  assert(BVTypeCheck(*a));
  b->AddAssert(*a);
  // A certified UF map belongs to one completed root. An assertion changes
  // that root even before the next query clears the ordinary model tables.
  if (stp_i->Ctr_Example->getUFTheoryAdapter() != NULL)
    stp_i->Ctr_Example->getUFTheoryAdapter()->invalidateCertifiedModel();
}

//! Check validity of e in the current context. e must be a FORMULA
//
// if returned 0 then input is INVALID.
//
// if returned 1 then input is VALID
//
// if returned 2 then ERROR
//
//! Check validity of e in the current context.
/*! If the result is true, then the resulting context is the same as
 * the starting context.  If the result is false, then the resulting
 * context is a context in which e is false.  e must have Boolean
 * type. */
int vc_query(VC vc, Expr e)
{
  return vc_query_with_timeout(vc, e, -1, -1);
}

int vc_query_with_timeout(VC vc, Expr e, int timeout_max_conflicts, int timeout_max_time)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::ASTNode* a = (stp::ASTNode*)e;
  stp::STPMgr* b = stp_i->bm;

  // Make this checker's manager current so floating-point blasting during the
  // solve targets it, not whichever checker was created or solved last.
  stp::GlobalParserBM = b;

  /*
   * -1 is the only negative value that means anything ("no limit"). Reject
   * the rest rather than silently running unlimited, which is the dangerous
   * direction for a caller that computed a budget and got the sign wrong.
   */
  if (timeout_max_conflicts < -1)
  {
    std::cerr << "CInterface: timeout_max_conflicts must be -1 (no limit) or "
                 "greater"
              << std::endl;
    return 2;
  }

  if (timeout_max_time < -1)
  {
    std::cerr << "CInterface: timeout_max_time must be -1 (no limit) or greater"
              << std::endl;
    return 2;
  }

  if (a->GetSourceSort().kind() != stp::SourceSort::Kind::Bool ||
      !stp::is_Form_kind(a->GetKind()))
  {
    stp::FatalError("CInterface: Trying to QUERY a NON formula: ", *a);
  }

  assert(BVTypeCheck(*a));
  // Cached in case someone runs PrintQuery()
  b->SetQuery(*a);

  stp_i->ClearAllTables();

  stp_i->bm->UserFlags.timeout_max_conflicts = timeout_max_conflicts;
  stp_i->bm->UserFlags.timeout_max_time = timeout_max_time;

  // Incremental sessions (a vc_push happened, or vc_setFlags 'i'): solve
  // through the persistent driver. vc_query decides asserts AND NOT query,
  // and the negated query is appended as one more retractable level -- an
  // assumption for exactly this call, which is also what sidesteps the
  // un-stacked _current_query. The driver populates the same
  // counterexample tables the batch path does, so the C API's model
  // contract (the counterexample belongs to the last query and survives
  // the push/query/pop bracket) is untouched. Engagement follows the same
  // policy object as the SMT-LIB2 frontend: by default the third solve, so
  // the first solves keep the batch pipeline's whole-formula simplification
  // and a two-query session -- whose final solve can never repay the
  // driver's persistent encoding -- stays batch throughout. There is no
  // set-logic here, so the longer pure-QF_BV default is not claimed. This
  // used to be a literal 3 that incremental_auto_engage_at could not reach:
  // the override was documented and inert for every embedder.
  // vc_setFlags 'i' still forces the driver from the first solve.
  const bool use_incremental =
      stp_i->sessionIncremental &&
      (stp_i->incrementalFromStart ||
       stp::IncrementalSolver::automaticEngagementReady(
           stp_i->bm->UserFlags.incremental_auto_engage_at,
           /*delayedBvLogic=*/false, stp_i->incrementalSolvesRun));
  // Same policy object as the SMT-LIB2 frontend. The `use_incremental &&`
  // this used to carry was dead: the value is read only inside the
  // `if (use_incremental)` branch below.
  const bool firstForcedIncrementalSolve =
      stp::IncrementalSolver::forcedFirstSolve(stp_i->incrementalFromStart,
                                               stp_i->incrementalSolvesRun);
  stp_i->incrementalSolvesRun++;
  if (use_incremental)
  {
    // The driver treats its base level as permanent -- base conjuncts
    // become unit clauses for the rest of the session. The SMT-LIB2
    // frontend guarantees such a level (it exists from startup and can
    // never be popped); the C API guarantees no such thing: the stack
    // starts empty, the first vc_push creates a level that vc_pop will
    // remove again, and even pre-push assertions can be popped. So here
    // NOTHING is permanent: the driver's base is a synthetic TRUE, every
    // real level rides as retractable assumptions, and the negated query
    // is one more retractable level of its own.
    stp::ASTVec levels;
    levels.push_back(b->ASTTrue);
    const stp::ASTVec current = b->getVectorOfAsserts();
    levels.insert(levels.end(), current.begin(), current.end());
    levels.push_back(b->CreateNode(stp::NOT, *a));

    stp::IncrementalSolver* inc = stp_i->getIncrementalSolver();
    if (inc->canHandle(levels))
      return recordQueryOutcome(
          stp_i, inc->checkSat(levels, false, firstForcedIncrementalSolve));
  }

  const stp::ASTVec v = b->GetAsserts();
  stp::ASTNode o;
  int output;
  if (!v.empty())
  {
    if (v.size() == 1)
    {
      output = stp_i->TopLevelSTP(v[0], *a);
    }
    else
    {
      output = stp_i->TopLevelSTP(b->CreateNode(stp::AND, v), *a);
    }
  }
  else
  {
    output = stp_i->TopLevelSTP(b->CreateNode(stp::TRUE), *a);
  }

  return recordQueryOutcome(stp_i, output);
}

void vc_push(VC vc)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;

  // The session is incremental from the first push on, exactly as the
  // SMT-LIB2 frontend behaves; sessions that never push are untouched, and a
  // caller that set IncrementalMode::OFF has asked that not even a pushing
  // session become incremental.
  if (b->UserFlags.incremental_mode !=
      stp::UserDefinedFlags::IncrementalMode::OFF)
    stp_i->sessionIncremental = true;

  stp_i->ClearAllTables();
  b->Push();
}

//NB, doesn't remove symbols from decls, so they will be kept alive.
//
// Deliberately does NOT discard the counterexample tables, unlike vc_push
// and vc_query: the C API's idiom brackets each query in push/pop and reads
// the counterexample afterwards (see tests/api/C/stp-counterex.cpp). The
// model belongs to the last vc_query, not to the assertion stack, and stays
// readable until the next vc_push or vc_query clears it -- both of which
// run before any state they clear could be reused for solving.
void vc_pop(VC vc)
{
  stp::STP* stp_i = static_cast<stp::STP*>(vc);
  stp::STPMgr* b = stp_i->bm;
  b->Pop();

  // Preserve the historical ordinary-scalar/array counterexample contract,
  // but not a UF certified handle map: that map is explicitly rooted in one
  // unchanged stack/block and every real pop invalidates it.
  if (stp_i->Ctr_Example->getUFTheoryAdapter() != NULL)
    stp_i->Ctr_Example->getUFTheoryAdapter()->invalidateCertifiedModel();
}

void vc_printCounterExample(VC vc)
{
  materializePendingModel(vc);
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::AbsRefine_CounterExample* ce =
      (stp::AbsRefine_CounterExample*)(stp_i->Ctr_Example);

  bool currentPrint = b->UserFlags.print_counterexample_flag;
  b->UserFlags.print_counterexample_flag = true;
  cout << "COUNTEREXAMPLE BEGIN: \n";
  ce->PrintCounterExample(true);
  cout << "COUNTEREXAMPLE END: \n";
  b->UserFlags.print_counterexample_flag = currentPrint;
}

void vc_printCounterExampleSMTLIB2(VC vc)
{
  materializePendingModel(vc);
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::AbsRefine_CounterExample* ce =
      (stp::AbsRefine_CounterExample*)(stp_i->Ctr_Example);

  bool currentPrint = b->UserFlags.print_counterexample_flag;
  b->UserFlags.print_counterexample_flag = true;
  ce->PrintCounterExampleSMTLIB2(cout);
  b->UserFlags.print_counterexample_flag = currentPrint;
}

// //! Return the counterexample after a failed query.
// /*! This method should only be called after a query which returns
//  * false.  It will try to return the simplest possible set of
//  * assertions which are sufficient to make the queried expression
//  * false.  The caller is responsible for freeing the array when
//  * finished with it.
//  */

Expr vc_getCounterExample(VC vc, Expr e)
{
  if (vc != NULL && e != NULL &&
      static_cast<stp::ASTNode*>(e)->GetKind() == stp::UF_APPLY)
    return vc_getUninterpretedFunctionValue(vc, e);
  stp::STP* stp_i = (stp::STP*)vc;
  stp::ASTNode* a = (stp::ASTNode*)e;

  // A constant already is its own value. Nothing about it is read out of a
  // model, so the refusal below has nothing to protect it from: it answers
  // with no query behind it, which is what this entry point has always done
  // and what reading the value of a literal through the bindings relies on.
  // The narrowing is to constants alone -- a symbol, or any term that has to
  // be evaluated to reach a value, still has nothing to say without a model.
  const bool isOwnValue = (a != NULL && a->isConstant());

  // For everything else, no decided query behind this call means no model to
  // read: either none has been run, or the last one timed out or errored, or
  // a vc_push or vc_query has discarded the one there was. Refuse, rather
  // than evaluate against an empty counterexample map -- which returned an
  // invented value for a bit-vector or a Boolean, and for a float reached the
  // model evaluator's fatal and took the process down. The SMT-LIB2 frontend
  // has always answered this "unsupported"; this is the same refusal in the
  // shape this interface already uses for a nonfatal misuse -- a diagnostic
  // through the handler vc_registerErrorHandler installs, and NULL -- which
  // is also what the header documents for the sibling entry point
  // vc_getUninterpretedFunctionValue.
  if (!isOwnValue && !stp_i->queryAnswered)
  {
    reportCAPIError("vc_getCounterExample: no model to read -- no query has "
                    "been answered since the last vc_push or vc_query");
    return NULL;
  }

  materializePendingModel(vc);

  // Reading a floating-point value blasts the term, so this checker's manager
  // must be current (see vc_query_with_timeout).
  stp::GlobalParserBM = stp_i->bm;

  stp::AbsRefine_CounterExample* ce =
      (stp::AbsRefine_CounterExample*)(stp_i->Ctr_Example);
  return wrap(ce->GetCounterExample(*a));
}

void vc_getCounterExampleArray(VC vc, Expr e, Expr** indices, Expr** values,
                               int* size)
{
  materializePendingModel(vc);
  stp::STP* stp_i = (stp::STP*)vc;
  stp::ASTNode* a = (stp::ASTNode*)e;
  stp::AbsRefine_CounterExample* ce =
      (stp::AbsRefine_CounterExample*)(stp_i->Ctr_Example);

  bool t = false;
  if (ce->CounterExampleSize())
    t = true;

  vector<std::pair<ASTNode, ASTNode>> entries =
      ce->GetCounterExampleArray(t, *a);
  *size = entries.size();
  if (*size != 0)
  {
    *indices = (Expr*)malloc(*size * sizeof(Expr*));
    assert(*indices);
    *values = (Expr*)malloc(*size * sizeof(Expr*));
    assert(*values);

    for (int i = 0; i < *size; ++i)
    {
      (*indices)[i] = registerCExpression(new stp::ASTNode(entries[i].first));
      (*values)[i] = registerCExpression(new stp::ASTNode(entries[i].second));
    }
  }
}

void vc_deleteCounterExampleArray(Expr* indices, Expr* values, int size)
{
  if (size <= 0)
    return;
  for (int i = 0; i < size; ++i)
  {
    vc_DeleteExpr(indices[i]);
    vc_DeleteExpr(values[i]);
  }
  free(indices);
  free(values);
}

int vc_counterexample_size(VC vc)
{
  materializePendingModel(vc);
  stp::STP* stp_i = (stp::STP*)vc;
  stp::AbsRefine_CounterExample* ce =
      (stp::AbsRefine_CounterExample*)(stp_i->Ctr_Example);
  return ce->CounterExampleSize();
}

WholeCounterExample vc_getWholeCounterExample(VC vc)
{
  materializePendingModel(vc);
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::AbsRefine_CounterExample* ce =
      (stp::AbsRefine_CounterExample*)(stp_i->Ctr_Example);

  stp::CompleteCounterExample* c =
      new stp::CompleteCounterExample(ce->GetCompleteCounterExample(), b);
  return c;
}

Expr vc_getTermFromCounterExample(VC /*vc*/, Expr e, WholeCounterExample cc)
{
  stp::ASTNode* n = (stp::ASTNode*)e;
  stp::CompleteCounterExample* c = (stp::CompleteCounterExample*)cc;

  return wrap(c->GetCounterExample(*n));
}

void vc_deleteWholeCounterExample(WholeCounterExample cc)
{
  stp::CompleteCounterExample* c = (stp::CompleteCounterExample*)cc;

  delete c;
}

int vc_getBVLength(VC /*vc*/, Expr ex)
{
  stp::ASTNode* e = (stp::ASTNode*)ex;

  if (e->GetSourceSort().kind() != stp::SourceSort::Kind::BitVector)
  {
    stp::FatalError("c_interface: vc_GetBVLength: "
                    "Input expression must be a bit-vector");
  }
  return e->GetValueWidth();
}

/////////////////////////////////////////////////////////////////////////////
// Expr Creation methods                                                   //
/////////////////////////////////////////////////////////////////////////////
//! Create a variable with a given name and type
/*! The type cannot be a function type. */
Expr vc_varExpr1(VC vc, const char* name, int indexwidth, int valuewidth)
{
  stp::STPMgr* b = mgr(vc);

  if (b->getUFContextIfAny() != NULL &&
      b->getUFContextIfAny()->lookup(name) != NULL)
  {
    reportCAPIError(std::string("name '") + name +
                    "' already denotes an uninterpreted function");
    return NULL;
  }

  // An array of zero-width elements is not a sort, and SourceSort::bitVector
  // asserts as much -- which is an abort inside a header on an asserting build
  // and a zero-width element carried onward without one. vc_bvType has
  // refused a zero width by the other route for years; this entrance did not,
  // so the precondition stayed reachable from the C API after the parser had
  // been closed against it.
  //
  // FatalError rather than a NULL return: every other refusal in this file is
  // fatal, the registered error handler is documented as being called for each
  // fatal error, and a caller that ignored a NULL would fault later on a null
  // Expr instead of here, where the message names the mistake.
  if (indexwidth > 0 && valuewidth <= 0)
  {
    stp::FatalError("CInterface: vc_varExpr1: number of bits in an array's "
                    "elements must be a positive integer");
  }

  stp::SourceSort source_sort;
  if (indexwidth > 0)
    source_sort = stp::SourceSort::array(
        stp::SourceSort::bitVector(indexwidth),
        stp::SourceSort::bitVector(valuewidth));
  else if (valuewidth > 0)
    source_sort = stp::SourceSort::bitVector(valuewidth);
  else
    source_sort = stp::SourceSort::boolean();
  stp::ASTNode o = createPublicSourceSymbol(b, name, source_sort);

  stp::ASTNode* output = new stp::ASTNode(o);
  registerCExpression(output);
  ////if(cinterface_exprdelete_on) created_exprs.push_back(output);
  assert(BVTypeCheck(*output));

  // store the decls in a vector for printing purposes
  b->decls.push_back(o);
  return output;
}

Expr vc_varExpr(VC vc, const char* name, Type type)
{
  stp::STPMgr* b = mgr(vc);
  if (b->getUFContextIfAny() != NULL &&
      b->getUFContextIfAny()->lookup(name) != NULL)
  {
    reportCAPIError(std::string("name '") + name +
                    "' already denotes an uninterpreted function");
    return NULL;
  }
  stp::ASTNode* typeNode = (stp::ASTNode*)type;
  switch (typeNode->GetKind())
  {
    case stp::BOOLEAN:
    case stp::BITVECTOR:
    case stp::FLOATINGPOINT:
    case stp::ROUNDINGMODE:
    case stp::ARRAY:
      break;
    default:
      stp::FatalError("CInterface: vc_varExpr expects a type node: ",
                      *typeNode);
  }
  const stp::SourceSort source_sort = typeNode->GetSourceSort();
  if (!source_sort.isKnown())
    stp::FatalError("CInterface: vc_varExpr: unsupported source sort: ",
                    *typeNode);
  stp::ASTNode o = createPublicSourceSymbol(b, name, source_sort);

  // A RoundingMode variable must range over exactly the five modes: pin the
  // 5-bit carrier to the one-hot encodings (asserted at the current
  // assertion level) and register the symbol so counterexamples print its
  // value by mode name -- exactly as the parser declares one.
  //
  // The assertion is the pin for this level, not the guarantee. vc_pop drops
  // a level's assertions and the symbol node survives it hash-consed, so what
  // actually holds the mode to five values is FpTotalise re-pinning every one
  // the formula names at solve time.
  if (typeNode->GetKind() == stp::ROUNDINGMODE)
  {
    b->AddAssert(b->roundingModeValidConstraint(o));
  }

  stp::ASTNode* output = new stp::ASTNode(o);
  registerCExpression(output);
  ////if(cinterface_exprdelete_on) created_exprs.push_back(output);
  assert(BVTypeCheck(*output));

  // store the decls in a vector for printing purposes
  b->decls.push_back(o);
  return output;
}

static bool cTypeToUFSort(VC vc, Type type, const char* position,
                          stp::SourceSort& sort, std::string& diagnostic)
{
  stp::ASTNode* node = NULL;
  if (!liveCExpression(vc, type, node, diagnostic))
  {
    diagnostic = std::string(position) + " type: " + diagnostic;
    return false;
  }
  // A type handle has to be a type: a value expression of the right sort is
  // not one, and accepting it would let vc_bvType's discipline slip.
  switch (node->GetKind())
  {
    case stp::BOOLEAN:
    case stp::BITVECTOR:
    case stp::FLOATINGPOINT:
    case stp::ROUNDINGMODE:
    case stp::ARRAY:
      break;
    default:
      diagnostic = std::string(position) + " type is not a sort";
      return false;
  }

  // Every type node the C API hands out already denotes its SourceSort, so
  // ask it rather than re-deriving one here, and put the answer through the
  // same admission gate the parser uses. The two frontends drifting apart is
  // exactly what went wrong before: an .smt2 file could declare a sort that
  // this function, with its own hand-rolled list, refused.
  sort = node->GetSourceSort();
  if (stp::UFSignature::isSupportedSort(sort))
    return true;
  diagnostic = std::string(position) + " type " + sourceSortToSMTLib(sort) +
               " is unsupported (" +
               stp::UFSignature::supportedSortsPhrase() + ")";
  return false;
}

UFDeclHandle vc_declareUninterpretedFunction(
    VC vc, const char* name, const Type* domainTypes, size_t domainCount,
    Type codomain)
{
  if (vc == NULL || name == NULL ||
      (domainCount != 0 && domainTypes == NULL) || codomain == NULL)
  {
    reportCAPIError(
        "vc_declareUninterpretedFunction received a null required argument");
    return 0;
  }

  CContextRecord context;
  if (!liveCContext(vc, context))
  {
    reportCAPIError("vc_declareUninterpretedFunction received an invalid or "
                    "destroyed validity-checker handle");
    return 0;
  }
  stp::STPMgr* b = context.manager;
  if (!b->UserFlags.enable_uninterpreted_functions)
  {
    reportCAPIError("uninterpreted functions are not enabled");
    return 0;
  }
  if (domainCount == 0)
  {
    reportCAPIError("zero-arity functions are ordinary symbols");
    return 0;
  }
  if (b->c_api_source_sorts.find(name) != b->c_api_source_sorts.end())
  {
    reportCAPIError(std::string("name '") + name +
                    "' already denotes an ordinary symbol");
    return 0;
  }

  std::string diagnostic;
  std::vector<stp::SourceSort> domainSorts;
  domainSorts.reserve(domainCount);
  for (size_t i = 0; i < domainCount; ++i)
  {
    stp::SourceSort sourceSort;
    if (!cTypeToUFSort(vc, domainTypes[i], "domain", sourceSort, diagnostic))
    {
      reportCAPIError(diagnostic);
      return 0;
    }
    domainSorts.push_back(sourceSort);
  }
  stp::SourceSort codomainSort;
  if (!cTypeToUFSort(vc, codomain, "codomain", codomainSort, diagnostic))
  {
    reportCAPIError(diagnostic);
    return 0;
  }

  const stp::UFDecl* declaration = b->getUFContext()->declareFunction(
      name, domainSorts, codomainSort, &diagnostic);
  if (declaration == NULL)
  {
    reportCAPIError(diagnostic);
    return 0;
  }
  stp::STP* stp_i = static_cast<stp::STP*>(vc);
  if (stp_i->Ctr_Example->getUFTheoryAdapter() != NULL)
    stp_i->Ctr_Example->getUFTheoryAdapter()->invalidateCertifiedModel();
  return registerCUFDecl(vc, declaration);
}

Expr vc_applyUninterpretedFunction(VC vc, UFDeclHandle function,
                                   const Expr* arguments,
                                   size_t argumentCount)
{
  if (vc == NULL || function == 0 ||
      (argumentCount != 0 && arguments == NULL))
  {
    reportCAPIError(
        "vc_applyUninterpretedFunction received a null required argument");
    return NULL;
  }

  CContextRecord context;
  if (!liveCContext(vc, context))
  {
    reportCAPIError("vc_applyUninterpretedFunction received an invalid or "
                    "destroyed validity-checker handle");
    return NULL;
  }
  std::string diagnostic;
  const stp::UFDecl* declaration = NULL;
  if (!liveCUFDecl(vc, function, declaration, diagnostic))
  {
    reportCAPIError(diagnostic);
    return NULL;
  }

  stp::ASTVec actuals;
  actuals.reserve(argumentCount);
  for (size_t i = 0; i < argumentCount; ++i)
  {
    stp::ASTNode* actual = NULL;
    if (!liveCExpression(vc, arguments[i], actual, diagnostic))
    {
      reportCAPIError("vc_applyUninterpretedFunction argument " +
                      std::to_string(i) + ": " + diagnostic);
      return NULL;
    }
    actuals.push_back(*actual);
  }

  stp::STPMgr* b = context.manager;
  const stp::ASTNode application =
      b->getUFContext()->apply(declaration, actuals, &diagnostic);
  if (application.GetKind() == stp::UNDEFINED)
  {
    reportCAPIError(diagnostic);
    return NULL;
  }
  return wrap(application);
}

Expr vc_getUninterpretedFunctionValue(VC vc, Expr application)
{
  if (vc == NULL || application == NULL)
  {
    reportCAPIError(
        "vc_getUninterpretedFunctionValue received a null required argument");
    return NULL;
  }
  CContextRecord context;
  if (!liveCContext(vc, context))
  {
    reportCAPIError("vc_getUninterpretedFunctionValue received an invalid or "
                    "destroyed validity-checker handle");
    return NULL;
  }
  stp::ASTNode* durable = NULL;
  std::string diagnostic;
  if (!liveCExpression(vc, application, durable, diagnostic))
  {
    reportCAPIError("vc_getUninterpretedFunctionValue: " + diagnostic);
    return NULL;
  }
  materializePendingModel(vc);
  stp::STP* stp_i = static_cast<stp::STP*>(vc);
  stp::ASTNode value;
  if (!stp::UFModel::evaluateApplication(
          stp_i->bm, stp_i->Ctr_Example->getUFTheoryAdapter(),
          *durable, value, diagnostic))
  {
    reportCAPIError(diagnostic);
    return NULL;
  }
  return wrap(value);
}

//! Create an equality expression.  The two children must have the
// same type.
Expr vc_eqExpr(VC vc, Expr ccc0, Expr ccc1)
{
  stp::STPMgr* b = mgr(vc);

  stp::ASTNode* a = (stp::ASTNode*)ccc0;
  stp::ASTNode* aa = (stp::ASTNode*)ccc1;
  assert(BVTypeCheck(*a));
  assert(BVTypeCheck(*aa));
  requireSamePublicSort("vc_eqExpr", b, *a, *aa);

  // Mirror the parser's source-sort equality. SMT-LIB '=' over floats is
  // FP_SMT_EQ, not the generic EQ, mirroring the parser's (= ...) rule: +0
  // and -0 stay distinct, and every NaN equals every NaN. A plain EQ over
  // floating-point operands is a node the later passes cannot discharge --
  // the solve died without a conclusion (found by murxla; vc_fpEqExpr's doc
  // sends '=' callers here, so this is the documented route). With only one
  // float operand, FP_SMT_EQ's typecheck then rejects the float/bitvector
  // mix, exactly as the parser does. A Bool source sort takes IFF for the
  // same reason: a generic EQ over it reaches BV-only solving at width zero.
  const stp::SourceSort::Kind sourceKind = a->GetSourceSort().kind();
  const stp::Kind k =
      sourceKind == stp::SourceSort::Kind::Bool
          ? stp::IFF
          : (sourceKind == stp::SourceSort::Kind::FloatingPoint ||
             aa->GetSourceSort().kind() ==
                 stp::SourceSort::Kind::FloatingPoint)
                ? stp::FP_SMT_EQ
                : stp::EQ;
  stp::ASTNode o = b->CreateNode(k, *a, *aa);

  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return wrap(o);
}

Expr vc_boolType(VC vc)
{
  stp::STPMgr* b = mgr(vc);

  stp::ASTNode output = b->CreateNode(stp::BOOLEAN);
  return persistNode(vc, output);
}

// ---------------------------------------------------------------------------
// Floating point
// ---------------------------------------------------------------------------

// Every route by which a floating-point format enters through the C API --
// vc_fpType's type node and the entry points that take the widths as raw
// ints. One funnel: the parser's copy of this drifted from its sort rule's
// once already.
static void checkFpWidths(int eb, int sb)
{
  if (eb < 2 || sb < 2)
  {
    stp::FatalError("CInterface: a floating-point format needs at least 2 "
                    "exponent and 2 significand bits");
  }
}

Type vc_fpType(VC vc, int exp_bits, int sig_bits)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;

  checkFpWidths(exp_bits, sig_bits);

  // Mirror vc_bvType/vc_arrayType: a type is a node whose children hold the
  // widths -- here the exponent and significand widths.
  stp::ASTNode e = b->CreateBVConst(32, exp_bits);
  stp::ASTNode s = b->CreateBVConst(32, sig_bits);
  stp::ASTNode output = b->CreateNode(stp::FLOATINGPOINT, e, s);
  return persistNode(vc, output);
}

Type vc_fpRoundingModeType(VC vc)
{
  stp::STPMgr* b = ((stp::STP*)vc)->bm;

  // The sort has no parameters, so the type node is childless; vc_varExpr
  // recognises it and builds the constrained 5-bit variable.
  return persistNode(vc, b->CreateNode(stp::ROUNDINGMODE));
}

int vc_getExpWidth(Expr e)
{
  return (int)((stp::ASTNode*)e)->GetExpWidth();
}

int vc_getSigWidth(Expr e)
{
  return (int)((stp::ASTNode*)e)->GetSigWidth();
}

Expr vc_fpConstFromBits(VC vc, int exp_bits, int sig_bits, Expr bv)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* bits = (stp::ASTNode*)bv;

  checkFpWidths(exp_bits, sig_bits);
  requireBitVectorOperand("vc_fpConstFromBits", *bits);

  if (bits->GetKind() != stp::BVCONST)
  {
    stp::FatalError("CInterface: vc_fpConstFromBits: the bits argument must be "
                    "a bitvector constant: ",
                    *bits);
  }
  if ((int)bits->GetValueWidth() != exp_bits + sig_bits)
  {
    stp::FatalError("CInterface: vc_fpConstFromBits: the bitvector width must "
                    "equal exp_bits + sig_bits: ",
                    *bits);
  }

  stp::ASTNode output = b->CreateFPConst(*bits, exp_bits, sig_bits);
  return persistNode(vc, output);
}

Expr vc_fpEqExpr(VC vc, Expr a, Expr b)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* bm = stp_i->bm;
  stp::ASTNode* l = (stp::ASTNode*)a;
  stp::ASTNode* r = (stp::ASTNode*)b;

  if (l->GetSourceSort().kind() != stp::SourceSort::Kind::FloatingPoint ||
      r->GetSourceSort().kind() != stp::SourceSort::Kind::FloatingPoint)
  {
    stp::FatalError("CInterface: vc_fpEqExpr requires floating-point operands: ",
                    l->GetType() == stp::FLOATINGPOINT_TYPE ? *r : *l);
  }
  requireSamePublicSort("vc_fpEqExpr", bm, *l, *r);

  stp::ASTNode output = bm->CreateNode(stp::FP_EQ, *l, *r);
  assert(BVTypeCheck(output));
  return persistNode(vc, output);
}

// A floating-point operation returns a value of the same format as its
// operands, so the result node carries the format taken from `fmt` (as the
// parser's setFPFormat does).
//
// Through withFormat, because the operation need not have produced a node of
// its own kind: the factory folds (fp.min x x) to x, (fp.mul rm x 1.0) to x,
// (fp.neg (fp.neg x)) to x, and so hands back an operand that is already a
// float of exactly this format and may be of any kind at all -- an ite, an
// array read, a symbol, a constant. Stamping such a node is unnecessary, and
// on a bitvector-kind interior node it is forbidden (SetExpWidth asserts):
// the format is per-node state and nodes are hash-consed, so it would retype
// every other use of the same bits. withFormat knows when the stamp is
// needed and where it can go.
static Expr fpTermResult(VC vc, stp::Kind k, const stp::ASTNode& fmt,
                         const stp::ASTVec& children)
{
  stp::STPMgr* b = ((stp::STP*)vc)->bm;
  if (fmt.GetSourceSort().kind() != stp::SourceSort::Kind::FloatingPoint)
  {
    stp::FatalError("CInterface: floating-point operation applied to a "
                    "non-float operand: ",
                    fmt);
  }

  // Every operation built through this helper has only floating-point value
  // operands, except that rounded operations carry their RoundingMode first.
  // Check the complete public signature here, in ordinary Release code.  The
  // assertion below protects STP's internal construction; it is not an API
  // contract check because Release deliberately compiles it out.
  size_t first_float = 0;
  switch (k)
  {
    case stp::FP_ADD:
    case stp::FP_SUB:
    case stp::FP_MUL:
    case stp::FP_DIV:
    case stp::FP_FMA:
    case stp::FP_SQRT:
    case stp::FP_ROUNDTOINTEGRAL:
      first_float = 1;
      break;
    default:
      break;
  }
  for (size_t i = first_float; i < children.size(); i++)
    requireSamePublicSort("floating-point operation", b, fmt, children[i]);

  stp::ASTNode r = stp::FloatBlaster::withFormat(
      b, b->CreateTerm(k, fmt.GetValueWidth(), children), fmt.GetExpWidth(),
      fmt.GetSigWidth());
  assert(BVTypeCheck(r));
  assert(r.GetType() == stp::FLOATINGPOINT_TYPE);
  return persistNode(vc, r);
}

// A floating-point predicate returns a Boolean and carries no format.
static Expr fpPredResult(VC vc, stp::Kind k, const stp::ASTVec& children)
{
  stp::STPMgr* b = ((stp::STP*)vc)->bm;
  if (children.empty() ||
      children[0].GetSourceSort().kind() !=
          stp::SourceSort::Kind::FloatingPoint)
  {
    stp::FatalError("CInterface: floating-point predicate requires a "
                    "floating-point operand");
  }
  for (size_t i = 1; i < children.size(); i++)
    requireSamePublicSort("floating-point predicate", b, children[0],
                          children[i]);

  stp::ASTNode r = b->CreateNode(k, children);
  assert(BVTypeCheck(r));
  return persistNode(vc, r);
}

Expr vc_fpRoundingMode(VC vc, enum VCRoundingMode mode)
{
  stp::STPMgr* b = ((stp::STP*)vc)->bm;

  // The enum's values are one-hot (they mirror the internal encoding), so a
  // plausible-looking OR of two modes is not a mode; anything but the five
  // exact values would silently fall through symfpu's mode dispatch.
  switch (mode)
  {
    case VC_RM_RNE:
    case VC_RM_RTP:
    case VC_RM_RTN:
    case VC_RM_RTZ:
    case VC_RM_RNA:
      break;
    default:
      stp::FatalError("CInterface: vc_fpRoundingMode: not one of the five "
                      "rounding modes");
  }

  // A rounding mode is a 5-bit one-hot bitvector constant.
  return persistNode(vc, b->CreateRMConst((unsigned)mode));
}

Expr vc_fpRoundingModeVar(VC vc, const char* name)
{
  // Convenience for vc_varExpr over vc_fpRoundingModeType, which does the
  // real work: a 5-bit symbol pinned to the five one-hot encodings and
  // registered so counterexamples print its value by mode name. (Without
  // the constraint the carrier's 27 junk values would be satisfiable
  // "modes", which is also why a plain 5-bit vc_varExpr is no substitute.)
  return vc_varExpr(vc, name, vc_fpRoundingModeType(vc));
}

Expr vc_fpAbsExpr(VC vc, Expr f)
{
  stp::ASTNode* x = (stp::ASTNode*)f;
  return fpTermResult(vc, stp::FP_ABS, *x, {*x});
}

Expr vc_fpNegExpr(VC vc, Expr f)
{
  stp::ASTNode* x = (stp::ASTNode*)f;
  return fpTermResult(vc, stp::FP_NEG, *x, {*x});
}

Expr vc_fpAddExpr(VC vc, Expr rm, Expr a, Expr b)
{
  stp::ASTNode* m = (stp::ASTNode*)rm;
  stp::ASTNode* x = (stp::ASTNode*)a;
  stp::ASTNode* y = (stp::ASTNode*)b;
  checkRoundingMode("vc_fpAddExpr", ((stp::STP*)vc)->bm, *m);
  return fpTermResult(vc, stp::FP_ADD, *x, {*m, *x, *y});
}

Expr vc_fpSubExpr(VC vc, Expr rm, Expr a, Expr b)
{
  stp::ASTNode* m = (stp::ASTNode*)rm;
  stp::ASTNode* x = (stp::ASTNode*)a;
  stp::ASTNode* y = (stp::ASTNode*)b;
  checkRoundingMode("vc_fpSubExpr", ((stp::STP*)vc)->bm, *m);
  return fpTermResult(vc, stp::FP_SUB, *x, {*m, *x, *y});
}

Expr vc_fpMulExpr(VC vc, Expr rm, Expr a, Expr b)
{
  stp::ASTNode* m = (stp::ASTNode*)rm;
  stp::ASTNode* x = (stp::ASTNode*)a;
  stp::ASTNode* y = (stp::ASTNode*)b;
  checkRoundingMode("vc_fpMulExpr", ((stp::STP*)vc)->bm, *m);
  return fpTermResult(vc, stp::FP_MUL, *x, {*m, *x, *y});
}

Expr vc_fpDivExpr(VC vc, Expr rm, Expr a, Expr b)
{
  stp::ASTNode* m = (stp::ASTNode*)rm;
  stp::ASTNode* x = (stp::ASTNode*)a;
  stp::ASTNode* y = (stp::ASTNode*)b;
  checkRoundingMode("vc_fpDivExpr", ((stp::STP*)vc)->bm, *m);
  return fpTermResult(vc, stp::FP_DIV, *x, {*m, *x, *y});
}

Expr vc_fpFMAExpr(VC vc, Expr rm, Expr a, Expr b, Expr c)
{
  stp::ASTNode* m = (stp::ASTNode*)rm;
  stp::ASTNode* x = (stp::ASTNode*)a;
  stp::ASTNode* y = (stp::ASTNode*)b;
  stp::ASTNode* z = (stp::ASTNode*)c;
  checkRoundingMode("vc_fpFMAExpr", ((stp::STP*)vc)->bm, *m);
  return fpTermResult(vc, stp::FP_FMA, *x, {*m, *x, *y, *z});
}

Expr vc_fpSqrtExpr(VC vc, Expr rm, Expr f)
{
  stp::ASTNode* m = (stp::ASTNode*)rm;
  stp::ASTNode* x = (stp::ASTNode*)f;
  checkRoundingMode("vc_fpSqrtExpr", ((stp::STP*)vc)->bm, *m);
  return fpTermResult(vc, stp::FP_SQRT, *x, {*m, *x});
}

Expr vc_fpRoundToIntegralExpr(VC vc, Expr rm, Expr f)
{
  stp::ASTNode* m = (stp::ASTNode*)rm;
  stp::ASTNode* x = (stp::ASTNode*)f;
  checkRoundingMode("vc_fpRoundToIntegralExpr", ((stp::STP*)vc)->bm, *m);
  return fpTermResult(vc, stp::FP_ROUNDTOINTEGRAL, *x, {*m, *x});
}

Expr vc_fpRemExpr(VC vc, Expr a, Expr b)
{
  stp::ASTNode* x = (stp::ASTNode*)a;
  stp::ASTNode* y = (stp::ASTNode*)b;
  // A non-float operand gets its own diagnosis first (fpTermResult's, at
  // the end, comes too late): asking remSupported about a format of (0, 0)
  // underflows its step count and reported the format-limit message for
  // what is really a sort error.
  if (x->GetSourceSort().kind() != stp::SourceSort::Kind::FloatingPoint)
  {
    stp::FatalError("CInterface: vc_fpRemExpr: fp.rem applied to a "
                    "non-float operand: ",
                    *x);
  }
  // The remainder circuit's unrolling is exponential in the exponent width;
  // refuse at term creation, where the caller can see it, rather than
  // during solving (the parser does the same for SMT-LIB input).
  if (!stp::FloatBlaster::remSupported(x->GetExpWidth(), x->GetSigWidth()))
  {
    stp::FatalError("CInterface: vc_fpRemExpr: fp.rem is not supported at "
                    "this format: its circuit unrolls one divide step per "
                    "representable exponent difference, which is exponential "
                    "in the exponent width; use a format no larger than "
                    "binary64");
  }
  return fpTermResult(vc, stp::FP_REM, *x, {*x, *y});
}

Expr vc_fpMinExpr(VC vc, Expr a, Expr b)
{
  stp::ASTNode* x = (stp::ASTNode*)a;
  stp::ASTNode* y = (stp::ASTNode*)b;
  return fpTermResult(vc, stp::FP_MIN, *x, {*x, *y});
}

Expr vc_fpMaxExpr(VC vc, Expr a, Expr b)
{
  stp::ASTNode* x = (stp::ASTNode*)a;
  stp::ASTNode* y = (stp::ASTNode*)b;
  return fpTermResult(vc, stp::FP_MAX, *x, {*x, *y});
}

Expr vc_fpLtExpr(VC vc, Expr a, Expr b)
{
  return fpPredResult(vc, stp::FP_LT, {*(stp::ASTNode*)a, *(stp::ASTNode*)b});
}

Expr vc_fpLeqExpr(VC vc, Expr a, Expr b)
{
  return fpPredResult(vc, stp::FP_LEQ, {*(stp::ASTNode*)a, *(stp::ASTNode*)b});
}

Expr vc_fpGtExpr(VC vc, Expr a, Expr b)
{
  return fpPredResult(vc, stp::FP_GT, {*(stp::ASTNode*)a, *(stp::ASTNode*)b});
}

Expr vc_fpGeqExpr(VC vc, Expr a, Expr b)
{
  return fpPredResult(vc, stp::FP_GEQ, {*(stp::ASTNode*)a, *(stp::ASTNode*)b});
}

Expr vc_fpIsNormalExpr(VC vc, Expr f)
{
  return fpPredResult(vc, stp::FP_ISNORMAL, {*(stp::ASTNode*)f});
}

Expr vc_fpIsSubnormalExpr(VC vc, Expr f)
{
  return fpPredResult(vc, stp::FP_ISSUBNORMAL, {*(stp::ASTNode*)f});
}

Expr vc_fpIsZeroExpr(VC vc, Expr f)
{
  return fpPredResult(vc, stp::FP_ISZERO, {*(stp::ASTNode*)f});
}

Expr vc_fpIsInfiniteExpr(VC vc, Expr f)
{
  return fpPredResult(vc, stp::FP_ISINFINITE, {*(stp::ASTNode*)f});
}

Expr vc_fpIsNaNExpr(VC vc, Expr f)
{
  return fpPredResult(vc, stp::FP_ISNAN, {*(stp::ASTNode*)f});
}

Expr vc_fpIsNegativeExpr(VC vc, Expr f)
{
  return fpPredResult(vc, stp::FP_ISNEGATIVE, {*(stp::ASTNode*)f});
}

Expr vc_fpIsPositiveExpr(VC vc, Expr f)
{
  return fpPredResult(vc, stp::FP_ISPOSITIVE, {*(stp::ASTNode*)f});
}

// Extract (eb, sb) from a floating-point type node (see vc_fpType).
static void fpTypeWidths(Type fpType, unsigned& eb, unsigned& sb)
{
  stp::ASTNode* t = (stp::ASTNode*)fpType;
  if (t->GetKind() != stp::FLOATINGPOINT)
  {
    // Reading children of, say, a bitvector type would index out of bounds.
    stp::FatalError("CInterface: expected a floating-point type "
                    "(from vc_fpType): ",
                    *t);
  }
  eb = (*t)[0].GetUnsignedConst();
  sb = (*t)[1].GetUnsignedConst();
}

static Expr fpSpecial(VC vc, stp::FPSpecial which, Type fpType)
{
  stp::STPMgr* b = ((stp::STP*)vc)->bm;
  unsigned eb, sb;
  fpTypeWidths(fpType, eb, sb);
  return persistNode(vc, b->CreateFPSpecialConst(which, eb, sb));
}

Expr vc_fpNaN(VC vc, Type fpType)
{
  return fpSpecial(vc, stp::FPSpecial::NaN, fpType);
}
Expr vc_fpPlusInfinity(VC vc, Type fpType)
{
  return fpSpecial(vc, stp::FPSpecial::PlusInfinity, fpType);
}
Expr vc_fpMinusInfinity(VC vc, Type fpType)
{
  return fpSpecial(vc, stp::FPSpecial::MinusInfinity, fpType);
}
Expr vc_fpPlusZero(VC vc, Type fpType)
{
  return fpSpecial(vc, stp::FPSpecial::PlusZero, fpType);
}
Expr vc_fpMinusZero(VC vc, Type fpType)
{
  return fpSpecial(vc, stp::FPSpecial::MinusZero, fpType);
}

// Build a to_fp node: the (eb,sb) width children the blaster reads, an
// optional rounding mode, then the source. The result is a float of (eb, sb).
// `k` is FP_TOFP for the bits and float-to-float forms and FP_TOFP_SIGNED for
// the integer one. SMT-LIB spells all three `to_fp` and tells them apart by
// the source's sort, but a float is carried as its packed bits, so the sort
// stops being readable the moment the source is lowered. Each entry point
// below knows which operation the caller asked for; the kind records it.
static Expr fpToFP(VC vc, stp::Kind k, int eb, int sb, const stp::ASTNode* rm,
                   const stp::ASTNode& src)
{
  stp::STPMgr* b = ((stp::STP*)vc)->bm;
  checkFpWidths(eb, sb);

  const bool expects_float = k == stp::FP_TOFP && rm != NULL;
  const stp::SourceSort::Kind source_kind = src.GetSourceSort().kind();
  if ((expects_float &&
       source_kind != stp::SourceSort::Kind::FloatingPoint) ||
      (!expects_float && source_kind != stp::SourceSort::Kind::BitVector))
  {
    stp::FatalError(expects_float
                        ? "CInterface: float-to-float conversion requires a "
                          "floating-point source: "
                        : "CInterface: bitvector-to-float conversion requires "
                          "a bitvector source: ",
                    src);
  }

  stp::ASTVec kids;
  kids.push_back(b->CreateBVConst(32, eb));
  kids.push_back(b->CreateBVConst(32, sb));
  if (rm != NULL)
  {
    // Covers vc_fpToFPFrom{FP,SignedBV,UnsignedBV} and, through them,
    // vc_fpConstFrom{Double,Float}. The bits form takes no mode at all.
    checkRoundingMode("to_fp", b, *rm);
    kids.push_back(*rm);
  }
  kids.push_back(src);
  // withFormat rather than a bare stamp, for the reason fpTermResult gives:
  // what comes back need not be a fresh to_fp node.
  stp::ASTNode r =
      stp::FloatBlaster::withFormat(b, b->CreateTerm(k, eb + sb, kids), eb, sb);
  return persistNode(vc, r);
}

Expr vc_fpToFPFromIEEEBV(VC vc, int eb, int sb, Expr bv)
{
  return fpToFP(vc, stp::FP_TOFP, eb, sb, NULL, *(stp::ASTNode*)bv);
}

Expr vc_fpToFPFromFP(VC vc, int eb, int sb, Expr rm, Expr f)
{
  return fpToFP(vc, stp::FP_TOFP, eb, sb, (stp::ASTNode*)rm, *(stp::ASTNode*)f);
}

Expr vc_fpToFPFromSignedBV(VC vc, int eb, int sb, Expr rm, Expr bv)
{
  return fpToFP(vc, stp::FP_TOFP_SIGNED, eb, sb, (stp::ASTNode*)rm,
                *(stp::ASTNode*)bv);
}

Expr vc_fpToFPFromUnsignedBV(VC vc, int eb, int sb, Expr rm, Expr bv)
{
  // Through fpToFP like its signed sibling. It used to carry its own copy of
  // that body -- identical but for the kind -- and so was the one to_fp form
  // that never checked its rounding mode.
  return fpToFP(vc, stp::FP_TOFP_UNSIGNED, eb, sb, (stp::ASTNode*)rm,
                *(stp::ASTNode*)bv);
}

// fp.to_ubv / fp.to_sbv: a float in, a `width`-bit bitvector out. The result is
// a bitvector, so it carries no floating-point format.
static Expr fpToBV(VC vc, stp::Kind k, int width, const stp::ASTNode& rm,
                   const stp::ASTNode& f)
{
  stp::STPMgr* b = ((stp::STP*)vc)->bm;
  if (width < 1)
  {
    stp::FatalError("CInterface: fp.to_ubv/fp.to_sbv need a positive "
                    "target width");
  }
  if (f.GetSourceSort().kind() != stp::SourceSort::Kind::FloatingPoint)
  {
    stp::FatalError("CInterface: fp.to_ubv/fp.to_sbv applied to a "
                    "non-float: ",
                    f);
  }
  checkRoundingMode("fp.to_ubv/fp.to_sbv", b, rm);
  stp::ASTVec kids;
  kids.push_back(b->CreateBVConst(32, width));
  kids.push_back(rm);
  kids.push_back(f);
  return persistNode(vc, b->CreateTerm(k, width, kids));
}

Expr vc_fpToUBVExpr(VC vc, int width, Expr rm, Expr f)
{
  return fpToBV(vc, stp::FP_TO_UBV, width, *(stp::ASTNode*)rm,
                *(stp::ASTNode*)f);
}

Expr vc_fpToSBVExpr(VC vc, int width, Expr rm, Expr f)
{
  return fpToBV(vc, stp::FP_TO_SBV, width, *(stp::ASTNode*)rm,
                *(stp::ASTNode*)f);
}

Expr vc_fpToIEEEBV(VC vc, Expr f)
{
  stp::STPMgr* b = ((stp::STP*)vc)->bm;
  stp::ASTNode* x = (stp::ASTNode*)f;
  if (x->GetSourceSort().kind() != stp::SourceSort::Kind::FloatingPoint)
  {
    stp::FatalError("CInterface: vc_fpToIEEEBV applied to a non-float: ", *x);
  }
  const unsigned width = x->GetExpWidth() + x->GetSigWidth();
  // The result is a bitvector (the packed bits), so it carries no fp format.
  return persistNode(vc, b->CreateTerm(stp::FP_TO_IEEE_BV, width, *x));
}

Expr vc_fpConstFromDouble(VC vc, Type target, Expr rm, double d)
{
  checkRoundingMode("vc_fpConstFromDouble", ((stp::STP*)vc)->bm,
                    *(stp::ASTNode*)rm);
  uint64_t bits;
  std::memcpy(&bits, &d, sizeof(bits)); // d is already IEEE-754 binary64
  Expr dbl =
      vc_fpConstFromBits(vc, 11, 53, vc_bvConstExprFromLL(vc, 64, bits));
  unsigned eb, sb;
  fpTypeWidths(target, eb, sb);
  if (eb == 11 && sb == 53)
    return dbl; // target is binary64: the reinterpret is exact
  return vc_fpToFPFromFP(vc, eb, sb, rm, dbl);
}

Expr vc_fpConstFromFloat(VC vc, Type target, Expr rm, float f)
{
  checkRoundingMode("vc_fpConstFromFloat", ((stp::STP*)vc)->bm,
                    *(stp::ASTNode*)rm);
  uint32_t bits;
  std::memcpy(&bits, &f, sizeof(bits)); // f is already IEEE-754 binary32
  Expr single =
      vc_fpConstFromBits(vc, 8, 24, vc_bvConstExprFromLL(vc, 32, bits));
  unsigned eb, sb;
  fpTypeWidths(target, eb, sb);
  if (eb == 8 && sb == 24)
    return single; // target is binary32: the reinterpret is exact
  return vc_fpToFPFromFP(vc, eb, sb, rm, single);
}

/////////////////////////////////////////////////////////////////////////////
// BOOLEAN EXPR Creation methods                                           //
/////////////////////////////////////////////////////////////////////////////
// The following functions create Boolean expressions.  The children
// provided as arguments must be of type Boolean.
Expr vc_trueExpr(VC vc)
{
  stp::STPMgr* b = mgr(vc);
  stp::ASTNode c = b->CreateNode(stp::TRUE);

  // if(cinterface_exprdelete_on) created_exprs.push_back(d);
  return wrap(c);
}

Expr vc_falseExpr(VC vc)
{
  stp::STPMgr* b = mgr(vc);
  stp::ASTNode c = b->CreateNode(stp::FALSE);

  // if(cinterface_exprdelete_on) created_exprs.push_back(d);
  return wrap(c);
}

Expr vc_notExpr(VC vc, Expr ccc)
{
  stp::STPMgr* b = mgr(vc);
  stp::ASTNode* a = (stp::ASTNode*)ccc;
  requireBooleanOperand("vc_notExpr", *a);

  stp::ASTNode o = b->CreateNode(stp::NOT, *a);
  assert(BVTypeCheck(o));

  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return wrap(o);
}

Expr vc_andExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::AND, left, right);
}

Expr vc_orExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::OR, left, right);
}

Expr vc_xorExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::XOR, left, right);
}

Expr vc_nandExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::NAND, left, right);
}

Expr vc_norExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::NOR, left, right);
}

Expr vc_andExprN(VC vc, Expr* cc, int n)
{
  stp::STPMgr* b = mgr(vc);
  stp::ASTNode** c = (stp::ASTNode**)cc;
  assert(n > 0);

  stp::ASTVec d;
  for (int i = 0; i < n; i++)
  {
    requireBooleanOperand("vc_andExprN", *c[i]);
    d.push_back(*c[i]);
  }

  stp::ASTNode o = b->CreateNode(stp::AND, d);
  assert(BVTypeCheck(o));

  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return wrap(o);
}

Expr vc_orExprN(VC vc, Expr* cc, int n)
{
  stp::STPMgr* b = mgr(vc);
  stp::ASTNode** c = (stp::ASTNode**)cc;
  stp::ASTVec d;

  for (int i = 0; i < n; i++)
  {
    requireBooleanOperand("vc_orExprN", *c[i]);
    d.push_back(*c[i]);
  }

  stp::ASTNode o = b->CreateNode(stp::OR, d);
  assert(BVTypeCheck(o));

  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return wrap(o);
}

Expr vc_bvPlusExprN(VC vc, int n_bits, Expr* cc, int n)
{
  stp::STPMgr* b = mgr(vc);
  stp::ASTNode** c = (stp::ASTNode**)cc;
  stp::ASTVec d;

  for (int i = 0; i < n; i++)
  {
    requireBitVectorOperand("vc_bvPlusExprN", *c[i]);
    d.push_back(*c[i]);
  }

  stp::ASTNode o = b->CreateTerm(stp::BVPLUS, n_bits, d);
  assert(BVTypeCheck(o));

  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return wrap(o);
}

Expr vc_iteExpr(VC vc, Expr cond, Expr thenpart, Expr elsepart)
{
  stp::STPMgr* b = mgr(vc);
  stp::ASTNode* c = (stp::ASTNode*)cond;
  stp::ASTNode* t = (stp::ASTNode*)thenpart;
  stp::ASTNode* e = (stp::ASTNode*)elsepart;

  assert(BVTypeCheck(*c));
  assert(BVTypeCheck(*t));
  assert(BVTypeCheck(*e));

  if (c->GetSourceSort().kind() != stp::SourceSort::Kind::Bool)
  {
    stp::FatalError("CInterface: vc_iteExpr requires a Boolean condition: ",
                    *c);
  }

  // Branches that BOTH claim to be floats must agree on the format: two
  // formats can share one packed width -- (8, 24) and (24, 8) are both 32
  // bits -- so the width checks cannot tell them apart, and the node would
  // derive whichever branch's format comes first (see deriveFPFormat) and
  // silently read the other branch's bits at it. Checked here, not only in
  // BVTypeCheck: the asserts above compile out of a release build, and a
  // constant condition folds the if-then-else to one branch before any
  // type check can see the pair. Covers arrays too, whose exponent and
  // significand widths carry the element's format. The general sort check
  // above rejects a float/BitVec pair even when their packed widths match.
  if (t->GetExpWidth() != 0 && e->GetExpWidth() != 0 &&
      (t->GetExpWidth() != e->GetExpWidth() ||
       t->GetSigWidth() != e->GetSigWidth()))
  {
    stp::FatalError("CInterface: vc_iteExpr: the then and else branches "
                    "differ in floating-point format: ",
                    *t);
  }
  requireSamePublicSort("vc_iteExpr", b, *t, *e);

  stp::ASTNode o;
  // if the user asks for a formula then produce a formula, else
  // prodcue a term
  if (stp::BOOLEAN_TYPE == t->GetType())
    o = b->CreateNode(stp::ITE, *c, *t, *e);
  else
  {
    o = b->CreateTerm(stp::ITE, t->GetValueWidth(), *c, *t, *e);
    o.SetIndexWidth(t->GetIndexWidth());
  }
  assert(BVTypeCheck(o));
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return wrap(o);
}

Expr vc_impliesExpr(VC vc, Expr antecedent, Expr consequent)
{
  return createBinaryNode(vc, stp::IMPLIES, antecedent, consequent);
}

Expr vc_iffExpr(VC vc, Expr e0, Expr e1)
{
  return createBinaryNode(vc, stp::IFF, e0, e1);
}

Expr vc_boolToBVExpr(VC vc, Expr form)
{
  stp::STPMgr* b = mgr(vc);
  stp::ASTNode* c = (stp::ASTNode*)form;
  requireBooleanOperand("vc_boolToBVExpr", *c);

  assert(BVTypeCheck(*c));
  if (!is_Form_kind(c->GetKind()))
  {
    stp::FatalError("CInterface: vc_BoolToBVExpr: "
                    "You have input a NON formula:",
                    *c);
  }

  stp::ASTNode o;
  stp::ASTNode one = b->CreateOneConst(1);
  stp::ASTNode zero = b->CreateZeroConst(1);
  o = b->CreateTerm(stp::ITE, 1, *c, one, zero);

  assert(BVTypeCheck(o));
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return wrap(o);
}

Expr vc_paramBoolExpr(VC vc, Expr boolvar, Expr parameter)
{
  stp::STPMgr* b = mgr(vc);
  stp::ASTNode* c = (stp::ASTNode*)boolvar;
  stp::ASTNode* t = (stp::ASTNode*)parameter;

  requireBooleanOperand("vc_paramBoolExpr", *c);
  requireBitVectorOperand("vc_paramBoolExpr", *t);

  assert(BVTypeCheck(*c));
  assert(BVTypeCheck(*t));

  if (stp::BVCONST != t->GetKind())
    stp::FatalError("vc_paramBoolExpr: the parameter must be a constant "
                    "bit-vector",
                    *t);

  stp::ASTNode o = b->NewParameterized_BooleanVar(*c, *t);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return wrap(o);
}

/////////////////////////////////////////////////////////////////////////////
// BITVECTOR EXPR Creation methods                                         //
/////////////////////////////////////////////////////////////////////////////
Type vc_bvType(VC vc, int num_bits)
{
  stp::STPMgr* b = mgr(vc);

  if (!(0 < num_bits))
  {
    stp::FatalError("CInterface: number of bits in a bvtype"
                    " must be a positive integer:",
                    b->CreateNode(stp::UNDEFINED));
  }

  stp::ASTNode e = b->CreateBVConst(32, num_bits);
  stp::ASTNode output = (b->CreateNode(stp::BITVECTOR, e));
  return persistNode(vc, output);
}

Type vc_bv32Type(VC vc)
{
  return vc_bvType(vc, 32);
}

int vc_getValueSize(VC /* vc */, Type type)
{
  std::pair<unsigned int, unsigned int> typeSizes(getTypeSizes(type));
  unsigned int valueWidth = typeSizes.first;
  return valueWidth;
}

int vc_getIndexSize(VC /* vc */, Type type)
{
  std::pair<unsigned int, unsigned int> typeSizes(getTypeSizes(type));
  unsigned int indexWidth = typeSizes.second;
  return indexWidth;
}

Expr vc_bvConstExprFromDecStr(VC vc, int width, const char* decimalInput)
{
  stp::STPMgr* b = mgr(vc);

  std::string str(decimalInput);
  stp::ASTNode n = b->CreateBVConst(str, 10, width);
  assert(BVTypeCheck(n));
  return wrap(n);
}

Expr vc_bvConstExprFromStr(VC vc, const char* binary_repr)
{
  stp::STPMgr* b = mgr(vc);

  stp::ASTNode n = b->CreateBVConst(binary_repr, 2);
  assert(BVTypeCheck(n));
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return wrap(n);
}

Expr vc_bvConstExprFromInt(VC vc, int n_bits, unsigned int value)
{
  stp::STPMgr* b = mgr(vc);

  if (n_bits <= 0)
  {
    printf("CInterface: vc_bvConstExprFromInt: "
           "Bit width must be positive, got %d.\n",
           n_bits);
    stp::FatalError("FatalError");
  }

  const uint64_t v = value;

  // The largest value representable in n_bits bits. Written as a branch
  // because the shift that computed it, 0xFF..FF >> (64 - n_bits), has an
  // operand that goes negative as soon as n_bits exceeds 64 -- undefined,
  // and on x86-64 the count is masked to six bits, so the bound collapsed
  // instead of growing: width 65 yielded a maximum of 1 and width 66 a
  // maximum of 3, rejecting constants that fit with room to spare.
  const uint64_t max_n_bits =
      (n_bits >= 64) ? UINT64_MAX : ((UINT64_C(1) << n_bits) - 1);

  if (v > max_n_bits)
  {
    printf("CInterface: vc_bvConstExprFromInt: "
           "Cannot construct a constant %" PRIu64 " in %d bits, "
           "the maximum is %" PRIu64 ".\n",
           v, n_bits, max_n_bits);
    stp::FatalError("FatalError");
  }
  stp::ASTNode n = b->CreateBVConst(n_bits, v);
  assert(BVTypeCheck(n));
  return persistNode(vc, n);
}

Expr vc_bvConstExprFromLL(VC vc, int n_bits, uint64_t value)
{
  stp::STPMgr* b = mgr(vc);

  stp::ASTNode n = b->CreateBVConst(n_bits, value);
  assert(BVTypeCheck(n));
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return wrap(n);
}

Expr vc_bvConcatExpr(VC vc, Expr left, Expr right)
{
  stp::STPMgr* b = mgr(vc);
  stp::ASTNode* l = (stp::ASTNode*)left;
  stp::ASTNode* r = (stp::ASTNode*)right;

  requireBitVectorOperand("vc_bvConcatExpr", *l);
  requireBitVectorOperand("vc_bvConcatExpr", *r);

  assert(BVTypeCheck(*l));
  assert(BVTypeCheck(*r));
  stp::ASTNode o = b->CreateTerm(
      stp::BVCONCAT, l->GetValueWidth() + r->GetValueWidth(), *l, *r);
  assert(BVTypeCheck(o));
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return wrap(o);
}

Expr createBinaryTerm(VC vc, int n_bits, Kind k, Expr left, Expr right)
{
  stp::STPMgr* b = mgr(vc);
  stp::ASTNode* l = (stp::ASTNode*)left;
  stp::ASTNode* r = (stp::ASTNode*)right;

  requireBitVectorOperand("bitvector operation", *l);
  requireBitVectorOperand("bitvector operation", *r);

  assert(BVTypeCheck(*l));
  assert(BVTypeCheck(*r));
  stp::ASTNode o = b->CreateTerm(k, n_bits, *l, *r);
  assert(BVTypeCheck(o));
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return wrap(o);
}

Expr vc_bvPlusExpr(VC vc, int n_bits, Expr left, Expr right)
{
  return createBinaryTerm(vc, n_bits, stp::BVPLUS, left, right);
}

Expr vc_bv32PlusExpr(VC vc, Expr left, Expr right)
{
  return vc_bvPlusExpr(vc, 32, left, right);
}

Expr vc_bvMinusExpr(VC vc, int n_bits, Expr left, Expr right)
{
  return createBinaryTerm(vc, n_bits, stp::BVSUB, left, right);
}

Expr vc_bv32MinusExpr(VC vc, Expr left, Expr right)
{
  return vc_bvMinusExpr(vc, 32, left, right);
}

Expr vc_bvMultExpr(VC vc, int n_bits, Expr left, Expr right)
{
  return createBinaryTerm(vc, n_bits, stp::BVMULT, left, right);
}

Expr vc_bvDivExpr(VC vc, int n_bits, Expr left, Expr right)
{
  return createBinaryTerm(vc, n_bits, stp::BVDIV, left, right);
}

Expr vc_bvModExpr(VC vc, int n_bits, Expr left, Expr right)
{
  return createBinaryTerm(vc, n_bits, stp::BVMOD, left, right);
}

Expr vc_bvRemExpr(VC vc, int n_bits, Expr left, Expr right)
{
  /*
   * bvurem gets mapped to BVMOD -- this is a wrapper to
   * allow for API consistency
   */
  return createBinaryTerm(vc, n_bits, stp::BVMOD, left, right);
}

Expr vc_sbvDivExpr(VC vc, int n_bits, Expr left, Expr right)
{
  return createBinaryTerm(vc, n_bits, stp::SBVDIV, left, right);
}

Expr vc_sbvModExpr(VC vc, int n_bits, Expr left, Expr right)
{
  return createBinaryTerm(vc, n_bits, stp::SBVMOD, left, right);
}

Expr vc_sbvRemExpr(VC vc, int n_bits, Expr left, Expr right)
{
  return createBinaryTerm(vc, n_bits, stp::SBVREM, left, right);
}

Expr vc_bv32MultExpr(VC vc, Expr left, Expr right)
{
  return vc_bvMultExpr(vc, 32, left, right);
}

Expr createBinaryNode(VC vc, Kind k, Expr left, Expr right)
{
  stp::STPMgr* b = mgr(vc);
  stp::ASTNode* l = (stp::ASTNode*)left;
  stp::ASTNode* r = (stp::ASTNode*)right;

  switch (k)
  {
    case stp::BVLT:
    case stp::BVLE:
    case stp::BVGT:
    case stp::BVGE:
    case stp::BVSLT:
    case stp::BVSLE:
    case stp::BVSGT:
    case stp::BVSGE:
    case stp::BVUADDO:
    case stp::BVSADDO:
    case stp::BVUMULO:
    case stp::BVSMULO:
    case stp::BVUSUBO:
    case stp::BVSSUBO:
      requireBitVectorOperand("bitvector predicate", *l);
      requireBitVectorOperand("bitvector predicate", *r);
      break;
    case stp::AND:
    case stp::OR:
    case stp::XOR:
    case stp::NAND:
    case stp::NOR:
    case stp::IMPLIES:
    case stp::IFF:
      requireBooleanOperand("Boolean connective", *l);
      requireBooleanOperand("Boolean connective", *r);
      break;
    default:
      break;
  }
  assert(BVTypeCheck(*l));
  assert(BVTypeCheck(*r));
  stp::ASTNode o = b->CreateNode(k, *l, *r);
  assert(BVTypeCheck(o));
  // if(cinterface_exprdelete_on)
  //  created_exprs.push_back(output);
  return wrap(o);
}

// unsigned comparators
Expr vc_bvLtExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::BVLT, left, right);
}
Expr vc_bvLeExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::BVLE, left, right);
}
Expr vc_bvGtExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::BVGT, left, right);
}
Expr vc_bvGeExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::BVGE, left, right);
}
// signed comparators
Expr vc_sbvLtExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::BVSLT, left, right);
}
Expr vc_sbvLeExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::BVSLE, left, right);
}
Expr vc_sbvGtExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::BVSGT, left, right);
}
Expr vc_sbvGeExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::BVSGE, left, right);
}

// overflow predicates
Expr vc_bvUnsignedAddOverflowExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::BVUADDO, left, right);
}
Expr vc_bvSignedAddOverflowExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::BVSADDO, left, right);
}
Expr vc_bvUnsignedSubOverflowExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::BVUSUBO, left, right);
}
Expr vc_bvSignedSubOverflowExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::BVSSUBO, left, right);
}
Expr vc_bvUnsignedMulOverflowExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::BVUMULO, left, right);
}
Expr vc_bvSignedMulOverflowExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::BVSMULO, left, right);
}

Expr vc_bvLeftShiftExprExpr(VC vc, int n_bits, Expr left, Expr right)
{
  return createBinaryTerm(vc, n_bits, stp::BVLEFTSHIFT, left, right);
}

Expr vc_bvRightShiftExprExpr(VC vc, int n_bits, Expr left, Expr right)
{
  return createBinaryTerm(vc, n_bits, stp::BVRIGHTSHIFT, left, right);
}

Expr vc_bvSignedRightShiftExprExpr(VC vc, int n_bits, Expr left, Expr right)
{
  return createBinaryTerm(vc, n_bits, stp::BVSRSHIFT, left, right);
}

Expr vc_bvUMinusExpr(VC vc, Expr ccc)
{
  stp::STPMgr* b = mgr(vc);

  stp::ASTNode* a = (stp::ASTNode*)ccc;
  requireBitVectorOperand("vc_bvUMinusExpr", *a);
  assert(BVTypeCheck(*a));

  stp::ASTNode o = b->CreateTerm(stp::BVUMINUS, a->GetValueWidth(), *a);
  assert(BVTypeCheck(o));
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return wrap(o);
}

// Expr createBinaryTerm(VC vc, int n_bits, Kind k, Expr left, Expr right){

// bitwise operations: these are terms not formulas
Expr vc_bvAndExpr(VC vc, Expr left, Expr right)
{
  return createBinaryTerm(vc, (*((stp::ASTNode*)left)).GetValueWidth(),
                          stp::BVAND, left, right);
}

Expr vc_bvOrExpr(VC vc, Expr left, Expr right)
{
  return createBinaryTerm(vc, (*((stp::ASTNode*)left)).GetValueWidth(),
                          stp::BVOR, left, right);
}

Expr vc_bvXorExpr(VC vc, Expr left, Expr right)
{
  return createBinaryTerm(vc, (*((stp::ASTNode*)left)).GetValueWidth(),
                          stp::BVXOR, left, right);
}

/*
 * The bitwise nand/nor/xnor below are built as a negated and/or/xor rather
 * than as the BVNAND/BVNOR/BVXNOR kinds their names suggest. Those kinds are
 * vestigial: no parser produces them -- the SMT-LIB2 grammar expands bvnand,
 * bvnor and bvxnor exactly this way, see lib/Parser/smt2.y -- so while the
 * bit-blaster handles them, constant folding (BVConstEvaluator) and printing
 * (functionToSMTLIBName has no BVXNOR) do not. Building them here would make
 * those kinds reachable for the first time and abort on a constant operand.
 */
static Expr createNegatedBinaryTerm(VC vc, Kind k, Expr left, Expr right)
{
  stp::STPMgr* b = mgr(vc);
  stp::ASTNode* l = (stp::ASTNode*)left;
  stp::ASTNode* r = (stp::ASTNode*)right;

  requireBitVectorOperand("bitvector operation", *l);
  requireBitVectorOperand("bitvector operation", *r);

  assert(BVTypeCheck(*l));
  assert(BVTypeCheck(*r));

  const unsigned int width = l->GetValueWidth();
  stp::ASTNode o =
      b->CreateTerm(stp::BVNOT, width, b->CreateTerm(k, width, *l, *r));
  assert(BVTypeCheck(o));
  return wrap(o);
}

Expr vc_bvNandExpr(VC vc, Expr left, Expr right)
{
  return createNegatedBinaryTerm(vc, stp::BVAND, left, right);
}

Expr vc_bvNorExpr(VC vc, Expr left, Expr right)
{
  return createNegatedBinaryTerm(vc, stp::BVOR, left, right);
}

Expr vc_bvXnorExpr(VC vc, Expr left, Expr right)
{
  return createNegatedBinaryTerm(vc, stp::BVXOR, left, right);
}

Expr vc_bvNotExpr(VC vc, Expr ccc)
{
  stp::STPMgr* b = mgr(vc);
  stp::ASTNode* a = (stp::ASTNode*)ccc;

  requireBitVectorOperand("vc_bvNotExpr", *a);
  assert(BVTypeCheck(*a));
  stp::ASTNode o = b->CreateTerm(stp::BVNOT, a->GetValueWidth(), *a);
  assert(BVTypeCheck(o));
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return wrap(o);
}

Expr vc_bvLeftShiftExpr(VC vc, int sh_amt, Expr ccc)
{
  stp::STPMgr* b = mgr(vc);
  stp::ASTNode* a = (stp::ASTNode*)ccc;
  requireBitVectorOperand("vc_bvLeftShiftExpr", *a);
  assert(BVTypeCheck(*a));

  // convert leftshift to bvconcat
  if (0 != sh_amt)
  {
    stp::ASTNode len = b->CreateBVConst(sh_amt, 0);
    stp::ASTNode o =
        b->CreateTerm(stp::BVCONCAT, a->GetValueWidth() + sh_amt, *a, len);
    assert(BVTypeCheck(o));
    // if(cinterface_exprdelete_on) created_exprs.push_back(output);
    return wrap(o);
  }
  else
    return a;
}

Expr vc_bvRightShiftExpr(VC vc, int sh_amt, Expr ccc)
{
  stp::STPMgr* b = mgr(vc);
  stp::ASTNode* a = (stp::ASTNode*)ccc;
  requireBitVectorOperand("vc_bvRightShiftExpr", *a);
  assert(BVTypeCheck(*a));

  unsigned int w = a->GetValueWidth();
  // the amount by which you are rightshifting
  // is less-than/equal-to the length of input
  // bitvector
  if (0 < (unsigned)sh_amt && (unsigned)sh_amt < w)
  {
    stp::ASTNode len = b->CreateBVConst(sh_amt, 0);
    stp::ASTNode hi = b->CreateBVConst(32, w - 1);
    stp::ASTNode low = b->CreateBVConst(32, sh_amt);
    stp::ASTNode extract =
        b->CreateTerm(stp::BVEXTRACT, w - sh_amt, *a, hi, low);

    stp::ASTNode n = b->CreateTerm(stp::BVCONCAT, w, len, extract);
    BVTypeCheck(n);
    // if(cinterface_exprdelete_on) created_exprs.push_back(output);
    return wrap(n);
  }
  else if ((unsigned)sh_amt == w)
  {
    return wrap(b->CreateBVConst(w, 0));
  }
  else if (sh_amt == 0)
    return a;
  else
  {
    if (0 == w)
    {
      stp::FatalError("CInterface: vc_bvRightShiftExpr: "
                      "cannot have a bitvector of length 0:",
                      *a);
    }
    // if(cinterface_exprdelete_on) created_exprs.push_back(output);
    return wrap(b->CreateBVConst(w, 0));
  }
}

/* Same as vc_bvLeftShift only that the answer in 32 bits long */
Expr vc_bv32LeftShiftExpr(VC vc, int sh_amt, Expr child)
{
  return vc_bvExtract(vc, vc_bvLeftShiftExpr(vc, sh_amt, child), 31, 0);
}

/* Same as vc_bvRightShift only that the answer in 32 bits long */
Expr vc_bv32RightShiftExpr(VC vc, int sh_amt, Expr child)
{
  return vc_bvExtract(vc, vc_bvRightShiftExpr(vc, sh_amt, child), 31, 0);
}

Expr vc_bvVar32LeftShiftExpr(VC vc, Expr sh_amt, Expr child)
{
  Expr ifpart;
  Expr thenpart;
  Expr elsepart = vc_trueExpr(vc);
  Expr ite = vc_trueExpr(vc);
  int child_width = vc_getBVLength(vc, child);
  int shift_width = vc_getBVLength(vc, sh_amt);

  assert(child_width > 0);

  for (int count = 32; count >= 0; count--)
  {
    if (count != 32)
    {
      ifpart =
          vc_eqExpr(vc, sh_amt, vc_bvConstExprFromInt(vc, shift_width, count));
      thenpart = vc_bvExtract(vc, vc_bvLeftShiftExpr(vc, count, child),
                              child_width - 1, 0);

      ite = vc_iteExpr(vc, ifpart, thenpart, elsepart);
      elsepart = ite;
    }
    else
    {
      elsepart = vc_bvConstExprFromInt(vc, child_width, 0);
    }
  }
  return ite;
}

Expr vc_bvVar32DivByPowOfTwoExpr(VC vc, Expr child, Expr rhs)
{
  Expr ifpart;
  Expr thenpart;
  Expr elsepart = vc_trueExpr(vc);
  Expr ite = vc_trueExpr(vc);

  for (int count = 32; count >= 0; count--)
  {
    if (count != 32)
    {
      ifpart = vc_eqExpr(vc, rhs, vc_bvConstExprFromInt(vc, 32, 1 << count));
      thenpart = vc_bvRightShiftExpr(vc, count, child);
      ite = vc_iteExpr(vc, ifpart, thenpart, elsepart);
      elsepart = ite;
    }
    else
    {
      elsepart = vc_bvConstExprFromInt(vc, 32, 0);
    }
  }
  return ite;
}

Expr vc_bvVar32RightShiftExpr(VC vc, Expr sh_amt, Expr child)
{
  Expr ifpart;
  Expr thenpart;
  Expr elsepart = vc_trueExpr(vc);
  Expr ite = vc_trueExpr(vc);

  int child_width = vc_getBVLength(vc, child);
  int shift_width = vc_getBVLength(vc, sh_amt);

  assert(child_width > 0);

  for (int count = 32; count >= 0; count--)
  {
    if (count != 32)
    {
      ifpart =
          vc_eqExpr(vc, sh_amt, vc_bvConstExprFromInt(vc, shift_width, count));
      thenpart = vc_bvRightShiftExpr(vc, count, child);
      ite = vc_iteExpr(vc, ifpart, thenpart, elsepart);
      elsepart = ite;
    }
    else
    {
      elsepart = vc_bvConstExprFromInt(vc, child_width, 0);
    }
  }
  return ite;
}

Expr vc_bvExtract(VC vc, Expr ccc, int hi_num, int low_num)
{
  stp::STPMgr* b = mgr(vc);
  stp::ASTNode* a = (stp::ASTNode*)ccc;
  requireBitVectorOperand("vc_bvExtract", *a);
  BVTypeCheck(*a);

  stp::ASTNode hi = b->CreateBVConst(32, hi_num);
  stp::ASTNode low = b->CreateBVConst(32, low_num);
  stp::ASTNode o =
      b->CreateTerm(stp::BVEXTRACT, hi_num - low_num + 1, *a, hi, low);
  BVTypeCheck(o);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return wrap(o);
}

Expr vc_bvBoolExtract(VC vc, Expr ccc, int bit_num)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* a = (stp::ASTNode*)ccc;
  requireBitVectorOperand("vc_bvBoolExtract", *a);
  BVTypeCheck(*a);

  stp::ASTNode bit = b->CreateBVConst(32, bit_num);
  // stp::ASTNode o = b->CreateNode(stp::BVGETBIT,*a,bit);
  stp::ASTNode zero = b->CreateBVConst(1, 0);
  stp::ASTNode oo = b->CreateTerm(stp::BVEXTRACT, 1, *a, bit, bit);
  stp::ASTNode o = b->CreateNode(stp::EQ, oo, zero);
  BVTypeCheck(o);
  stp::ASTNode* output = new stp::ASTNode(o);
  registerCExpression(output);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_bvBoolExtract_Zero(VC vc, Expr ccc, int bit_num)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* a = (stp::ASTNode*)ccc;
  requireBitVectorOperand("vc_bvBoolExtract_Zero", *a);
  BVTypeCheck(*a);

  stp::ASTNode bit = b->CreateBVConst(32, bit_num);
  // stp::ASTNode o = b->CreateNode(stp::BVGETBIT,*a,bit);
  stp::ASTNode zero = b->CreateBVConst(1, 0);
  stp::ASTNode oo = b->CreateTerm(stp::BVEXTRACT, 1, *a, bit, bit);
  stp::ASTNode o = b->CreateNode(stp::EQ, oo, zero);
  BVTypeCheck(o);
  stp::ASTNode* output = new stp::ASTNode(o);
  registerCExpression(output);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_bvBoolExtract_One(VC vc, Expr ccc, int bit_num)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* a = (stp::ASTNode*)ccc;
  requireBitVectorOperand("vc_bvBoolExtract_One", *a);
  BVTypeCheck(*a);

  stp::ASTNode bit = b->CreateBVConst(32, bit_num);
  // stp::ASTNode o = b->CreateNode(stp::BVGETBIT,*a,bit);
  stp::ASTNode one = b->CreateBVConst(1, 1);
  stp::ASTNode oo = b->CreateTerm(stp::BVEXTRACT, 1, *a, bit, bit);
  stp::ASTNode o = b->CreateNode(stp::EQ, oo, one);
  BVTypeCheck(o);
  stp::ASTNode* output = new stp::ASTNode(o);
  registerCExpression(output);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_bvSignExtend(VC vc, Expr ccc, int nbits)
{
  stp::STPMgr* b = mgr(vc);
  stp::ASTNode* a = (stp::ASTNode*)ccc;

  requireBitVectorOperand("vc_bvSignExtend", *a);

  // width of the expr which is being sign extended. nbits is the
  // resulting length of the signextended expr
  BVTypeCheck(*a);

  unsigned exprlen = a->GetValueWidth();
  unsigned outputlen = nbits;
  stp::ASTNode n;
  if (exprlen >= outputlen)
  {
    // extract
    stp::ASTNode hi = b->CreateBVConst(32, outputlen - 1);
    stp::ASTNode low = b->CreateBVConst(32, 0);
    n = b->CreateTerm(stp::BVEXTRACT, nbits, *a, hi, low);
    BVTypeCheck(n);
  }
  else
  {
    // sign extend
    stp::ASTNode width = b->CreateBVConst(32, nbits);
    n = b->CreateTerm(stp::BVSX, nbits, *a, width);
  }

  BVTypeCheck(n);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return wrap(n);
}

Expr vc_bvZeroExtend(VC vc, Expr ccc, int nbits)
{
  stp::STPMgr* b = mgr(vc);
  stp::ASTNode* a = (stp::ASTNode*)ccc;

  requireBitVectorOperand("vc_bvZeroExtend", *a);

  // width of the expr which is being zero extended. nbits is the
  // resulting length of the zeroextended expr
  BVTypeCheck(*a);

  if (nbits <= 0)
    stp::FatalError("vc_bvZeroExtend: the new width must be positive");

  unsigned exprlen = a->GetValueWidth();
  unsigned outputlen = nbits;
  stp::ASTNode n;
  if (exprlen >= outputlen)
  {
    // extract
    stp::ASTNode hi = b->CreateBVConst(32, outputlen - 1);
    stp::ASTNode low = b->CreateBVConst(32, 0);
    n = b->CreateTerm(stp::BVEXTRACT, nbits, *a, hi, low);
  }
  else
  {
    // zero extend
    stp::ASTNode width = b->CreateBVConst(32, nbits);
    n = b->CreateTerm(stp::BVZX, nbits, *a, width);
  }

  BVTypeCheck(n);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return wrap(n);
}

//! Return an int from a constant bitvector expression
int getBVInt(Expr e)
{
  stp::ASTNode* a = (stp::ASTNode*)e;

  if (stp::BVCONST != a->GetKind())
  {
    stp::FatalError("CInterface: getBVInt: Attempting to "
                    "extract int value from a NON-constant BITVECTOR: ",
                    *a);
  }
  return (int)a->GetUnsignedConst();
}

//! Return an unsigned int from a constant bitvector expression
unsigned int getBVUnsigned(Expr e)
{
  stp::ASTNode* a = (stp::ASTNode*)e;

  if (stp::BVCONST != a->GetKind())
  {
    stp::FatalError("getBVUnsigned: Attempting to extract int "
                    "value from a NON-constant BITVECTOR: ",
                    *a);
  }
  return (unsigned int)a->GetUnsignedConst();
}

//! Return a uint64_t from a constant bitvector expression
uint64_t getBVUnsignedLongLong(Expr e)
{
  stp::ASTNode* a = (stp::ASTNode*)e;

  if (stp::BVCONST != a->GetKind())
    stp::FatalError("getBVUnsigned: Attempting to extract int value"
                    "from a NON-constant BITVECTOR: ",
                    *a);
  unsigned* bv = a->GetBVConst();

  char* str_bv = (char*)CONSTANTBV::BitVector_to_Bin(bv);
  uint64_t tmp = std::strtoull(str_bv, NULL, 2);
  CONSTANTBV::BitVector_Dispose((unsigned char*)str_bv);
  return tmp;
}

void vc_printBVBitStringToBuffer(Expr e, char** buf, size_t* len)
{
  assert(buf);
  assert(len);

  // get the current value for the BV
  stp::ASTNode* a = (stp::ASTNode*)e;

  if (stp::BVCONST != a->GetKind())
    stp::FatalError("vc_printBVToBuffer: Attempting to extract bit string"
                    "from a NON-constant BITVECTOR: ",
                    *a);
  unsigned* bv = a->GetBVConst();

  // Convert it to a bit string
  char* char_bv = (char*)CONSTANTBV::BitVector_to_Bin(bv);

  // Ensure our bit string is allocated string
  assert(char_bv);

  // Convert the char* to a c-style string
  string string_bv(char_bv);

  // Free the char* bit string
  CONSTANTBV::BitVector_Dispose((unsigned char*)char_bv);

  // convert to a c buffer
  const char* cstr = string_bv.c_str();
  size_t size = string_bv.size() + 1; // number of chars + terminating null
  *buf = (char*)malloc(size);
  if (!(*buf))
  {
    fprintf(stderr, "malloc(%zu) failed.", size);
    assert(*buf);
  }
  *len = size;
  memcpy(*buf, cstr, size);
}

Expr vc_simplify(VC vc, Expr e)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::Simplifier* simp = (stp::Simplifier*)(stp_i->simp);
  stp::ASTNode* a = (stp::ASTNode*)e;

  // Simplification is a public entrance to the same source-level graph as
  // solving. Lower native distinct before the ordinary simplifier, then give
  // partial floating-point operations the internal child that makes their
  // otherwise-unspecified result a congruent total function. The solve paths
  // establish these same boundaries before preprocessing.
  const stp::ASTNode semantic =
      stp_i->bm->has_distinct ? stp::lowerDistinct(stp_i->bm, *a) : *a;
  stp::FpTotalise totalise(stp_i->bm);
  const stp::ASTNode totalised = totalise.topLevel(semantic);

  if (stp::BOOLEAN_TYPE == totalised.GetType())
  {
    stp::ASTNode* round1 =
        new stp::ASTNode(simp->SimplifyFormula_TopLevel(totalised, false));
    stp::ASTNode* output =
        new stp::ASTNode(simp->SimplifyFormula_TopLevel(*round1, false));
    delete round1;
    return registerCExpression(output);
  }
  else
  {
    stp::ASTNode* round1 = new stp::ASTNode(simp->SimplifyTerm(totalised));
    stp::ASTNode* output = new stp::ASTNode(simp->SimplifyTerm(*round1));
    delete round1;
    return registerCExpression(output);
  }
}

/* C pointer support: C interface to support C memory arrays in CVCL */
Expr vc_bvCreateMemoryArray(VC vc, const char* arrayName)
{
  Type bv8 = vc_bvType(vc, 8);
  Type bv32 = vc_bvType(vc, 32);

  Type malloced_mem0 = vc_arrayType(vc, bv32, bv8);
  return vc_varExpr(vc, arrayName, malloced_mem0);
}

Expr vc_bvReadMemoryArray(VC vc, Expr array, Expr byteIndex, int numOfBytes)
{
  if (!(numOfBytes > 0))
    stp::FatalError("numOfBytes must be greater than 0");

  if (numOfBytes == 1)
    return vc_readExpr(vc, array, byteIndex);
  else
  {
    int count = 1;
    Expr a = vc_readExpr(vc, array, byteIndex);
    while (--numOfBytes > 0)
    {
      Expr b = vc_readExpr(vc, array,
                           /*vc_simplify(vc, */
                           vc_bvPlusExpr(vc, 32, byteIndex,
                                         vc_bvConstExprFromInt(vc, 32, count)));
      a = vc_bvConcatExpr(vc, b, a);
      count++;
    }
    return a;
  }
}

Expr vc_bvWriteToMemoryArray(VC vc, Expr array, Expr byteIndex, Expr element,
                             int numOfBytes)
{
  if (!(numOfBytes > 0))
    stp::FatalError("numOfBytes must be greater than 0");

  if (numOfBytes == 1)
    return vc_writeExpr(vc, array, byteIndex, element);
  else
  {
    int count = 1;
    int low_elem = 0;
    int hi_elem = low_elem + 7;
    Expr c = vc_bvExtract(vc, element, hi_elem, low_elem);
    Expr newarray = vc_writeExpr(vc, array, byteIndex, c);
    while (--numOfBytes > 0)
    {
      low_elem = low_elem + 8;
      hi_elem = low_elem + 7;

      c = vc_bvExtract(vc, element, hi_elem, low_elem);
      newarray = vc_writeExpr(
          vc, newarray, vc_bvPlusExpr(vc, 32, byteIndex,
                                      vc_bvConstExprFromInt(vc, 32, count)),
          c);
      count++;
    }
    return newarray;
  }
}

Expr vc_bv32ConstExprFromInt(VC vc, unsigned int value)
{
  return vc_bvConstExprFromInt(vc, 32, value);
}

Expr vc_parseExpr(VC vc, const char* infile)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;

  extern FILE *cvcin, *smtin;
  cvcin = fopen(infile, "r");
  if (cvcin == NULL)
  {
    fprintf(stderr, "STP: Error: cannot open %s\n", infile);
    stp::FatalError("Cannot open file");
    return 0;
  }

  CONSTANTBV::ErrCode c = CONSTANTBV::BitVector_Boot();
  if (0 != c)
  {
    cout << CONSTANTBV::BitVector_Error(c) << endl;
    return 0;
  }

  stp::Cpp_interface cpp_inter(*b, b->defaultNodeFactory);
  stp::GlobalParserInterface = &cpp_inter;

  stp::ASTVec* AssertsQuery = new stp::ASTVec;
  if (b->UserFlags.smtlib1_parser_flag)
  {
    smtin = cvcin;
    cvcin = NULL;
    stp::GlobalSTP = stp_i;
    stp::GlobalParserBM = b;
    smtparse((void*)AssertsQuery);
    stp::GlobalSTP = NULL;
    stp::GlobalParserBM = NULL;
  }
  else
  {
    stp::GlobalSTP = stp_i;
    stp::GlobalParserBM = b;
    stp::GlobalParserInterface->letMgr->frameMode = false;
    cvcparse((void*)AssertsQuery);
    stp::GlobalSTP = NULL;
    stp::GlobalParserBM = NULL;
  }

  stp::ASTNode asserts = (*(stp::ASTVec*)AssertsQuery)[0];
  stp::ASTNode query = (*(stp::ASTVec*)AssertsQuery)[1];

  stp::ASTNode oo = b->CreateNode(stp::NOT, query);
  stp::ASTNode o = b->CreateNode(stp::AND, asserts, oo);
  stp::ASTNode* output = new stp::ASTNode(o);
  registerCExpression(output);
  delete AssertsQuery;

  // cpp_inter is about to go out of scope, so give back the global that
  // points at it. (~Cpp_interface does this too, for the paths that don't
  // reach here.)
  stp::GlobalParserInterface = NULL;
  return output;
}

char* exprString(Expr e)
{
  stringstream ss;
  ((stp::ASTNode*)e)->PL_Print(ss, 0);
  string s = ss.str();
  char* copy = strdup(s.c_str());
  return copy;
}

char* typeString(Type t)
{
  stringstream ss;
  ((stp::ASTNode*)t)->PL_Print(ss, 0);

  string s = ss.str();
  char* copy = strdup(s.c_str());
  return copy;
}

Expr getChild(Expr e, int i)
{
  stp::ASTNode* a = (stp::ASTNode*)e;

  const stp::ASTChildren c = a->GetChildren();
  if (0 <= i && (unsigned)i < c.size())
  {
    stp::ASTNode o = c[i];
    // if(cinterface_exprdelete_on) created_exprs.push_back(output);
    return wrap(o);
  }
  else
  {
    stp::FatalError("getChild: Error accessing childNode "
                    "in expression: ",
                    *a);
  }
}

void vc_registerErrorHandler(void (*error_hdlr)(const char* err_msg))
{
  stp::vc_error_hdlr = error_hdlr;
}

int vc_getHashQueryStateToBuffer(VC vc, Expr query)
{
  stp::STPMgr* b = mgr(vc);
  stp::ASTNode* qry = (stp::ASTNode*)query;
  assert(vc);
  assert(query);

  stp::ASTVec v = b->GetAsserts();
  stp::ASTNode out = b->CreateNode(stp::AND, b->CreateNode(stp::NOT, *qry), v);
  return out.Hash();
}

Type vc_getType(VC vc, Expr ex)
{
  stp::ASTNode* e = (stp::ASTNode*)ex;
  const stp::SourceSort sort = e->GetSourceSort();
  const auto scalar_type = [vc](const stp::SourceSort& scalar) -> Type {
    switch (scalar.kind())
    {
      case stp::SourceSort::Kind::BitVector:
        return vc_bvType(vc, scalar.bitVectorWidth());
      case stp::SourceSort::Kind::FloatingPoint:
        return vc_fpType(vc, scalar.exponentWidth(),
                         scalar.significandWidth());
      case stp::SourceSort::Kind::RoundingMode:
        return vc_fpRoundingModeType(vc);
      case stp::SourceSort::Kind::Uninterpreted:
        // No Type stands for a declared sort, and the C API cannot declare
        // one, so this is unreachable rather than unimplemented. Named so it
        // stays unreachable: reporting the carrier here would hand a caller a
        // bit-vector type for a sort that deliberately is not one.
        stp::FatalError("c_interface: vc_getType: a sort declared by "
                        "declare-sort has no C API type");
      default:
        stp::FatalError("c_interface: vc_GetType: expected scalar sort");
    }
  };

  switch (sort.kind())
  {
    case stp::SourceSort::Kind::Bool:
      return vc_boolType(vc);
    case stp::SourceSort::Kind::BitVector:
    case stp::SourceSort::Kind::FloatingPoint:
    case stp::SourceSort::Kind::RoundingMode:
      return scalar_type(sort);
    case stp::SourceSort::Kind::Array:
      return vc_arrayType(vc, scalar_type(sort.index()),
                          scalar_type(sort.element()));
    default:
      stp::FatalError("c_interface: vc_GetType: "
                      "expression with bad typing: "
                      "please check your expression construction");
      return vc_boolType(vc);
      break;
  }
}

//!if e is TRUE then return 1; if e is FALSE then return 0; otherwise
// return -1
int vc_isBool(Expr e)
{
  stp::ASTNode* input = (stp::ASTNode*)e;
  if (stp::TRUE == input->GetKind())
  {
    return 1;
  }

  if (stp::FALSE == input->GetKind())
  {
    return 0;
  }

  return -1;
}

void vc_Destroy(VC vc)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;

  if (b->UserFlags.cinterface_exprdelete_on_flag)
  {
    for (vector<stp::ASTNode*>::iterator it = b->persist.begin();
         it != b->persist.end(); it++)
      if (*it != NULL)
        vc_DeleteExpr(*it);
    b->persist.clear();
  }

  Cnf_ManFree();
  vc_clearDecls(vc);
  retireCContext(vc);
  stp_i->deleteObjects();

  // Never leave the global aimed at a dead manager.
  if (stp::GlobalParserBM == b)
    stp::GlobalParserBM = NULL;

  delete stp_i;
  if (b->defaultNodeFactory != b->hashingNodeFactory)
    delete b->defaultNodeFactory;
  delete b;
}

void vc_DeleteExpr(Expr e)
{
  if (e == NULL)
    return;
  stp::ASTNode* const node = static_cast<stp::ASTNode*>(e);
  // vc_DeleteExpr has always required a live raw pointer. Consulting its
  // manager here lets unrelated legacy contexts retain the lock-free path
  // even when another context in the process has enabled UF support.
  if (node->GetNodeManager()->UserFlags.enable_uninterpreted_functions)
  {
    std::lock_guard<std::mutex> lock(cHandleMutex);
    const std::unordered_map<Expr, CExpressionRecord>::iterator found =
        cExpressions.find(e);
    if (found != cExpressions.end())
    {
      const std::unordered_map<VC, CContextRecord>::iterator context =
          liveCContexts.find(found->second.owner);
      if (context != liveCContexts.end())
      {
        context->second.expressions.erase(e);
        // Context-managed handles also sit in STPMgr::persist. Mark the slot
        // empty so vc_Destroy never revisits a caller-deleted wrapper.
        if (context->second.manager->UserFlags.cinterface_exprdelete_on_flag)
          for (stp::ASTNode*& persisted : context->second.manager->persist)
            if (persisted == e)
            {
              persisted = NULL;
              break;
            }
      }
      cExpressions.erase(found);
      delete node;
      return;
    }
  }
  // A deleted Expr is no longer a valid C handle. The live registry makes UF
  // API validation nonfatal before deletion, but the legacy raw-pointer ABI
  // cannot distinguish a second delete from allocator address reuse without
  // retaining process-lifetime tombstones. Preserve the baseline ownership
  // contract here and release untracked wrappers immediately.
  delete node;
}

// exprkind_t mirrors stp::Kind, which is generated from ASTKind.kinds, and
// getExprKind is a raw cast -- so the two enums must stay in numeric
// lockstep. These anchors catch a kind added to one side but not the other.
static_assert((int)UNDEFINED == (int)stp::UNDEFINED, "exprkind_t drift");
static_assert((int)BVCONST == (int)stp::BVCONST, "exprkind_t drift");
static_assert((int)FP_ABS == (int)stp::FP_ABS, "exprkind_t drift");
static_assert((int)FP_TO_IEEE_BV == (int)stp::FP_TO_IEEE_BV,
              "exprkind_t drift");
static_assert((int)FP_SMT_EQ == (int)stp::FP_SMT_EQ, "exprkind_t drift");
static_assert((int)UF_APPLY == (int)stp::UF_APPLY, "exprkind_t drift");
static_assert((int)DISTINCT == (int)stp::DISTINCT, "exprkind_t drift");
static_assert((int)BOOLEAN_TYPE == (int)stp::BOOLEAN_TYPE &&
                  (int)FLOATINGPOINT_TYPE == (int)stp::FLOATINGPOINT_TYPE &&
                  (int)UNKNOWN_TYPE == (int)stp::UNKNOWN_TYPE,
              "type_t drift");

exprkind_t getExprKind(Expr e)
{
  stp::ASTNode* input = (stp::ASTNode*)e;
  // ARRAY_EQ is an internal, opaque representation of ordinary equality.
  // Do not expose a new C API enum value (or shift the stable existing ones).
  if (input->GetKind() == stp::ARRAY_EQ)
    return EQ;
  return (exprkind_t)(input->GetKind());
}

int getDegree(Expr e)
{
  stp::ASTNode* input = (stp::ASTNode*)e;
  return input->Degree();
}

int getBVLength(Expr ex)
{
  stp::ASTNode* e = (stp::ASTNode*)ex;

  if (e->GetSourceSort().kind() != stp::SourceSort::Kind::BitVector)
  {
    stp::FatalError("c_interface: vc_GetBVLength: "
                    "Input expression must be a bit-vector");
  }

  return e->GetValueWidth();
}

type_t getType(Expr ex)
{
  stp::ASTNode* e = (stp::ASTNode*)ex;
  switch (e->GetSourceSort().kind())
  {
    case stp::SourceSort::Kind::Bool:
      return BOOLEAN_TYPE;
    case stp::SourceSort::Kind::BitVector:
      return BITVECTOR_TYPE;
    case stp::SourceSort::Kind::Array:
      return ARRAY_TYPE;
    case stp::SourceSort::Kind::FloatingPoint:
      return FLOATINGPOINT_TYPE;
    case stp::SourceSort::Kind::RoundingMode:
      return ROUNDINGMODE_TYPE;
    case stp::SourceSort::Kind::Uninterpreted:
      // type_t has no enumerator for a sort declared by declare-sort, and
      // adding one changes a public enum. Unknown is the honest answer and is
      // also unreachable today, since the C API cannot declare such a sort;
      // stated as its own arm so it is a decision rather than a fall-through.
      return UNKNOWN_TYPE;
    default:
      return UNKNOWN_TYPE;
  }
}

int getVWidth(Expr ex)
{
  stp::ASTNode* e = (stp::ASTNode*)ex;
  return e->GetValueWidth();
}

int getIWidth(Expr ex)
{
  stp::ASTNode* e = (stp::ASTNode*)ex;
  return e->GetIndexWidth();
}

void vc_printCounterExampleFile(VC vc, int fd)
{
  materializePendingModel(vc);
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;

  stp::FdOStream os(fd);
  stp::AbsRefine_CounterExample* ce =
      (stp::AbsRefine_CounterExample*)(stp_i->Ctr_Example);

  bool currentPrint = b->UserFlags.print_counterexample_flag;
  b->UserFlags.print_counterexample_flag = true;
  os << "COUNTEREXAMPLE BEGIN: \n";
  ce->PrintCounterExample(true, os);
  os << "COUNTEREXAMPLE END: \n";
  b->UserFlags.print_counterexample_flag = currentPrint;
}

const char* exprName(Expr e)
{
  return ((stp::ASTNode*)e)->GetName();
}

uint64_t getExprID(Expr ex)
{
  stp::ASTNode q = (*(stp::ASTNode*)ex);
  return q.GetNodeNum();
}

void process_argument(const char ch, VC vc)
{
  stp::STPMgr* bm = mgr(vc);

  switch (ch)
  {
    case 'a':
      bm->UserFlags.optimize_flag = false;
      break;
    case 'c':
      bm->UserFlags.request_counterexample = true;
      break;
    case 'd':
      bm->UserFlags.request_counterexample = true;
      bm->UserFlags.check_counterexample_flag = true;
      break;

    case 'h':
      assert(0 && "This API is dumb, don't use it!");
      exit(-1);
      break;
    case 'i':
      // Incremental solving from the first vc_query on (it switches itself
      // on at the first vc_push even without this): one SAT solver and one
      // encoding live across queries, with the negated query and the
      // pushed levels' assertions assumed rather than re-encoded. See
      // docs/incremental-solving.rst.
      bm->UserFlags.incremental_mode =
          stp::UserDefinedFlags::IncrementalMode::ON;
      ((stp::STP*)vc)->incrementalFromStart = true;
      ((stp::STP*)vc)->sessionIncremental = true;
      break;
    case 'm':
      bm->UserFlags.smtlib1_parser_flag = true;
      if (bm->UserFlags.smtlib2_parser_flag)
        stp::FatalError("Can't use both the smtlib and smtlib2 parsers");
      break;
    case 'n':
      bm->UserFlags.print_output_flag = true;
      break;
    case 'p':
      bm->UserFlags.print_counterexample_flag = true;
      break;
    case 'q':
      bm->UserFlags.print_arrayval_declaredorder_flag = true;
      break;
    case 'r':
      bm->UserFlags.ackermannisation = true;
      break;
    case 's':
      bm->UserFlags.stats_flag = true;
      break;
    case 't':
      bm->UserFlags.quick_statistics_flag = true;
      break;
    case 'u':
      bm->UserFlags.enable_uninterpreted_functions = true;
      enableCExpressionTracking(vc);
      break;
    case 'v':
      bm->UserFlags.print_nodes_flag = true;
      break;
    case 'w':
      bm->UserFlags.wordlevel_solve_flag = false;
      break;
    case 'x':
      // Decide whole-array equality/disequality (the extensional
      // theory of arrays) with the lemmas-on-demand procedure of
      // Brummayer & Biere. This must be set before a whole-array equality
      // is built; construction preserves an opaque ARRAY_EQ until the
      // completed query is lowered at the solve boundary.
      bm->UserFlags.enable_array_equality = true;
      break;
    case 'y':
      bm->UserFlags.print_binary_flag = true;
      break;
    default:
      // fprintf(stderr,usage,prog);
      // cout << helpstring;
      assert(0 && "Unrecognised option");
      exit(-1);
      break;
  }
}

//////////////////////////////////////////////////////////////////////////
// extended version

int vc_parseMemExpr(VC vc, const char* s, Expr* oquery, Expr* oasserts)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;

  stp::Cpp_interface pi(*b, b->defaultNodeFactory);
  stp::GlobalParserInterface = &pi;

  stp::ASTVec AssertsQuery;
  if (b->UserFlags.smtlib1_parser_flag)
  {
    stp::GlobalSTP = stp_i;
    stp::GlobalParserBM = b;
    stp::SMTScanString(s);
    smtparse((void*)&AssertsQuery);
    stp::GlobalSTP = NULL;
    stp::GlobalParserBM = NULL;
  }
  else
  {
    stp::GlobalSTP = stp_i;
    stp::GlobalParserBM = b;
    stp::CVCScanString(s);
    cvcparse((void*)&AssertsQuery);
    stp::GlobalSTP = NULL;
    stp::GlobalParserBM = NULL;
  }

  if (oquery)
  {
    *(stp::ASTNode**)oquery = static_cast<stp::ASTNode*>(
        registerCExpression(new stp::ASTNode(AssertsQuery[1])));
  }
  if (oasserts)
  {
    *(stp::ASTNode**)oasserts = static_cast<stp::ASTNode*>(
        registerCExpression(new stp::ASTNode(AssertsQuery[0])));
  }

  // pi is about to go out of scope, so give back the global that points at
  // it. (~Cpp_interface does this too, for the paths that don't reach here.)
  stp::GlobalParserInterface = NULL;
  return 1;
}

void _vc_useSolver(VC vc, stp::UserDefinedFlags::SATSolvers solver)
{
  /* Helper method to encapsulate setting a solver */
  stp::STPMgr* b = mgr(vc);
  b->UserFlags.solver_to_use = solver;
}

bool _vc_isUsingSolver(VC vc, stp::UserDefinedFlags::SATSolvers solver)
{
  /* Helper method to encapsulate getting a solver */
  stp::STPMgr* b = mgr(vc);
  return b->UserFlags.solver_to_use == solver;
}

bool vc_supportsMinisat(VC /*vc*/)
{
#ifdef USE_MINISAT
  return true;
#else
  return false;
#endif
}

bool vc_useMinisat(VC
#ifdef USE_MINISAT
vc
#endif
)
{
#ifdef USE_MINISAT
  _vc_useSolver(vc, stp::UserDefinedFlags::MINISAT_SOLVER);
  return true;
#else
  return false;
#endif
}

bool vc_isUsingMinisat(VC
#ifdef USE_MINISAT
vc
#endif
)
{
#ifdef USE_MINISAT
  return _vc_isUsingSolver(vc, stp::UserDefinedFlags::MINISAT_SOLVER);
#else
  return false;
#endif
}

bool vc_supportsSimplifyingMinisat(VC /*vc*/)
{
#ifdef USE_MINISAT
  return true;
#else
  return false;
#endif
}

bool vc_useSimplifyingMinisat(VC
#ifdef USE_MINISAT
vc
#endif
)
{
#ifdef USE_MINISAT
  _vc_useSolver(vc, stp::UserDefinedFlags::SIMPLIFYING_MINISAT_SOLVER);
  return true;
#else
  return false;
#endif
}

bool vc_isUsingSimplifyingMinisat(VC
#ifdef USE_MINISAT
vc
#endif
)
{
#ifdef USE_MINISAT
  return _vc_isUsingSolver(vc, stp::UserDefinedFlags::SIMPLIFYING_MINISAT_SOLVER);
#else
  return false;
#endif
}

bool vc_supportsCryptominisat(VC /*vc*/)
{
#ifdef USE_CRYPTOMINISAT
  return true;
#else
  return false;
#endif
}

bool vc_useCryptominisat(VC
#ifdef USE_CRYPTOMINISAT
vc
#endif
)
{
#ifdef USE_CRYPTOMINISAT
  _vc_useSolver(vc, stp::UserDefinedFlags::CRYPTOMINISAT5_SOLVER);
  return true;
#else
  return false;
#endif
}

bool vc_isUsingCryptominisat(VC
#ifdef USE_CRYPTOMINISAT
vc
#endif
)
{
#ifdef USE_CRYPTOMINISAT
  return _vc_isUsingSolver(vc, stp::UserDefinedFlags::CRYPTOMINISAT5_SOLVER);
#else
  return false;
#endif
}

bool vc_supportsCadical(VC /*vc*/)
{
#ifdef USE_CADICAL
  return true;
#else
  return false;
#endif
}

bool vc_useCadical(VC
#ifdef USE_CADICAL
vc
#endif
)
{
#ifdef USE_CADICAL
  _vc_useSolver(vc, stp::UserDefinedFlags::CADICAL_SOLVER);
  return true;
#else
  return false;
#endif
}

bool vc_isUsingCadical(VC
#ifdef USE_CADICAL
vc
#endif
)
{
#ifdef USE_CADICAL
  return _vc_isUsingSolver(vc, stp::UserDefinedFlags::CADICAL_SOLVER);
#else
  return false;
#endif
}
