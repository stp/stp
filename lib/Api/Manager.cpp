/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: September, 2026
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

// Manager.cpp -- the term manager: sorts, symbols and literal values over an
// STPMgr.

#include "Internal.h"
#include "NodeAccess.h"

#include "Lra/LraBudgetRefusal.h"

#include "stp/FloatBlaster/DecimalLiteral.h"
#include "stp/FloatBlaster/FloatBlaster.h"
#include "stp/FloatBlaster/rounding_modes.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/UninterpretedFunctions/UFDecl.h"

#include <algorithm>
#include <atomic>
#include <cctype>
#include <cmath>
#include <cstring>
#include <mutex>
#include <new>
#include <ostream>
#include <unordered_set>

namespace stp
{
namespace api
{
namespace detail
{

namespace
{
std::atomic<std::uint64_t> g_manager_ids{1};

// A literal named in a message: the whole of a short one, the start of a long
// one.
std::string literal_for_message(std::string_view text)
{
  constexpr std::size_t shown = 64;
  if (text.size() <= shown)
    return "'" + std::string(text) + "'";
  return "'" + std::string(text.substr(0, shown)) + "...' (" + std::to_string(text.size()) +
         " characters)";
}
} // namespace

// CONSTANTBV keeps its constants thread-local, so the boot is per thread: a
// manager used from a second thread must not run on zeroed constants. Every
// entry point passes through check_alive or engine_call, which call this, and
// so does rm_const, which an argument list may evaluate before either; the
// check is one thread-local read once a thread has booted.
void boot_constant_bv()
{
  static thread_local bool booted = false;
  if (booted)
    return;
  const CONSTANTBV::ErrCode c = CONSTANTBV::BitVector_Boot();
  if (c != 0)
    fail_resource("TermManager", "the constant bit-vector library failed to boot");
  booted = true;
}

// ------------------------------------------------------------ lifecycle

ManagerImpl::ManagerImpl(const TermManager::Config& cfg) : config(cfg)
{
  // The engine prints nothing of its own while a manager is built; the
  // first route also puts the dispatching buffers in front of std::cout and
  // std::cerr, before any parse swaps std::cout's buffer for its own.
  OutputRoute quiet(&kNoOutput);
  boot_constant_bv();
  id = g_manager_ids.fetch_add(1);
  bm = new STPMgr();
  // The engine builds through the simplifying factory whatever the manager's
  // simplify switch says; the switch picks the factory the API's own
  // construction and the parsers use (ManagerImpl::factory).
  bm->defaultNodeFactory = new SimplifyingNodeFactory(*bm->hashingNodeFactory, *bm);
  build_factory_ = config.simplify ? bm->defaultNodeFactory : bm->hashingNodeFactory;
  bm->UserFlags.uf_sort_width = config.uf_sort_width;
  // The counterexample construction of the engine is on by default for the
  // API: a model is what produce-models (default true) promises.
  bm->UserFlags.request_counterexample = true;
  bool_sort = intern_sort("B", [] {
    SortRec r;
    r.kind = SortKind::BOOL;
    r.source = SourceSort::boolean();
    r.has_source = true;
    return r;
  }());
  rm_sort = intern_sort("M", [] {
    SortRec r;
    r.kind = SortKind::RM;
    r.source = SourceSort::roundingMode();
    r.has_source = true;
    return r;
  }());
  real_sort = intern_sort("Q", [] {
    SortRec r;
    r.kind = SortKind::REAL;
    r.source = SourceSort::real();
    r.has_source = true;
    return r;
  }());
}

ManagerImpl::~ManagerImpl()
{
  OutputRoute quiet(&kNoOutput);
  // Every node the API tables hold must be released before the manager's
  // unique tables go: clear the tables first.
  fun_sort_of_identity.clear();
  names_by_node.clear();
  symbols.clear();
  if (bm->defaultNodeFactory != bm->hashingNodeFactory)
    delete bm->defaultNodeFactory;
  delete bm;
}

void ManagerImpl::check_alive(const char* fn) const
{
  if (callback_depth() != 0)
    fail(ErrorCode::STATE, fn,
         "called from inside one of the library's callbacks (a sink, the terminator, the "
         "fatal-error handler, a text source or the error callback), which must not call it");
  boot_constant_bv();
  if (poisoned)
    fail(ErrorCode::STATE, fn, "the term manager is poisoned: " + poison_message);
}

namespace
{
void poison(ManagerImpl* m, const char* fn, const std::string& what)
{
  const std::string where = fn ? fn : "";
  if (m != nullptr && !m->poisoned)
  {
    m->poisoned = true;
    m->poison_message =
        "an engine failure in " + where + " (" + what + ") may have left its state inconsistent";
  }
}
} // namespace

void fail_engine(ManagerImpl* m, const char* fn, const std::string& what)
{
  poison(m, fn, what);
  fail_internal(fn, "the engine failed: " + what +
                        "; the term manager is poisoned and refuses every later call");
}

void fail_foreign(ManagerImpl* m, const char* fn, const std::exception& e)
{
  if (dynamic_cast<const std::bad_alloc*>(&e) == nullptr)
    fail_engine(m, fn, e.what());
  poison(m, fn, "out of memory");
  fail_resource(fn, "out of memory; the term manager is poisoned and refuses every later call");
}

void check_uf_sort_width(std::uint64_t width, const char* fn, std::optional<int> arg)
{
  // the uf-sort-width entry's range: a zero-width element is no bit-vector,
  // and a wider one overflows the word arithmetic underneath
  const OptionSpec* spec = find_option("uf-sort-width");
  if (width < static_cast<std::uint64_t>(spec->min) || width > static_cast<std::uint64_t>(spec->max))
    fail(ErrorCode::INVALID_ARGUMENT, fn,
         "uf_sort_width must be between " + std::to_string(spec->min) + " and " +
             std::to_string(spec->max) + " (it is " + std::to_string(width) + ")",
         arg);
}

// ------------------------------------------------------------ sorts

std::uint32_t ManagerImpl::intern_sort(const std::string& key, SortRec&& rec)
{
  auto it = sort_keys.find(key);
  if (it != sort_keys.end())
    return it->second;
  const std::uint32_t index = static_cast<std::uint32_t>(sorts.size());
  sorts.push_back(std::move(rec));
  sort_keys.emplace(key, index);
  return index;
}

std::uint32_t ManagerImpl::bv_sort(std::uint32_t width)
{
  SortRec r;
  r.kind = SortKind::BV;
  r.a = width;
  r.source = SourceSort::bitVector(width);
  r.has_source = true;
  return intern_sort("V" + std::to_string(width), std::move(r));
}

std::uint32_t ManagerImpl::fp_sort(std::uint32_t e, std::uint32_t s)
{
  SortRec r;
  r.kind = SortKind::FP;
  r.a = e;
  r.b = s;
  r.source = SourceSort::floatingPoint(e, s);
  r.has_source = true;
  return intern_sort("F" + std::to_string(e) + ":" + std::to_string(s), std::move(r));
}

std::uint32_t ManagerImpl::array_sort(std::uint32_t index, std::uint32_t element,
                                      const char* fn)
{
  const SortRec& i = sorts[index];
  const SortRec& e = sorts[element];
  auto scalar = [](const SortRec& r) {
    return r.kind == SortKind::BV || r.kind == SortKind::FP || r.kind == SortKind::RM ||
           r.kind == SortKind::UNINTERPRETED;
  };
  if (!scalar(i) || !scalar(e))
    fail(ErrorCode::UNSUPPORTED, fn,
         "the engine supports arrays indexed by and holding bit-vectors, "
         "floating-point numbers, rounding modes and declared sorts only "
         "(capabilities: array.element-sorts)",
         std::nullopt, {}, {make_sort(this, index), make_sort(this, element)});
  SortRec r;
  r.kind = SortKind::ARRAY;
  r.index = index;
  r.element = element;
  r.source = SourceSort::array(i.source, e.source);
  r.has_source = true;
  return intern_sort("A" + std::to_string(index) + ":" + std::to_string(element),
                     std::move(r));
}

std::uint32_t ManagerImpl::fun_sort(const std::vector<std::uint32_t>& domain,
                                    std::uint32_t codomain)
{
  std::string key = "M";
  for (std::uint32_t d : domain)
    key += std::to_string(d) + ",";
  key += "->" + std::to_string(codomain);
  SortRec r;
  r.kind = SortKind::FUN;
  r.domain = domain;
  r.codomain = codomain;
  return intern_sort(key, std::move(r));
}

std::uint32_t ManagerImpl::uninterpreted_sort(const std::string& name, bool anonymous)
{
  auto it = sorts_by_name.find(name);
  if (it != sorts_by_name.end())
    return it->second;
  SortRec r;
  r.kind = SortKind::UNINTERPRETED;
  r.name = name;
  r.anonymous = anonymous;
  r.b = config.uf_sort_width;
  r.source = registerUninterpretedSort(name, config.uf_sort_width);
  r.engine_id = r.source.uninterpretedId();
  r.has_source = true;
  const std::uint32_t index = intern_sort("N" + name, std::move(r));
  sorts_by_name.emplace(name, index);
  sorts_by_engine_id.emplace(sorts[index].engine_id, index);
  if (!anonymous)
    declared_sort_order.push_back(index);
  return index;
}

std::uint32_t ManagerImpl::sort_of_source(const SourceSort& ss, const char* fn)
{
  switch (ss.kind())
  {
    case SourceSort::Kind::Bool:
      return bool_sort;
    case SourceSort::Kind::BitVector:
      return bv_sort(ss.bitVectorWidth());
    case SourceSort::Kind::FloatingPoint:
      return fp_sort(ss.exponentWidth(), ss.significandWidth());
    case SourceSort::Kind::RoundingMode:
      return rm_sort;
    case SourceSort::Kind::Real:
      return real_sort;
    case SourceSort::Kind::Array:
      return array_sort(sort_of_source(ss.index(), fn), sort_of_source(ss.element(), fn),
                        fn);
    case SourceSort::Kind::Uninterpreted:
    {
      auto it = sorts_by_engine_id.find(ss.uninterpretedId());
      if (it != sorts_by_engine_id.end())
        return it->second;
      // A sort declared by a parsed script: adopt it under its declared name.
      const std::string name = uninterpretedSortName(ss.uninterpretedId());
      SortRec r;
      r.kind = SortKind::UNINTERPRETED;
      r.name = name;
      r.b = ss.packedWidth();
      r.source = ss;
      r.engine_id = ss.uninterpretedId();
      r.has_source = true;
      const std::uint32_t index = intern_sort("N" + name, std::move(r));
      sorts_by_name.emplace(name, index);
      sorts_by_engine_id.emplace(ss.uninterpretedId(), index);
      declared_sort_order.push_back(index);
      return index;
    }
    case SourceSort::Kind::Unknown:
      break;
  }
  fail_internal(fn, "a term without a source sort");
}

std::uint32_t ManagerImpl::sort_of_node(const ASTNode& n, const char* fn)
{
  if (n.GetKind() == SYMBOL)
  {
    auto it = fun_sort_of_identity.find(n);
    if (it != fun_sort_of_identity.end())
      return it->second;
  }
  const SourceSort ss = n.GetSourceSort();
  if (ss.kind() == SourceSort::Kind::Unknown)
  {
    // A function identity reached before its declaration was adopted.
    if (const UFDecl* d = decl_of(n))
    {
      std::vector<std::uint32_t> domain;
      for (const SourceSort& s : d->signature().domain())
        domain.push_back(sort_of_source(s, fn));
      const std::uint32_t fs = fun_sort(domain, sort_of_source(d->signature().codomain(), fn));
      fun_sort_of_identity.emplace(n, fs);
      return fs;
    }
    fail_internal(fn, "a term without a source sort");
  }
  return sort_of_source(ss, fn);
}

std::string ManagerImpl::sort_text(std::uint32_t index) const
{
  const SortRec& r = sorts[index];
  switch (r.kind)
  {
    case SortKind::BOOL: return "Bool";
    case SortKind::BV: return "(_ BitVec " + std::to_string(r.a) + ")";
    case SortKind::FP: return "(_ FloatingPoint " + std::to_string(r.a) + " " + std::to_string(r.b) + ")";
    case SortKind::RM: return "RoundingMode";
    case SortKind::REAL: return "Real";
    case SortKind::ARRAY: return "(Array " + sort_text(r.index) + " " + sort_text(r.element) + ")";
    case SortKind::UNINTERPRETED: return quote_symbol(r.name);
    case SortKind::FUN:
    {
      std::string s = "(";
      for (std::size_t i = 0; i < r.domain.size(); ++i)
        s += (i ? " " : "") + sort_text(r.domain[i]);
      return s + ") " + sort_text(r.codomain);
    }
  }
  return "?";
}

// ------------------------------------------------------------ symbols

const SymbolRec* ManagerImpl::find_symbol(const std::string& name) const
{
  auto it = symbols.find(name);
  return it == symbols.end() ? nullptr : &it->second;
}

const SymbolRec* ManagerImpl::find_symbol(const ASTNode& n) const
{
  auto it = names_by_node.find(n);
  if (it == names_by_node.end())
    return nullptr;
  return find_symbol(it->second);
}

const UFDecl* ManagerImpl::decl_of(const ASTNode& identity) const
{
  UFContext* ctx = bm->getUFContextIfAny();
  if (ctx == nullptr || identity.IsNull() || identity.GetKind() != SYMBOL)
    return nullptr;
  return ctx->lookupIdentity(identity);
}

std::string ManagerImpl::fresh_name(std::string_view prefix)
{
  std::string base(prefix);
  for (;;)
  {
    std::string name = base + "!" + std::to_string(fresh_counter++);
    if (symbols.find(name) == symbols.end() && !bm->LookupSymbol(name.c_str()))
      return name;
  }
}

Term ManagerImpl::declare(const char* fn, const std::string& name, std::uint32_t sort,
                          bool anonymous)
{
  if (name.empty())
    fail(ErrorCode::INVALID_ARGUMENT, fn, "a symbol needs a name", 0);
  if (!anonymous && STPMgr::isReservedSymbolName(name.c_str()))
    fail(ErrorCode::INVALID_ARGUMENT, fn,
         "names beginning with '@' or '.' are reserved for the solver's own "
         "symbols (SMT-LIB 2.6, 3.1)",
         0);
  if (const SymbolRec* existing = find_symbol(name))
  {
    if (existing->anonymous)
      fail(ErrorCode::INVALID_ARGUMENT, fn,
           "the name '" + name + "' belongs to an anonymous symbol made by mk_fresh", 0);
    if (existing->sort != sort)
      fail(ErrorCode::SORT_MISMATCH, fn,
           "the name '" + name + "' is already declared with sort " +
               sort_text(existing->sort),
           0, {make_term(this, existing->node)},
           {make_sort(this, sort), make_sort(this, existing->sort)});
    return make_term(this, existing->node);
  }
  const SortRec& r = sorts[sort];
  // Recording a symbol can change the engine's model tables (a Real symbol
  // resets the exact Real model), so a model the active solver has not been
  // asked for yet is taken first, while the tables still hold it.
  if (active != nullptr)
    active->ensure_snapshot();
  SymbolRec rec;
  rec.sort = sort;
  rec.anonymous = anonymous;
  if (r.kind == SortKind::FUN)
  {
    std::vector<SourceSort> domain;
    for (std::uint32_t d : r.domain)
    {
      const SortRec& dr = sorts[d];
      if (!dr.has_source || !UFSignature::isSupportedSort(dr.source))
        fail(ErrorCode::UNSUPPORTED, fn,
             std::string("an uninterpreted function cannot take ") + sort_text(d) +
                 " (" + UFSignature::supportedSortsPhrase() + ")",
             std::nullopt, {}, {make_sort(this, d)});
      domain.push_back(dr.source);
    }
    const SortRec& cr = sorts[r.codomain];
    if (!cr.has_source || !UFSignature::isSupportedSort(cr.source))
      fail(ErrorCode::UNSUPPORTED, fn,
           std::string("an uninterpreted function cannot return ") + sort_text(r.codomain) +
               " (" + UFSignature::supportedSortsPhrase() + ")",
           std::nullopt, {}, {make_sort(this, r.codomain)});
    if (domain.empty())
      fail(ErrorCode::INVALID_ARGUMENT, fn,
           "a function sort needs at least one domain sort; a zero-arity function "
           "is an ordinary symbol of the codomain sort");
    bm->UserFlags.enable_uninterpreted_functions = true;
    std::string diagnostic;
    const UFDecl* decl = bm->getUFContext()->declareFunction(name, domain, cr.source,
                                                              &diagnostic);
    if (decl == nullptr)
      fail(ErrorCode::INVALID_ARGUMENT, fn, diagnostic, 0);
    rec.node = decl->identityNode();
    rec.is_function = true;
    rec.decl = decl;
    fun_sort_of_identity.emplace(rec.node, sort);
  }
  else
  {
    if (!r.has_source)
      fail_internal(fn, "a sort without an engine representation");
    rec.node = bm->CreateSourceSymbol(name.c_str(), r.source);
  }
  const ASTNode node = rec.node;
  symbols.emplace(name, std::move(rec));
  names_by_node.emplace(node, name);
  if (!anonymous)
    symbol_order.push_back(name);
  return make_term(this, node);
}

void ManagerImpl::adopt_engine_symbols(const std::vector<ASTNode>& roots)
{
  ASTNodeSet visited;
  std::vector<ASTNode> stack(roots.begin(), roots.end());
  while (!stack.empty())
  {
    const ASTNode n = stack.back();
    stack.pop_back();
    if (n.IsNull() || !visited.insert(n).second)
      continue;
    if (n.GetKind() == SYMBOL)
    {
      if (names_by_node.count(n) != 0)
        continue;
      // A function's identity node is an introduced, reserved (@-prefixed)
      // symbol standing for the declaration; it is the declaration that is
      // adopted, under the function's own name.
      if (const UFDecl* d = decl_of(n))
      {
        std::vector<std::uint32_t> domain;
        for (const SourceSort& s : d->signature().domain())
          domain.push_back(sort_of_source(s, "parse"));
        const std::uint32_t fs =
            fun_sort(domain, sort_of_source(d->signature().codomain(), "parse"));
        fun_sort_of_identity.emplace(n, fs);
        SymbolRec rec;
        rec.node = n;
        rec.sort = fs;
        rec.is_function = true;
        rec.decl = d;
        if (symbols.find(d->name()) == symbols.end())
        {
          symbols.emplace(d->name(), std::move(rec));
          names_by_node.emplace(n, d->name());
          symbol_order.push_back(d->name());
        }
        continue;
      }
      if (bm->FoundIntroducedSymbolSet(n))
        continue;
      const std::string name = n.GetName();
      if (STPMgr::isReservedSymbolName(name.c_str()))
        continue;
      if (n.GetSourceSort().kind() == SourceSort::Kind::Unknown)
        continue;
      if (symbols.find(name) != symbols.end())
        continue; // a parsed symbol shadowing an API name: leave the API's
      SymbolRec rec;
      rec.node = n;
      rec.sort = sort_of_node(n, "parse");
      symbols.emplace(name, std::move(rec));
      names_by_node.emplace(n, name);
      symbol_order.push_back(name);
      continue;
    }
    for (const ASTNode& c : n.GetChildren())
      stack.push_back(c);
  }
}

// ------------------------------------------------------------ values

ASTNode ManagerImpl::bv_const(std::uint32_t width, std::uint64_t value)
{
  return bm->CreateBVConst(width, value);
}

ASTNode ManagerImpl::bv_const_bits(std::uint32_t width, const std::string& bits)
{
  return bm->CreateBVConst(bits, 2, static_cast<int>(width));
}

ASTNode ManagerImpl::fp_const_from_bits(std::uint32_t e, std::uint32_t s,
                                        const ASTNode& bits)
{
  return bm->CreateFPConst(bits, e, s);
}

unsigned rm_encoding(RoundingMode rm)
{
  switch (rm)
  {
    case RoundingMode::RNE: return symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN;
    case RoundingMode::RNA: return symbolic_fp::ROUND_NEAREST_TIES_TO_AWAY;
    case RoundingMode::RTP: return symbolic_fp::ROUND_TOWARD_POSITIVE;
    case RoundingMode::RTN: return symbolic_fp::ROUND_TOWARD_NEGATIVE;
    case RoundingMode::RTZ: return symbolic_fp::ROUND_TOWARD_ZERO;
  }
  return symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN;
}

ASTNode ManagerImpl::rm_const(RoundingMode rm)
{
  boot_constant_bv();
  return bm->CreateRMConst(rm_encoding(rm));
}

ASTNode ManagerImpl::real_const(const char* fn, const std::string& text)
{
  try
  {
    const std::size_t slash = text.find('/');
    if (slash != std::string::npos)
      return bm->CreateRealConst(text.substr(0, slash), text.substr(slash + 1));
    return bm->CreateRealConst(text);
  }
  catch (const stp::EngineFatal&)
  {
    throw;
  }
  catch (const std::exception& failure)
  {
    // A literal too large for the exact arithmetic is well formed, and is
    // refused as Real arithmetic beyond the budget is.
    if (stp::lra::gaveUpOnABudget(failure))
      fail(ErrorCode::UNSUPPORTED, fn,
           literal_for_message(text) + " exceeds the exact-arithmetic budget: " + failure.what());
    fail(ErrorCode::INVALID_ARGUMENT, fn,
         literal_for_message(text) + " is not a real literal: " + failure.what());
  }
}

ASTNode ManagerImpl::default_value(std::uint32_t sort, const char* fn)
{
  const SortRec& r = sorts[sort];
  switch (r.kind)
  {
    case SortKind::BOOL: return bm->ASTFalse;
    case SortKind::BV: return bm->CreateZeroConst(r.a);
    case SortKind::FP: return bm->CreateFPSpecialConst(FPSpecial::PlusZero, r.a, r.b);
    case SortKind::RM: return rm_const(RoundingMode::RNE);
    case SortKind::REAL: return real_const(fn, "0");
    case SortKind::UNINTERPRETED:
      return bm->CreateUninterpretedConst(bm->CreateZeroConst(r.b), r.source);
    case SortKind::ARRAY:
      return build_term(this, fn, Kind::CONST_ARRAY, {default_value(r.element, fn)}, {}, sort);
    case SortKind::FUN:
      break;
  }
  fail(ErrorCode::INVALID_ARGUMENT, fn, "a function sort has no default value");
}

// ------------------------------------------------------------ handles

Term make_term(ManagerImpl* m, const ASTNode& n)
{
  return Term(m, NodeAccess::raw(n));
}

Sort make_sort(ManagerImpl* m, std::uint32_t index)
{
  return Sort(m, index);
}

bool ManagerImpl::is_const_array(const ASTNode& n) const
{
  return bm->isConstArray(n);
}

const ASTNode& ManagerImpl::const_array_default(const ASTNode& n) const
{
  return bm->constArrayDefault(n);
}

std::string quote_symbol(const std::string& name)
{
  if (name.empty())
    return "||";
  // SMT-LIB 2.6 section 3.1: a reserved word is not a symbol, so a name
  // that spells one must be quoted to be read back as a symbol.
  static const char* const reserved[] = {
      "BINARY", "DECIMAL", "HEXADECIMAL", "NUMERAL", "STRING", "_", "!", "as", "let",
      "exists", "forall", "match", "par", "assert", "check-sat", "check-sat-assuming",
      "declare-const", "declare-datatype", "declare-datatypes", "declare-fun",
      "declare-sort", "define-fun", "define-fun-rec", "define-funs-rec", "define-sort",
      "echo", "exit", "get-assertions", "get-assignment", "get-info", "get-model",
      "get-option", "get-proof", "get-unsat-assumptions", "get-unsat-core", "get-value",
      "pop", "push", "reset", "reset-assertions", "set-info", "set-logic", "set-option"};
  for (const char* r : reserved)
    if (name == r)
      return "|" + name + "|";
  bool simple = true;
  for (char c : name)
  {
    const bool ok = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
                    (c >= '0' && c <= '9') || std::strchr("~!@$%^&*_-+=<>.?/", c) != nullptr;
    if (!ok)
    {
      simple = false;
      break;
    }
  }
  if (simple && !(name[0] >= '0' && name[0] <= '9'))
    return name;
  return "|" + name + "|";
}

bool predefined_symbol(const std::string& name)
{
  // What the SMT-LIB 2 reader takes as the theories' own: Core, FixedSizeBitVectors
  // (with STP's reductions and overflow predicates), ArraysEx, FloatingPoint and Reals.
  static const std::unordered_set<std::string> symbols = {
      "true", "false", "not", "and", "or", "xor", "=>", "=", "distinct", "ite",
      "concat", "extract", "repeat", "zero_extend", "sign_extend", "rotate_left", "rotate_right",
      "bvnot", "bvand", "bvor", "bvxor", "bvnand", "bvnor", "bvxnor", "bvneg", "bvadd", "bvsub",
      "bvmul", "bvudiv", "bvurem", "bvsdiv", "bvsrem", "bvsmod", "bvshl", "bvlshr", "bvashr",
      "bvcomp", "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge",
      "bvredor", "bvredand", "bvnego", "bvuaddo", "bvsaddo", "bvumulo", "bvsmulo", "bvusubo",
      "bvssubo", "bvsdivo",
      "select", "store",
      "fp", "fp.abs", "fp.neg", "fp.add", "fp.sub", "fp.mul", "fp.div", "fp.fma", "fp.sqrt",
      "fp.rem", "fp.roundToIntegral", "fp.min", "fp.max", "fp.leq", "fp.lt", "fp.geq", "fp.gt",
      "fp.eq", "fp.isNormal", "fp.isSubnormal", "fp.isZero", "fp.isInfinite", "fp.isNaN",
      "fp.isNegative", "fp.isPositive", "fp.to_ubv", "fp.to_sbv", "fp.to_real", "fp.to_ieee_bv",
      "to_fp", "to_fp_unsigned", "NaN", "+oo", "-oo", "+zero", "-zero",
      "RNE", "RNA", "RTP", "RTN", "RTZ", "roundNearestTiesToEven", "roundNearestTiesToAway",
      "roundTowardPositive", "roundTowardNegative", "roundTowardZero",
      "+", "-", "*", "/", "<", "<=", ">", ">="};
  return symbols.count(name) != 0;
}

bool predefined_sort_symbol(const std::string& name)
{
  static const std::unordered_set<std::string> sorts = {
      "Bool", "BitVec", "Array", "FloatingPoint", "Float16", "Float32", "Float64", "Float128",
      "RoundingMode", "Real"};
  return sorts.count(name) != 0;
}

} // namespace detail

using detail::ManagerImpl;

// ============================================================ Sort

Sort::Sort() noexcept : mgr_(nullptr), index_(0) {}
Sort::Sort(detail::ManagerImpl* m, std::uint32_t index) noexcept : mgr_(m), index_(index)
{
  if (mgr_)
    mgr_->retain();
}
Sort::Sort(const Sort& o) noexcept : mgr_(o.mgr_), index_(o.index_)
{
  if (mgr_)
    mgr_->retain();
}
Sort::Sort(Sort&& o) noexcept : mgr_(o.mgr_), index_(o.index_)
{
  o.mgr_ = nullptr;
}
Sort& Sort::operator=(const Sort& o) noexcept
{
  if (o.mgr_)
    o.mgr_->retain();
  if (mgr_)
    mgr_->release();
  mgr_ = o.mgr_;
  index_ = o.index_;
  return *this;
}
Sort& Sort::operator=(Sort&& o) noexcept
{
  if (this != &o)
  {
    if (mgr_)
      mgr_->release();
    mgr_ = o.mgr_;
    index_ = o.index_;
    o.mgr_ = nullptr;
  }
  return *this;
}
Sort::~Sort()
{
  if (mgr_)
    mgr_->release();
}

bool Sort::is_null() const noexcept
{
  return mgr_ == nullptr;
}

namespace
{
const detail::SortRec& rec_of(const Sort& s, const char* fn)
{
  if (s.is_null())
    detail::fail(ErrorCode::NULL_HANDLE, fn, "the sort is null");
  return s.impl_manager()->rec(s.impl_index());
}
} // namespace

SortKind Sort::kind() const { return rec_of(*this, "Sort::kind").kind; }
bool Sort::is_bool() const { return kind() == SortKind::BOOL; }
bool Sort::is_bv() const { return kind() == SortKind::BV; }
bool Sort::is_fp() const { return kind() == SortKind::FP; }
bool Sort::is_rm() const { return kind() == SortKind::RM; }
bool Sort::is_real() const { return kind() == SortKind::REAL; }
bool Sort::is_array() const { return kind() == SortKind::ARRAY; }
bool Sort::is_fun() const { return kind() == SortKind::FUN; }
bool Sort::is_uninterpreted() const { return kind() == SortKind::UNINTERPRETED; }

std::uint32_t Sort::bv_size() const
{
  const detail::SortRec& r = rec_of(*this, "Sort::bv_size");
  if (r.kind != SortKind::BV)
    detail::fail(ErrorCode::INVALID_ARGUMENT, "Sort::bv_size", "not a bit-vector sort",
                 std::nullopt, {}, {*this});
  return r.a;
}
std::uint32_t Sort::fp_exp_size() const
{
  const detail::SortRec& r = rec_of(*this, "Sort::fp_exp_size");
  if (r.kind != SortKind::FP)
    detail::fail(ErrorCode::INVALID_ARGUMENT, "Sort::fp_exp_size", "not a floating-point sort",
                 std::nullopt, {}, {*this});
  return r.a;
}
std::uint32_t Sort::fp_sig_size() const
{
  const detail::SortRec& r = rec_of(*this, "Sort::fp_sig_size");
  if (r.kind != SortKind::FP)
    detail::fail(ErrorCode::INVALID_ARGUMENT, "Sort::fp_sig_size", "not a floating-point sort",
                 std::nullopt, {}, {*this});
  return r.b;
}
Sort Sort::array_index() const
{
  const detail::SortRec& r = rec_of(*this, "Sort::array_index");
  if (r.kind != SortKind::ARRAY)
    detail::fail(ErrorCode::INVALID_ARGUMENT, "Sort::array_index", "not an array sort",
                 std::nullopt, {}, {*this});
  return Sort(mgr_, r.index);
}
Sort Sort::array_element() const
{
  const detail::SortRec& r = rec_of(*this, "Sort::array_element");
  if (r.kind != SortKind::ARRAY)
    detail::fail(ErrorCode::INVALID_ARGUMENT, "Sort::array_element", "not an array sort",
                 std::nullopt, {}, {*this});
  return Sort(mgr_, r.element);
}
std::vector<Sort> Sort::fun_domain() const
{
  const detail::SortRec& r = rec_of(*this, "Sort::fun_domain");
  if (r.kind != SortKind::FUN)
    detail::fail(ErrorCode::INVALID_ARGUMENT, "Sort::fun_domain", "not a function sort",
                 std::nullopt, {}, {*this});
  std::vector<Sort> out;
  for (std::uint32_t d : r.domain)
    out.emplace_back(mgr_, d);
  return out;
}
Sort Sort::fun_codomain() const
{
  const detail::SortRec& r = rec_of(*this, "Sort::fun_codomain");
  if (r.kind != SortKind::FUN)
    detail::fail(ErrorCode::INVALID_ARGUMENT, "Sort::fun_codomain", "not a function sort",
                 std::nullopt, {}, {*this});
  return Sort(mgr_, r.codomain);
}
std::uint32_t Sort::fun_arity() const
{
  const detail::SortRec& r = rec_of(*this, "Sort::fun_arity");
  if (r.kind != SortKind::FUN)
    detail::fail(ErrorCode::INVALID_ARGUMENT, "Sort::fun_arity", "not a function sort",
                 std::nullopt, {}, {*this});
  return static_cast<std::uint32_t>(r.domain.size());
}
std::string Sort::name() const
{
  const detail::SortRec& r = rec_of(*this, "Sort::name");
  if (r.kind != SortKind::UNINTERPRETED)
    detail::fail(ErrorCode::INVALID_ARGUMENT, "Sort::name", "not an uninterpreted sort",
                 std::nullopt, {}, {*this});
  return r.name;
}
std::uint64_t Sort::id() const noexcept
{
  return mgr_ ? index_ + 1 : 0; // 0 is the null sort's id
}
TermManager Sort::manager() const
{
  if (!mgr_)
    detail::fail(ErrorCode::NULL_HANDLE, "Sort::manager", "the sort is null");
  return TermManager(mgr_);
}
std::string Sort::str() const
{
  if (!mgr_)
    return "<null sort>";
  return mgr_->sort_text(index_);
}
bool operator==(const Sort& a, const Sort& b) noexcept
{
  return a.mgr_ == b.mgr_ && a.index_ == b.index_;
}
bool operator!=(const Sort& a, const Sort& b) noexcept
{
  return !(a == b);
}
bool operator<(const Sort& a, const Sort& b) noexcept
{
  if (a.mgr_ != b.mgr_)
    return a.mgr_ < b.mgr_;
  return a.index_ < b.index_;
}
std::ostream& operator<<(std::ostream& os, const Sort& s)
{
  return os << s.str();
}

// ============================================================ TermManager

TermManager::TermManager() : TermManager(Config{}) {}

namespace
{
const TermManager::Config& checked(const TermManager::Config& cfg)
{
  detail::check_uf_sort_width(cfg.uf_sort_width, "TermManager", std::nullopt);
  return cfg;
}
} // namespace

TermManager::TermManager(const Config& cfg) : impl_(new ManagerImpl(checked(cfg)))
{
  impl_->retain();
}

namespace
{
// The three manager-scoped registry entries, read from an Options value; a
// solver-scoped entry that was SET in it has no home here and is refused.
TermManager::Config config_from_options(const Options& o)
{
  TermManager::Config cfg;
  std::size_t n = 0;
  const detail::OptionSpec* specs = detail::option_specs(n);
  for (std::size_t i = 0; i < n; ++i)
    if (specs[i].scope == OptionScope::SOLVER && o.is_set(specs[i].name))
      detail::fail_option(ErrorCode::OPTION_VALUE, specs[i].name,
                          "solver-scoped: pass it to Solver, not to TermManager");
  cfg.simplify = o.get_bool("simplify");
  const std::string rm = o.get_str("default-rounding-mode");
  cfg.default_rounding_mode = rm == "RNA"   ? RoundingMode::RNA
                              : rm == "RTP" ? RoundingMode::RTP
                              : rm == "RTN" ? RoundingMode::RTN
                              : rm == "RTZ" ? RoundingMode::RTZ
                                            : RoundingMode::RNE;
  // the registry holds the entry to the range TermManager(Config) checks
  cfg.uf_sort_width = static_cast<std::uint32_t>(o.get_uint("uf-sort-width"));
  return cfg;
}
} // namespace

TermManager::TermManager(const Options& manager_options)
    : TermManager(config_from_options(manager_options))
{
}

TermManager::TermManager(detail::ManagerImpl* m) noexcept : impl_(m)
{
  if (impl_)
    impl_->retain();
}

TermManager::TermManager(const TermManager& o) noexcept : impl_(o.impl_)
{
  if (impl_)
    impl_->retain();
}
TermManager::TermManager(TermManager&& o) noexcept : impl_(o.impl_)
{
  o.impl_ = nullptr;
}
TermManager& TermManager::operator=(const TermManager& o) noexcept
{
  if (o.impl_)
    o.impl_->retain();
  if (impl_)
    impl_->release();
  impl_ = o.impl_;
  return *this;
}
TermManager& TermManager::operator=(TermManager&& o) noexcept
{
  if (this != &o)
  {
    if (impl_)
      impl_->release();
    impl_ = o.impl_;
    o.impl_ = nullptr;
  }
  return *this;
}
TermManager::~TermManager()
{
  if (impl_)
    impl_->release();
}

namespace
{
ManagerImpl* live(const TermManager& tm, const char* fn)
{
  ManagerImpl* m = tm.impl();
  if (m == nullptr)
    detail::fail(ErrorCode::STATE, fn, "the term manager handle was moved from");
  m->check_alive(fn);
  return m;
}
} // namespace

std::uint64_t TermManager::id() const noexcept
{
  return impl_ ? impl_->id : 0;
}
bool operator==(const TermManager& a, const TermManager& b) noexcept
{
  return a.impl_ == b.impl_;
}
bool operator!=(const TermManager& a, const TermManager& b) noexcept
{
  return a.impl_ != b.impl_;
}
bool TermManager::simplify() const noexcept
{
  return impl_ ? impl_->config.simplify : true;
}
RoundingMode TermManager::default_rounding_mode() const noexcept
{
  return impl_ ? impl_->config.default_rounding_mode : RoundingMode::RNE;
}
void TermManager::set_default_rounding_mode(RoundingMode rm)
{
  live(*this, "TermManager::set_default_rounding_mode")->config.default_rounding_mode = rm;
}
std::uint32_t TermManager::uf_sort_width() const noexcept
{
  return impl_ ? impl_->config.uf_sort_width : 16;
}

// -- sorts

Sort TermManager::mk_bool_sort()
{
  ManagerImpl* m = live(*this, "TermManager::mk_bool_sort");
  return Sort(m, m->bool_sort);
}
Sort TermManager::mk_bv_sort(std::uint32_t width)
{
  ManagerImpl* m = live(*this, "TermManager::mk_bv_sort");
  if (width == 0)
    detail::fail(ErrorCode::INVALID_ARGUMENT, "TermManager::mk_bv_sort",
                 "a bit-vector sort needs a positive width", 0);
  return Sort(m, m->bv_sort(width));
}
Sort TermManager::mk_fp_sort(std::uint32_t e, std::uint32_t s)
{
  ManagerImpl* m = live(*this, "TermManager::mk_fp_sort");
  if (e < 2 || s < 2)
    detail::fail(ErrorCode::INVALID_ARGUMENT, "TermManager::mk_fp_sort",
                 "a floating-point sort needs at least 2 exponent and 2 significand bits",
                 e < 2 ? 0 : 1);
  if (std::uint64_t(e) + s > 0xffffffffu) // the engine keeps a width in 32 bits
    detail::fail(ErrorCode::INVALID_ARGUMENT, "TermManager::mk_fp_sort",
                 "a floating-point sort of " + std::to_string(e) + " + " + std::to_string(s) +
                     " bits is wider than the largest width, 4294967295");
  return Sort(m, m->fp_sort(e, s));
}
Sort TermManager::mk_fp16_sort() { return mk_fp_sort(5, 11); }
Sort TermManager::mk_fp32_sort() { return mk_fp_sort(8, 24); }
Sort TermManager::mk_fp64_sort() { return mk_fp_sort(11, 53); }
Sort TermManager::mk_fp128_sort() { return mk_fp_sort(15, 113); }
Sort TermManager::mk_rm_sort()
{
  ManagerImpl* m = live(*this, "TermManager::mk_rm_sort");
  return Sort(m, m->rm_sort);
}
Sort TermManager::mk_real_sort()
{
  ManagerImpl* m = live(*this, "TermManager::mk_real_sort");
  return Sort(m, m->real_sort);
}
Sort TermManager::mk_array_sort(const Sort& index, const Sort& element)
{
  ManagerImpl* m = live(*this, "TermManager::mk_array_sort");
  if (index.is_null() || element.is_null())
    detail::fail(ErrorCode::NULL_HANDLE, "TermManager::mk_array_sort", "a sort is null",
                 index.is_null() ? 0 : 1);
  if (index.impl_manager() != m || element.impl_manager() != m)
    detail::fail(ErrorCode::FOREIGN_MANAGER, "TermManager::mk_array_sort",
                 "the sort belongs to another term manager",
                 index.impl_manager() != m ? 0 : 1);
  return Sort(m, m->array_sort(index.impl_index(), element.impl_index(),
                               "TermManager::mk_array_sort"));
}
Sort TermManager::mk_fun_sort(const std::vector<Sort>& domain, const Sort& codomain)
{
  ManagerImpl* m = live(*this, "TermManager::mk_fun_sort");
  std::vector<std::uint32_t> d;
  for (std::size_t i = 0; i < domain.size(); ++i)
  {
    if (domain[i].is_null())
      detail::fail(ErrorCode::NULL_HANDLE, "TermManager::mk_fun_sort", "a domain sort is null", 0);
    if (domain[i].impl_manager() != m)
      detail::fail(ErrorCode::FOREIGN_MANAGER, "TermManager::mk_fun_sort",
                   "a domain sort belongs to another term manager", 0);
    d.push_back(domain[i].impl_index());
  }
  if (codomain.is_null())
    detail::fail(ErrorCode::NULL_HANDLE, "TermManager::mk_fun_sort", "the codomain is null", 1);
  if (codomain.impl_manager() != m)
    detail::fail(ErrorCode::FOREIGN_MANAGER, "TermManager::mk_fun_sort",
                 "the codomain belongs to another term manager", 1);
  if (d.empty())
    detail::fail(ErrorCode::INVALID_ARGUMENT, "TermManager::mk_fun_sort",
                 "a function sort needs at least one domain sort", 0);
  return Sort(m, m->fun_sort(d, codomain.impl_index()));
}
namespace
{
void refuse_predefined(ManagerImpl* m, const std::string& name, bool sort, const char* fn)
{
  if (m->predefined_names_accepted)
    return;
  if (sort ? detail::predefined_sort_symbol(name) : detail::predefined_symbol(name))
    detail::fail(ErrorCode::INVALID_ARGUMENT, fn,
                 "'" + name + "' is a symbol SMT-LIB predefines, which no quoting tells a " +
                     (sort ? "declared sort" : "declaration") + " apart from; choose another name",
                 0);
}
} // namespace

Sort TermManager::declare_sort(std::string_view name)
{
  ManagerImpl* m = live(*this, "TermManager::declare_sort");
  if (name.empty())
    detail::fail(ErrorCode::INVALID_ARGUMENT, "TermManager::declare_sort",
                 "a sort needs a name", 0);
  refuse_predefined(m, std::string(name), true, "TermManager::declare_sort");
  return Sort(m, m->uninterpreted_sort(std::string(name), false));
}
Sort TermManager::mk_fresh_sort(std::string_view prefix)
{
  ManagerImpl* m = live(*this, "TermManager::mk_fresh_sort");
  std::string base(prefix);
  for (;;)
  {
    const std::string name = base + "!" + std::to_string(m->fresh_counter++);
    if (m->sorts_by_name.find(name) == m->sorts_by_name.end())
      return Sort(m, m->uninterpreted_sort(name, true));
  }
}

// -- symbols

Term TermManager::declare(std::string_view name, const Sort& sort)
{
  ManagerImpl* m = live(*this, "TermManager::declare");
  refuse_predefined(m, std::string(name), false, "TermManager::declare");
  if (sort.is_null())
    detail::fail(ErrorCode::NULL_HANDLE, "TermManager::declare", "the sort is null", 1);
  if (sort.impl_manager() != m)
    detail::fail(ErrorCode::FOREIGN_MANAGER, "TermManager::declare",
                 "the sort belongs to another term manager", 1);
  return detail::engine_call(m, "TermManager::declare", [&] {
    return m->declare("TermManager::declare", std::string(name), sort.impl_index(), false);
  });
}
Term TermManager::mk_fresh(const Sort& sort, std::string_view prefix)
{
  ManagerImpl* m = live(*this, "TermManager::mk_fresh");
  if (sort.is_null())
    detail::fail(ErrorCode::NULL_HANDLE, "TermManager::mk_fresh", "the sort is null", 0);
  if (sort.impl_manager() != m)
    detail::fail(ErrorCode::FOREIGN_MANAGER, "TermManager::mk_fresh",
                 "the sort belongs to another term manager", 0);
  return detail::engine_call(m, "TermManager::mk_fresh", [&] {
    return m->declare("TermManager::mk_fresh", m->fresh_name(prefix), sort.impl_index(), true);
  });
}
std::optional<Term> TermManager::symbol(std::string_view name) const
{
  ManagerImpl* m = live(*this, "TermManager::symbol");
  const detail::SymbolRec* rec = m->find_symbol(std::string(name));
  if (rec == nullptr || rec->anonymous)
    return std::nullopt;
  return detail::make_term(m, rec->node);
}
std::vector<Term> TermManager::symbols() const
{
  ManagerImpl* m = live(*this, "TermManager::symbols");
  std::vector<Term> out;
  out.reserve(m->symbol_order.size());
  for (const std::string& name : m->symbol_order)
    out.push_back(detail::make_term(m, m->symbols.at(name).node));
  return out;
}
std::vector<Sort> TermManager::declared_sorts() const
{
  ManagerImpl* m = live(*this, "TermManager::declared_sorts");
  std::vector<Sort> out;
  for (std::uint32_t index : m->declared_sort_order)
    out.emplace_back(m, index);
  return out;
}
void TermManager::bind_symbol(std::string_view name, const Term& t)
{
  ManagerImpl* m = live(*this, "TermManager::bind_symbol");
  if (t.is_null())
    detail::fail(ErrorCode::NULL_HANDLE, "TermManager::bind_symbol", "the term is null", 1);
  if (t.impl_manager() != m)
    detail::fail(ErrorCode::FOREIGN_MANAGER, "TermManager::bind_symbol",
                 "the term belongs to another term manager", 1);
  const std::string key(name);
  if (key.empty())
    detail::fail(ErrorCode::INVALID_ARGUMENT, "TermManager::bind_symbol", "a name is needed", 0);
  refuse_predefined(m, key, false, "TermManager::bind_symbol");
  const ASTNode node = detail::node_of(t);
  // The table maps names to symbols (declared or fresh); a compound term has
  // no place in it -- the parser's frames and the declaration printers walk
  // the table expecting symbols.
  if (node.GetKind() != SYMBOL || m->is_const_array(node))
    detail::fail(ErrorCode::INVALID_ARGUMENT, "TermManager::bind_symbol",
                 "bind_symbol takes a symbol (a declared or fresh constant), not a compound term",
                 1, {t});
  if (const detail::SymbolRec* existing = m->find_symbol(key))
  {
    if (existing->node == node)
      return;
    detail::fail(ErrorCode::SORT_MISMATCH, "TermManager::bind_symbol",
                 "the name '" + key + "' is already bound to another term", 0,
                 {detail::make_term(m, existing->node), t});
  }
  detail::SymbolRec rec;
  rec.node = node;
  rec.sort = m->sort_of_node(node, "TermManager::bind_symbol");
  rec.is_function = m->decl_of(node) != nullptr;
  rec.decl = rec.is_function ? m->decl_of(node) : nullptr;
  m->symbols.emplace(key, std::move(rec));
  if (m->names_by_node.count(node) == 0)
    m->names_by_node.emplace(node, key);
  m->symbol_order.push_back(key);
}
Term TermManager::term_from_id(std::uint64_t id) const
{
  ManagerImpl* m = live(*this, "TermManager::term_from_id");
  const ASTNode n = m->bm->ExposedNode(id);
  if (n.IsNull())
    detail::fail(ErrorCode::INVALID_ARGUMENT, "TermManager::term_from_id",
                 "no live term has id " + std::to_string(id) +
                     " (only ids obtained from Term::id() resolve)",
                 0);
  return detail::make_term(m, n);
}

// -- values

Term TermManager::mk_true()
{
  ManagerImpl* m = live(*this, "TermManager::mk_true");
  return detail::make_term(m, m->bm->ASTTrue);
}
Term TermManager::mk_false()
{
  ManagerImpl* m = live(*this, "TermManager::mk_false");
  return detail::make_term(m, m->bm->ASTFalse);
}
Term TermManager::mk_bool(bool b)
{
  return b ? mk_true() : mk_false();
}

namespace
{
void check_width(std::uint32_t width, const char* fn)
{
  if (width == 0)
    detail::fail(ErrorCode::INVALID_ARGUMENT, fn, "a bit-vector needs a positive width", 0);
}
} // namespace

Term TermManager::mk_bv(std::uint32_t width, std::uint64_t value)
{
  ManagerImpl* m = live(*this, "TermManager::mk_bv");
  check_width(width, "TermManager::mk_bv");
  if (width < 64 && (value >> width) != 0)
    detail::fail(ErrorCode::VALUE_OUT_OF_RANGE, "TermManager::mk_bv",
                 "value " + std::to_string(value) + " does not fit " + std::to_string(width) +
                     " bits (use mk_bv_wrapped to wrap)",
                 1, {}, {Sort(m, m->bv_sort(width))});
  return detail::make_term(m, m->bv_const(width, value));
}
Term TermManager::mk_bv_signed(std::uint32_t width, std::int64_t value)
{
  ManagerImpl* m = live(*this, "TermManager::mk_bv_signed");
  check_width(width, "TermManager::mk_bv_signed");
  bool fits = true;
  if (width < 64)
  {
    const std::int64_t lo = -(std::int64_t(1) << (width - 1));
    const std::int64_t hi = (std::int64_t(1) << (width - 1)) - 1;
    fits = value >= lo && value <= hi;
  }
  if (!fits)
    detail::fail(ErrorCode::VALUE_OUT_OF_RANGE, "TermManager::mk_bv_signed",
                 "value " + std::to_string(value) + " does not fit the two's complement range of " +
                     std::to_string(width) + " bits",
                 1, {}, {Sort(m, m->bv_sort(width))});
  const std::uint64_t bits = static_cast<std::uint64_t>(value);
  if (width >= 64)
  {
    // sign-extend into the wider constant through the binary string
    std::string s(width, value < 0 ? '1' : '0');
    for (std::uint32_t i = 0; i < 64; ++i)
      s[width - 1 - i] = ((bits >> i) & 1) ? '1' : '0';
    return detail::make_term(m, m->bv_const_bits(width, s));
  }
  return detail::make_term(m, m->bv_const(width, bits & ((std::uint64_t(1) << width) - 1)));
}

namespace
{
// Parses digits of the given base into a binary string of exactly `width`
// bits (MSB first); false when the value does not fit.
bool digits_to_bits(std::string_view digits, int base, std::uint32_t width, std::string& bits,
                    std::string& why)
{
  bool negative = false;
  if (!digits.empty() && (digits[0] == '-' || digits[0] == '+'))
  {
    negative = digits[0] == '-';
    digits.remove_prefix(1);
  }
  if (base == 2 && digits.size() >= 2 && digits[0] == '#' && digits[1] == 'b')
    digits.remove_prefix(2);
  else if (base == 16 && digits.size() >= 2 && digits[0] == '#' && digits[1] == 'x')
    digits.remove_prefix(2);
  else if (base == 16 && digits.size() >= 2 && digits[0] == '0' && (digits[1] == 'x' || digits[1] == 'X'))
    digits.remove_prefix(2);
  else if (base == 2 && digits.size() >= 2 && digits[0] == '0' && (digits[1] == 'b' || digits[1] == 'B'))
    digits.remove_prefix(2);
  if (digits.empty())
  {
    why = "no digits";
    return false;
  }
  if (negative && base != 10)
  {
    why = "a sign is only meaningful in base 10";
    return false;
  }
  // accumulate into a vector of bits, LSB first, by repeated multiply-add
  std::vector<bool> acc; // little-endian magnitude
  auto mul_add = [&acc](unsigned mul, unsigned add) {
    unsigned carry = add;
    for (std::size_t i = 0; i < acc.size(); ++i)
    {
      const unsigned v = (acc[i] ? mul : 0) + carry;
      acc[i] = (v & 1) != 0;
      carry = v >> 1;
    }
    while (carry != 0)
    {
      acc.push_back((carry & 1) != 0);
      carry >>= 1;
    }
  };
  for (std::size_t i = 0; i < digits.size(); ++i)
  {
    const char c = digits[i];
    int d;
    if (c >= '0' && c <= '9')
      d = c - '0';
    else if (c >= 'a' && c <= 'f')
      d = 10 + (c - 'a');
    else if (c >= 'A' && c <= 'F')
      d = 10 + (c - 'A');
    else if (c == '_' && i > 0 && i + 1 < digits.size() &&
             std::isxdigit(static_cast<unsigned char>(digits[i - 1])) &&
             std::isxdigit(static_cast<unsigned char>(digits[i + 1])))
      continue; // a separator between two digits
    else
    {
      why = std::string("unexpected character '") + c + "'";
      return false;
    }
    if (d >= base)
    {
      why = std::string("digit '") + c + "' is not valid in base " + std::to_string(base);
      return false;
    }
    mul_add(static_cast<unsigned>(base), static_cast<unsigned>(d));
  }
  while (!acc.empty() && !acc.back())
    acc.pop_back();
  if (negative)
  {
    // two's complement: value must be >= -2^(width-1)
    if (acc.size() > width)
    {
      why = "the value does not fit";
      return false;
    }
    if (acc.size() == width && !(acc.size() == width && acc.back() &&
                                 std::none_of(acc.begin(), acc.end() - 1, [](bool b) { return b; })))
    {
      why = "the value does not fit the two's complement range";
      return false;
    }
    // negate: invert and add one over width bits
    std::vector<bool> ext(width, false);
    for (std::size_t i = 0; i < acc.size(); ++i)
      ext[i] = acc[i];
    bool carry = true;
    for (std::size_t i = 0; i < width; ++i)
    {
      const bool v = !ext[i];
      ext[i] = v ^ carry;
      carry = v && carry;
    }
    acc = ext;
  }
  else if (acc.size() > width)
  {
    why = "the value does not fit " + std::to_string(width) + " bits";
    return false;
  }
  bits.assign(width, '0');
  for (std::size_t i = 0; i < acc.size() && i < width; ++i)
    if (acc[i])
      bits[width - 1 - i] = '1';
  return true;
}
} // namespace

Term TermManager::mk_bv(std::uint32_t width, std::string_view digits, int base)
{
  ManagerImpl* m = live(*this, "TermManager::mk_bv");
  check_width(width, "TermManager::mk_bv");
  if (base != 2 && base != 10 && base != 16)
    detail::fail(ErrorCode::INVALID_ARGUMENT, "TermManager::mk_bv", "base must be 2, 10 or 16", 2);
  std::string bits, why;
  if (!digits_to_bits(digits, base, width, bits, why))
    detail::fail(ErrorCode::VALUE_OUT_OF_RANGE, "TermManager::mk_bv",
                 "'" + std::string(digits) + "': " + why, 1, {}, {Sort(m, m->bv_sort(width))});
  return detail::make_term(m, m->bv_const_bits(width, bits));
}
Term TermManager::mk_bv_limbs(std::uint32_t width, const std::vector<std::uint64_t>& limbs)
{
  ManagerImpl* m = live(*this, "TermManager::mk_bv_limbs");
  check_width(width, "TermManager::mk_bv_limbs");
  std::string bits(width, '0');
  for (std::size_t i = 0; i < limbs.size(); ++i)
    for (unsigned b = 0; b < 64; ++b)
    {
      const std::size_t pos = i * 64 + b;
      const bool set = ((limbs[i] >> b) & 1) != 0;
      if (pos >= width)
      {
        if (set)
          detail::fail(ErrorCode::VALUE_OUT_OF_RANGE, "TermManager::mk_bv_limbs",
                       "the limbs carry bits above the width", 1, {}, {Sort(m, m->bv_sort(width))});
        continue;
      }
      if (set)
        bits[width - 1 - pos] = '1';
    }
  return detail::make_term(m, m->bv_const_bits(width, bits));
}
Term TermManager::mk_bv_bytes(std::uint32_t width, const std::vector<std::uint8_t>& bytes,
                              bool little_endian)
{
  ManagerImpl* m = live(*this, "TermManager::mk_bv_bytes");
  check_width(width, "TermManager::mk_bv_bytes");
  std::string bits(width, '0');
  for (std::size_t i = 0; i < bytes.size(); ++i)
  {
    const std::size_t byte_index = little_endian ? i : bytes.size() - 1 - i;
    for (unsigned b = 0; b < 8; ++b)
    {
      const std::size_t pos = byte_index * 8 + b;
      const bool set = ((bytes[i] >> b) & 1) != 0;
      if (pos >= width)
      {
        if (set)
          detail::fail(ErrorCode::VALUE_OUT_OF_RANGE, "TermManager::mk_bv_bytes",
                       "the bytes carry bits above the width", 1, {}, {Sort(m, m->bv_sort(width))});
        continue;
      }
      if (set)
        bits[width - 1 - pos] = '1';
    }
  }
  return detail::make_term(m, m->bv_const_bits(width, bits));
}
Term TermManager::mk_bv_wrapped(std::uint32_t width, std::uint64_t value)
{
  ManagerImpl* m = live(*this, "TermManager::mk_bv_wrapped");
  check_width(width, "TermManager::mk_bv_wrapped");
  if (width < 64)
    value &= (std::uint64_t(1) << width) - 1;
  return detail::make_term(m, m->bv_const(width, value));
}
Term TermManager::mk_bv_zero(std::uint32_t width)
{
  ManagerImpl* m = live(*this, "TermManager::mk_bv_zero");
  check_width(width, "TermManager::mk_bv_zero");
  return detail::make_term(m, m->bm->CreateZeroConst(width));
}
Term TermManager::mk_bv_ones(std::uint32_t width)
{
  ManagerImpl* m = live(*this, "TermManager::mk_bv_ones");
  check_width(width, "TermManager::mk_bv_ones");
  return detail::make_term(m, m->bm->CreateMaxConst(width));
}
Term TermManager::mk_bv_min_signed(std::uint32_t width)
{
  ManagerImpl* m = live(*this, "TermManager::mk_bv_min_signed");
  check_width(width, "TermManager::mk_bv_min_signed");
  std::string bits(width, '0');
  bits[0] = '1';
  return detail::make_term(m, m->bv_const_bits(width, bits));
}
Term TermManager::mk_bv_max_signed(std::uint32_t width)
{
  ManagerImpl* m = live(*this, "TermManager::mk_bv_max_signed");
  check_width(width, "TermManager::mk_bv_max_signed");
  std::string bits(width, '1');
  bits[0] = '0';
  return detail::make_term(m, m->bv_const_bits(width, bits));
}

namespace
{
const detail::SortRec& fp_rec(ManagerImpl* m, const Sort& fp, const char* fn, int arg)
{
  if (fp.is_null())
    detail::fail(ErrorCode::NULL_HANDLE, fn, "the sort is null", arg);
  if (fp.impl_manager() != m)
    detail::fail(ErrorCode::FOREIGN_MANAGER, fn, "the sort belongs to another term manager", arg);
  const detail::SortRec& r = m->rec(fp.impl_index());
  if (r.kind != SortKind::FP)
    detail::fail(ErrorCode::SORT_MISMATCH, fn, "expected a floating-point sort", arg, {}, {fp});
  return r;
}
} // namespace

Term TermManager::mk_fp_from_bits(const Sort& fp, const Term& bv)
{
  ManagerImpl* m = live(*this, "TermManager::mk_fp_from_bits");
  const detail::SortRec& r = fp_rec(m, fp, "TermManager::mk_fp_from_bits", 0);
  if (bv.is_null())
    detail::fail(ErrorCode::NULL_HANDLE, "TermManager::mk_fp_from_bits", "the term is null", 1);
  if (bv.impl_manager() != m)
    detail::fail(ErrorCode::FOREIGN_MANAGER, "TermManager::mk_fp_from_bits",
                 "the term belongs to another term manager", 1);
  const ASTNode n = detail::node_of(bv);
  if (n.GetKind() != BVCONST || n.GetSourceSort().kind() != SourceSort::Kind::BitVector)
    detail::fail(ErrorCode::NOT_A_VALUE, "TermManager::mk_fp_from_bits",
                 "the bits must be a bit-vector value; use to_fp_from_bits for a symbolic term", 1,
                 {bv});
  if (n.GetValueWidth() != r.a + r.b)
    detail::fail(ErrorCode::SORT_MISMATCH, "TermManager::mk_fp_from_bits",
                 "the bit-vector must have exp_size + sig_size = " + std::to_string(r.a + r.b) +
                     " bits",
                 1, {bv}, {fp, bv.sort()});
  return detail::make_term(m, m->fp_const_from_bits(r.a, r.b, n));
}
Term TermManager::mk_fp_from_bits(const Sort& fp, std::string_view bits)
{
  ManagerImpl* m = live(*this, "TermManager::mk_fp_from_bits");
  const detail::SortRec& r = fp_rec(m, fp, "TermManager::mk_fp_from_bits", 0);
  const std::uint32_t width = r.a + r.b;
  const int base = (bits.size() >= 2 && (bits[1] == 'x' || bits[1] == 'X')) ? 16 : 2;
  std::string binary, why;
  if (!digits_to_bits(bits, base, width, binary, why))
    detail::fail(ErrorCode::VALUE_OUT_OF_RANGE, "TermManager::mk_fp_from_bits",
                 "'" + std::string(bits) + "': " + why, 1, {}, {fp});
  return detail::make_term(m, m->fp_const_from_bits(r.a, r.b, m->bv_const_bits(width, binary)));
}
Term TermManager::mk_fp(const Term& sign, const Term& exponent, const Term& significand)
{
  ManagerImpl* m = live(*this, "TermManager::mk_fp");
  return detail::make_term(
      m, detail::build_term(m, "TermManager::mk_fp", Kind::FP_FP,
                            {detail::node_of(sign), detail::node_of(exponent),
                             detail::node_of(significand)},
                            {}, std::nullopt));
}
Term TermManager::mk_fp_pos_zero(const Sort& fp)
{
  ManagerImpl* m = live(*this, "TermManager::mk_fp_pos_zero");
  const detail::SortRec& r = fp_rec(m, fp, "TermManager::mk_fp_pos_zero", 0);
  return detail::make_term(m, detail::engine_call(m, "TermManager::mk_fp_pos_zero", [&] {
    return m->bm->CreateFPSpecialConst(FPSpecial::PlusZero, r.a, r.b);
  }));
}
Term TermManager::mk_fp_neg_zero(const Sort& fp)
{
  ManagerImpl* m = live(*this, "TermManager::mk_fp_neg_zero");
  const detail::SortRec& r = fp_rec(m, fp, "TermManager::mk_fp_neg_zero", 0);
  return detail::make_term(m, detail::engine_call(m, "TermManager::mk_fp_neg_zero", [&] {
    return m->bm->CreateFPSpecialConst(FPSpecial::MinusZero, r.a, r.b);
  }));
}
Term TermManager::mk_fp_pos_inf(const Sort& fp)
{
  ManagerImpl* m = live(*this, "TermManager::mk_fp_pos_inf");
  const detail::SortRec& r = fp_rec(m, fp, "TermManager::mk_fp_pos_inf", 0);
  return detail::make_term(m, detail::engine_call(m, "TermManager::mk_fp_pos_inf", [&] {
    return m->bm->CreateFPSpecialConst(FPSpecial::PlusInfinity, r.a, r.b);
  }));
}
Term TermManager::mk_fp_neg_inf(const Sort& fp)
{
  ManagerImpl* m = live(*this, "TermManager::mk_fp_neg_inf");
  const detail::SortRec& r = fp_rec(m, fp, "TermManager::mk_fp_neg_inf", 0);
  return detail::make_term(m, detail::engine_call(m, "TermManager::mk_fp_neg_inf", [&] {
    return m->bm->CreateFPSpecialConst(FPSpecial::MinusInfinity, r.a, r.b);
  }));
}
Term TermManager::mk_fp_nan(const Sort& fp)
{
  ManagerImpl* m = live(*this, "TermManager::mk_fp_nan");
  const detail::SortRec& r = fp_rec(m, fp, "TermManager::mk_fp_nan", 0);
  return detail::make_term(m, detail::engine_call(m, "TermManager::mk_fp_nan", [&] {
    return m->bm->CreateFPSpecialConst(FPSpecial::NaN, r.a, r.b);
  }));
}

namespace
{
// Decimal big-integer helpers for the exact conversion of a double: the
// value is mantissa * 2^exponent, and the literal converters want decimal
// strings.
std::string mul_pow2(std::string dec, int k)
{
  // dec: decimal digits, no sign
  for (int i = 0; i < k; ++i)
  {
    int carry = 0;
    for (std::size_t j = dec.size(); j-- > 0;)
    {
      const int v = (dec[j] - '0') * 2 + carry;
      dec[j] = static_cast<char>('0' + (v % 10));
      carry = v / 10;
    }
    if (carry)
      dec.insert(dec.begin(), static_cast<char>('0' + carry));
  }
  return dec;
}

// A decimal literal, [+-]digits[.digits][(e|E)[+-]digits]: its sign, its
// significant digits (none for zero) and where the decimal point falls among
// them, the value being 0.digits x 10^point. The exponent saturates at
// +-2^62; the callers bound the point long before that matters.
struct DecimalLiteral
{
  bool negative = false;
  std::string digits;
  std::int64_t point = 0;
};

bool parse_decimal(std::string_view text, DecimalLiteral& d)
{
  constexpr std::int64_t saturated = std::int64_t{1} << 62;
  std::size_t i = 0;
  if (i < text.size() && (text[i] == '-' || text[i] == '+'))
    d.negative = text[i++] == '-';
  std::int64_t point = -1;
  bool any = false;
  for (; i < text.size() && text[i] != 'e' && text[i] != 'E'; ++i)
  {
    const char c = text[i];
    if (c == '.')
    {
      if (point >= 0)
        return false;
      point = static_cast<std::int64_t>(d.digits.size());
    }
    else if (c >= '0' && c <= '9')
    {
      any = true;
      d.digits.push_back(c);
    }
    else
      return false;
  }
  if (!any)
    return false;
  if (point < 0)
    point = static_cast<std::int64_t>(d.digits.size());
  std::int64_t exponent = 0;
  if (i < text.size())
  {
    ++i; // the e
    bool negative_exponent = false;
    if (i < text.size() && (text[i] == '-' || text[i] == '+'))
      negative_exponent = text[i++] == '-';
    if (i == text.size())
      return false;
    for (; i < text.size(); ++i)
    {
      if (text[i] < '0' || text[i] > '9')
        return false;
      exponent = exponent > (saturated - 9) / 10 ? saturated : exponent * 10 + (text[i] - '0');
    }
    if (negative_exponent)
      exponent = -exponent;
  }
  // leading zeros move the point, not the value
  const std::size_t zeros = std::min(d.digits.find_first_not_of('0'), d.digits.size());
  d.digits.erase(0, zeros);
  d.point = d.digits.empty() ? 0 : point - static_cast<std::int64_t>(zeros) + exponent;
  return true;
}

// The plain decimal form the literal converters take: "-0.0025", "100000",
// "7" ("-0" for a negative zero).
std::string plain_decimal(const DecimalLiteral& d)
{
  const std::string sign = d.negative ? "-" : "";
  if (d.digits.empty())
    return sign + "0";
  const std::int64_t n = static_cast<std::int64_t>(d.digits.size());
  if (d.point <= 0)
    return sign + "0." + std::string(static_cast<std::size_t>(-d.point), '0') + d.digits;
  if (d.point >= n)
    return sign + d.digits + std::string(static_cast<std::size_t>(d.point - n), '0');
  return sign + d.digits.substr(0, static_cast<std::size_t>(d.point)) + "." +
         d.digits.substr(static_cast<std::size_t>(d.point));
}

// Where a decimal point further out no longer changes a float literal's
// rounded value: from `hi` up every literal is at least 2^(emax+1), past the
// largest finite value, and from `lo` down every one lies below half the
// smallest subnormal; either way it rounds as the bound does, by its sign and
// the rounding mode alone.
void decimal_point_bounds(std::uint32_t eb, std::uint32_t sb, std::int64_t& lo, std::int64_t& hi)
{
  constexpr long double log10_2 = 0.301029995663981195213738894724493027L;
  const long double cap = std::ldexp(1.0L, 62);
  const long double emax = std::ldexp(1.0L, static_cast<int>(std::min<std::uint32_t>(eb, 20000)) - 1) - 1;
  const long double up = std::ceil((emax + 1) * log10_2) + 2;
  const long double down = std::ceil((emax + sb - 1) * log10_2) + 2;
  hi = up >= cap ? static_cast<std::int64_t>(cap) : static_cast<std::int64_t>(up);
  lo = down >= cap ? -static_cast<std::int64_t>(cap) : -static_cast<std::int64_t>(down);
}

// The Real arithmetic's number limits are 65536 bits, under 20,000 decimal
// digits; a literal whose point lies further out is refused unexpanded.
constexpr std::int64_t real_literal_point_limit = 100000;
} // namespace

Term TermManager::mk_fp(const Sort& fp, RoundingMode rm, double value)
{
  ManagerImpl* m = live(*this, "TermManager::mk_fp");
  const detail::SortRec& r = fp_rec(m, fp, "TermManager::mk_fp", 0);
  if (std::isnan(value))
    return mk_fp_nan(fp);
  if (std::isinf(value))
    return value > 0 ? mk_fp_pos_inf(fp) : mk_fp_neg_inf(fp);
  if (value == 0.0)
    return std::signbit(value) ? mk_fp_neg_zero(fp) : mk_fp_pos_zero(fp);
  std::uint64_t raw;
  std::memcpy(&raw, &value, sizeof raw);
  const bool negative = (raw >> 63) != 0;
  const int biased = static_cast<int>((raw >> 52) & 0x7ff);
  std::uint64_t mantissa = raw & ((std::uint64_t(1) << 52) - 1);
  int exponent;
  if (biased == 0)
    exponent = -1074;
  else
  {
    mantissa |= std::uint64_t(1) << 52;
    exponent = biased - 1075;
  }
  while ((mantissa & 1) == 0)
  {
    mantissa >>= 1;
    ++exponent;
  }
  std::string bits, err;
  bool ok;
  if (exponent >= 0)
    ok = decimalToPackedFPBits((negative ? "-" : "") + mul_pow2(std::to_string(mantissa), exponent),
                               r.a, r.b, detail::rm_encoding(rm), bits, err);
  else
    ok = rationalToPackedFPBits(std::to_string(mantissa), mul_pow2("1", -exponent), negative, r.a,
                                r.b, detail::rm_encoding(rm), bits, err);
  if (!ok)
    detail::fail(ErrorCode::UNSUPPORTED, "TermManager::mk_fp", err, 2, {}, {fp});
  return detail::make_term(m, m->fp_const_from_bits(r.a, r.b, m->bv_const_bits(r.a + r.b, bits)));
}
Term TermManager::mk_fp(const Sort& fp, RoundingMode rm, std::string_view text)
{
  ManagerImpl* m = live(*this, "TermManager::mk_fp");
  const detail::SortRec& r = fp_rec(m, fp, "TermManager::mk_fp", 0);
  std::string bits, err;
  bool ok = false;
  const std::size_t slash = text.find('/');
  if (slash != std::string_view::npos)
  {
    std::string num(text.substr(0, slash)), den(text.substr(slash + 1));
    bool negative = false;
    if (!num.empty() && (num[0] == '-' || num[0] == '+'))
    {
      negative = num[0] == '-';
      num.erase(0, 1);
    }
    if (num.empty() || den.empty() || den == "0" ||
        num.find_first_not_of("0123456789") != std::string::npos ||
        den.find_first_not_of("0123456789") != std::string::npos)
      detail::fail(ErrorCode::INVALID_ARGUMENT, "TermManager::mk_fp",
                   "'" + std::string(text) + "' is not a rational literal", 2);
    // the literal converters lose the sign of zero; "-0/1" is the negative zero
    if (negative && num.find_first_not_of('0') == std::string::npos)
      return mk_fp_neg_zero(fp);
    ok = rationalToPackedFPBits(num, den, negative, r.a, r.b, detail::rm_encoding(rm), bits, err);
  }
  else
  {
    DecimalLiteral d;
    if (!parse_decimal(text, d))
      detail::fail(ErrorCode::INVALID_ARGUMENT, "TermManager::mk_fp",
                   detail::literal_for_message(text) + " is not a decimal literal", 2);
    if (d.negative && d.digits.empty())
      return mk_fp_neg_zero(fp);
    std::int64_t lo, hi;
    decimal_point_bounds(r.a, r.b, lo, hi);
    d.point = std::clamp(d.point, lo, hi);
    ok = decimalToPackedFPBits(plain_decimal(d), r.a, r.b, detail::rm_encoding(rm), bits, err);
  }
  if (!ok)
    detail::fail(ErrorCode::UNSUPPORTED, "TermManager::mk_fp", err, 2, {}, {fp});
  return detail::make_term(m, m->fp_const_from_bits(r.a, r.b, m->bv_const_bits(r.a + r.b, bits)));
}
Term TermManager::mk_rm(RoundingMode rm)
{
  ManagerImpl* m = live(*this, "TermManager::mk_rm");
  return detail::make_term(m, m->rm_const(rm));
}

Term TermManager::mk_real(std::int64_t v)
{
  ManagerImpl* m = live(*this, "TermManager::mk_real");
  return detail::make_term(m, m->real_const("TermManager::mk_real", std::to_string(v)));
}
Term TermManager::mk_real(std::int64_t num, std::int64_t den)
{
  ManagerImpl* m = live(*this, "TermManager::mk_real");
  if (den == 0)
    detail::fail(ErrorCode::INVALID_ARGUMENT, "TermManager::mk_real", "the denominator is zero", 1);
  bool negative = (num < 0) != (den < 0);
  std::string n = std::to_string(num), d = std::to_string(den);
  if (!n.empty() && n[0] == '-')
    n.erase(0, 1);
  if (!d.empty() && d[0] == '-')
    d.erase(0, 1);
  return detail::make_term(m, m->real_const("TermManager::mk_real", (negative ? "-" : "") + n + "/" + d));
}
Term TermManager::mk_real(std::string_view literal)
{
  ManagerImpl* m = live(*this, "TermManager::mk_real");
  std::string text(literal);
  if (text.find('/') == std::string::npos)
  {
    DecimalLiteral d;
    if (!parse_decimal(text, d))
      detail::fail(ErrorCode::INVALID_ARGUMENT, "TermManager::mk_real",
                   detail::literal_for_message(text) + " is not a real literal", 0);
    if (d.point > real_literal_point_limit || d.point < -real_literal_point_limit)
      detail::fail(ErrorCode::UNSUPPORTED, "TermManager::mk_real",
                   detail::literal_for_message(text) + " exceeds the exact-arithmetic budget: its " +
                       "exponent puts it beyond the number limits",
                   0);
    text = plain_decimal(d);
  }
  return detail::make_term(m, m->real_const("TermManager::mk_real", text));
}

Term TermManager::mk_const_array(const Sort& array_sort, const Term& element)
{
  ManagerImpl* m = live(*this, "TermManager::mk_const_array");
  if (array_sort.is_null())
    detail::fail(ErrorCode::NULL_HANDLE, "TermManager::mk_const_array", "the sort is null", 0);
  if (array_sort.impl_manager() != m)
    detail::fail(ErrorCode::FOREIGN_MANAGER, "TermManager::mk_const_array",
                 "the sort belongs to another term manager", 0);
  if (element.is_null())
    detail::fail(ErrorCode::NULL_HANDLE, "TermManager::mk_const_array", "the element is null", 1);
  return detail::make_term(m, detail::build_term(m, "TermManager::mk_const_array", Kind::CONST_ARRAY,
                                                 {detail::node_of(element)}, {},
                                                 array_sort.impl_index()));
}

Term TermManager::mk_term(Kind k, const std::vector<Term>& args,
                          const std::vector<std::uint32_t>& indices,
                          std::optional<Sort> result_sort)
{
  ManagerImpl* m = live(*this, "TermManager::mk_term");
  std::vector<ASTNode> nodes;
  nodes.reserve(args.size());
  for (std::size_t i = 0; i < args.size(); ++i)
  {
    if (args[i].is_null())
      detail::fail(ErrorCode::NULL_HANDLE, "TermManager::mk_term", "the term is null",
                   static_cast<int>(i));
    if (args[i].impl_manager() != m)
      detail::fail(ErrorCode::FOREIGN_MANAGER, "TermManager::mk_term",
                   "the term belongs to another term manager", static_cast<int>(i));
    nodes.push_back(detail::node_of(args[i]));
  }
  std::optional<std::uint32_t> rs;
  if (result_sort.has_value())
  {
    if (result_sort->is_null())
      detail::fail(ErrorCode::NULL_HANDLE, "TermManager::mk_term", "the result sort is null");
    if (result_sort->impl_manager() != m)
      detail::fail(ErrorCode::FOREIGN_MANAGER, "TermManager::mk_term",
                   "the result sort belongs to another term manager");
    rs = result_sort->impl_index();
  }
  return detail::make_term(m, detail::build_term(m, "TermManager::mk_term", k, nodes, indices, rs));
}
Term TermManager::mk_term(Kind k, std::initializer_list<Term> args,
                          std::initializer_list<std::uint32_t> indices)
{
  return mk_term(k, std::vector<Term>(args), std::vector<std::uint32_t>(indices), std::nullopt);
}

Term TermManager::simplify(const Term& t) const
{
  ManagerImpl* m = live(*this, "TermManager::simplify");
  if (t.is_null())
    detail::fail(ErrorCode::NULL_HANDLE, "TermManager::simplify", "the term is null", 0);
  if (t.impl_manager() != m)
    detail::fail(ErrorCode::FOREIGN_MANAGER, "TermManager::simplify",
                 "the term belongs to another term manager", 0);
  return detail::engine_call(m, "TermManager::simplify", [&]() -> Term {
  // Rebuild bottom-up through the folding factory, on an explicit stack (a
  // deep term costs heap, not the C++ stack); a memo bounds the work by the
  // DAG size. A conversion to a Real rebuilds from its operand, anything else
  // the factory takes from its children, and a leaf, an application or a
  // Real term is kept.
  std::unordered_map<ASTNode, ASTNode, ASTNode::ASTNodeHasher> memo;
  const auto inputs = [&](const ASTNode& n) -> ASTVec {
    const ASTNode operand = n.GetKind() == ITE ? m->bm->FpToRealOperand(n) : ASTNode();
    if (!operand.IsNull())
      return ASTVec{operand};
    if (n.Degree() > 0 && n.GetKind() != UF_APPLY && !n.isRealTerm())
      return ASTVec(n.GetChildren().begin(), n.GetChildren().end());
    return ASTVec();
  };
  const auto rebuild_one = [&](const ASTNode& n) -> ASTNode {
    const ASTNode operand = n.GetKind() == ITE ? m->bm->FpToRealOperand(n) : ASTNode();
    if (!operand.IsNull())
    {
      // A conversion is rebuilt from its simplified operand by the
      // construction itself, which folds a float value to its Real value.
      const ASTNode& simplified = memo.at(operand);
      return simplified == operand ? n : m->bm->CreateFpToReal(simplified);
    }
    if (n.Degree() == 0 || n.GetKind() == UF_APPLY || n.isRealTerm())
      return n;
    // Always through the folding factory, children changed or not: a node
    // may have been built without folding (parse_term, or a non-simplifying
    // manager), and a node that folds no further comes back as itself from a
    // hash lookup.
    ASTVec kids;
    kids.reserve(n.Degree());
    for (const ASTNode& c : n.GetChildren())
      kids.push_back(memo.at(c));
    NodeFactory* f = m->folding_factory();
    if (n.GetType() == BOOLEAN_TYPE)
      return f->CreateNode(n.GetKind(), kids);
    if (n.GetType() == ARRAY_TYPE)
      return f->CreateArrayTerm(n.GetKind(), n.GetIndexWidth(), n.GetValueWidth(), kids);
    ASTNode out = f->CreateTerm(n.GetKind(), n.GetValueWidth(), kids);
    if (n.GetExpWidth() != 0)
      out = FloatBlaster::withFormat(m->bm, out, n.GetExpWidth(), n.GetSigWidth());
    return out;
  };
  const ASTNode root = detail::node_of(t);
  std::vector<std::pair<ASTNode, bool>> stack{{root, false}};
  while (!stack.empty())
  {
    const auto [n, expanded] = stack.back();
    if (memo.count(n) != 0)
    {
      stack.pop_back();
      continue;
    }
    if (!expanded)
    {
      stack.back().second = true;
      for (const ASTNode& c : inputs(n))
        if (memo.count(c) == 0)
          stack.emplace_back(c, false);
      continue;
    }
    stack.pop_back();
    memo.emplace(n, rebuild_one(n));
  }
  ASTNode out = memo.at(root);
  // A closed term (no symbol, no array, no function anywhere in it) is a
  // value: evaluate it through the model evaluator over an empty snapshot,
  // which folds what the factory leaves alone (a ground distinct, a Real
  // ordering, a partial floating-point operation over values). A term with
  // a free symbol is never evaluated: the evaluator completes an absent
  // symbol with its sort's default, which is a model's business and would
  // turn `(= a1 a2)` over two declared arrays into `true` here.
  const auto closed = [](const ASTNode& from) {
    std::unordered_set<ASTNode, ASTNode::ASTNodeHasher> seen;
    std::vector<ASTNode> todo{from};
    while (!todo.empty())
    {
      const ASTNode n = todo.back();
      todo.pop_back();
      if (n.GetKind() == SYMBOL || n.GetKind() == UF_APPLY)
        return false;
      if (!seen.insert(n).second)
        continue;
      for (const ASTNode& c : n.GetChildren())
        todo.push_back(c);
    }
    return true;
  };
  if (!out.isConstant() && closed(out))
  {
    detail::ModelSnapshot empty;
    empty.mgr = m;
    m->retain();
    try
    {
      detail::Evaluator ev(empty, "TermManager::simplify", false);
      const ASTNode v = ev.eval(out);
      if (!ev.incomplete() && v.isConstant())
        out = v;
    }
    catch (const Error&)
    {
      // not evaluable: keep the rebuilt term
    }
  }
  return detail::make_term(m, out);
  });
}

} // namespace api
} // namespace stp
