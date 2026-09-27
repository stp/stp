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

// c_interface2.cpp -- libstp2: the 2.x C API (stp/c_interface.h) over the 3.x
// C API (stp/stp.h). This file holds the checker's lifecycle, the error
// policy, ownership, options and flags, the assertion stack and queries,
// model reads, the printers, the parsers, uninterpreted functions and the
// introspection entry points; c_interface2_terms.cpp holds the constructors.
//
// The behaviour reproduced is that of STP 2.x's own implementation of the
// header over the engine (lib/Interface/c_interface.cpp, removed once this
// library replaced it); NOTES.md records where the two differ.

#include "Compat2.h"

#include <algorithm>
#include <atomic>
#include <cinttypes>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <mutex>
#include <sstream>

#ifdef _WIN32
#include <io.h>
#define compat2_write _write
#else
#include <unistd.h>
#define compat2_write write
#endif

// Workaround for a 3.x defect (NOTES.md, "3.x defects"): the constant
// bit-vector library keeps its machine constants in thread-local storage, and
// lib/Api/Manager.cpp boots it through a process-wide std::call_once, so a
// manager created on any thread but the first one to create a manager runs
// with zeroed constants; its first constant then under-allocates and corrupts
// the heap. 2.x booted the library on every vc_createValidityChecker, which is
// what made checkers on several threads work; the shim does the same, once per
// thread. This is the one symbol used beyond stp.h; it is the library's own
// C-linkage entry point, and the declaration goes away with the defect.
extern "C" int BitVector_Boot(void);

namespace compat2
{

// ============================================================ process state

namespace
{
thread_local bool t_constant_bv_booted = false;

void boot_constant_bv_on_this_thread()
{
  if (t_constant_bv_booted)
    return;
  if (BitVector_Boot() != 0)
    fatal("vc_createValidityChecker: the constant bit-vector library failed to boot");
  t_constant_bv_booted = true;
}


void (*g_handler)(const char*) = nullptr;
std::atomic<int> g_policy{STP_ON_ERROR_ABORT};

std::mutex g_mutex;
std::unordered_set<VCImpl*> g_live_vcs;
// The 'u' registry: every live handle of a checker that has tracking on,
// with its owner. Consulted only by the UF entry points, which have to reject
// a stale, foreign or invalid pointer without dereferencing it.
std::unordered_map<Handle*, VCImpl*> g_registry;
std::atomic<bool> g_registry_used{false};
// UF declaration identities: monotonic, never reused, owner known while the
// owning checker lives.
std::unordered_map<UFDeclHandle, VCImpl*> g_uf_owner;
std::uint64_t g_next_uf = 0;

bool vc_is_live(VCImpl* vc)
{
  std::lock_guard<std::mutex> lock(g_mutex);
  return g_live_vcs.count(vc) != 0;
}

void stdout_sink(const char* text, std::size_t len, void*)
{
  std::fwrite(text, 1, len, stdout);
}

} // namespace

// ============================================================ diagnostics

void report(const std::string& msg)
{
  if (g_handler != nullptr)
    g_handler(msg.c_str());
  else
    std::cerr << "CInterface: " << msg << std::endl;
}

void fatal(const std::string& msg)
{
  if (g_handler != nullptr)
    g_handler(msg.c_str());
  std::cerr << "Fatal Error: " << msg << std::endl;
  if (g_policy.load() != STP_ON_ERROR_RETURN)
    std::abort();
}

std::string take_error(VCImpl* vc, stp_error_code* code)
{
  std::string out = "unknown error";
  if (code != nullptr)
    *code = static_cast<stp_error_code>(0);
  const stp_error* e = vc != nullptr ? stp_tm_error(vc->tm) : nullptr;
  if (e == nullptr)
    e = stp_last_error();
  if (e != nullptr)
  {
    out = std::string(e->function != nullptr ? e->function : "stp") + ": " +
          (e->message != nullptr ? e->message : "");
    if (code != nullptr)
      *code = e->code;
  }
  if (vc != nullptr)
  {
    stp_tm_clear_error(vc->tm);
    if (vc->solver != nullptr && stp_solver_failed(vc->solver) != nullptr)
      stp_solver_clear_error(vc->solver);
  }
  return out;
}

// ============================================================ handles

VCImpl* vcimpl(VC vc, const char* who)
{
  if (vc == nullptr)
  {
    fatal(std::string("CInterface: ") + who + ": null validity checker");
    return nullptr;
  }
  return static_cast<VCImpl*>(vc);
}

Handle* handle(Expr e)
{
  return static_cast<Handle*>(e);
}

stp_term term_of(Expr e, const char* who)
{
  Handle* h = handle(e);
  if (h == nullptr)
  {
    // 2.x's wording, which its acceptance tests pin.
    fatal(std::string("CInterface: ") + who + " received a null Expr");
    return nullptr;
  }
  if (h->is_type())
  {
    fatal(std::string("CInterface: ") + who + ": a type handle is not an expression");
    return nullptr;
  }
  return h->term;
}

stp_sort type_of(Type t, const char* who)
{
  Handle* h = handle(t);
  if (h == nullptr)
  {
    fatal(std::string("CInterface: ") + who + ": null type handle");
    return nullptr;
  }
  if (!h->is_type())
  {
    fatal(std::string("CInterface: ") + who + " expects a type node: ");
    return nullptr;
  }
  return h->sort;
}

stp_sort sort_of(Expr e)
{
  Handle* h = handle(e);
  if (h == nullptr)
    return nullptr;
  return h->is_type() ? h->sort : stp_term_sort(h->term);
}

Expr wrap(VCImpl* vc, stp_term t, bool checker_owned)
{
  if (t == nullptr)
    return nullptr;
  Handle* h = new Handle;
  h->term = t;
  h->vc = vc;
  if (checker_owned && vc->exprdelete)
  {
    h->checker_owned = true;
    vc->persist.insert(h);
  }
  if (vc->tracking)
    registry_add(h);
  return h;
}

Type wrap_type(VCImpl* vc, stp_sort s)
{
  if (s == nullptr)
    return nullptr;
  Handle* h = new Handle;
  h->sort = s;
  h->vc = vc;
  if (vc->exprdelete)
  {
    h->checker_owned = true;
    vc->persist.insert(h);
  }
  if (vc->tracking)
    registry_add(h);
  return h;
}

// Releases the reference and frees the wrapper; the persist set and the
// registry are the caller's to update.
void free_handle(Handle* h)
{
  if (h->term != nullptr)
    stp_term_release(h->term);
  delete h;
}

void registry_add(Handle* h)
{
  std::lock_guard<std::mutex> lock(g_mutex);
  g_registry[h] = h->vc;
  g_registry_used.store(true);
}

void registry_erase(Handle* h)
{
  if (!g_registry_used.load())
    return;
  std::lock_guard<std::mutex> lock(g_mutex);
  g_registry.erase(h);
}

bool registry_holds(VCImpl* vc, Expr e)
{
  if (e == nullptr)
    return false;
  std::lock_guard<std::mutex> lock(g_mutex);
  auto it = g_registry.find(static_cast<Handle*>(e));
  return it != g_registry.end() && it->second == vc;
}

void enable_tracking(VCImpl* vc)
{
  if (vc->tracking)
    return;
  vc->tracking = true;
  // As 2.x did: the checker-owned handles that predate the flag are adopted;
  // caller-owned ones made before it stay outside the registry.
  std::lock_guard<std::mutex> lock(g_mutex);
  for (Handle* h : vc->persist)
    g_registry[h] = vc;
  g_registry_used.store(true);
}

// ============================================================ sorts

stp_sort_kind sort_kind(stp_sort s)
{
  stp_sort_kind k;
  if (s == nullptr || stp_sort_get_kind(s, &k) != STP_OK)
    return static_cast<stp_sort_kind>(-1);
  return k;
}
bool is_bool(stp_sort s) { return sort_kind(s) == STP_SORT_BOOL; }
bool is_bv(stp_sort s) { return sort_kind(s) == STP_SORT_BV; }
bool is_fp(stp_sort s) { return sort_kind(s) == STP_SORT_FP; }
bool is_rm(stp_sort s) { return sort_kind(s) == STP_SORT_RM; }
bool is_array(stp_sort s) { return sort_kind(s) == STP_SORT_ARRAY; }
bool is_real(stp_sort s) { return sort_kind(s) == STP_SORT_REAL; }
bool is_fun(stp_sort s) { return sort_kind(s) == STP_SORT_FUN; }

std::uint32_t bv_width(stp_sort s)
{
  std::uint32_t w = 0;
  if (is_bv(s) && stp_sort_bv_size(s, &w) == STP_OK)
    return w;
  return 0;
}

std::uint32_t packed_width(stp_sort s)
{
  std::uint32_t a = 0, b = 0;
  switch (sort_kind(s))
  {
    case STP_SORT_BV:
      return bv_width(s);
    case STP_SORT_FP:
      stp_sort_fp_exp_size(s, &a);
      stp_sort_fp_sig_size(s, &b);
      return a + b;
    case STP_SORT_RM:
      return 5;
    case STP_SORT_ARRAY:
      return packed_width(stp_sort_array_element(s));
    default:
      return 0;
  }
}

std::uint32_t index_width(stp_sort s)
{
  if (!is_array(s))
    return 0;
  return packed_width(stp_sort_array_index(s));
}

bool fp_format(stp_sort s, std::uint32_t& eb, std::uint32_t& sb)
{
  if (is_array(s))
    return fp_format(stp_sort_array_element(s), eb, sb);
  if (!is_fp(s))
    return false;
  return stp_sort_fp_exp_size(s, &eb) == STP_OK && stp_sort_fp_sig_size(s, &sb) == STP_OK;
}

std::string sort_text(VCImpl*, stp_sort s)
{
  if (s == nullptr)
    return "?";
  if (is_fun(s))
  {
    std::uint32_t n = 0;
    stp_sort_fun_arity(s, &n);
    std::string out = "(";
    for (std::uint32_t i = 0; i < n; ++i)
      out += (i ? " " : "") + sort_text(nullptr, stp_sort_fun_domain(s, i));
    return out + ") " + sort_text(nullptr, stp_sort_fun_codomain(s));
  }
  char* t = stp_sort_str(s);
  std::string out = t != nullptr ? t : "?";
  stp_free(t);
  return out;
}

std::string type_text(stp_sort s)
{
  std::uint32_t eb = 0, sb = 0;
  switch (sort_kind(s))
  {
    case STP_SORT_BOOL:
      return "BOOLEAN";
    case STP_SORT_BV:
      return "BITVECTOR(" + std::to_string(bv_width(s)) + ")";
    case STP_SORT_ARRAY:
      return "ARRAY " + type_text(stp_sort_array_index(s)) + " OF " +
             type_text(stp_sort_array_element(s));
    case STP_SORT_FP:
      fp_format(s, eb, sb);
      return "FLOATINGPOINT(" + std::to_string(eb) + ", " + std::to_string(sb) + ")";
    case STP_SORT_RM:
      return "ROUNDINGMODE";
    case STP_SORT_REAL:
      return "REAL";
    default:
      return sort_text(nullptr, s);
  }
}

// ============================================================ solver

namespace
{

void install_sink(VCImpl* vc)
{
  if (vc->solver != nullptr && vc->flag_diag)
    stp_solver_set_diagnostic_sink(vc->solver, stdout_sink, nullptr);
}

// A new solver over the option record, with the assertion stack replayed.
bool rebuild_solver(VCImpl* vc)
{
  if (vc->solver != nullptr)
  {
    stp_solver_delete(vc->solver);
    vc->solver = nullptr;
  }
  vc->solver = stp_solver_new(vc->tm, vc->opts);
  if (vc->solver == nullptr)
  {
    fatal("CInterface: cannot create the solver: " + take_error(vc));
    return false;
  }
  install_sink(vc);
  for (std::size_t l = 0; l < vc->levels.size(); ++l)
  {
    if (l > 0 && stp_solver_push(vc->solver, 1) != STP_OK)
      report("rebuilding the solver: " + take_error(vc));
    for (stp_term t : vc->levels[l])
      if (stp_solver_assert(vc->solver, t) != STP_OK)
        report("rebuilding the solver: " + take_error(vc));
  }
  return true;
}

} // namespace

stp_solver ensure_solver(VCImpl* vc)
{
  if (vc->solver != nullptr)
    return vc->solver;
  rebuild_solver(vc);
  return vc->solver;
}

bool set_option(VCImpl* vc, const char* name, const std::string& value,
                const char* what)
{
  if (stp_options_set_str(vc->opts, name, value.c_str()) != STP_OK)
  {
    const stp_error* e = stp_options_error(vc->opts);
    report(std::string(what) + ": " +
           (e != nullptr && e->message != nullptr ? e->message : "refused"));
    stp_options_clear_error(vc->opts);
    return false;
  }
  if (vc->solver == nullptr)
    return true;
  if (stp_solver_set_str(vc->solver, name, value.c_str()) == STP_OK)
    return true;
  stp_error_code code;
  const std::string msg = take_error(vc, &code);
  if (code == STP_ERR_OPTION_TIMING)
  {
    // 2.x setters were write-only and took effect at the next query. The
    // record already holds the value: a solver rebuilt from it, with the
    // stack replayed, is exactly that.
    return rebuild_solver(vc);
  }
  report(std::string(what) + ": " + msg);
  return false;
}

void discard_model(VCImpl* vc)
{
  if (vc->model != nullptr)
  {
    stp_model_release(vc->model);
    vc->model = nullptr;
  }
  vc->uf_certified = false;
}

Expr fp_result(VCImpl* vc, stp_term t)
{
  return wrap(vc, t, /* checker_owned */ true);
}

unsigned rm_onehot(stp_rm rm)
{
  switch (rm)
  {
    case STP_RM_RNE: return VC_RM_RNE;
    case STP_RM_RTP: return VC_RM_RTP;
    case STP_RM_RTN: return VC_RM_RTN;
    case STP_RM_RTZ: return VC_RM_RTZ;
    case STP_RM_RNA: return VC_RM_RNA;
    case STP_RM_MAX_ENUM: break;
  }
  return VC_RM_RNE;
}

bool rm_from_onehot(unsigned bits, stp_rm& out)
{
  switch (bits)
  {
    case VC_RM_RNE: out = STP_RM_RNE; return true;
    case VC_RM_RTP: out = STP_RM_RTP; return true;
    case VC_RM_RTN: out = STP_RM_RTN; return true;
    case VC_RM_RTZ: out = STP_RM_RTZ; return true;
    case VC_RM_RNA: out = STP_RM_RNA; return true;
    default: return false;
  }
}

void to_buffer(const std::string& s, char** buf, std::size_t* len)
{
  const std::size_t size = s.size() + 1;
  *buf = static_cast<char*>(std::malloc(size));
  if (*buf == nullptr)
  {
    std::fprintf(stderr, "malloc(%zu) failed.", size);
    std::abort();
  }
  std::memcpy(*buf, s.c_str(), size);
  if (len != nullptr)
    *len = size;
}

namespace
{

// The bits of a value term MSB first: a bit-vector's own, a float's IEEE
// interchange bits, a rounding mode's one-hot 5-bit carrier.
bool value_bits(stp_term t, std::string& bits)
{
  if (t == nullptr || !stp_term_is_value(t))
    return false;
  const stp_sort s = stp_term_sort(t);
  if (is_bv(s))
  {
    char* b = stp_term_to_bv_string(t, 2, true);
    if (b == nullptr)
      return false;
    bits = b;
    stp_free(b);
    return true;
  }
  if (is_fp(s))
  {
    char* b = stp_term_fp_bits(t);
    if (b == nullptr)
      return false;
    bits = b;
    stp_free(b);
    return true;
  }
  if (is_rm(s))
  {
    stp_rm rm;
    if (stp_term_to_rm(t, &rm) != STP_OK)
      return false;
    const unsigned v = rm_onehot(rm);
    bits.clear();
    for (int i = 4; i >= 0; --i)
      bits += ((v >> i) & 1u) ? '1' : '0';
    return true;
  }
  return false;
}

} // namespace

bool value_uint64(stp_term t, std::uint64_t& out, const char* who)
{
  std::string bits;
  if (!value_bits(t, bits))
  {
    fatal(std::string(who) + ": Attempting to extract int value from a NON-constant BITVECTOR: ");
    return false;
  }
  out = 0;
  bool saturate = false;
  for (std::size_t i = 0; i < bits.size(); ++i)
  {
    const bool one = bits[i] == '1';
    if (bits.size() - i > 64)
    {
      if (one)
        saturate = true;
      continue;
    }
    out = (out << 1) | (one ? 1u : 0u);
  }
  if (saturate)
    out = UINT64_MAX;
  return true;
}

// ============================================================ presentation-language text

std::string cvc_text(VCImpl* vc, stp_term t, const char* who, bool* ok)
{
  char* s = stp_term_to_string(t, STP_FORMAT_CVC, false);
  if (s == nullptr)
  {
    stp_error_code code;
    const std::string err = take_error(vc, &code);
    if (ok != nullptr)
      *ok = false;
    if (code == STP_ERR_UNSUPPORTED)
      fatal(std::string("CInterface: ") + who +
            ": the presentation language has no floating-point syntax; print "
            "this with SMTLIB2_PrintBack (vc_printSMTLIB2 in the C API)");
    else
      fatal(std::string("CInterface: ") + who + ": " + err);
    return std::string();
  }
  if (ok != nullptr)
    *ok = true;
  std::string out(s);
  stp_free(s);
  return out;
}

namespace
{

std::string trim(std::string s)
{
  while (!s.empty() && std::isspace(static_cast<unsigned char>(s.back())))
    s.pop_back();
  std::size_t i = 0;
  while (i < s.size() && std::isspace(static_cast<unsigned char>(s[i])))
    ++i;
  return s.substr(i);
}

std::string bits_to_cvc(VCImpl* vc, const std::string& bits)
{
  // Through the engine's own printer, so a 32-bit value prints 0x0000002A and
  // a 5-bit one 0b00001 exactly as 2.x printed the packed carrier.
  stp_term bv = stp_mk_bv_str(vc->tm, static_cast<std::uint32_t>(bits.size()), bits.c_str(), 2);
  if (bv == nullptr)
  {
    take_error(vc);
    return "0b" + bits;
  }
  char* s = stp_term_to_string(bv, STP_FORMAT_CVC, false);
  std::string out = s != nullptr ? trim(s) : "0b" + bits;
  stp_free(s);
  stp_term_release(bv);
  return out;
}

} // namespace

std::string cvc_value_text(VCImpl* vc, stp_term value)
{
  const stp_sort s = stp_term_sort(value);
  if (is_bool(s))
  {
    bool b = false;
    stp_term_to_bool(value, &b);
    return b ? "TRUE" : "FALSE";
  }
  std::string bits;
  if (value_bits(value, bits))
    return bits_to_cvc(vc, bits);
  char* t = stp_term_str(value);
  std::string out = t != nullptr ? trim(t) : "?";
  stp_free(t);
  return out;
}

} // namespace compat2

using namespace compat2;

// ============================================================ versions

const char* get_git_version_sha(void)
{
  return stp_get_version().git_sha;
}

const char* get_git_version_tag(void)
{
  return stp_get_version().git_tag;
}

const char* get_compilation_env(void)
{
  return stp_get_version().build_info;
}

// ============================================================ flags

namespace
{

std::string bool_text(int v)
{
  return v != 0 ? "true" : "false";
}

// The interface passes an int for fields that are unsigned in the engine.
bool non_negative(int v, const char* flag)
{
  if (v >= 0)
    return true;
  report(std::string(flag) + " must not be negative");
  return false;
}

// The FP_ABSTRACTION_OPS / CHAIN_OPS bit mask as the option's name list.
bool fp_ops_names(int mask, const char* flag, const char* empty, std::string& out)
{
  static const char* const names[] = {"mul", "div",  "sqrt", "add",    "sub",
                                      "fma", "rem",  "rti",  "to_sbv", "to_ubv"};
  if (mask == 0)
  {
    out = empty;
    return true;
  }
  if (mask >= (1 << 10))
  {
    report(std::string(flag) + ": unknown bit in the operation mask");
    return false;
  }
  out.clear();
  for (int i = 0; i < 10; ++i)
    if (mask & (1 << i))
      out += (out.empty() ? "" : ",") + std::string(names[i]);
  return true;
}

const char* cnf_effort_name(int v)
{
  static const char* const names[] = {"very-low", "low",          "medium",    "high",
                                      "very-high", "auto",         "new-very-low", "new-low",
                                      "new-medium", "gia-low",     "gia-high",  "gia-very-high",
                                      "new-high"};
  if (v < 0 || v > 12)
    return nullptr;
  return names[v];
}

bool use_backend(VCImpl* vc, const char* name)
{
  if (!stp_has_sat_backend(name))
    return false;
  if (!set_option(vc, "sat-backend", name, "sat-backend"))
    return false;
  vc->backend = name;
  return true;
}

// The backend a fresh checker runs: the engine's own 'auto' order.
std::string default_backend()
{
  if (stp_has_sat_backend("cryptominisat"))
    return "cryptominisat";
  if (stp_has_sat_backend("cadical"))
    return "cadical";
  return "minisat";
}

} // namespace

void process_argument(const char ch, VC vcp)
{
  VCImpl* vc = vcimpl(vcp, "process_argument");
  if (vc == nullptr)
    return;
  switch (ch)
  {
    case 'a':
      set_option(vc, "disable-opt-inc", "true", "flag 'a'");
      break;
    case 'c':
      set_option(vc, "produce-models", "true", "flag 'c'");
      break;
    case 'd':
      set_option(vc, "produce-models", "true", "flag 'd'");
      set_option(vc, "check-sanity", "true", "flag 'd'");
      break;
    case 'h':
      fatal("CInterface: process_argument: 'h' (help) is not a flag a library can act on");
      break;
    case 'i':
      set_option(vc, "incremental", "on", "flag 'i'");
      break;
    case 'm':
      vc->flag_m = true;
      break;
    case 'n':
      vc->flag_n = true;
      break;
    case 'p':
      vc->flag_p = true;
      break;
    case 'q':
      vc->flag_diag = true;
      set_option(vc, "print-arrayval", "true", "flag 'q'");
      install_sink(vc);
      break;
    case 'r':
      set_option(vc, "ackermanize", "true", "flag 'r'");
      break;
    case 's':
      vc->flag_diag = true;
      set_option(vc, "print-functionstat", "true", "flag 's'");
      install_sink(vc);
      break;
    case 't':
      vc->flag_diag = true;
      set_option(vc, "print-quickstat", "true", "flag 't'");
      install_sink(vc);
      break;
    case 'u':
      vc->flag_u = true;
      set_option(vc, "uninterpreted-functions", "on", "flag 'u'");
      enable_tracking(vc);
      break;
    case 'v':
      vc->flag_diag = true;
      set_option(vc, "print-nodes", "true", "flag 'v'");
      install_sink(vc);
      break;
    case 'w':
      set_option(vc, "switch-word", "true", "flag 'w'");
      break;
    case 'x':
      vc->flag_x = true;
      set_option(vc, "array-equality", "on", "flag 'x'");
      // 2.x completed an unobserved array cell to 0x00 with this flag and to
      // 0xFF without it.
      set_option(vc, "model-array-fill", "zero", "flag 'x'");
      break;
    case 'y':
      vc->flag_diag = true;
      set_option(vc, "print-counterexbin", "true", "flag 'y'");
      install_sink(vc);
      break;
    default:
      fatal(std::string("CInterface: process_argument: unrecognised flag '") + ch + "'");
      break;
  }
}

void vc_setFlags(VC vc, char c, int /* num_absrefine */)
{
  process_argument(c, vc);
}

void vc_setFlag(VC vc, char c)
{
  process_argument(c, vc);
}

void vc_setInterfaceFlags(VC vcp, enum ifaceflag_t f, int v)
{
  VCImpl* vc = vcimpl(vcp, "vc_setInterfaceFlags");
  if (vc == nullptr)
    return;
  const std::string sv = std::to_string(v);
  std::string names;
  switch (f)
  {
    case EXPRDELETE:
      vc->exprdelete = v != 0;
      break;
    case MS:
    case MSP:
      use_backend(vc, "minisat");
      break;
    case SMS:
      use_backend(vc, "simplifying-minisat");
      break;
    case CMS4:
      use_backend(vc, "cryptominisat");
      break;
    case CADICAL:
      use_backend(vc, "cadical");
      break;
    case INCREMENTAL_AUTO_ENGAGE_AT:
      // a negative value restores the default, which is -1 by name
      set_option(vc, "incremental-auto-engage-at", v < 0 ? "-1" : sv, "INCREMENTAL_AUTO_ENGAGE_AT");
      break;
    case UF_NARROW_RESULTS:
      set_option(vc, "uf-narrow-results", bool_text(v), "UF_NARROW_RESULTS");
      break;
    case UF_EQUALITY_INJECTIVITY:
      set_option(vc, "uf-inject-args", bool_text(v), "UF_EQUALITY_INJECTIVITY");
      break;
    case UF_LEMMAS_PER_ROUND:
      if (non_negative(v, "UF_LEMMAS_PER_ROUND"))
        set_option(vc, "uf-lemmas-per-round", sv, "UF_LEMMAS_PER_ROUND");
      break;
    case UF_ACKERMANN:
      if (v == 0)
        set_option(vc, "uf-ackermann", "auto", "UF_ACKERMANN");
      else if (v == 1)
        set_option(vc, "uf-ackermann", "on", "UF_ACKERMANN");
      else if (v == 2)
        set_option(vc, "uf-ackermann", "off", "UF_ACKERMANN");
      else
        report("UF_ACKERMANN must be 0 (auto), 1 (on) or 2 (off)");
      break;
    case UF_ACKERMANN_BUDGET:
      if (non_negative(v, "UF_ACKERMANN_BUDGET"))
        set_option(vc, "uf-ackermann-budget", sv, "UF_ACKERMANN_BUDGET");
      break;
    case UF_PHASE_HINTS:
      set_option(vc, "uf-phase-hints", bool_text(v), "UF_PHASE_HINTS");
      break;
    case UF_SORT_WIDTH:
      // A manager-scoped, construction-time setting in 3.x, and a sort no
      // C API entry point can declare: recorded, and otherwise inert.
      if (v < 1 || v > 1024)
        report("UF_SORT_WIDTH must be between 1 and 1024");
      else
        vc->uf_sort_width = v;
      break;
    case DISTINCT_ORDERING:
      set_option(vc, "distinct-ordering", bool_text(v), "DISTINCT_ORDERING");
      break;
    case AIG_NODE_BUDGET:
      if (v < -1)
        report("AIG_NODE_BUDGET must be -1 (no limit) or a count");
      else
        set_option(vc, "aig-node-budget", sv, "AIG_NODE_BUDGET");
      break;
    case BV_EQ_ABSTRACTION:
      set_option(vc, "bv-eq-abstraction", bool_text(v), "BV_EQ_ABSTRACTION");
      break;
    case BV_ABSTRACTION_WIDTH:
      if (non_negative(v, "BV_ABSTRACTION_WIDTH"))
        set_option(vc, "bv-abstraction-width", sv, "BV_ABSTRACTION_WIDTH");
      break;
    case BV_EQ_REFINE_WIDTH:
      if (non_negative(v, "BV_EQ_REFINE_WIDTH"))
        set_option(vc, "bv-eq-refine-width", sv, "BV_EQ_REFINE_WIDTH");
      break;
    case BV_TERM_ABSTRACTION:
      set_option(vc, "bv-term-abstraction", bool_text(v), "BV_TERM_ABSTRACTION");
      break;
    case BV_TERM_ABSTRACTION_MULT:
      set_option(vc, "bv-term-abstraction-mult", bool_text(v), "BV_TERM_ABSTRACTION_MULT");
      // This flag covered division and remainder before the DIVMOD switch
      // existed, and still does unless the caller has named DIV/MOD itself.
      if (!vc->divmod_explicit)
        set_option(vc, "bv-term-abstraction-divmod", bool_text(v), "BV_TERM_ABSTRACTION_MULT");
      break;
    case BV_TERM_ABSTRACTION_ROUNDS:
      if (non_negative(v, "BV_TERM_ABSTRACTION_ROUNDS"))
        set_option(vc, "bv-term-abstraction-rounds", sv, "BV_TERM_ABSTRACTION_ROUNDS");
      break;
    case BV_TERM_ABSTRACTION_SCHEMAS:
      set_option(vc, "bv-term-abstraction-schemas", bool_text(v), "BV_TERM_ABSTRACTION_SCHEMAS");
      break;
    case BV_TERM_ABSTRACTION_VALUE_DIVISOR:
      if (non_negative(v, "BV_TERM_ABSTRACTION_VALUE_DIVISOR"))
        set_option(vc, "bv-term-abstraction-value-divisor", sv, "BV_TERM_ABSTRACTION_VALUE_DIVISOR");
      break;
    case BV_TERM_ABSTRACTION_INC_BITBLAST:
      set_option(vc, "bv-term-abstraction-inc-bitblast", bool_text(v), "BV_TERM_ABSTRACTION_INC_BITBLAST");
      break;
    case CNF_GENERATION_EFFORT:
      if (const char* name = cnf_effort_name(v))
        set_option(vc, "cnf-generation-effort", name, "CNF_GENERATION_EFFORT");
      else
        report("CNF_GENERATION_EFFORT takes an effort ordinal from 0 (very low) to 11 (gia very high)");
      break;
    case INCREMENTAL_SCOPED_PREPROCESSING:
      set_option(vc, "incremental-scoped-preprocessing", bool_text(v), "INCREMENTAL_SCOPED_PREPROCESSING");
      break;
    case INCREMENTAL_PIECE_REWRITING:
      set_option(vc, "incremental-piece-rewriting", bool_text(v), "INCREMENTAL_PIECE_REWRITING");
      break;
    case CNF_AUTO_THRESHOLD:
      if (non_negative(v, "CNF_AUTO_THRESHOLD"))
        set_option(vc, "cnf-auto-threshold", sv, "CNF_AUTO_THRESHOLD");
      break;
    case BV_TERM_ABSTRACTION_DIVMOD:
      vc->divmod_explicit = true;
      set_option(vc, "bv-term-abstraction-divmod", bool_text(v), "BV_TERM_ABSTRACTION_DIVMOD");
      break;
    case BV_TERM_ABSTRACTION_PROFILE:
      if (v == STP_BV_TERM_ABSTRACTION_PROFILE_QUALIFIED)
        set_option(vc, "bv-term-abstraction-profile", "qualified", "BV_TERM_ABSTRACTION_PROFILE");
      else if (v == STP_BV_TERM_ABSTRACTION_PROFILE_BROAD)
        set_option(vc, "bv-term-abstraction-profile", "broad", "BV_TERM_ABSTRACTION_PROFILE");
      else if (v == STP_BV_TERM_ABSTRACTION_PROFILE_AGGRESSIVE)
        set_option(vc, "bv-term-abstraction-profile", "aggressive", "BV_TERM_ABSTRACTION_PROFILE");
      else
        report("BV_TERM_ABSTRACTION_PROFILE takes a bv_term_abstraction_profile_t ordinal");
      break;
    case BV_TERM_ABSTRACTION_DIVMOD_VALUE_LIMIT:
      if (non_negative(v, "BV_TERM_ABSTRACTION_DIVMOD_VALUE_LIMIT"))
        set_option(vc, "bv-term-abstraction-divmod-value-limit", sv, "BV_TERM_ABSTRACTION_DIVMOD_VALUE_LIMIT");
      break;
    case BV_TERM_ABSTRACTION_PLUS:
      set_option(vc, "bv-term-abstraction-plus", bool_text(v), "BV_TERM_ABSTRACTION_PLUS");
      break;
    case BV_TERM_ABSTRACTION_ITE:
      set_option(vc, "bv-term-abstraction-ite", bool_text(v), "BV_TERM_ABSTRACTION_ITE");
      break;
    case BV_TERM_ABSTRACTION_COMPARE:
      set_option(vc, "bv-term-abstraction-compare", bool_text(v), "BV_TERM_ABSTRACTION_COMPARE");
      break;
    case UF_PROPAGATE_EQUALITIES:
      set_option(vc, "uf-propagate-equalities", v != 0 ? "on" : "off", "UF_PROPAGATE_EQUALITIES");
      break;
    case UF_SKELETON_PREPROC:
      set_option(vc, "uf-skeleton-preproc", v != 0 ? "on" : "off", "UF_SKELETON_PREPROC");
      break;
    case UF_BV_TERM_ABSTRACTION:
      set_option(vc, "uf-bv-term-abstraction", v == 0 ? "off" : v == 1 ? "on" : "auto",
                 "UF_BV_TERM_ABSTRACTION");
      break;
    case UF_CHECK_DURING_BV_REFINEMENT:
      set_option(vc, "uf-check-during-bv-refinement", bool_text(v), "UF_CHECK_DURING_BV_REFINEMENT");
      break;
    case REFINEMENT_TRAIL_REUSE:
      set_option(vc, "refinement-trail-reuse", bool_text(v), "REFINEMENT_TRAIL_REUSE");
      break;
    case FP_ABSTRACTION:
      set_option(vc, "fp-abstraction", bool_text(v), "FP_ABSTRACTION");
      break;
    case FP_ABSTRACTION_OPS:
      if (non_negative(v, "FP_ABSTRACTION_OPS") && fp_ops_names(v, "FP_ABSTRACTION_OPS", "default", names))
        set_option(vc, "fp-abstraction-ops", names, "FP_ABSTRACTION_OPS");
      break;
    case FP_ABSTRACTION_INCREMENTAL:
      set_option(vc, "fp-abstraction-incremental", bool_text(v), "FP_ABSTRACTION_INCREMENTAL");
      break;
    case FP_ABSTRACTION_CHAIN_OPS:
      if (non_negative(v, "FP_ABSTRACTION_CHAIN_OPS") &&
          fp_ops_names(v, "FP_ABSTRACTION_CHAIN_OPS", "none", names))
        set_option(vc, "fp-abstraction-chain-ops", names, "FP_ABSTRACTION_CHAIN_OPS");
      break;
    case FP_ABSTRACTION_WIDTH:
      if (non_negative(v, "FP_ABSTRACTION_WIDTH"))
        set_option(vc, "fp-abstraction-width", sv, "FP_ABSTRACTION_WIDTH");
      break;
    case FP_ABSTRACTION_TIERS:
      if (non_negative(v, "FP_ABSTRACTION_TIERS"))
        set_option(vc, "fp-abstraction-tiers", sv, "FP_ABSTRACTION_TIERS");
      break;
    case FP_ABSTRACTION_VALUES:
      if (non_negative(v, "FP_ABSTRACTION_VALUES"))
        set_option(vc, "fp-abstraction-values", sv, "FP_ABSTRACTION_VALUES");
      break;
    case FP_ABSTRACTION_SHAPE:
      set_option(vc, "fp-abstraction-shape", bool_text(v), "FP_ABSTRACTION_SHAPE");
      break;
    case FP_ABSTRACTION_RELATIONAL:
      set_option(vc, "fp-abstraction-relational", bool_text(v), "FP_ABSTRACTION_RELATIONAL");
      break;
    case FP_ABSTRACTION_RELATIONAL_LAST_WIDTH:
      if (non_negative(v, "FP_ABSTRACTION_RELATIONAL_LAST_WIDTH"))
        set_option(vc, "fp-abstraction-relational-last-width", sv, "FP_ABSTRACTION_RELATIONAL_LAST_WIDTH");
      break;
    case FP_ABSTRACTION_BOX_LEMMAS:
      set_option(vc, "fp-abstraction-box-lemmas", bool_text(v), "FP_ABSTRACTION_BOX_LEMMAS");
      break;
    case FP_ABSTRACTION_PHASE_HINTS:
      set_option(vc, "fp-abstraction-phase-hints", bool_text(v), "FP_ABSTRACTION_PHASE_HINTS");
      break;
    case FP_ABSTRACTION_REPAIR:
      set_option(vc, "fp-abstraction-repair", bool_text(v), "FP_ABSTRACTION_REPAIR");
      break;
    case FP_ABSTRACTION_RESTART_LIMIT:
      if (non_negative(v, "FP_ABSTRACTION_RESTART_LIMIT"))
        set_option(vc, "fp-abstraction-restart-limit", sv, "FP_ABSTRACTION_RESTART_LIMIT");
      break;
    case FP_ABSTRACTION_RESTART_WIDTH:
      if (non_negative(v, "FP_ABSTRACTION_RESTART_WIDTH"))
        set_option(vc, "fp-abstraction-restart-width", sv, "FP_ABSTRACTION_RESTART_WIDTH");
      break;
    case FP_ABSTRACTION_SIGNIFICAND_BITS:
      if (non_negative(v, "FP_ABSTRACTION_SIGNIFICAND_BITS"))
        set_option(vc, "fp-abstraction-significand-bits", sv, "FP_ABSTRACTION_SIGNIFICAND_BITS");
      break;
    case FP_ABSTRACTION_SIGNIFICAND_BITS_WIDE:
      if (non_negative(v, "FP_ABSTRACTION_SIGNIFICAND_BITS_WIDE"))
        set_option(vc, "fp-abstraction-significand-bits-wide", sv, "FP_ABSTRACTION_SIGNIFICAND_BITS_WIDE");
      break;
    case FP_ABSTRACTION_DECLINE_PINNED:
      set_option(vc, "fp-abstraction-decline-pinned", bool_text(v), "FP_ABSTRACTION_DECLINE_PINNED");
      break;
    case FP_ABSTRACTION_BUDGET:
      if (non_negative(v, "FP_ABSTRACTION_BUDGET"))
        set_option(vc, "fp-abstraction-budget", sv, "FP_ABSTRACTION_BUDGET");
      break;
    case FP_ABSTRACTION_CONSTANT_OPERANDS:
      set_option(vc, "fp-abstraction-constant-operands", v == 0 ? "off" : v == 1 ? "on" : "auto",
                 "FP_ABSTRACTION_CONSTANT_OPERANDS");
      break;
    case LRA_THEORY_PROPAGATION:
      set_option(vc, "lra-theory-propagation", bool_text(v), "LRA_THEORY_PROPAGATION");
      break;
    case LRA_VERIFY_CONFLICTS:
      set_option(vc, "lra-verify-conflicts", bool_text(v), "LRA_VERIFY_CONFLICTS");
      break;
    case LRA_VERIFY_CANONICAL:
      set_option(vc, "lra-verify-canonical", bool_text(v), "LRA_VERIFY_CANONICAL");
      break;
    case LRA_PRESOLVE_SUBST:
      set_option(vc, "lra-presolve-subst", bool_text(v), "LRA_PRESOLVE_SUBST");
      break;
    case LRA_PRESOLVE_BOUNDS:
      set_option(vc, "lra-presolve-bounds", bool_text(v), "LRA_PRESOLVE_BOUNDS");
      break;
    case LRA_PRESOLVE_ROWS:
      set_option(vc, "lra-presolve-rows", bool_text(v), "LRA_PRESOLVE_ROWS");
      break;
    case LRA_PRESOLVE_PROPAGATE:
      set_option(vc, "lra-presolve-propagate", bool_text(v), "LRA_PRESOLVE_PROPAGATE");
      break;
    case LRA_PRESOLVE_UNCONSTRAINED:
      set_option(vc, "lra-presolve-unconstrained", bool_text(v), "LRA_PRESOLVE_UNCONSTRAINED");
      break;
    case LRA_FLOAT_DRIVER:
      set_option(vc, "lra-float-driver", bool_text(v), "LRA_FLOAT_DRIVER");
      break;
    case LRA_INCREMENTAL_SESSION:
      set_option(vc, "lra-incremental-session", bool_text(v), "LRA_INCREMENTAL_SESSION");
      break;
    default:
      fatal("C_interface: vc_setInterfaceFlags: Unrecognized flag\n");
      break;
  }
}

void make_division_total(VC /* vc */)
{
}

// ------------------------------------------------------------ schema groups and counters

namespace
{

// The groups in the order the engine's BVSchemaGroup enumerates them, which
// is the order the option lists its members and the index
// vc_getSchemaGroupCounter takes.
const char* const kSchemaGroups[STP_BV_SCHEMA_GROUP_COUNT] = {
    "base",          "udiv15",            "udiv-observed",     "udiv-tail",
    "urem",          "quotient-one-quot", "quotient-one-rem",  "quotient-thresholds",
    "divisor-magnitude", "divrem-full",   "mul8",              "mul-ref3",
    "mul-tail",      "add",               "low-prefix"};

// The 2.x counter ordinals as statistics.toml names them.
const char* counter_name(enum stp_counter_t c)
{
  switch (c)
  {
    case STP_COUNTER_QUERIES_BITBLASTED: return "checks.bitblasted";
    case STP_COUNTER_BV_CANDIDATES_EQ: return "bv.candidates.eq";
    case STP_COUNTER_BV_CANDIDATES_COMPARE: return "bv.candidates.compare";
    case STP_COUNTER_BV_CANDIDATES_ITE: return "bv.candidates.ite";
    case STP_COUNTER_BV_CANDIDATES_PLUS: return "bv.candidates.plus";
    case STP_COUNTER_BV_CANDIDATES_MULT: return "bv.candidates.mult";
    case STP_COUNTER_BV_CANDIDATES_DIVMOD: return "bv.candidates.divmod";
    case STP_COUNTER_BV_ABSTRACTED_EQ: return "bv.abstracted.eq";
    case STP_COUNTER_BV_ABSTRACTED_COMPARE: return "bv.abstracted.compare";
    case STP_COUNTER_BV_ABSTRACTED_ITE: return "bv.abstracted.ite";
    case STP_COUNTER_BV_ABSTRACTED_PLUS: return "bv.abstracted.plus";
    case STP_COUNTER_BV_ABSTRACTED_MULT: return "bv.abstracted.mult";
    case STP_COUNTER_BV_ABSTRACTED_DIVMOD: return "bv.abstracted.divmod";
    case STP_COUNTER_BV_REFINEMENT_ROUNDS: return "bv.refinement_rounds";
    case STP_COUNTER_BV_BLOCKING_LEMMAS: return "bv.blocking_lemmas";
    case STP_COUNTER_UF_APPLICATIONS_LOWERED: return "uf.applications_lowered";
    case STP_COUNTER_UF_CONSTRAINTS_INSTALLED: return "uf.constraints_installed";
    case STP_COUNTER_BV_SCHEMA_LEMMAS: return "bv.schema_lemmas";
    case STP_COUNTER_BV_EXACT_ESCALATIONS: return "bv.exact.escalations";
    case STP_COUNTER_BV_EXACT_ESCALATIONS_MULT: return "bv.exact.escalations_mult";
    case STP_COUNTER_BV_EXACT_ESCALATIONS_DIVMOD: return "bv.exact.escalations_divmod";
    case STP_COUNTER_BV_EXACT_CLAUSES: return "bv.exact.clauses";
    case STP_COUNTER_BV_EXACT_VARIABLES: return "bv.exact.variables";
    case STP_COUNTER_BV_EXACT_MICROSECONDS: return "bv.exact.microseconds";
    case STP_COUNTER_BV_SCHEMA_CLAUSES: return "bv.schema.clauses";
    case STP_COUNTER_BV_SCHEMA_VARIABLES: return "bv.schema.variables";
    case STP_COUNTER_BV_SCHEMA_MICROSECONDS: return "bv.schema.microseconds";
    case STP_COUNTER_FP_CANDIDATES: return "fp.candidates";
    case STP_COUNTER_FP_ABSTRACTED: return "fp.abstracted";
    case STP_COUNTER_FP_SHARED: return "fp.shared";
    case STP_COUNTER_FP_CHAINED: return "fp.chained";
    case STP_COUNTER_FP_RULE_LEMMAS: return "fp.rule_lemmas";
    case STP_COUNTER_FP_CROSS_RULES: return "fp.cross_rules";
    case STP_COUNTER_FP_CHECKS: return "fp.checks";
    case STP_COUNTER_FP_SKIPPED_CHECKS: return "fp.skipped_checks";
    case STP_COUNTER_FP_INCONSISTENT: return "fp.inconsistent";
    case STP_COUNTER_FP_VALUE_LEMMAS: return "fp.value_lemmas";
    case STP_COUNTER_FP_BOX_LEMMAS: return "fp.box_lemmas";
    case STP_COUNTER_FP_SHAPE_LEMMAS: return "fp.shape_lemmas";
    case STP_COUNTER_FP_RELATIONAL_LEMMAS: return "fp.relational_lemmas";
    case STP_COUNTER_FP_RELEASES: return "fp.releases";
    case STP_COUNTER_FP_REFINEMENT_ROUNDS: return "fp.refinement_rounds";
    case STP_COUNTER_FP_RESTARTS: return "fp.restarts";
    case STP_COUNTER_FP_REPAIRS: return "fp.repairs";
    case STP_COUNTER_FP_LEMMA_MICROSECONDS: return "fp.lemma_microseconds";
  }
  return nullptr;
}

unsigned long long read_statistic(VCImpl* vc, const std::string& name, bool* known)
{
  *known = false;
  stp_solver s = ensure_solver(vc);
  if (s == nullptr)
    return 0;
  stp_statistics st = stp_solver_statistics(s);
  if (st == nullptr)
  {
    take_error(vc);
    return 0;
  }
  std::uint64_t v = 0;
  if (stp_statistics_uint64(st, name.c_str(), &v) == STP_OK)
    *known = true;
  else
    take_error(vc);
  stp_statistics_release(st);
  return v;
}

} // namespace

unsigned long long vc_getCounter(VC vcp, enum stp_counter_t counter)
{
  VCImpl* vc = vcimpl(vcp, "vc_getCounter");
  if (vc == nullptr)
    return 0;
  const char* name = counter_name(counter);
  if (name == nullptr)
  {
    report("vc_getCounter: unrecognised counter");
    return 0;
  }
  bool known = false;
  const unsigned long long v = read_statistic(vc, name, &known);
  if (!known)
    report(std::string("vc_getCounter: the statistic '") + name + "' is not published by this build");
  return v;
}

int vc_setSchemaGroups(VC vcp, const char* groups)
{
  VCImpl* vc = vcimpl(vcp, "vc_setSchemaGroups");
  if (vc == nullptr)
    return 0;
  if (groups == nullptr)
  {
    report("vc_setSchemaGroups: no group list");
    return 0;
  }
  if (*groups == '\0')
  {
    report("vc_setSchemaGroups: empty group list");
    return 0;
  }
  return set_option(vc, "bv-term-abstraction-schema-groups", groups, "vc_setSchemaGroups") ? 1 : 0;
}

unsigned long long vc_getSchemaGroupCounter(VC vcp, unsigned group)
{
  VCImpl* vc = vcimpl(vcp, "vc_getSchemaGroupCounter");
  if (vc == nullptr)
    return 0;
  if (group >= STP_BV_SCHEMA_GROUP_COUNT)
  {
    report("vc_getSchemaGroupCounter: schema group index out of range");
    return 0;
  }
  // statistics.toml promises bv.schema_group.<name>.lemmas; the snapshot the
  // 3.x solver publishes does not carry it yet (NOTES.md), so this reads 0.
  bool known = false;
  return read_statistic(vc, std::string("bv.schema_group.") + kSchemaGroups[group] + ".lemmas", &known);
}

const char* vc_schemaGroupName(unsigned group)
{
  if (group >= STP_BV_SCHEMA_GROUP_COUNT)
  {
    report("vc_schemaGroupName: schema group index out of range");
    return nullptr;
  }
  return kSchemaGroups[group];
}

// ============================================================ lifecycle

VC vc_createValidityChecker(void)
{
  boot_constant_bv_on_this_thread();
  stp_tm tm = stp_tm_new(nullptr);
  if (tm == nullptr)
  {
    const stp_error* e = stp_last_error();
    std::cout << "CInterface: cannot create a term manager"
              << (e != nullptr && e->message != nullptr ? std::string(": ") + e->message : "") << std::endl;
    return nullptr;
  }
  VCImpl* vc = new VCImpl;
  vc->tm = tm;
  vc->opts = stp_options_new();
  vc->backend = default_backend();
  {
    std::lock_guard<std::mutex> lock(g_mutex);
    g_live_vcs.insert(vc);
  }
  // As 2.x: 'd' for every checker (build and check the counterexample), and
  // the 2.x completion of unobserved array cells (0xFF; 'x' makes it 0x00).
  set_option(vc, "produce-models", "true", "vc_createValidityChecker");
  set_option(vc, "check-sanity", "true", "vc_createValidityChecker");
  set_option(vc, "model-array-fill", "ones", "vc_createValidityChecker");
  return vc;
}

VC vc_createValidityCheckerReuse(void* /* _bm */)
{
  // The 3.x API has no door through which a raw engine manager can be
  // adopted, by design; a checker cannot be built around one (NOTES.md).
  report("vc_createValidityCheckerReuse is not available over the 3.x API: a "
         "checker cannot adopt a raw STPMgr; use vc_createValidityChecker");
  return nullptr;
}

void vc_Destroy(VC vcp)
{
  if (vcp == nullptr)
    return;
  VCImpl* vc = static_cast<VCImpl*>(vcp);

  // Every handle this checker still owns: the checker-owned ones, and, with
  // the 'u' registry on, every tracked handle (2.x retired the registry's
  // handles at destruction too).
  std::vector<Handle*> owned(vc->persist.begin(), vc->persist.end());
  vc->persist.clear();
  {
    std::lock_guard<std::mutex> lock(g_mutex);
    g_live_vcs.erase(vc);
    for (auto it = g_uf_owner.begin(); it != g_uf_owner.end();)
      it = it->second == vc ? g_uf_owner.erase(it) : std::next(it);
    if (vc->tracking)
      for (auto it = g_registry.begin(); it != g_registry.end();)
      {
        if (it->second == vc)
        {
          if (!it->first->checker_owned)
            owned.push_back(it->first);
          it = g_registry.erase(it);
        }
        else
          ++it;
      }
  }
  for (Handle* h : owned)
    free_handle(h);

  for (WholeCE* w : vc->whole_ces)
  {
    if (w->model != nullptr)
      stp_model_release(w->model);
    delete w;
  }
  vc->whole_ces.clear();
  discard_model(vc);
  for (auto& uf : vc->ufs)
    stp_term_release(uf.second.fun);
  vc->ufs.clear();
  if (vc->last_query != nullptr)
    stp_term_release(vc->last_query);
  for (auto& level : vc->levels)
    for (stp_term t : level)
      stp_term_release(t);
  vc->levels.clear();
  if (vc->solver != nullptr)
    stp_solver_delete(vc->solver);
  stp_options_delete(vc->opts);
  // Whatever caller-owned handles were never deleted keep references; drop
  // them all so that the manager dies with the checker, as 2.x's did (the
  // handles dangle from here on, which is the 2.x contract too).
  stp_tm_release_all(vc->tm);
  stp_tm_release(vc->tm);
  delete vc;
}

void vc_DeleteExpr(Expr e)
{
  Handle* h = handle(e);
  if (h == nullptr)
    return;
  registry_erase(h);
  if (h->checker_owned && h->vc != nullptr)
    h->vc->persist.erase(h);
  free_handle(h);
}

void vc_registerErrorHandler(void (*error_hdlr)(const char* err_msg))
{
  g_handler = error_hdlr;
}

void vc_setErrorPolicy(enum stp_error_policy_t policy)
{
  g_policy.store(policy == STP_ON_ERROR_RETURN ? STP_ON_ERROR_RETURN : STP_ON_ERROR_ABORT);
}

// ============================================================ SAT backends

bool vc_supportsMinisat(VC) { return stp_has_sat_backend("minisat"); }
bool vc_supportsSimplifyingMinisat(VC) { return stp_has_sat_backend("simplifying-minisat"); }
bool vc_supportsCryptominisat(VC) { return stp_has_sat_backend("cryptominisat"); }
bool vc_supportsCadical(VC) { return stp_has_sat_backend("cadical"); }

bool vc_useMinisat(VC vcp)
{
  VCImpl* vc = vcimpl(vcp, "vc_useMinisat");
  return vc != nullptr && use_backend(vc, "minisat");
}
bool vc_useSimplifyingMinisat(VC vcp)
{
  VCImpl* vc = vcimpl(vcp, "vc_useSimplifyingMinisat");
  return vc != nullptr && use_backend(vc, "simplifying-minisat");
}
bool vc_useCryptominisat(VC vcp)
{
  VCImpl* vc = vcimpl(vcp, "vc_useCryptominisat");
  return vc != nullptr && use_backend(vc, "cryptominisat");
}
bool vc_useCadical(VC vcp)
{
  VCImpl* vc = vcimpl(vcp, "vc_useCadical");
  return vc != nullptr && use_backend(vc, "cadical");
}

bool vc_isUsingMinisat(VC vcp)
{
  VCImpl* vc = vcimpl(vcp, "vc_isUsingMinisat");
  return vc != nullptr && stp_has_sat_backend("minisat") && vc->backend == "minisat";
}
bool vc_isUsingSimplifyingMinisat(VC vcp)
{
  VCImpl* vc = vcimpl(vcp, "vc_isUsingSimplifyingMinisat");
  return vc != nullptr && stp_has_sat_backend("simplifying-minisat") &&
         vc->backend == "simplifying-minisat";
}
bool vc_isUsingCryptominisat(VC vcp)
{
  VCImpl* vc = vcimpl(vcp, "vc_isUsingCryptominisat");
  return vc != nullptr && stp_has_sat_backend("cryptominisat") && vc->backend == "cryptominisat";
}
bool vc_isUsingCadical(VC vcp)
{
  VCImpl* vc = vcimpl(vcp, "vc_isUsingCadical");
  return vc != nullptr && stp_has_sat_backend("cadical") && vc->backend == "cadical";
}

// ============================================================ the stack and queries

void vc_assertFormula(VC vcp, Expr e)
{
  VCImpl* vc = vcimpl(vcp, "vc_assertFormula");
  if (vc == nullptr)
    return;
  stp_term t = term_of(e, "vc_assertFormula");
  if (t == nullptr)
    return;
  if (!is_bool(stp_term_sort(t)))
  {
    fatal("Trying to assert a NON formula: ");
    return;
  }
  stp_solver s = ensure_solver(vc);
  if (s == nullptr)
    return;
  if (stp_solver_assert(s, t) != STP_OK)
  {
    fatal("CInterface: vc_assertFormula: " + take_error(vc));
    return;
  }
  vc->levels.back().push_back(stp_term_copy(t));
  // The BV model survives an assertion (the 2.x contract); a certified UF
  // reading belongs to one asserted root and does not, and neither does the
  // exact Real model.
  vc->uf_certified = false;
  vc->real_model_stale = true;
}

void vc_push(VC vcp)
{
  VCImpl* vc = vcimpl(vcp, "vc_push");
  if (vc == nullptr)
    return;
  stp_solver s = ensure_solver(vc);
  if (s == nullptr)
    return;
  discard_model(vc);
  if (stp_solver_push(s, 1) != STP_OK)
  {
    fatal("CInterface: vc_push: " + take_error(vc));
    return;
  }
  vc->levels.emplace_back();
}

void vc_pop(VC vcp)
{
  VCImpl* vc = vcimpl(vcp, "vc_pop");
  if (vc == nullptr)
    return;
  if (vc->levels.size() <= 1)
  {
    // 2.x deleted the base assertions here (defect D10); an unmatched pop is
    // an error in this library.
    fatal("CInterface: vc_pop: no matching vc_push (the assertion stack is at its base level)");
    return;
  }
  stp_solver s = ensure_solver(vc);
  if (s == nullptr)
    return;
  if (stp_solver_pop(s, 1) != STP_OK)
  {
    fatal("CInterface: vc_pop: " + take_error(vc));
    return;
  }
  for (stp_term t : vc->levels.back())
    stp_term_release(t);
  vc->levels.pop_back();
  // The BV model is deliberately retained (see vc_pop's header comment); a
  // certified UF map is keyed by the solved stack and is not, and neither is
  // the exact Real model.
  vc->uf_certified = false;
  vc->real_model_stale = true;
}

namespace
{

enum reason_unknown_t map_reason(stp_unknown_reason r)
{
  switch (r)
  {
    case STP_REASON_NONE: return REASON_UNKNOWN_NONE;
    case STP_REASON_TIMEOUT: return REASON_UNKNOWN_TIMEOUT;
    case STP_REASON_CONFLICT_LIMIT: return REASON_UNKNOWN_CONFLICT_BUDGET;
    case STP_REASON_CARRIER_EXHAUSTED: return REASON_UNKNOWN_CARRIER_EXHAUSTED;
    case STP_REASON_ASSUMED_INJECTIVITY: return REASON_UNKNOWN_ASSUMED_INJECTIVITY;
    case STP_REASON_RESOURCE_LIMIT: return REASON_UNKNOWN_AIG_BUDGET;
    case STP_REASON_INTERRUPTED:
    case STP_REASON_INCOMPLETE:
    case STP_REASON_STOPPED_AFTER_CNF:
    case STP_REASON_OTHER:
    case STP_REASON_MAX_ENUM:
      return REASON_UNKNOWN_INCOMPLETE;
  }
  return REASON_UNKNOWN_INCOMPLETE;
}

void print_counterexample_lines(VCImpl* vc, std::ostream& os);

} // namespace

int vc_query(VC vc, Expr e)
{
  return vc_query_with_timeout(vc, e, -1, -1);
}

int vc_query_with_timeout(VC vcp, Expr e, int timeout_max_conflicts, int timeout_max_time)
{
  VCImpl* vc = vcimpl(vcp, "vc_query");
  if (vc == nullptr)
    return 2;
  vc->reason = REASON_UNKNOWN_NONE;
  vc->reason_detail.clear();
  discard_model(vc);

  // -1 is the only negative value that means anything ("no limit").
  if (timeout_max_conflicts < -1)
  {
    std::cerr << "CInterface: timeout_max_conflicts must be -1 (no limit) or greater" << std::endl;
    return 2;
  }
  if (timeout_max_time < -1)
  {
    std::cerr << "CInterface: timeout_max_time must be -1 (no limit) or greater" << std::endl;
    return 2;
  }

  stp_term q = term_of(e, "vc_query");
  if (q == nullptr)
    return 2;
  if (!is_bool(stp_term_sort(q)))
  {
    fatal("CInterface: Trying to QUERY a NON formula: ");
    return 2;
  }
  stp_solver s = ensure_solver(vc);
  if (s == nullptr)
    return 2;

  if (vc->last_query != nullptr)
    stp_term_release(vc->last_query);
  vc->last_query = stp_term_copy(q);

  stp_budget budget;
  budget.has_time = timeout_max_time >= 0;
  budget.time_ms = static_cast<std::uint64_t>(timeout_max_time < 0 ? 0 : timeout_max_time) * 1000u;
  budget.has_conflicts = timeout_max_conflicts >= 0;
  budget.conflicts = static_cast<std::uint64_t>(timeout_max_conflicts < 0 ? 0 : timeout_max_conflicts);

  stp_entailment out;
  if (stp_solver_entails(s, q, &budget, &out) != STP_OK)
  {
    report("vc_query: " + take_error(vc));
    return 2;
  }
  int result = 2;
  switch (out.kind)
  {
    case STP_VALID:
      result = 1;
      break;
    case STP_INVALID:
      result = 0;
      vc->model = stp_solver_model(s);
      if (vc->model == nullptr)
        take_error(vc); // produce-models off: nothing to read later
      vc->uf_certified = vc->model != nullptr;
      vc->real_model_symbols = stp_tm_num_symbols(vc->tm);
      vc->real_model_stale = false;
      break;
    case STP_UNKNOWN_VALIDITY:
      result = 3;
      vc->reason = map_reason(out.reason);
      if (char* msg = stp_solver_last_reason_message(s))
      {
        vc->reason_detail = msg;
        stp_free(msg);
      }
      break;
    case STP_VALIDITY_MAX_ENUM:
      break;
  }
  if (vc->flag_n)
  {
    if (result == 1)
      std::cout << "Valid." << std::endl;
    else if (result == 0)
      std::cout << "Invalid." << std::endl;
    else
      std::cout << "Unknown." << std::endl;
  }
  if (vc->flag_p && result == 0)
    print_counterexample_lines(vc, std::cout);
  return result;
}

enum reason_unknown_t vc_getReasonUnknown(VC vcp)
{
  VCImpl* vc = vcimpl(vcp, "vc_getReasonUnknown");
  return vc != nullptr ? vc->reason : REASON_UNKNOWN_NONE;
}

void vc_getReasonUnknownToBuffer(VC vcp, char** buf, size_t* len)
{
  VCImpl* vc = vcimpl(vcp, "vc_getReasonUnknownToBuffer");
  to_buffer(vc != nullptr ? vc->reason_detail : std::string(), buf, len);
}

// ============================================================ models

Expr vc_getCounterExample(VC vcp, Expr e)
{
  VCImpl* vc = vcimpl(vcp, "vc_getCounterExample");
  if (vc == nullptr)
    return nullptr;
  stp_term t = term_of(e, "vc_getCounterExample");
  if (t == nullptr)
    return nullptr;
  // A constant already is its own value: no query is needed behind it.
  if (stp_term_is_value(t))
    return wrap(vc, stp_term_copy(t), false);
  stp_kind k;
  if (stp_term_get_kind(t, &k) == STP_OK && k == STP_KIND_APPLY)
    return uf_value(vc, e, "vc_getCounterExample");
  if (vc->model == nullptr)
  {
    report("vc_getCounterExample: no model to read -- no query has been answered "
           "since the last vc_push or vc_query");
    return nullptr;
  }
  stp_term v = stp_model_value(vc->model, t);
  if (v == nullptr)
  {
    report("vc_getCounterExample: " + take_error(vc));
    return nullptr;
  }
  return wrap(vc, v, false);
}

void vc_getCounterExampleArray(VC vcp, Expr e, Expr** indices, Expr** values, int* size)
{
  if (size != nullptr)
    *size = 0;
  VCImpl* vc = vcimpl(vcp, "vc_getCounterExampleArray");
  if (vc == nullptr || indices == nullptr || values == nullptr || size == nullptr)
    return;
  stp_term t = term_of(e, "vc_getCounterExampleArray");
  if (t == nullptr || vc->model == nullptr || !is_array(stp_term_sort(t)))
    return;
  stp_array_value av = stp_model_array_value(vc->model, t);
  if (av == nullptr)
  {
    report("vc_getCounterExampleArray: " + take_error(vc));
    return;
  }
  const std::size_t n = stp_array_value_size(av);
  if (n == 0)
  {
    stp_array_value_release(av);
    return;
  }
  *indices = static_cast<Expr*>(std::malloc(n * sizeof(Expr)));
  *values = static_cast<Expr*>(std::malloc(n * sizeof(Expr)));
  if (*indices == nullptr || *values == nullptr)
  {
    std::fprintf(stderr, "malloc(%zu) failed.", n * sizeof(Expr));
    std::abort();
  }
  int count = 0;
  for (std::size_t i = 0; i < n; ++i)
  {
    stp_term index = nullptr, element = nullptr;
    bool observed = false;
    if (stp_array_value_entry(av, i, &index, &element, &observed) != STP_OK)
    {
      take_error(vc);
      continue;
    }
    (*indices)[count] = wrap(vc, index, false);
    (*values)[count] = wrap(vc, element, false);
    ++count;
  }
  stp_array_value_release(av);
  *size = count;
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
  std::free(indices);
  std::free(values);
}

int vc_counterexample_size(VC vcp)
{
  VCImpl* vc = vcimpl(vcp, "vc_counterexample_size");
  if (vc == nullptr || vc->model == nullptr)
    return 0;
  return static_cast<int>(stp_model_num_symbols(vc->model));
}

WholeCounterExample vc_getWholeCounterExample(VC vcp)
{
  VCImpl* vc = vcimpl(vcp, "vc_getWholeCounterExample");
  if (vc == nullptr)
    return nullptr;
  WholeCE* w = new WholeCE;
  w->vc = vc;
  w->model = vc->model != nullptr ? stp_model_copy(vc->model) : nullptr;
  vc->whole_ces.insert(w);
  return w;
}

Expr vc_getTermFromCounterExample(VC vcp, Expr e, WholeCounterExample cc)
{
  VCImpl* vc = vcimpl(vcp, "vc_getTermFromCounterExample");
  if (vc == nullptr)
    return nullptr;
  WholeCE* w = static_cast<WholeCE*>(cc);
  stp_term t = term_of(e, "vc_getTermFromCounterExample");
  if (t == nullptr)
    return nullptr;
  if (stp_term_is_value(t))
    return wrap(vc, stp_term_copy(t), false);
  if (w == nullptr || w->model == nullptr)
  {
    report("vc_getTermFromCounterExample: the snapshot holds no model");
    return nullptr;
  }
  stp_term v = stp_model_value(w->model, t);
  if (v == nullptr)
  {
    // 2.x handed an unrecorded term straight back
    take_error(vc);
    return wrap(vc, stp_term_copy(t), false);
  }
  return wrap(vc, v, false);
}

void vc_deleteWholeCounterExample(WholeCounterExample cc)
{
  WholeCE* w = static_cast<WholeCE*>(cc);
  if (w == nullptr)
    return;
  if (w->vc != nullptr)
    w->vc->whole_ces.erase(w);
  if (w->model != nullptr)
    stp_model_release(w->model);
  delete w;
}

// ------------------------------------------------------------ exact Real models

namespace
{

bool any_real_symbol(VCImpl* vc)
{
  const std::size_t n = stp_tm_num_symbols(vc->tm);
  for (std::size_t i = 0; i < n; ++i)
  {
    stp_term s = stp_tm_symbol_at(vc->tm, i);
    if (s == nullptr)
      continue;
    const bool real = is_real(stp_term_sort(s));
    stp_term_release(s);
    if (real)
      return true;
  }
  return false;
}

// 2.x's HasRealModel(): the exact Real model published by the last INVALID
// query, unless a declaration, an assertion, a push or a pop happened since.
bool real_model_current(VCImpl* vc)
{
  return vc->model != nullptr && !vc->real_model_stale &&
         stp_tm_num_symbols(vc->tm) == vc->real_model_symbols;
}

char* real_strings(VCImpl* vc, const char* who, Expr term, int which)
{
  stp_term t = term_of(term, who);
  if (t == nullptr)
    return nullptr;
  if (!is_real(stp_term_sort(t)))
  {
    fatal(std::string("CInterface: ") + who + " requires Real operands: ");
    return nullptr;
  }
  if (!real_model_current(vc))
  {
    fatal(std::string("CInterface: ") + who + " failed: no exact Real model");
    return nullptr;
  }
  stp_term v = stp_model_value(vc->model, t);
  if (v == nullptr)
  {
    fatal(std::string("CInterface: ") + who + " failed: " + take_error(vc));
    return nullptr;
  }
  char* num = stp_term_real_numerator(v);
  char* den = stp_term_real_denominator(v);
  stp_term_release(v);
  if (num == nullptr || den == nullptr)
  {
    stp_free(num);
    stp_free(den);
    fatal(std::string("CInterface: ") + who + " failed: " + take_error(vc));
    return nullptr;
  }
  std::string n(num), d(den);
  stp_free(num);
  stp_free(den);
  std::string out;
  const bool negative = !n.empty() && n[0] == '-';
  const std::string magnitude = negative ? n.substr(1) : n;
  switch (which)
  {
    case 0: // canonical n/d text
      out = d == "1" ? n : n + "/" + d;
      break;
    case 1:
      out = n;
      break;
    case 2:
      out = d;
      break;
    default: // SMT-LIB value
      if (d == "1")
        out = negative ? "(- " + magnitude + ")" : magnitude;
      else
        out = negative ? "(- (/ " + magnitude + " " + d + "))" : "(/ " + magnitude + " " + d + ")";
      break;
  }
  return strdup(out.c_str());
}

} // namespace

int vc_hasRealConstruction(void) { return 1; }
int vc_hasQFLRA(void) { return 1; }
int vc_hasRealIte(void) { return 1; }
int vc_hasQFUFLRA(void) { return 1; }

int vc_hasRealModel(VC vcp)
{
  VCImpl* vc = vcimpl(vcp, "vc_hasRealModel");
  return vc != nullptr && real_model_current(vc) && any_real_symbol(vc) ? 1 : 0;
}

int vc_hasRealModelValue(VC vcp, Expr term)
{
  VCImpl* vc = vcimpl(vcp, "vc_hasRealModelValue");
  if (vc == nullptr || term == nullptr || !real_model_current(vc))
    return 0;
  Handle* h = handle(term);
  if (h->is_type() || h->vc != vc || !is_real(stp_term_sort(h->term)))
    return 0;
  stp_term v = stp_model_value(vc->model, h->term);
  if (v == nullptr)
  {
    take_error(vc);
    return 0;
  }
  stp_term_release(v);
  return 1;
}

char* vc_getRealModelValue(VC vcp, Expr term)
{
  VCImpl* vc = vcimpl(vcp, "vc_getRealModelValue");
  return vc != nullptr ? real_strings(vc, "vc_getRealModelValue", term, 0) : nullptr;
}

char* vc_getRealModelNumerator(VC vcp, Expr term)
{
  VCImpl* vc = vcimpl(vcp, "vc_getRealModelNumerator");
  return vc != nullptr ? real_strings(vc, "vc_getRealModelNumerator", term, 1) : nullptr;
}

char* vc_getRealModelDenominator(VC vcp, Expr term)
{
  VCImpl* vc = vcimpl(vcp, "vc_getRealModelDenominator");
  return vc != nullptr ? real_strings(vc, "vc_getRealModelDenominator", term, 2) : nullptr;
}

char* vc_getRealModelSMTLIBValue(VC vcp, Expr term)
{
  VCImpl* vc = vcimpl(vcp, "vc_getRealModelSMTLIBValue");
  return vc != nullptr ? real_strings(vc, "vc_getRealModelSMTLIBValue", term, 3) : nullptr;
}

char* vc_getRealModelSMTLIB2(VC vcp)
{
  VCImpl* vc = vcimpl(vcp, "vc_getRealModelSMTLIB2");
  if (vc == nullptr)
    return nullptr;
  std::ostringstream os;
  os << "(\n";
  if (real_model_current(vc))
  {
    const std::size_t n = stp_tm_num_symbols(vc->tm);
    for (std::size_t i = 0; i < n; ++i)
    {
      stp_term s = stp_tm_symbol_at(vc->tm, i);
      if (s == nullptr)
        continue;
      if (is_real(stp_term_sort(s)))
      {
        Expr h = wrap(vc, stp_term_copy(s), false);
        char* name = stp_term_symbol(s);
        char* value = real_strings(vc, "vc_getRealModelSMTLIB2", h, 3);
        if (name != nullptr && value != nullptr)
          os << "  (define-fun |" << name << "| () Real " << value << ")\n";
        stp_free(name);
        std::free(value);
        vc_DeleteExpr(h);
      }
      stp_term_release(s);
    }
  }
  os << ")\n";
  return strdup(os.str().c_str());
}

void vc_deleteString(char* value)
{
  std::free(value);
}

// ============================================================ value readers

namespace
{

bool value_uint32(Expr e, std::uint32_t& out, const char* who)
{
  stp_term t = term_of(e, who);
  if (t == nullptr)
    return false;
  std::uint64_t v = 0;
  if (!value_uint64(t, v, who))
    return false;
  std::string bits;
  value_bits(t, bits);
  bool too_wide = bits.size() > 32;
  if (too_wide)
  {
    too_wide = false;
    for (std::size_t i = 0; i + 32 < bits.size(); ++i)
      if (bits[i] == '1')
        too_wide = true;
  }
  if (too_wide)
  {
    fatal("GetUnsignedConst: cannot convert bvconst of length greater than 32 to unsigned int");
    return false;
  }
  out = static_cast<std::uint32_t>(v);
  return true;
}

} // namespace

int getBVInt(Expr e)
{
  std::uint32_t v = 0;
  if (!value_uint32(e, v, "CInterface: getBVInt"))
    return 0;
  return static_cast<int>(v);
}

unsigned int getBVUnsigned(Expr e)
{
  std::uint32_t v = 0;
  if (!value_uint32(e, v, "getBVUnsigned"))
    return 0;
  return v;
}

uint64_t getBVUnsignedLongLong(Expr e)
{
  stp_term t = term_of(e, "getBVUnsignedLongLong");
  if (t == nullptr)
    return 0;
  std::uint64_t v = 0;
  if (!value_uint64(t, v, "getBVUnsigned"))
    return 0;
  return v;
}

void vc_printBVBitStringToBuffer(Expr e, char** buf, size_t* len)
{
  stp_term t = term_of(e, "vc_printBVBitStringToBuffer");
  std::string bits;
  if (t == nullptr || !value_bits(t, bits))
  {
    fatal("vc_printBVToBuffer: Attempting to extract bit string from a NON-constant BITVECTOR: ");
    to_buffer(std::string(), buf, len);
    return;
  }
  to_buffer(bits, buf, len);
}

int vc_isBool(Expr e)
{
  Handle* h = handle(e);
  if (h == nullptr || h->is_type() || !stp_term_is_value(h->term) || !is_bool(stp_term_sort(h->term)))
    return -1;
  bool b = false;
  if (stp_term_to_bool(h->term, &b) != STP_OK)
    return -1;
  return b ? 1 : 0;
}

// ============================================================ printers

void vc_printExpr(VC vcp, Expr e)
{
  VCImpl* vc = vcimpl(vcp, "vc_printExpr");
  stp_term t = term_of(e, "vc_printExpr");
  if (vc == nullptr || t == nullptr)
    return;
  bool ok = false;
  const std::string s = cvc_text(vc, t, "vc_printExpr", &ok);
  if (ok)
    std::cout << s << std::flush;
}

void vc_printExprFile(VC vcp, Expr e, int fd)
{
  VCImpl* vc = vcimpl(vcp, "vc_printExprFile");
  stp_term t = term_of(e, "vc_printExprFile");
  if (vc == nullptr || t == nullptr)
    return;
  bool ok = false;
  const std::string s = cvc_text(vc, t, "vc_printExprFile", &ok);
  if (!ok)
    return;
  std::size_t done = 0;
  while (done < s.size())
  {
    const auto n = compat2_write(fd, s.data() + done, static_cast<unsigned>(s.size() - done));
    if (n <= 0)
      break;
    done += static_cast<std::size_t>(n);
  }
}

void vc_printExprToBuffer(VC vcp, Expr e, char** buf, size_t* len)
{
  VCImpl* vc = vcimpl(vcp, "vc_printExprToBuffer");
  stp_term t = term_of(e, "vc_printExprToBuffer");
  if (vc == nullptr || t == nullptr)
  {
    to_buffer(std::string(), buf, len);
    return;
  }
  bool ok = false;
  to_buffer(cvc_text(vc, t, "vc_printExprToBuffer", &ok), buf, len);
}

char* exprString(Expr e)
{
  Handle* h = handle(e);
  if (h == nullptr)
  {
    fatal("CInterface: exprString: null expression handle");
    return strdup("");
  }
  if (h->is_type())
    return strdup(type_text(h->sort).c_str());
  // The presentation language where it exists; the SMT-LIB 2 spelling for a
  // term of a sort it has no syntax for (2.x died inside the printer).
  char* s = stp_term_to_string(h->term, STP_FORMAT_CVC, false);
  if (s == nullptr)
  {
    take_error(h->vc);
    s = stp_term_str(h->term);
  }
  char* out = strdup(s != nullptr ? s : "");
  stp_free(s);
  return out;
}

char* typeString(Type t)
{
  Handle* h = handle(t);
  if (h == nullptr)
  {
    fatal("CInterface: typeString: null type handle");
    return strdup("");
  }
  return strdup(type_text(h->is_type() ? h->sort : stp_term_sort(h->term)).c_str());
}

namespace
{

// The symbols a term is built from, in first-seen order, with the theories
// they bring in.
struct Symbols
{
  std::vector<stp_term> list; // +1 each
  std::unordered_set<std::uint64_t> seen;
  bool fp = false, arrays = false, uf = false, real = false, bv = false;

  ~Symbols()
  {
    for (stp_term t : list)
      stp_term_release(t);
  }
};

void note_sort(Symbols& out, stp_sort s)
{
  switch (sort_kind(s))
  {
    case STP_SORT_FP:
    case STP_SORT_RM:
      out.fp = true;
      break;
    case STP_SORT_BV:
      out.bv = true;
      break;
    case STP_SORT_ARRAY:
      out.arrays = true;
      note_sort(out, stp_sort_array_index(s));
      note_sort(out, stp_sort_array_element(s));
      break;
    case STP_SORT_REAL:
      out.real = true;
      break;
    case STP_SORT_FUN:
    {
      out.uf = true;
      std::uint32_t n = 0;
      stp_sort_fun_arity(s, &n);
      for (std::uint32_t i = 0; i < n; ++i)
        note_sort(out, stp_sort_fun_domain(s, i));
      note_sort(out, stp_sort_fun_codomain(s));
      break;
    }
    default:
      break;
  }
}

void collect_symbols(stp_term root, Symbols& out)
{
  std::vector<stp_term> stack; // +1 each
  stack.push_back(stp_term_copy(root));
  while (!stack.empty())
  {
    stp_term t = stack.back();
    stack.pop_back();
    const std::uint64_t id = stp_term_id(t);
    if (!out.seen.insert(id).second)
    {
      stp_term_release(t);
      continue;
    }
    note_sort(out, stp_term_sort(t));
    if (stp_term_is_const(t))
    {
      out.list.push_back(t);
      continue;
    }
    std::size_t n = 0;
    if (stp_term_num_children(t, &n) == STP_OK)
      for (std::size_t i = 0; i < n; ++i)
        if (stp_term c = stp_term_child(t, i))
          stack.push_back(c);
    stp_term_release(t);
  }
}

std::string logic_of(const Symbols& s)
{
  if (s.real)
    return s.uf ? "QF_UFLRA" : "QF_LRA";
  if (s.fp && s.uf)
    return s.arrays ? "QF_AUFBVFP" : "QF_UFBVFP";
  if (s.fp)
    return s.arrays ? "QF_ABVFP" : "QF_BVFP";
  if (s.uf && s.arrays && !s.bv)
    return "QF_AX";
  if (s.uf)
    return s.arrays ? "QF_AUFBV" : "QF_UFBV";
  return s.arrays ? "QF_ABV" : "QF_BV";
}

std::string symbol_name(stp_term t)
{
  char* n = stp_term_symbol(t);
  std::string out = n != nullptr ? n : "";
  stp_free(n);
  return out;
}

void print_declarations_smt2(VCImpl* vc, const Symbols& syms, std::ostream& os)
{
  for (stp_term t : syms.list)
  {
    const std::string name = symbol_name(t);
    if (name.empty())
      continue;
    const stp_sort s = stp_term_sort(t);
    if (is_fun(s))
      os << "(declare-fun |" << name << "| " << sort_text(vc, s) << ")\n";
    else
      os << "(declare-fun |" << name << "| () " << sort_text(vc, s) << ")\n";
  }
}

// The declarations of vc_printVarDecls: the checker's symbols from the
// clearDecls watermark on, those of the sorts the presentation language has.
void print_var_decls(VCImpl* vc, std::ostream& os)
{
  const std::size_t n = stp_tm_num_symbols(vc->tm);
  for (std::size_t i = vc->decls_cleared; i < n; ++i)
  {
    stp_term t = stp_tm_symbol_at(vc->tm, i);
    if (t == nullptr)
      continue;
    const std::string name = symbol_name(t);
    const stp_sort s = stp_term_sort(t);
    if (!name.empty())
      switch (sort_kind(s))
      {
        case STP_SORT_BV:
          os << name << " : BITVECTOR(" << bv_width(s) << ");\n";
          break;
        case STP_SORT_ARRAY:
          if (is_bv(stp_sort_array_index(s)) && is_bv(stp_sort_array_element(s)))
            os << name << " : ARRAY BITVECTOR(" << index_width(s) << ") OF BITVECTOR("
               << packed_width(s) << ");\n";
          break;
        case STP_SORT_BOOL:
          os << name << " : BOOLEAN;\n";
          break;
        default:
          break; // no presentation-language spelling
      }
    stp_term_release(t);
  }
}

bool print_asserts(VCImpl* vc, std::ostream& os, int simplify_print)
{
  for (const auto& level : vc->levels)
    for (stp_term t : level)
    {
      stp_term shown = t;
      if (simplify_print == 1)
      {
        shown = stp_tm_simplify(vc->tm, t);
        if (shown == nullptr)
        {
          take_error(vc);
          shown = t;
        }
      }
      bool ok = false;
      const std::string text = cvc_text(vc, shown, "vc_printAsserts", &ok);
      if (shown != t)
        stp_term_release(shown);
      if (!ok)
        return false;
      os << "ASSERT( " << text << ");\n";
    }
  return true;
}

// The value of a model-core symbol as a string in the presentation language:
// one "ASSERT( ... );" line per scalar and per observed array cell.
void print_counterexample_lines(VCImpl* vc, std::ostream& os)
{
  if (vc->model == nullptr)
    return;
  const std::size_t n = stp_model_num_symbols(vc->model);
  for (std::size_t i = 0; i < n; ++i)
  {
    stp_term sym = stp_model_symbol(vc->model, i);
    if (sym == nullptr)
      continue;
    const std::string name = symbol_name(sym);
    const stp_sort s = stp_term_sort(sym);
    if (name.empty() || is_fun(s) || is_real(s))
    {
      stp_term_release(sym);
      continue;
    }
    if (is_array(s))
    {
      if (stp_array_value av = stp_model_array_value(vc->model, sym))
      {
        const std::size_t m = stp_array_value_size(av);
        for (std::size_t j = 0; j < m; ++j)
        {
          stp_term index = nullptr, element = nullptr;
          bool observed = false;
          if (stp_array_value_entry(av, j, &index, &element, &observed) != STP_OK)
            continue;
          os << "ASSERT( " << name << "[" << cvc_value_text(vc, index) << "] = "
             << cvc_value_text(vc, element) << " );\n";
          stp_term_release(index);
          stp_term_release(element);
        }
        stp_array_value_release(av);
      }
      else
        take_error(vc);
    }
    else if (stp_term v = stp_model_value(vc->model, sym))
    {
      os << "ASSERT( " << name << (is_bool(s) ? "<=>" : " = ") << cvc_value_text(vc, v) << " );\n";
      stp_term_release(v);
    }
    else
      take_error(vc);
    stp_term_release(sym);
  }
}

std::string smt2_value_text(stp_term v)
{
  char* s = stp_term_str(v);
  std::string out = s != nullptr ? trim(s) : "?";
  stp_free(s);
  return out;
}

// The model in SMT-LIB 2, every value at its declared sort.
void print_counterexample_smt2(VCImpl* vc, std::ostream& os)
{
  if (vc->model == nullptr)
    return;
  const std::size_t n = stp_model_num_symbols(vc->model);
  for (std::size_t i = 0; i < n; ++i)
  {
    stp_term sym = stp_model_symbol(vc->model, i);
    if (sym == nullptr)
      continue;
    const std::string name = symbol_name(sym);
    const stp_sort s = stp_term_sort(sym);
    if (name.empty())
    {
      stp_term_release(sym);
      continue;
    }
    if (is_fun(s))
    {
      if (stp_fun_value fv = stp_model_fun_value(vc->model, sym))
      {
        const std::uint32_t arity = stp_fun_value_arity(fv);
        os << "(define-fun |" << name << "| (";
        for (std::uint32_t k = 0; k < arity; ++k)
          os << (k ? " " : "") << "(x!" << k << " " << sort_text(vc, stp_sort_fun_domain(s, k)) << ")";
        os << ") " << sort_text(vc, stp_sort_fun_codomain(s)) << " ";
        std::string body;
        if (stp_term e = stp_fun_value_else(fv))
        {
          body = smt2_value_text(e);
          stp_term_release(e);
        }
        const std::size_t m = stp_fun_value_size(fv);
        std::vector<stp_term> args(arity, nullptr);
        for (std::size_t j = m; j-- > 0;)
        {
          stp_term value = nullptr;
          bool observed = false;
          if (stp_fun_value_entry(fv, j, args.data(), &value, &observed) != STP_OK)
            continue;
          std::string guard;
          for (std::uint32_t k = 0; k < arity; ++k)
          {
            guard += (k ? " " : "") + std::string("(= x!") + std::to_string(k) + " " +
                     smt2_value_text(args[k]) + ")";
            stp_term_release(args[k]);
          }
          if (arity != 1)
            guard = "(and " + guard + ")";
          body = "(ite " + guard + " " + smt2_value_text(value) + " " + body + ")";
          stp_term_release(value);
        }
        os << body << ")\n";
        stp_fun_value_release(fv);
      }
      else
        take_error(vc);
    }
    else if (is_array(s))
    {
      if (stp_array_value av = stp_model_array_value(vc->model, sym))
      {
        if (stp_term as_term = stp_array_value_as_term(av))
        {
          os << "(define-fun |" << name << "| () " << sort_text(vc, s) << " " << smt2_value_text(as_term)
             << ")\n";
          stp_term_release(as_term);
        }
        stp_array_value_release(av);
      }
      else
        take_error(vc);
    }
    else if (stp_term v = stp_model_value(vc->model, sym))
    {
      os << "(define-fun |" << name << "| () " << sort_text(vc, s) << " " << smt2_value_text(v) << ")\n";
      stp_term_release(v);
    }
    else
      take_error(vc);
    stp_term_release(sym);
  }
}

} // namespace

char* vc_printSMTLIB2(VC vcp, Expr e)
{
  VCImpl* vc = vcimpl(vcp, "vc_printSMTLIB2");
  stp_term t = term_of(e, "vc_printSMTLIB2");
  if (vc == nullptr || t == nullptr)
    return strdup("");
  Symbols syms;
  collect_symbols(t, syms);
  std::ostringstream os;
  os << "(set-logic " << logic_of(syms) << ")\n";
  os << "(set-info :smt-lib-version 2.0)\n";
  print_declarations_smt2(vc, syms, os);
  // The engine's printer (the shared form), as 2.x's SMTLIB2_PrintBack used:
  // every symbol |quoted|, Reals as numerals. The 3.x unshared printer
  // spells simple names bare, which 2.x clients comparing text would notice.
  char* body = stp_term_to_string(t, STP_FORMAT_SMTLIB2, true);
  os << "(assert " << (body != nullptr ? body : "true") << ")\n";
  stp_free(body);
  return strdup(os.str().c_str());
}

void vc_printVarDecls(VC vcp)
{
  VCImpl* vc = vcimpl(vcp, "vc_printVarDecls");
  if (vc == nullptr)
    return;
  print_var_decls(vc, std::cout);
  std::cout << std::flush;
}

void vc_clearDecls(VC vcp)
{
  VCImpl* vc = vcimpl(vcp, "vc_clearDecls");
  if (vc == nullptr)
    return;
  vc->decls_cleared = stp_tm_num_symbols(vc->tm);
}

void vc_printAsserts(VC vcp, int simplify_print)
{
  VCImpl* vc = vcimpl(vcp, "vc_printAsserts");
  if (vc == nullptr)
    return;
  std::ostringstream os;
  if (print_asserts(vc, os, simplify_print))
    std::cout << os.str() << std::flush;
}

void vc_printQuery(VC vcp)
{
  VCImpl* vc = vcimpl(vcp, "vc_printQuery");
  if (vc == nullptr)
    return;
  std::string text = "TRUE";
  if (vc->last_query != nullptr)
  {
    bool ok = false;
    text = cvc_text(vc, vc->last_query, "vc_printQuery", &ok);
    if (!ok)
      return;
  }
  std::cout << "QUERY(" << text << ");" << std::endl;
}

void vc_printQueryStateToBuffer(VC vcp, Expr e, char** buf, size_t* len, int simplify_print)
{
  VCImpl* vc = vcimpl(vcp, "vc_printQueryStateToBuffer");
  stp_term q = term_of(e, "vc_printQueryStateToBuffer");
  if (vc == nullptr || q == nullptr || buf == nullptr)
  {
    if (buf != nullptr)
      to_buffer(std::string(), buf, len);
    return;
  }
  std::ostringstream os;
  print_var_decls(vc, os);
  os << "%----------------------------------------------------\n";
  print_asserts(vc, os, simplify_print);
  os << "%----------------------------------------------------\n";
  stp_term shown = q;
  if (simplify_print == 1)
  {
    shown = stp_tm_simplify(vc->tm, q);
    if (shown == nullptr)
    {
      take_error(vc);
      shown = q;
    }
  }
  bool ok = false;
  os << "QUERY( " << cvc_text(vc, shown, "vc_printQueryStateToBuffer", &ok) << " );\n";
  if (shown != q)
    stp_term_release(shown);
  to_buffer(os.str(), buf, len);
}

void vc_printCounterExample(VC vcp)
{
  VCImpl* vc = vcimpl(vcp, "vc_printCounterExample");
  if (vc == nullptr)
    return;
  std::cout << "COUNTEREXAMPLE BEGIN: \n";
  print_counterexample_lines(vc, std::cout);
  std::cout << "COUNTEREXAMPLE END: \n" << std::flush;
}

void vc_printCounterExampleFile(VC vcp, int fd)
{
  VCImpl* vc = vcimpl(vcp, "vc_printCounterExampleFile");
  if (vc == nullptr)
    return;
  std::ostringstream os;
  os << "COUNTEREXAMPLE BEGIN: \n";
  print_counterexample_lines(vc, os);
  os << "COUNTEREXAMPLE END: \n";
  const std::string s = os.str();
  std::size_t done = 0;
  while (done < s.size())
  {
    const auto n = compat2_write(fd, s.data() + done, static_cast<unsigned>(s.size() - done));
    if (n <= 0)
      break;
    done += static_cast<std::size_t>(n);
  }
}

void vc_printCounterExampleToBuffer(VC vcp, char** buf, size_t* len)
{
  VCImpl* vc = vcimpl(vcp, "vc_printCounterExampleToBuffer");
  if (vc == nullptr || buf == nullptr)
    return;
  std::ostringstream os;
  os << "COUNTEREXAMPLE BEGIN: \n";
  print_counterexample_lines(vc, os);
  os << "COUNTEREXAMPLE END: \n";
  to_buffer(os.str(), buf, len);
}

void vc_printCounterExampleSMTLIB2(VC vcp)
{
  VCImpl* vc = vcimpl(vcp, "vc_printCounterExampleSMTLIB2");
  if (vc == nullptr)
    return;
  print_counterexample_smt2(vc, std::cout);
  std::cout << std::flush;
}

int vc_getHashQueryStateToBuffer(VC vcp, Expr query)
{
  VCImpl* vc = vcimpl(vcp, "vc_getHashQueryStateToBuffer");
  stp_term q = term_of(query, "vc_getHashQueryStateToBuffer");
  if (vc == nullptr || q == nullptr)
    return 0;
  std::vector<stp_term> parts;
  stp_term nq = stp_not(vc->tm, q);
  if (nq == nullptr)
  {
    take_error(vc);
    return 0;
  }
  parts.push_back(nq);
  for (const auto& level : vc->levels)
    parts.insert(parts.end(), level.begin(), level.end());
  stp_term all = parts.size() == 1 ? stp_term_copy(nq) : stp_and(vc->tm, parts.size(), parts.data());
  std::uint64_t h = 0;
  if (all != nullptr)
  {
    h = stp_term_hash(all);
    stp_term_release(all);
  }
  else
    take_error(vc);
  stp_term_release(nq);
  return static_cast<int>(h ^ (h >> 32));
}

// ============================================================ parsing

namespace
{

// The QUERY statement of a CVC text: where it starts, its formula, and the
// text with the statement replaced by "QUERY TRUE;". The 3.x CVC parser
// asserts the negated query along with the ASSERTs; 2.x asserted the ASSERTs
// alone and returned the query separately, which this reproduces by parsing
// the query on its own inside a push/pop bracket.
bool split_cvc_query(const std::string& text, std::string& without, std::string& query)
{
  std::size_t query_at = std::string::npos;
  bool in_comment = false;
  for (std::size_t i = 0; i < text.size(); ++i)
  {
    const char c = text[i];
    if (in_comment)
    {
      if (c == '\n')
        in_comment = false;
      continue;
    }
    if (c == '%')
    {
      in_comment = true;
      continue;
    }
    if (text.compare(i, 5, "QUERY") == 0)
    {
      const bool starts = i == 0 || !(std::isalnum(static_cast<unsigned char>(text[i - 1])) || text[i - 1] == '_');
      const bool ends = i + 5 >= text.size() ||
                        !(std::isalnum(static_cast<unsigned char>(text[i + 5])) || text[i + 5] == '_');
      if (starts && ends)
        query_at = i;
    }
  }
  if (query_at == std::string::npos)
    return false;
  const std::size_t end = text.find(';', query_at);
  if (end == std::string::npos)
    return false;
  query = text.substr(query_at + 5, end - (query_at + 5));
  without = text.substr(0, query_at) + "QUERY TRUE;" + text.substr(end + 1);
  return true;
}

// Parses `text`, asserting into the current level, and hands back the
// formulas the parse added (one reference each) -- also recorded on the
// stack copy. False after a reported error.
bool parse_into(VCImpl* vc, const std::string& text, stp_format format, const char* who,
                std::vector<stp_term>& added)
{
  stp_solver s = ensure_solver(vc);
  if (s == nullptr)
    return false;
  const std::size_t before = stp_solver_num_assertions(s);
  if (stp_solver_parse(s, text.c_str(), format) != STP_OK)
  {
    fatal(std::string("CInterface: ") + who + ": " + take_error(vc));
    return false;
  }
  const std::size_t after = stp_solver_num_assertions(s);
  for (std::size_t i = before; i < after; ++i)
    if (stp_term t = stp_solver_assertion(s, i))
    {
      added.push_back(t);
      vc->levels.back().push_back(stp_term_copy(t));
    }
  return true;
}

// The query of a CVC text, parsed on its own inside a bracket: the parser
// asserts its negation, which is read back and negated again.
stp_term parse_cvc_query(VCImpl* vc, const std::string& query_text, const char* who)
{
  stp_solver s = ensure_solver(vc);
  if (s == nullptr)
    return nullptr;
  if (stp_solver_push(s, 1) != STP_OK)
  {
    fatal(std::string("CInterface: ") + who + ": " + take_error(vc));
    return nullptr;
  }
  const std::size_t before = stp_solver_num_assertions(s);
  stp_term query = nullptr;
  if (stp_solver_parse(s, ("QUERY " + query_text + ";\n").c_str(), STP_FORMAT_CVC) != STP_OK)
  {
    const std::string err = take_error(vc);
    stp_solver_pop(s, 1);
    take_error(vc);
    fatal(std::string("CInterface: ") + who + ": " + err);
    return nullptr;
  }
  const std::size_t after = stp_solver_num_assertions(s);
  if (after > before)
  {
    stp_term negated = stp_solver_assertion(s, after - 1);
    query = negated != nullptr ? stp_not(vc->tm, negated) : nullptr;
    if (negated != nullptr)
      stp_term_release(negated);
  }
  else
    query = stp_mk_true(vc->tm);
  if (stp_solver_pop(s, 1) != STP_OK)
    take_error(vc);
  return query;
}

// A conjunction (one reference) of the formulas, TRUE for none.
stp_term conjunction(VCImpl* vc, const std::vector<stp_term>& parts)
{
  if (parts.empty())
    return stp_mk_true(vc->tm);
  if (parts.size() == 1)
    return stp_term_copy(parts[0]);
  return stp_and(vc->tm, parts.size(), parts.data());
}

// Parses a whole CVC / SMT-LIB 1 text as the two 2.x entry points do:
// the ASSERTs are asserted; `asserts` and `query` come back as formulas.
bool parse_text(VCImpl* vc, const std::string& text, const char* who, stp_term& asserts, stp_term& query)
{
  asserts = nullptr;
  query = nullptr;
  std::vector<stp_term> added;
  bool ok;
  if (vc->flag_m)
  {
    // SMT-LIB 1: the assumptions and the formula are asserted alike, as the
    // parser has done for years; there is no separate query.
    ok = parse_into(vc, text, STP_FORMAT_SMTLIB1, who, added);
    if (ok)
      query = stp_mk_false(vc->tm);
  }
  else
  {
    std::string without, qtext;
    const bool has_query = split_cvc_query(text, without, qtext);
    ok = parse_into(vc, has_query ? without : text, STP_FORMAT_CVC, who, added);
    if (ok)
      query = has_query ? parse_cvc_query(vc, qtext, who) : stp_mk_true(vc->tm);
    ok = ok && query != nullptr;
  }
  if (ok)
    asserts = conjunction(vc, added);
  for (stp_term t : added)
    stp_term_release(t);
  if (!ok)
  {
    if (query != nullptr)
      stp_term_release(query);
    query = nullptr;
    return false;
  }
  return true;
}

} // namespace

Expr vc_parseExpr(VC vcp, const char* infile)
{
  VCImpl* vc = vcimpl(vcp, "vc_parseExpr");
  if (vc == nullptr)
    return nullptr;
  if (infile == nullptr)
  {
    fatal("Cannot open file");
    return nullptr;
  }
  std::ifstream in(infile, std::ios::binary);
  if (!in)
  {
    std::fprintf(stderr, "STP: Error: cannot open %s\n", infile);
    fatal("Cannot open file");
    return nullptr;
  }
  std::stringstream buffer;
  buffer << in.rdbuf();
  stp_term asserts = nullptr, query = nullptr;
  if (!parse_text(vc, buffer.str(), "vc_parseExpr", asserts, query))
    return nullptr;
  // 2.x returned the conjunction of the ASSERTs with the negated query.
  stp_term nq = stp_not(vc->tm, query);
  stp_term out = nq != nullptr ? stp_and2(vc->tm, asserts, nq) : nullptr;
  if (nq != nullptr)
    stp_term_release(nq);
  stp_term_release(asserts);
  stp_term_release(query);
  if (out == nullptr)
  {
    fatal("CInterface: vc_parseExpr: " + take_error(vc));
    return nullptr;
  }
  return wrap(vc, out, false);
}

int vc_parseMemExpr(VC vcp, const char* s, Expr* oquery, Expr* oasserts)
{
  VCImpl* vc = vcimpl(vcp, "vc_parseMemExpr");
  if (vc == nullptr)
    return 0;
  if (s == nullptr)
  {
    fatal("CInterface: vc_parseMemExpr: null text");
    return 0;
  }
  stp_term asserts = nullptr, query = nullptr;
  if (!parse_text(vc, s, "vc_parseMemExpr", asserts, query))
    return 0;
  if (oquery != nullptr)
    *oquery = wrap(vc, query, false);
  else
    stp_term_release(query);
  if (oasserts != nullptr)
    *oasserts = wrap(vc, asserts, false);
  else
    stp_term_release(asserts);
  return 1;
}

// ============================================================ uninterpreted functions

namespace
{

// A live handle of this checker, when the registry is on (it always is once
// 'u' has been set, which every UF entry point requires).
bool live_handle(VCImpl* vc, Expr e, std::string& diagnostic)
{
  if (e == nullptr)
  {
    diagnostic = "null expression handle";
    return false;
  }
  if (!vc->tracking)
  {
    diagnostic = "uninterpreted functions are not enabled";
    return false;
  }
  if (!registry_holds(vc, e))
  {
    diagnostic = "invalid or destroyed expression handle";
    return false;
  }
  return true;
}

bool uf_sort_of_type(VCImpl* vc, Type type, const char* position, stp_sort& sort, std::string& diagnostic)
{
  if (!live_handle(vc, type, diagnostic))
  {
    diagnostic = std::string(position) + " type: " + diagnostic;
    return false;
  }
  Handle* h = handle(type);
  if (!h->is_type())
  {
    diagnostic = std::string(position) + " type is not a sort";
    return false;
  }
  switch (sort_kind(h->sort))
  {
    case STP_SORT_BOOL:
    case STP_SORT_BV:
    case STP_SORT_FP:
    case STP_SORT_RM:
    case STP_SORT_REAL:
      sort = h->sort;
      return true;
    default:
      diagnostic = std::string(position) + " type " + sort_text(vc, h->sort) +
                   " is unsupported (Bool, bit-vector, floating-point, RoundingMode and Real sorts "
                   "are supported)";
      return false;
  }
}

UFDeclRec* uf_record(VCImpl* vc, UFDeclHandle h, std::string& diagnostic)
{
  if (h == 0)
  {
    diagnostic = "null uninterpreted-function declaration handle";
    return nullptr;
  }
  {
    std::lock_guard<std::mutex> lock(g_mutex);
    auto it = g_uf_owner.find(h);
    if (it == g_uf_owner.end() || it->second != vc)
    {
      diagnostic = "invalid, stale, destroyed, or cross-context uninterpreted-function declaration handle";
      return nullptr;
    }
  }
  auto it = vc->ufs.find(h);
  if (it == vc->ufs.end())
  {
    diagnostic = "invalid, stale, destroyed, or cross-context uninterpreted-function declaration handle";
    return nullptr;
  }
  return &it->second;
}

} // namespace

UFDeclHandle vc_declareUninterpretedFunction(VC vcp, const char* name, const Type* domainTypes,
                                             size_t domainCount, Type codomain)
{
  if (vcp == nullptr || name == nullptr || (domainCount != 0 && domainTypes == nullptr) || codomain == nullptr)
  {
    report("vc_declareUninterpretedFunction received a null required argument");
    return 0;
  }
  VCImpl* vc = static_cast<VCImpl*>(vcp);
  if (!vc_is_live(vc))
  {
    report("vc_declareUninterpretedFunction received an invalid or destroyed validity-checker handle");
    return 0;
  }
  if (!vc->flag_u)
  {
    report("uninterpreted functions are not enabled");
    return 0;
  }
  if (domainCount == 0)
  {
    report("zero-arity functions are ordinary symbols");
    return 0;
  }
  for (const auto& uf : vc->ufs)
    if (uf.second.name == name)
    {
      report(std::string("name '") + name + "' already denotes an uninterpreted function");
      return 0;
    }
  if (stp_term taken = stp_tm_symbol(vc->tm, name))
  {
    stp_term_release(taken);
    report(std::string("name '") + name + "' already denotes an ordinary symbol");
    return 0;
  }
  std::string diagnostic;
  std::vector<stp_sort> domain;
  domain.reserve(domainCount);
  for (std::size_t i = 0; i < domainCount; ++i)
  {
    stp_sort s = nullptr;
    if (!uf_sort_of_type(vc, domainTypes[i], "domain", s, diagnostic))
    {
      report(diagnostic);
      return 0;
    }
    domain.push_back(s);
  }
  stp_sort cod = nullptr;
  if (!uf_sort_of_type(vc, codomain, "codomain", cod, diagnostic))
  {
    report(diagnostic);
    return 0;
  }
  stp_sort fun = stp_mk_fun_sort(vc->tm, domain.size(), domain.data(), cod);
  if (fun == nullptr)
  {
    report("vc_declareUninterpretedFunction: " + take_error(vc));
    return 0;
  }
  stp_term f = stp_declare(vc->tm, name, fun);
  if (f == nullptr)
  {
    report("vc_declareUninterpretedFunction: " + take_error(vc));
    return 0;
  }
  UFDeclRec rec;
  rec.fun = f;
  rec.domain = domain;
  rec.codomain = cod;
  rec.name = name;
  UFDeclHandle h;
  {
    std::lock_guard<std::mutex> lock(g_mutex);
    h = ++g_next_uf;
    g_uf_owner[h] = vc;
  }
  vc->ufs.emplace(h, std::move(rec));
  vc->uf_certified = false;
  return h;
}

Expr vc_applyUninterpretedFunction(VC vcp, UFDeclHandle function, const Expr* arguments, size_t argumentCount)
{
  if (vcp == nullptr || function == 0 || (argumentCount != 0 && arguments == nullptr))
  {
    report("vc_applyUninterpretedFunction received a null required argument");
    return nullptr;
  }
  VCImpl* vc = static_cast<VCImpl*>(vcp);
  if (!vc_is_live(vc))
  {
    report("vc_applyUninterpretedFunction received an invalid or destroyed validity-checker handle");
    return nullptr;
  }
  std::string diagnostic;
  UFDeclRec* rec = uf_record(vc, function, diagnostic);
  if (rec == nullptr)
  {
    report(diagnostic);
    return nullptr;
  }
  if (argumentCount != rec->domain.size())
  {
    report(rec->name + " expects " + std::to_string(rec->domain.size()) + " argument(s), got " +
           std::to_string(argumentCount));
    return nullptr;
  }
  std::vector<stp_term> terms;
  terms.reserve(argumentCount + 1);
  terms.push_back(rec->fun);
  for (std::size_t i = 0; i < argumentCount; ++i)
  {
    if (!live_handle(vc, arguments[i], diagnostic))
    {
      report("vc_applyUninterpretedFunction argument " + std::to_string(i) + ": " + diagnostic);
      return nullptr;
    }
    Handle* h = handle(arguments[i]);
    if (h->is_type())
    {
      report("vc_applyUninterpretedFunction argument " + std::to_string(i) + ": a type is not a term");
      return nullptr;
    }
    if (stp_term_sort(h->term) != rec->domain[i])
    {
      report("argument " + std::to_string(i) + " of " + rec->name + " has sort " +
             sort_text(vc, stp_term_sort(h->term)) + " but the declaration requires " +
             sort_text(vc, rec->domain[i]));
      return nullptr;
    }
    terms.push_back(h->term);
  }
  stp_term app = stp_apply_n(vc->tm, terms.size(), terms.data());
  if (app == nullptr)
  {
    report("vc_applyUninterpretedFunction: " + take_error(vc));
    return nullptr;
  }
  return wrap(vc, app, false);
}

namespace compat2
{

Expr uf_value(VCImpl* vc, Expr application, const char* who)
{
  std::string diagnostic;
  if (!live_handle(vc, application, diagnostic))
  {
    report(std::string(who) + ": " + diagnostic);
    return nullptr;
  }
  Handle* h = handle(application);
  stp_kind k;
  if (h->is_type() || stp_term_get_kind(h->term, &k) != STP_OK || k != STP_KIND_APPLY)
  {
    report(std::string(who) + ": not an uninterpreted-function application");
    return nullptr;
  }
  if (vc->model == nullptr || !vc->uf_certified)
  {
    report(std::string(who) +
           ": no certified uninterpreted-function model -- no satisfiable query has been answered "
           "since the last assertion, vc_push or vc_pop");
    return nullptr;
  }
  std::size_t n = 0;
  stp_term_num_children(h->term, &n);
  stp_term f = n > 0 ? stp_term_child(h->term, 0) : nullptr;
  if (f == nullptr)
  {
    report(std::string(who) + ": " + take_error(vc));
    return nullptr;
  }
  stp_fun_value fv = stp_model_fun_value(vc->model, f);
  stp_term_release(f);
  if (fv == nullptr)
  {
    report(std::string(who) + ": " + take_error(vc));
    return nullptr;
  }
  // The values of the actual arguments in the model; a tuple the solve
  // observed is one the function's cases list (values are interned, so equal
  // values are the same handle). An argument over a symbol outside the
  // model's core was not part of the solve: try_value is NULL for it rather
  // than a completed value that could coincide with an observed tuple.
  std::vector<stp_term> actual;
  bool ok = true;
  bool unreachable = false;
  for (std::size_t i = 1; i < n && ok; ++i)
  {
    stp_term arg = stp_term_child(h->term, i);
    stp_term v = arg != nullptr ? stp_model_try_value(vc->model, arg) : nullptr;
    if (arg != nullptr)
      stp_term_release(arg);
    if (v == nullptr)
    {
      const std::string err = take_error(vc);
      if (!err.empty())
        report(std::string(who) + ": " + err);
      else
        unreachable = true;
      ok = false;
    }
    else
      actual.push_back(v);
  }
  Expr result = nullptr;
  bool observed_tuple = false;
  if (ok)
  {
    const std::size_t m = stp_fun_value_size(fv);
    std::vector<stp_term> args(actual.size(), nullptr);
    for (std::size_t j = 0; j < m && result == nullptr; ++j)
    {
      stp_term value = nullptr;
      bool observed = false;
      if (stp_fun_value_entry(fv, j, args.data(), &value, &observed) != STP_OK)
      {
        take_error(vc);
        continue;
      }
      bool same = true;
      for (std::size_t i = 0; i < actual.size(); ++i)
        same = same && args[i] == actual[i];
      for (stp_term a : args)
        stp_term_release(a);
      if (same)
      {
        observed_tuple = true;
        result = wrap(vc, value, false);
      }
      else
        stp_term_release(value);
    }
  }
  for (stp_term v : actual)
    stp_term_release(v);
  stp_fun_value_release(fv);
  if (!observed_tuple && (ok || unreachable))
    report(std::string(who) + ": the application was not reachable from the last satisfiable query, so "
                              "the certified model has no value for it");
  return result;
}

} // namespace compat2

Expr vc_getUninterpretedFunctionValue(VC vcp, Expr application)
{
  if (vcp == nullptr || application == nullptr)
  {
    report("vc_getUninterpretedFunctionValue received a null required argument");
    return nullptr;
  }
  VCImpl* vc = static_cast<VCImpl*>(vcp);
  if (!vc_is_live(vc))
  {
    report("vc_getUninterpretedFunctionValue received an invalid or destroyed validity-checker handle");
    return nullptr;
  }
  return uf_value(vc, application, "vc_getUninterpretedFunctionValue");
}

// ============================================================ introspection

namespace
{

exprkind_t kind_of_sort(stp_sort s)
{
  switch (sort_kind(s))
  {
    case STP_SORT_BOOL: return BOOLEAN;
    case STP_SORT_BV: return BITVECTOR;
    case STP_SORT_ARRAY: return ARRAY;
    case STP_SORT_FP: return FLOATINGPOINT;
    case STP_SORT_RM: return ROUNDINGMODE;
    case STP_SORT_REAL: return REAL_CONST;
    default: return UNDEFINED;
  }
}

exprkind_t kind_of_term(stp_term t)
{
  stp_kind k;
  if (stp_term_get_kind(t, &k) != STP_OK)
    return UNDEFINED;
  const stp_sort s = stp_term_sort(t);
  switch (k)
  {
    case STP_KIND_VALUE:
      if (is_bool(s))
      {
        bool b = false;
        stp_term_to_bool(t, &b);
        return b ? TRUE : FALSE;
      }
      if (is_real(s))
        return REAL_CONST;
      return BVCONST; // bit-vectors, and floats / rounding modes as 2.x reported them
    case STP_KIND_CONSTANT: return SYMBOL;
    case STP_KIND_ITE: return ITE;
    case STP_KIND_EQUAL:
    {
      // 2.x built IFF over Booleans and FP_SMT_EQ over floats.
      stp_term c = stp_term_child(t, 0);
      exprkind_t out = EQ;
      if (c != nullptr)
      {
        const stp_sort cs = stp_term_sort(c);
        if (is_bool(cs))
          out = IFF;
        else if (is_fp(cs))
          out = FP_SMT_EQ;
        stp_term_release(c);
      }
      return out;
    }
    case STP_KIND_DISTINCT: return DISTINCT;
    case STP_KIND_APPLY: return UF_APPLY;
    case STP_KIND_NOT: return NOT;
    case STP_KIND_AND: return AND;
    case STP_KIND_OR: return OR;
    case STP_KIND_XOR: return XOR;
    case STP_KIND_IMPLIES: return IMPLIES;
    case STP_KIND_BV_NOT: return BVNOT;
    case STP_KIND_BV_AND: return BVAND;
    case STP_KIND_BV_OR: return BVOR;
    case STP_KIND_BV_XOR: return BVXOR;
    case STP_KIND_BV_NAND: return BVNAND;
    case STP_KIND_BV_NOR: return BVNOR;
    case STP_KIND_BV_XNOR: return BVXNOR;
    case STP_KIND_BV_NEG: return BVUMINUS;
    case STP_KIND_BV_ADD: return BVPLUS;
    case STP_KIND_BV_SUB: return BVSUB;
    case STP_KIND_BV_MUL: return BVMULT;
    case STP_KIND_BV_UDIV: return BVDIV;
    case STP_KIND_BV_UREM: return BVMOD;
    case STP_KIND_BV_SDIV: return SBVDIV;
    case STP_KIND_BV_SREM: return SBVREM;
    case STP_KIND_BV_SMOD: return SBVMOD;
    case STP_KIND_BV_SHL: return BVLEFTSHIFT;
    case STP_KIND_BV_LSHR: return BVRIGHTSHIFT;
    case STP_KIND_BV_ASHR: return BVSRSHIFT;
    case STP_KIND_BV_CONCAT: return BVCONCAT;
    case STP_KIND_BV_EXTRACT: return BVEXTRACT;
    case STP_KIND_BV_ZERO_EXTEND: return BVZX;
    case STP_KIND_BV_SIGN_EXTEND: return BVSX;
    case STP_KIND_BV_ULT: return BVLT;
    case STP_KIND_BV_ULE: return BVLE;
    case STP_KIND_BV_UGT: return BVGT;
    case STP_KIND_BV_UGE: return BVGE;
    case STP_KIND_BV_SLT: return BVSLT;
    case STP_KIND_BV_SLE: return BVSLE;
    case STP_KIND_BV_SGT: return BVSGT;
    case STP_KIND_BV_SGE: return BVSGE;
    case STP_KIND_BV_UADDO: return BVUADDO;
    case STP_KIND_BV_SADDO: return BVSADDO;
    case STP_KIND_BV_UMULO: return BVUMULO;
    case STP_KIND_BV_SMULO: return BVSMULO;
    case STP_KIND_BV_USUBO: return BVUSUBO;
    case STP_KIND_BV_SSUBO: return BVSSUBO;
    case STP_KIND_SELECT: return READ;
    case STP_KIND_STORE: return WRITE;
    case STP_KIND_FP_ABS: return FP_ABS;
    case STP_KIND_FP_NEG: return FP_NEG;
    case STP_KIND_FP_ADD: return FP_ADD;
    case STP_KIND_FP_SUB: return FP_SUB;
    case STP_KIND_FP_MUL: return FP_MUL;
    case STP_KIND_FP_DIV: return FP_DIV;
    case STP_KIND_FP_FMA: return FP_FMA;
    case STP_KIND_FP_SQRT: return FP_SQRT;
    case STP_KIND_FP_REM: return FP_REM;
    case STP_KIND_FP_RTI: return FP_ROUNDTOINTEGRAL;
    case STP_KIND_FP_MIN: return FP_MIN;
    case STP_KIND_FP_MAX: return FP_MAX;
    case STP_KIND_FP_EQ: return FP_EQ;
    case STP_KIND_FP_LT: return FP_LT;
    case STP_KIND_FP_LEQ: return FP_LEQ;
    case STP_KIND_FP_GT: return FP_GT;
    case STP_KIND_FP_GEQ: return FP_GEQ;
    case STP_KIND_FP_IS_NORMAL: return FP_ISNORMAL;
    case STP_KIND_FP_IS_SUBNORMAL: return FP_ISSUBNORMAL;
    case STP_KIND_FP_IS_ZERO: return FP_ISZERO;
    case STP_KIND_FP_IS_INF: return FP_ISINFINITE;
    case STP_KIND_FP_IS_NAN: return FP_ISNAN;
    case STP_KIND_FP_IS_NEG: return FP_ISNEGATIVE;
    case STP_KIND_FP_IS_POS: return FP_ISPOSITIVE;
    case STP_KIND_FP_FP:
    case STP_KIND_FP_TO_FP_FROM_BV:
    case STP_KIND_FP_TO_FP_FROM_FP:
    case STP_KIND_FP_TO_FP_FROM_REAL:
      return FP_TOFP;
    case STP_KIND_FP_TO_FP_FROM_SBV: return FP_TOFP_SIGNED;
    case STP_KIND_FP_TO_FP_FROM_UBV: return FP_TOFP_UNSIGNED;
    case STP_KIND_FP_TO_UBV: return FP_TO_UBV;
    case STP_KIND_FP_TO_SBV: return FP_TO_SBV;
    case STP_KIND_FP_TO_IEEE_BV: return FP_TO_IEEE_BV;
    case STP_KIND_REAL_ADD: return REAL_ADD;
    case STP_KIND_REAL_SUB: return REAL_SUB;
    case STP_KIND_REAL_NEG: return REAL_NEG;
    case STP_KIND_REAL_MUL: return REAL_MUL;
    case STP_KIND_REAL_DIV: return REAL_DIV;
    case STP_KIND_REAL_LT: return REAL_LT;
    case STP_KIND_REAL_LE: return REAL_LE;
    case STP_KIND_REAL_GT: return REAL_GT;
    case STP_KIND_REAL_GE: return REAL_GE;
    default:
      return UNDEFINED; // no 2.x spelling: repeat, rotate, bvcomp, bvnego, bvsdivo, redand/or, const arrays, fp.to_real
  }
}

} // namespace

exprkind_t getExprKind(Expr e)
{
  Handle* h = handle(e);
  if (h == nullptr)
  {
    fatal("CInterface: getExprKind: null expression handle");
    return UNDEFINED;
  }
  return h->is_type() ? kind_of_sort(h->sort) : kind_of_term(h->term);
}

int getDegree(Expr e)
{
  Handle* h = handle(e);
  if (h == nullptr)
  {
    fatal("CInterface: getDegree: null expression handle");
    return 0;
  }
  if (h->is_type())
    return 0;
  std::size_t n = 0;
  stp_term_num_children(h->term, &n);
  return static_cast<int>(n);
}

Expr getChild(Expr e, int i)
{
  Handle* h = handle(e);
  if (h == nullptr || h->is_type())
  {
    fatal("getChild: Error accessing childNode in expression: ");
    return nullptr;
  }
  std::size_t n = 0;
  stp_term_num_children(h->term, &n);
  if (i < 0 || static_cast<std::size_t>(i) >= n)
  {
    fatal("getChild: Error accessing childNode in expression: ");
    return nullptr;
  }
  stp_term c = stp_term_child(h->term, static_cast<std::size_t>(i));
  if (c == nullptr)
  {
    fatal("getChild: Error accessing childNode in expression: " + take_error(h->vc));
    return nullptr;
  }
  return wrap(h->vc, c, false);
}

int getBVLength(Expr e)
{
  stp_sort s = sort_of(e);
  if (!is_bv(s))
  {
    fatal("c_interface: vc_GetBVLength: Input expression must be a bit-vector");
    return 0;
  }
  return static_cast<int>(bv_width(s));
}

int vc_getBVLength(VC /* vc */, Expr e)
{
  return getBVLength(e);
}

type_t getType(Expr e)
{
  switch (sort_kind(sort_of(e)))
  {
    case STP_SORT_BOOL: return BOOLEAN_TYPE;
    case STP_SORT_BV: return BITVECTOR_TYPE;
    case STP_SORT_ARRAY: return ARRAY_TYPE;
    case STP_SORT_FP: return FLOATINGPOINT_TYPE;
    case STP_SORT_RM: return ROUNDINGMODE_TYPE;
    case STP_SORT_REAL: return REAL_TYPE;
    default: return UNKNOWN_TYPE;
  }
}

namespace
{
// 2.x's width getters reached ASTNode's accessors, which are fatal on a
// mathematical Real (the messages below are theirs); the negative acceptance
// tests pin both the report and its wording.
bool real_has_no_width(Expr e, const char* engine_message)
{
  const stp_sort s = sort_of(e);
  if (s == nullptr || !is_real(s))
    return false;
  fatal(engine_message);
  return true;
}
} // namespace

int getVWidth(Expr e)
{
  if (real_has_no_width(e, "GetValueWidth: mathematical Real has no bit-vector width"))
    return 0;
  return static_cast<int>(packed_width(sort_of(e)));
}

int getIWidth(Expr e)
{
  if (real_has_no_width(e, "GetIndexWidth: mathematical Real has no array index width"))
    return 0;
  return static_cast<int>(index_width(sort_of(e)));
}

int vc_getExpWidth(Expr e)
{
  if (real_has_no_width(e, "GetExpWidth: mathematical Real has no floating-point format"))
    return 0;
  std::uint32_t eb = 0, sb = 0;
  return fp_format(sort_of(e), eb, sb) ? static_cast<int>(eb) : 0;
}

int vc_getSigWidth(Expr e)
{
  if (real_has_no_width(e, "GetSigWidth: mathematical Real has no floating-point format"))
    return 0;
  std::uint32_t eb = 0, sb = 0;
  return fp_format(sort_of(e), eb, sb) ? static_cast<int>(sb) : 0;
}

const char* exprName(Expr e)
{
  Handle* h = handle(e);
  if (h == nullptr || h->is_type())
    return nullptr;
  if (!h->has_name)
  {
    char* n = stp_term_symbol(h->term);
    if (n == nullptr)
      return nullptr;
    h->name = n;
    h->has_name = true;
    stp_free(n);
  }
  return h->name.c_str();
}

uint64_t getExprID(Expr e)
{
  Handle* h = handle(e);
  if (h == nullptr)
    return 0;
  return h->is_type() ? stp_sort_id(h->sort) : stp_term_id(h->term);
}

Type vc_getType(VC vcp, Expr e)
{
  VCImpl* vc = vcimpl(vcp, "vc_getType");
  if (vc == nullptr)
    return nullptr;
  stp_sort s = sort_of(e);
  if (s == nullptr)
  {
    fatal("c_interface: vc_GetType: expression with bad typing: please check your expression construction");
    return nullptr;
  }
  return wrap_type(vc, s);
}

namespace
{

bool type_sizes(Type type, std::uint32_t& value, std::uint32_t& index)
{
  stp_sort s = sort_of(type);
  value = 0;
  index = 0;
  switch (sort_kind(s))
  {
    case STP_SORT_BOOL:
      return true;
    case STP_SORT_BV:
    case STP_SORT_FP:
    case STP_SORT_RM:
      value = packed_width(s);
      return true;
    case STP_SORT_ARRAY:
      value = packed_width(s);
      index = index_width(s);
      return true;
    case STP_SORT_REAL:
      fatal("CInterface: mathematical Real has no bit width");
      return false;
    default:
      fatal("CInterface: vc_varExpr: Unsupported type");
      return false;
  }
}

} // namespace

int vc_getValueSize(VC /* vc */, Type type)
{
  std::uint32_t v = 0, i = 0;
  type_sizes(type, v, i);
  return static_cast<int>(v);
}

int vc_getIndexSize(VC /* vc */, Type type)
{
  std::uint32_t v = 0, i = 0;
  type_sizes(type, v, i);
  return static_cast<int>(i);
}

Expr vc_simplify(VC vcp, Expr e)
{
  VCImpl* vc = vcimpl(vcp, "vc_simplify");
  stp_term t = term_of(e, "vc_simplify");
  if (vc == nullptr || t == nullptr)
    return nullptr;
  stp_term s = stp_tm_simplify(vc->tm, t);
  if (s == nullptr)
  {
    fatal("CInterface: vc_simplify: " + take_error(vc));
    return nullptr;
  }
  return wrap(vc, s, false);
}
