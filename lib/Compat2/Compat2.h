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

// Compat2.h -- the internals shared by the two translation units of libstp2,
// the 2.x C API (stp/c_interface.h) implemented over the 3.x C API
// (stp/stp.h). Nothing here is installed; nothing here reaches the engine.
//
// The shape of the library (see NOTES.md for the reasoning):
//   - a VC is a VCImpl: one term manager, one solver (created lazily, so
//     that construction-time options such as the SAT backend can still be
//     chosen after the checker exists), the 2.x ownership state, the cached
//     model and a copy of the assertion stack;
//   - an Expr or Type is a Handle, a small heap object holding one 3.x term
//     reference (or, for a Type, a sort);
//   - the process-global error handler and policy of vc_registerErrorHandler
//     / vc_setErrorPolicy, and the registries the UF entry points consult to
//     reject stale handles without dereferencing them.

#ifndef STP_COMPAT2_H
#define STP_COMPAT2_H

#include "stp/c_interface.h"
#include "stp/stp.h"

#include <cstddef>
#include <cstdint>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace compat2
{

struct VCImpl;

// One Expr / Type handle.
//
// The term is deliberately the FIRST member and the only one before any
// padding: a 3.x term handle is the engine's own interned node, and some 2.x
// clients read an Expr as a `stp::ASTNode`, which is a single pointer to that
// same node, to compare two handles' nodes or to type-check them. Keeping the
// node where an ASTNode keeps it lets that pun go on working against this
// library.
struct Handle
{
  stp_term term = nullptr; // the term (NULL for a Type)
  stp_sort sort = nullptr; // the sort of a Type handle (NULL for an Expr)
  VCImpl* vc = nullptr;
  bool checker_owned = false; // in vc->persist: released by vc_Destroy
  bool has_name = false;      // exprName()'s cached string is valid
  std::string name;

  bool is_type() const { return term == nullptr; }
};

// A declared uninterpreted function, keyed by its UFDeclHandle.
struct UFDeclRec
{
  stp_term fun = nullptr; // the function symbol (one reference)
  std::vector<stp_sort> domain;
  stp_sort codomain = nullptr;
  std::string name;
};

// vc_getWholeCounterExample's handle: a detached copy of the model there was
// when it was taken (NULL when there was none), and the terms 2.x's
// counterexample map held then beyond the symbols and array cells (see
// VCImpl::evaluated), by id and held (one reference each), as the map held
// them.
struct WholeCE
{
  VCImpl* vc = nullptr;
  stp_model model = nullptr;
  std::unordered_set<std::uint64_t> recorded;
  std::vector<stp_term> held;
};

struct VCImpl
{
  stp_tm tm = nullptr;
  // Every option this checker has been given, applied to the live solver as
  // it arrives and replayed into a rebuilt one; stp_solver_new takes it.
  stp_options opts = nullptr;
  stp_solver solver = nullptr; // created on first need (ensure_solver)

  // The assertion stack, level 0 the base: one term reference per formula.
  // Kept so that the solver can be rebuilt when a construction-time option
  // changes, and so that the printers see what was asserted rather than what
  // the engine has since conjoined.
  std::vector<std::vector<stp_term>> levels{std::vector<stp_term>()};
  // The shallowest depth (levels.size()) at which the engine refused an
  // assertion (the exact-arithmetic budget, say), or 0. A query at that depth
  // or deeper is missing one of its constraints, so it answers unknown, as
  // 2.x's did; a pop back above the depth clears it.
  std::size_t refused_depth = 0;

  std::unordered_set<Handle*> persist;                 // checker-owned handles
  std::unordered_map<UFDeclHandle, UFDeclRec> ufs;    // this checker's UFs
  std::unordered_set<WholeCE*> whole_ces;              // outstanding snapshots

  stp_model model = nullptr; // the model of the last INVALID query, or NULL
  bool uf_certified = false; // that model may answer UF application reads
  // The terms vc_getCounterExample has evaluated against that model (one
  // reference each). 2.x's counterexample map kept every term such an
  // evaluation visited, and a whole counterexample copied the map, so what a
  // snapshot answers for is worked out from these when one is taken.
  std::vector<stp_term> evaluated;
  std::unordered_set<std::uint64_t> evaluated_ids;
  // 2.x's exact Real model is current only until the checker changes: a
  // declaration (of any sort), an assertion, a push or a pop invalidates it
  // until the next INVALID query republishes it. The bit-vector
  // counterexample keeps 2.x's own, longer life.
  std::size_t real_model_symbols = 0; // the symbol count at publication
  bool real_model_stale = false;      // an assertion since publication
  stp_term last_query = nullptr; // for vc_printQuery

  bool exprdelete = true; // EXPRDELETE: checker-owned handles exist
  bool tracking = false;  // the 'u' live-handle registry is on
  bool flag_x = false, flag_u = false, flag_m = false, flag_n = false,
       flag_p = false;
  bool divmod_explicit = false; // BV_TERM_ABSTRACTION_DIVMOD was named
  int uf_sort_width = 16;       // recorded only (see NOTES.md)

  enum reason_unknown_t reason = REASON_UNKNOWN_NONE;
  std::string reason_detail;

  std::size_t decls_cleared = 0; // vc_clearDecls: symbols before this are not printed
  std::string backend;           // the selected SAT backend, by option name
};

// ------------------------------------------------------------------ diagnostics

// A nonfatal diagnostic: the registered handler, else stderr.
void report(const std::string& msg);
// A fatal misuse: the handler, "Fatal Error: ..." on stderr, then abort() --
// unless vc_setErrorPolicy(STP_ON_ERROR_RETURN), in which case this returns
// and the caller returns its failure value.
void fatal(const std::string& msg);

// The pending 3.x error of a checker's manager (or the thread-local record),
// as "function: message", cleared on the way out together with the solver's
// failed state. `code` receives the error code (0 when none was pending).
std::string take_error(VCImpl* vc, stp_error_code* code = nullptr);

// ------------------------------------------------------------------ handles

VCImpl* vcimpl(VC vc, const char* who);           // NULL after a fatal report
Handle* handle(Expr e);                            // the cast; NULL stays NULL
// The term behind an Expr: fatal (and NULL) for a NULL or Type handle.
stp_term term_of(Expr e, const char* who);
// The sort behind a Type handle: fatal (and NULL) unless it is a Type.
stp_sort type_of(Type t, const char* who);
// The sort of an Expr or Type handle (NULL for a NULL handle).
stp_sort sort_of(Expr e);

// Wrap a term the 3.x API just handed out (+1) as a caller-owned handle, or,
// with `checker_owned`, as one the checker releases at vc_Destroy (when
// EXPRDELETE is on; off, every handle is caller-owned). NULL stays NULL.
Expr wrap(VCImpl* vc, stp_term t, bool checker_owned);
Type wrap_type(VCImpl* vc, stp_sort s);
void free_handle(Handle* h);

// The 'u' registry of live handles (only consulted by the UF entry points).
void registry_add(Handle* h);
void registry_erase(Handle* h);
bool registry_holds(VCImpl* vc, Expr e); // e is a live handle of vc
void enable_tracking(VCImpl* vc);

// ------------------------------------------------------------------ sorts

stp_sort_kind sort_kind(stp_sort s); // (stp_sort_kind)-1 for NULL
bool is_bool(stp_sort s);
bool is_bv(stp_sort s);
bool is_fp(stp_sort s);
bool is_rm(stp_sort s);
bool is_array(stp_sort s);
bool is_real(stp_sort s);
bool is_fun(stp_sort s);
std::uint32_t bv_width(stp_sort s);         // 0 unless a bit-vector sort
std::uint32_t packed_width(stp_sort s);     // BV: width, FP: eb+sb, RM: 5, array: element's
std::uint32_t index_width(stp_sort s);      // array: index's packed width, else 0
bool fp_format(stp_sort s, std::uint32_t& eb, std::uint32_t& sb); // FP, or array of FP
std::string sort_text(VCImpl* vc, stp_sort s); // SMT-LIB 2 sort text ("(D ..) C" for a function)
std::string type_text(stp_sort s);             // presentation-language type text

// ------------------------------------------------------------------ solver

stp_solver ensure_solver(VCImpl* vc); // NULL after a fatal report
// Set an option by name, on the record and on the live solver; a timing
// refusal rebuilds the solver from the record and the stack copy. Reports a
// nonfatal diagnostic and answers false when the value is refused.
bool set_option(VCImpl* vc, const char* name, const std::string& value,
                const char* what);
void discard_model(VCImpl* vc);
// A checker-owned RoundingMode / FP result etc.: `persist` says which.
Expr fp_result(VCImpl* vc, stp_term t);

// The value of a term as text in the presentation language, for the
// counterexample printers (a float or rounding mode as its packed carrier).
std::string cvc_value_text(VCImpl* vc, stp_term value);
std::string cvc_text(VCImpl* vc, stp_term t, const char* who, bool* ok);

// The read the UF entry points do (also reached from vc_getCounterExample).
Expr uf_value(VCImpl* vc, Expr application, const char* who);

// The one-hot VCRoundingMode encoding of a 3.x rounding mode, and back.
unsigned rm_onehot(stp_rm rm);
bool rm_from_onehot(unsigned bits, stp_rm& out);

// The value of a BV / FP / RM value term as an unsigned 64-bit integer,
// saturating at UINT64_MAX as 2.x's getBVUnsignedLongLong did. False (and a
// fatal report) unless the term is such a value.
bool value_uint64(stp_term t, std::uint64_t& out, const char* who);

// malloc'd copy for the *ToBuffer functions: text plus its terminating NUL,
// *len counting the NUL as 2.x did.
void to_buffer(const std::string& s, char** buf, std::size_t* len);

} // namespace compat2

#endif // STP_COMPAT2_H
