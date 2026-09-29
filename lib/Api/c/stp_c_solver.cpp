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

// stp_c_solver.cpp -- the solver, model, array/function value and statistics
// functions of <stp/stp.h>. A solver handle owns a C++ Solver and one reference
// on its CManager; the failed state lives beside it. A model handle is a heap
// copy of the C++ Model (a shared snapshot).

#include "stp_c_internal.h"

#include <sstream>

namespace stp
{
namespace api
{
namespace capi
{

CSolver::CSolver(CManager* m, const Options& o) : cm(m), solver(TermManager(m->impl), o) {}

} // namespace capi
} // namespace api
} // namespace stp

using namespace stp::api;
using namespace stp::api::capi;
using stp::api::detail::fail;
using stp::ASTInternal;

namespace
{
bool need(const void* p, const char* fn, int arg = 0) noexcept
{
  if (p != nullptr)
    return true;
  report_code(nullptr, nullptr, fn, ErrorCode::NULL_HANDLE, "the handle is null", arg);
  return false;
}

inline CArrayValue* carray(stp_array_value v) noexcept
{
  return reinterpret_cast<CArrayValue*>(v);
}
inline CFunValue* cfun(stp_fun_value v) noexcept
{
  return reinterpret_cast<CFunValue*>(v);
}
inline CStatistics* cstats(stp_statistics s) noexcept
{
  return reinterpret_cast<CStatistics*>(s);
}

// A read on a solver: the manager's record, no failed state involved.
template <class R, class F>
R solver_read(stp_solver s, const char* fn, R fail_value, F&& f) noexcept
{
  if (!need(s, fn))
    return fail_value;
  CSolver* cs = csolver(s);
  return guarded<R>(cs->cm, nullptr, fn, fail_value, [&] { return f(cs); });
}

template <class F>
stp_status solver_write(stp_solver s, const char* fn, F&& f) noexcept
{
  if (!need(s, fn))
    return STP_ERROR;
  CSolver* cs = csolver(s);
  return solver_mutate<stp_status>(cs, fn, STP_ERROR, [&] {
    f(cs);
    return STP_OK;
  });
}

template <class R, class F>
R solver_check(stp_solver s, const char* fn, R fail_value, F&& f) noexcept
{
  if (!need(s, fn))
    return fail_value;
  CSolver* cs = csolver(s);
  return solver_checked<R>(cs, fn, fail_value, [&] { return f(cs); });
}

template <class R, class F>
R model_call(stp_model m, const char* fn, R fail_value, F&& f) noexcept
{
  if (!need(m, fn))
    return fail_value;
  CModel* cmo = cmodel(m);
  return guarded<R>(cmo->cm, nullptr, fn, fail_value, [&] { return f(cmo); });
}

template <class F>
stp_status model_status(stp_model m, const char* fn, F&& f) noexcept
{
  return model_call<stp_status>(m, fn, STP_ERROR, [&](CModel* cmo) {
    f(cmo);
    return STP_OK;
  });
}

template <class F>
char* model_string(stp_model m, const char* fn, F&& f) noexcept
{
  return model_call<char*>(m, fn, nullptr, [&](CModel* cmo) { return dup_string(f(cmo)); });
}

// The value the model gives a term, as a C++ Term.
Term model_value(CModel* cmo, stp_term t, const char* fn)
{
  return cmo->model.value(term_arg(cmo->cm, t, fn, 1));
}

void copy_limbs(const std::vector<std::uint64_t>& limbs, std::size_t n, std::uint64_t* out,
                const char* fn, int arg)
{
  out_arg(out, fn, arg + 1);
  if (n < limbs.size())
    fail(ErrorCode::INVALID_ARGUMENT, fn,
         "the buffer holds " + std::to_string(n) + " limbs, " + std::to_string(limbs.size()) +
             " are needed",
         arg);
  for (std::size_t i = 0; i < limbs.size(); ++i)
    out[i] = limbs[i];
}

stp_model new_model(CManager* cm, const Model& m)
{
  CModel* out = new CModel{cm, m, std::nullopt};
  cm_retain(cm);
  return reinterpret_cast<stp_model>(out);
}

// Undoes the most recent export_term on a manager (for all-or-nothing batches).
void unexport_last(CManager* cm, stp_term t) noexcept
{
  if (!cm->scopes.empty())
  {
    cm->scopes.back().pop_back();
    return;
  }
  ASTInternal* p = raw(t);
  auto it = cm->unscoped.find(p);
  if (it != cm->unscoped.end() && --it->second == 0)
    cm->unscoped.erase(it);
  stp::api::detail::NodeAccess::release(p);
  --cm->refs; // the caller still holds the model, so this cannot reach zero
}

template <class R, class F>
R array_call(stp_array_value v, const char* fn, R fail_value, F&& f) noexcept
{
  if (!need(v, fn))
    return fail_value;
  CArrayValue* av = carray(v);
  return guarded<R>(av->cm, nullptr, fn, fail_value, [&] { return f(av); });
}

template <class R, class F>
R fun_call(stp_fun_value v, const char* fn, R fail_value, F&& f) noexcept
{
  if (!need(v, fn))
    return fail_value;
  CFunValue* fv = cfun(v);
  return guarded<R>(fv->cm, nullptr, fn, fail_value, [&] { return f(fv); });
}

template <class R, class F>
R stats_call(stp_statistics s, const char* fn, R fail_value, F&& f) noexcept
{
  if (!need(s, fn))
    return fail_value;
  return guarded<R>(nullptr, nullptr, fn, fail_value, [&] { return f(cstats(s)); });
}
} // namespace

extern "C" {

// ============================================================ solver

stp_solver stp_solver_new(stp_tm tm, stp_options options)
{
  if (!need(tm, "stp_solver_new"))
    return nullptr;
  CManager* cm = cm_of(tm);
  return guarded<stp_solver>(cm, nullptr, "stp_solver_new", nullptr, [&] {
    const Options o = options == nullptr ? Options() : coptions(options)->options;
    CSolver* cs = new CSolver(cm, o);
    cm_retain(cm);
    return reinterpret_cast<stp_solver>(cs);
  });
}

void stp_solver_delete(stp_solver s)
{
  if (s == nullptr)
    return;
  CSolver* cs = csolver(s);
  CManager* cm = cs->cm;
  delete cs;
  cm_release(cm);
}

const stp_error* stp_solver_failed(stp_solver s)
{
  if (s == nullptr)
    return nullptr;
  CSolver* cs = csolver(s);
  return cs->failed.pending ? &cs->failed.view : nullptr;
}

size_t stp_solver_failed_num_terms(stp_solver s)
{
  if (s == nullptr)
    return 0;
  CSolver* cs = csolver(s);
  return cs->failed.pending ? cs->failed.terms.size() : 0;
}

stp_term stp_solver_failed_term(stp_solver s, size_t i)
{
  return solver_read<stp_term>(s, "stp_solver_failed_term", nullptr, [&](CSolver* cs) {
    const std::size_t n = cs->failed.pending ? cs->failed.terms.size() : 0;
    if (i >= n)
      fail(ErrorCode::INDEX_OUT_OF_RANGE, "stp_solver_failed_term",
           "index " + std::to_string(i) + " out of range [0, " + std::to_string(n) + ")", 1);
    return export_term(cs->cm, cs->failed.terms[i]);
  });
}

size_t stp_solver_failed_num_sorts(stp_solver s)
{
  if (s == nullptr)
    return 0;
  CSolver* cs = csolver(s);
  return cs->failed.pending ? cs->failed.sorts.size() : 0;
}

stp_sort stp_solver_failed_sort(stp_solver s, size_t i)
{
  return solver_read<stp_sort>(s, "stp_solver_failed_sort", nullptr, [&](CSolver* cs) {
    const std::size_t n = cs->failed.pending ? cs->failed.sorts.size() : 0;
    if (i >= n)
      fail(ErrorCode::INDEX_OUT_OF_RANGE, "stp_solver_failed_sort",
           "index " + std::to_string(i) + " out of range [0, " + std::to_string(n) + ")", 1);
    return export_sort(cs->cm, cs->failed.sorts[i]);
  });
}

void stp_solver_clear_error(stp_solver s)
{
  if (s != nullptr)
    csolver(s)->failed.clear();
}

stp_tm stp_solver_manager(stp_solver s)
{
  if (!need(s, "stp_solver_manager"))
    return nullptr;
  return export_tm(csolver(s)->cm);
}

// ---------------------------------------------------------- assertions and checks

stp_status stp_solver_assert(stp_solver s, stp_term t)
{
  return solver_write(s, "stp_solver_assert", [&](CSolver* cs) {
    // unlike a constructor, an assert of NULL is an error: it would otherwise
    // drop an assertion silently
    if (t == nullptr)
      fail(ErrorCode::NULL_HANDLE, "stp_solver_assert", "the term is null", 1);
    cs->solver.assert_formula(term_arg(cs->cm, t, "stp_solver_assert", 1));
  });
}

stp_status stp_solver_push(stp_solver s, uint32_t n)
{
  return solver_write(s, "stp_solver_push", [&](CSolver* cs) { cs->solver.push(n); });
}

stp_status stp_solver_pop(stp_solver s, uint32_t n)
{
  return solver_write(s, "stp_solver_pop", [&](CSolver* cs) { cs->solver.pop(n); });
}

uint32_t stp_solver_level(stp_solver s)
{
  return s == nullptr ? 0 : csolver(s)->solver.level();
}

namespace
{
const std::vector<Term>& assertions_view(CSolver* cs)
{
  if (!cs->assertions)
    cs->assertions = cs->solver.assertions();
  return *cs->assertions;
}

const std::vector<Term>& unsat_assumptions_view(CSolver* cs)
{
  if (!cs->unsat_assumptions)
    cs->unsat_assumptions = cs->solver.unsat_assumptions();
  return *cs->unsat_assumptions;
}
} // namespace

size_t stp_solver_num_assertions(stp_solver s)
{
  return solver_read<size_t>(s, "stp_solver_num_assertions", 0,
                             [](CSolver* cs) { return assertions_view(cs).size(); });
}

stp_term stp_solver_assertion(stp_solver s, size_t i)
{
  return solver_read<stp_term>(s, "stp_solver_assertion", nullptr, [&](CSolver* cs) {
    const std::vector<Term>& all = assertions_view(cs);
    if (i >= all.size())
      fail(ErrorCode::INDEX_OUT_OF_RANGE, "stp_solver_assertion",
           "index " + std::to_string(i) + " out of range [0, " + std::to_string(all.size()) + ")",
           1);
    return export_term(cs->cm, all[i]);
  });
}

stp_status stp_solver_reset_assertions(stp_solver s)
{
  return solver_write(s, "stp_solver_reset_assertions",
                      [](CSolver* cs) { cs->solver.reset_assertions(); });
}

stp_status stp_solver_reset(stp_solver s)
{
  return solver_write(s, "stp_solver_reset", [](CSolver* cs) { cs->solver.reset(); });
}

stp_status stp_solver_check_sat(stp_solver s, stp_result* out)
{
  return solver_check<stp_status>(s, "stp_solver_check_sat", STP_ERROR, [&](CSolver* cs) {
    out_arg(out, "stp_solver_check_sat", 1);
    const Result r = cs->solver.check_sat();
    cs->last_reason = r.reason_message();
    *out = to_c(r);
    return STP_OK;
  });
}

// A check's assumptions. A NULL among them is an error of the check, as the
// formula of stp_solver_assert and stp_solver_entails is, not the unrecorded
// failure a NULL argument of a constructor propagates: a NULL here is most
// often a failed lookup (stp_tm_symbol answers NULL for an unknown name).
namespace
{
std::vector<Term> assumption_args(CSolver* cs, size_t n, const stp_term* assumptions,
                                  const char* fn)
{
  for (size_t i = 0; assumptions != nullptr && i < n; ++i)
    if (assumptions[i] == nullptr)
      fail(ErrorCode::NULL_HANDLE, fn, "assumption " + std::to_string(i) + " is null", 2);
  return term_args(cs->cm, n, assumptions, fn, 2);
}
} // namespace

stp_status stp_solver_check_sat_assuming(stp_solver s, size_t n, const stp_term* assumptions,
                                         stp_result* out)
{
  return solver_check<stp_status>(s, "stp_solver_check_sat_assuming", STP_ERROR, [&](CSolver* cs) {
    out_arg(out, "stp_solver_check_sat_assuming", 3);
    const Result r =
        cs->solver.check_sat(assumption_args(cs, n, assumptions, "stp_solver_check_sat_assuming"));
    cs->last_reason = r.reason_message();
    *out = to_c(r);
    return STP_OK;
  });
}

stp_status stp_solver_check_sat_budget(stp_solver s, size_t n, const stp_term* assumptions,
                                       const stp_budget* budget, stp_result* out)
{
  return solver_check<stp_status>(s, "stp_solver_check_sat_budget", STP_ERROR, [&](CSolver* cs) {
    out_arg(out, "stp_solver_check_sat_budget", 4);
    const Result r = cs->solver.check_sat(
        assumption_args(cs, n, assumptions, "stp_solver_check_sat_budget"), budget_arg(budget));
    cs->last_reason = r.reason_message();
    *out = to_c(r);
    return STP_OK;
  });
}

stp_status stp_solver_entails(stp_solver s, stp_term formula, const stp_budget* budget,
                              stp_entailment* out)
{
  return solver_check<stp_status>(s, "stp_solver_entails", STP_ERROR, [&](CSolver* cs) {
    out_arg(out, "stp_solver_entails", 3);
    if (formula == nullptr)
      fail(ErrorCode::NULL_HANDLE, "stp_solver_entails", "the formula is null", 1);
    const Entailment e = cs->solver.entails(term_arg(cs->cm, formula, "stp_solver_entails", 1),
                                            budget_arg(budget));
    cs->last_reason = e.reason_message();
    *out = to_c(e);
    return STP_OK;
  });
}

char* stp_solver_last_reason_message(stp_solver s)
{
  return solver_read<char*>(s, "stp_solver_last_reason_message", nullptr,
                            [](CSolver* cs) { return dup_string(cs->last_reason); });
}

size_t stp_solver_num_unsat_assumptions(stp_solver s)
{
  return solver_read<size_t>(s, "stp_solver_num_unsat_assumptions", 0,
                             [](CSolver* cs) { return unsat_assumptions_view(cs).size(); });
}

stp_term stp_solver_unsat_assumption(stp_solver s, size_t i)
{
  return solver_read<stp_term>(s, "stp_solver_unsat_assumption", nullptr, [&](CSolver* cs) {
    const std::vector<Term>& all = unsat_assumptions_view(cs);
    if (i >= all.size())
      fail(ErrorCode::INDEX_OUT_OF_RANGE, "stp_solver_unsat_assumption",
           "index " + std::to_string(i) + " out of range [0, " + std::to_string(all.size()) + ")",
           1);
    return export_term(cs->cm, all[i]);
  });
}

// ---------------------------------------------------------- models

stp_model stp_solver_model(stp_solver s)
{
  return solver_check<stp_model>(s, "stp_solver_model", nullptr,
                                 [](CSolver* cs) { return new_model(cs->cm, cs->solver.model()); });
}

stp_model stp_solver_candidate_model(stp_solver s)
{
  return solver_check<stp_model>(s, "stp_solver_candidate_model", nullptr, [](CSolver* cs) {
    const std::optional<Model> m = cs->solver.candidate_model();
    return m.has_value() ? new_model(cs->cm, *m) : nullptr;
  });
}

stp_term stp_solver_value(stp_solver s, stp_term t)
{
  return solver_check<stp_term>(s, "stp_solver_value", nullptr, [&](CSolver* cs) {
    return export_term(cs->cm, cs->solver.value(term_arg(cs->cm, t, "stp_solver_value", 1)));
  });
}

// ---------------------------------------------------------- interrupts

void stp_solver_interrupt(stp_solver s)
{
  // no guard, no lock, no allocation: this is the signal-safe entry point
  if (s != nullptr)
    csolver(s)->solver.interrupt();
}

void stp_solver_clear_interrupt(stp_solver s)
{
  if (s != nullptr)
    csolver(s)->solver.clear_interrupt();
}

bool stp_solver_interrupt_pending(stp_solver s)
{
  return s != nullptr && csolver(s)->solver.interrupt_pending();
}

stp_status stp_solver_set_terminator(stp_solver s, stp_terminate_callback cb, void* user)
{
  return solver_read<stp_status>(s, "stp_solver_set_terminator", STP_ERROR, [&](CSolver* cs) {
    cs->terminator.cb = cb;
    cs->terminator.user = user;
    cs->solver.set_terminator(cb == nullptr ? nullptr : &cs->terminator);
    return STP_OK;
  });
}

stp_statistics stp_solver_statistics(stp_solver s)
{
  return solver_read<stp_statistics>(s, "stp_solver_statistics", nullptr, [](CSolver* cs) {
    std::unique_ptr<CStatistics> st(new CStatistics{cs->solver.statistics(), {}});
    for (const auto& e : st->stats.entries())
      st->names.push_back(e.first);
    return reinterpret_cast<stp_statistics>(st.release());
  });
}

// ---------------------------------------------------------- symbols and scripts

stp_term stp_solver_symbol(stp_solver s, const char* name)
{
  return solver_read<stp_term>(s, "stp_solver_symbol", nullptr, [&](CSolver* cs) {
    const std::optional<Term> t = cs->solver.symbol(str_arg(name, "stp_solver_symbol", 1));
    return t.has_value() ? export_term(cs->cm, *t) : nullptr;
  });
}

stp_status stp_solver_parse_smt2(stp_solver s, const char* script, stp_parse_mode mode)
{
  return solver_write(s, "stp_solver_parse_smt2", [&](CSolver* cs) {
    if (static_cast<unsigned>(mode) > static_cast<unsigned>(STP_PARSE_ONLY))
      fail(ErrorCode::INVALID_ARGUMENT, "stp_solver_parse_smt2", "not a parse mode", 2);
    cs->solver.parse_smt2(str_arg(script, "stp_solver_parse_smt2", 1), static_cast<ParseMode>(mode));
  });
}

stp_status stp_solver_parse(stp_solver s, const char* text, stp_format f)
{
  return solver_write(s, "stp_solver_parse", [&](CSolver* cs) {
    cs->solver.parse(str_arg(text, "stp_solver_parse", 1), format_arg(f, "stp_solver_parse", 2));
  });
}

stp_status stp_solver_parse_file(stp_solver s, const char* path, stp_format f)
{
  return solver_write(s, "stp_solver_parse_file", [&](CSolver* cs) {
    cs->solver.parse_file(str_arg(path, "stp_solver_parse_file", 1),
                          format_arg(f, "stp_solver_parse_file", 2));
  });
}

stp_term stp_solver_parse_term(stp_solver s, const char* text)
{
  return solver_read<stp_term>(s, "stp_solver_parse_term", nullptr, [&](CSolver* cs) {
    return export_term(cs->cm, cs->solver.parse_term(str_arg(text, "stp_solver_parse_term", 1)));
  });
}

char* stp_solver_to_smt2(stp_solver s, bool with_check_sat)
{
  return solver_read<char*>(s, "stp_solver_to_smt2", nullptr,
                            [&](CSolver* cs) { return dup_string(cs->solver.to_smt2(with_check_sat)); });
}

char* stp_solver_to_string(stp_solver s, stp_format f)
{
  return solver_read<char*>(s, "stp_solver_to_string", nullptr, [&](CSolver* cs) {
    return dup_string(cs->solver.to_string(format_arg(f, "stp_solver_to_string", 1)));
  });
}

stp_status stp_solver_write_cnf(stp_solver s, stp_text_sink sink, void* user, stp_cnf_scope* scope)
{
  return solver_check<stp_status>(s, "stp_solver_write_cnf", STP_ERROR, [&](CSolver* cs) {
    if (sink == nullptr)
      fail(ErrorCode::NULL_HANDLE, "stp_solver_write_cnf", "the sink is null", 1);
    std::ostringstream os;
    const CnfScope c = cs->solver.write_cnf(os);
    const std::string text = os.str();
    if (scope != nullptr)
      *scope = static_cast<stp_cnf_scope>(c);
    sink(text.c_str(), text.size(), user);
    return STP_OK;
  });
}

void stp_solver_set_diagnostic_sink(stp_solver s, stp_text_sink sink, void* user)
{
  solver_read<stp_status>(s, "stp_solver_set_diagnostic_sink", STP_ERROR, [&](CSolver* cs) {
    if (sink == nullptr)
      cs->solver.set_diagnostic_sink(nullptr);
    else
      cs->solver.set_diagnostic_sink([sink, user](std::string_view sv) {
        const std::string text(sv); // NUL-terminated for the C side
        sink(text.c_str(), text.size(), user);
      });
    return STP_OK;
  });
}

namespace
{
// A stp_text_source behind the std::istream Solver::parse reads: one call
// per refill. A failed source fails the stream, which fails the parse (IO).
class SourceBuf final : public std::streambuf
{
public:
  SourceBuf(stp_text_source source, void* user) : source_(source), user_(user) {}

protected:
  int_type underflow() override
  {
    if (gptr() < egptr())
      return traits_type::to_int_type(*gptr());
    if (done_)
      return traits_type::eof();
    std::size_t n = source_(buf_, sizeof buf_, user_);
    if (n == static_cast<std::size_t>(-1))
    {
      done_ = true;
      throw std::ios_base::failure("the text source failed");
    }
    if (n == 0)
    {
      done_ = true;
      return traits_type::eof();
    }
    if (n > sizeof buf_)
      n = sizeof buf_;
    setg(buf_, buf_, buf_ + n);
    return traits_type::to_int_type(*gptr());
  }

private:
  stp_text_source source_;
  void* user_;
  char buf_[4096];
  bool done_ = false;
};
} // namespace

stp_status stp_solver_parse_source(stp_solver s, stp_text_source source, void* user,
                                   stp_format f, stp_parse_mode mode)
{
  return solver_write(s, "stp_solver_parse_source", [&](CSolver* cs) {
    if (source == nullptr)
      fail(ErrorCode::NULL_HANDLE, "stp_solver_parse_source", "the source is null", 1);
    if (static_cast<unsigned>(mode) > static_cast<unsigned>(STP_PARSE_ONLY))
      fail(ErrorCode::INVALID_ARGUMENT, "stp_solver_parse_source", "not a parse mode", 4);
    SourceBuf buf(source, user);
    std::istream in(&buf);
    cs->solver.parse(in, format_arg(f, "stp_solver_parse_source", 3), static_cast<ParseMode>(mode));
  });
}

char* stp_solver_input_to_string(stp_solver s, stp_format f)
{
  return solver_read<char*>(s, "stp_solver_input_to_string", nullptr, [&](CSolver* cs) {
    return dup_string(cs->solver.input_to_string(format_arg(f, "stp_solver_input_to_string", 1)));
  });
}

void stp_solver_set_output_sink(stp_solver s, stp_text_sink sink, void* user)
{
  solver_read<stp_status>(s, "stp_solver_set_output_sink", STP_ERROR, [&](CSolver* cs) {
    if (sink == nullptr)
      cs->solver.set_output_sink(nullptr);
    else
      cs->solver.set_output_sink([sink, user](std::string_view sv) {
        const std::string text(sv); // NUL-terminated for the C side; empty: a flush
        sink(text.c_str(), text.size(), user);
      });
    return STP_OK;
  });
}

void stp_solver_set_fatal_error_handler(stp_solver s, stp_fatal_error_handler handler, void* user)
{
  solver_read<stp_status>(s, "stp_solver_set_fatal_error_handler", STP_ERROR, [&](CSolver* cs) {
    if (handler == nullptr)
      cs->solver.set_fatal_error_handler(nullptr);
    else
      cs->solver.set_fatal_error_handler([handler, user](std::string_view sv) {
        const std::string text(sv);
        handler(text.c_str(), user);
      });
    return STP_OK;
  });
}

void stp_solver_set_cnf_sink(stp_solver s, stp_cnf_sink sink, void* user)
{
  solver_read<stp_status>(s, "stp_solver_set_cnf_sink", STP_ERROR, [&](CSolver* cs) {
    if (sink == nullptr)
      cs->solver.set_cnf_sink(nullptr);
    else
      cs->solver.set_cnf_sink([sink, user](std::string_view dimacs, CnfScope scope) {
        const std::string text(dimacs);
        sink(text.c_str(), text.size(), static_cast<stp_cnf_scope>(scope), user);
      });
    return STP_OK;
  });
}

// ============================================================ model

stp_model stp_model_copy(stp_model m)
{
  return model_call<stp_model>(m, "stp_model_copy", nullptr,
                               [](CModel* cmo) { return new_model(cmo->cm, cmo->model); });
}

void stp_model_release(stp_model m)
{
  if (m == nullptr)
    return;
  CModel* cmo = cmodel(m);
  CManager* cm = cmo->cm;
  delete cmo;
  cm_release(cm);
}

stp_tm stp_model_manager(stp_model m)
{
  if (!need(m, "stp_model_manager"))
    return nullptr;
  return export_tm(cmodel(m)->cm);
}

stp_term stp_model_value(stp_model m, stp_term t)
{
  return model_call<stp_term>(m, "stp_model_value", nullptr, [&](CModel* cmo) {
    return export_term(cmo->cm, model_value(cmo, t, "stp_model_value"));
  });
}

stp_term stp_model_try_value(stp_model m, stp_term t)
{
  return model_call<stp_term>(m, "stp_model_try_value", nullptr, [&](CModel* cmo) {
    const std::optional<Term> v = cmo->model.try_value(term_arg(cmo->cm, t, "stp_model_try_value", 1));
    return v.has_value() ? export_term(cmo->cm, *v) : nullptr;
  });
}

stp_status stp_model_values(stp_model m, size_t n, const stp_term* in, stp_term* out)
{
  return model_status(m, "stp_model_values", [&](CModel* cmo) {
    if (n == 0)
      return;
    out_arg(out, "stp_model_values", 3);
    const std::vector<Term> vals = cmo->model.values(term_args(cmo->cm, n, in, "stp_model_values", 2));
    std::size_t done = 0;
    try
    {
      for (; done < n; ++done)
        out[done] = export_term(cmo->cm, vals[done]);
    }
    catch (...)
    {
      // all or nothing: take back what was exported
      while (done-- > 0)
        unexport_last(cmo->cm, out[done]);
      throw;
    }
  });
}

stp_status stp_model_bool(stp_model m, stp_term t, bool* out)
{
  return model_status(m, "stp_model_bool", [&](CModel* cmo) {
    *out_arg(out, "stp_model_bool", 2) = model_value(cmo, t, "stp_model_bool").to_bool();
  });
}

stp_status stp_model_uint64(stp_model m, stp_term t, uint64_t* out)
{
  return model_status(m, "stp_model_uint64", [&](CModel* cmo) {
    *out_arg(out, "stp_model_uint64", 2) = model_value(cmo, t, "stp_model_uint64").to_uint64();
  });
}

stp_status stp_model_int64(stp_model m, stp_term t, int64_t* out)
{
  return model_status(m, "stp_model_int64", [&](CModel* cmo) {
    *out_arg(out, "stp_model_int64", 2) = model_value(cmo, t, "stp_model_int64").to_int64();
  });
}

char* stp_model_bv_string(stp_model m, stp_term t, int base, bool pad)
{
  return model_string(m, "stp_model_bv_string", [&](CModel* cmo) {
    return model_value(cmo, t, "stp_model_bv_string").to_bv_string(base, pad);
  });
}

stp_status stp_model_bv_num_limbs(stp_model m, stp_term t, size_t* out)
{
  return model_status(m, "stp_model_bv_num_limbs", [&](CModel* cmo) {
    *out_arg(out, "stp_model_bv_num_limbs", 2) =
        model_value(cmo, t, "stp_model_bv_num_limbs").to_bv_limbs().size();
  });
}

stp_status stp_model_bv_limbs(stp_model m, stp_term t, size_t n, uint64_t* out)
{
  return model_status(m, "stp_model_bv_limbs", [&](CModel* cmo) {
    copy_limbs(model_value(cmo, t, "stp_model_bv_limbs").to_bv_limbs(), n, out, "stp_model_bv_limbs",
               2);
  });
}

stp_status stp_model_bv_bytes(stp_model m, stp_term t, size_t n, uint8_t* out, bool little_endian)
{
  return model_status(m, "stp_model_bv_bytes", [&](CModel* cmo) {
    out_arg(out, "stp_model_bv_bytes", 3);
    const std::vector<std::uint8_t> bytes =
        model_value(cmo, t, "stp_model_bv_bytes").to_bv_bytes(little_endian);
    if (n < bytes.size())
      fail(ErrorCode::INVALID_ARGUMENT, "stp_model_bv_bytes",
           "the buffer holds " + std::to_string(n) + " bytes, " + std::to_string(bytes.size()) +
               " are needed",
           2);
    for (std::size_t i = 0; i < bytes.size(); ++i)
      out[i] = bytes[i];
  });
}

stp_status stp_model_fp(stp_model m, stp_term t, stp_float_value* out)
{
  return model_status(m, "stp_model_fp", [&](CModel* cmo) {
    to_c(model_value(cmo, t, "stp_model_fp").to_fp(), out_arg(out, "stp_model_fp", 2));
  });
}

stp_status stp_model_fp_significand_limbs(stp_model m, stp_term t, size_t n, uint64_t* out)
{
  return model_status(m, "stp_model_fp_significand_limbs", [&](CModel* cmo) {
    copy_limbs(model_value(cmo, t, "stp_model_fp_significand_limbs").to_fp().significand, n, out,
               "stp_model_fp_significand_limbs", 2);
  });
}

stp_status stp_model_fp_to_double(stp_model m, stp_term t, double* out)
{
  return model_status(m, "stp_model_fp_to_double", [&](CModel* cmo) {
    out_arg(out, "stp_model_fp_to_double", 2);
    const std::optional<double> d = model_value(cmo, t, "stp_model_fp_to_double").to_fp().to_double();
    if (!d.has_value())
      fail(ErrorCode::DOES_NOT_FIT, "stp_model_fp_to_double", "the format is wider than binary64", 1);
    *out = *d;
  });
}

stp_status stp_model_rm(stp_model m, stp_term t, stp_rm* out)
{
  return model_status(m, "stp_model_rm", [&](CModel* cmo) {
    *out_arg(out, "stp_model_rm", 2) = static_cast<stp_rm>(model_value(cmo, t, "stp_model_rm").to_rm());
  });
}

char* stp_model_real_numerator(stp_model m, stp_term t)
{
  return model_string(m, "stp_model_real_numerator", [&](CModel* cmo) {
    return model_value(cmo, t, "stp_model_real_numerator").to_rational().numerator;
  });
}

char* stp_model_real_denominator(stp_model m, stp_term t)
{
  return model_string(m, "stp_model_real_denominator", [&](CModel* cmo) {
    return model_value(cmo, t, "stp_model_real_denominator").to_rational().denominator;
  });
}

stp_status stp_model_uninterpreted_index(stp_model m, stp_term t, uint64_t* out)
{
  return model_status(m, "stp_model_uninterpreted_index", [&](CModel* cmo) {
    *out_arg(out, "stp_model_uninterpreted_index", 2) =
        model_value(cmo, t, "stp_model_uninterpreted_index").to_uninterpreted_index();
  });
}

stp_array_value stp_model_array_value(stp_model m, stp_term array)
{
  return model_call<stp_array_value>(m, "stp_model_array_value", nullptr, [&](CModel* cmo) {
    CArrayValue* av = new CArrayValue{
        cmo->cm, cmo->model.array_value(term_arg(cmo->cm, array, "stp_model_array_value", 1))};
    cm_retain(cmo->cm);
    return reinterpret_cast<stp_array_value>(av);
  });
}

stp_fun_value stp_model_fun_value(stp_model m, stp_term fun)
{
  return model_call<stp_fun_value>(m, "stp_model_fun_value", nullptr, [&](CModel* cmo) {
    CFunValue* fv = new CFunValue{
        cmo->cm, cmo->model.function_value(term_arg(cmo->cm, fun, "stp_model_fun_value", 1))};
    cm_retain(cmo->cm);
    return reinterpret_cast<stp_fun_value>(fv);
  });
}

stp_status stp_model_array_bytes(stp_model m, stp_term array, uint64_t first_index, size_t count,
                                 uint8_t* out)
{
  return model_status(m, "stp_model_array_bytes", [&](CModel* cmo) {
    if (count > 0)
      out_arg(out, "stp_model_array_bytes", 4);
    cmo->model.array_bytes(term_arg(cmo->cm, array, "stp_model_array_bytes", 1), first_index, count,
                           out);
  });
}

namespace
{
const std::vector<Term>& model_symbols_view(CModel* cmo)
{
  if (!cmo->symbols)
    cmo->symbols = cmo->model.symbols();
  return *cmo->symbols;
}
} // namespace

size_t stp_model_num_symbols(stp_model m)
{
  return model_call<size_t>(m, "stp_model_num_symbols", 0,
                            [](CModel* cmo) { return model_symbols_view(cmo).size(); });
}

stp_term stp_model_symbol(stp_model m, size_t i)
{
  return model_call<stp_term>(m, "stp_model_symbol", nullptr, [&](CModel* cmo) {
    const std::vector<Term>& all = model_symbols_view(cmo);
    if (i >= all.size())
      fail(ErrorCode::INDEX_OUT_OF_RANGE, "stp_model_symbol",
           "index " + std::to_string(i) + " out of range [0, " + std::to_string(all.size()) + ")",
           1);
    return export_term(cmo->cm, all[i]);
  });
}

bool stp_model_in_core(stp_model m, stp_term symbol)
{
  return model_call<bool>(m, "stp_model_in_core", false, [&](CModel* cmo) {
    return cmo->model.in_core(term_arg(cmo->cm, symbol, "stp_model_in_core", 1));
  });
}

char* stp_model_to_smt2(stp_model m)
{
  return model_string(m, "stp_model_to_smt2", [](CModel* cmo) { return cmo->model.to_smt2(); });
}

// ============================================================ array values

void stp_array_value_release(stp_array_value v)
{
  if (v == nullptr)
    return;
  CArrayValue* av = carray(v);
  CManager* cm = av->cm;
  delete av;
  cm_release(cm);
}

stp_sort stp_array_value_sort(stp_array_value v)
{
  return array_call<stp_sort>(v, "stp_array_value_sort", nullptr,
                              [](CArrayValue* av) { return export_sort(av->cm, av->value.sort()); });
}

stp_term stp_array_value_default(stp_array_value v)
{
  return array_call<stp_term>(v, "stp_array_value_default", nullptr, [](CArrayValue* av) {
    return export_term(av->cm, av->value.default_value());
  });
}

size_t stp_array_value_size(stp_array_value v)
{
  return array_call<size_t>(v, "stp_array_value_size", 0,
                            [](CArrayValue* av) { return av->value.size(); });
}

stp_status stp_array_value_entry(stp_array_value v, size_t i, stp_term* index, stp_term* element)
{
  return array_call<stp_status>(v, "stp_array_value_entry", STP_ERROR, [&](CArrayValue* av) {
    out_arg(index, "stp_array_value_entry", 2);
    out_arg(element, "stp_array_value_entry", 3);
    const ArrayValue::Entry e = av->value.entry(i);
    stp_term idx = export_term(av->cm, e.index);
    try
    {
      *element = export_term(av->cm, e.element);
    }
    catch (...)
    {
      unexport_last(av->cm, idx);
      throw;
    }
    *index = idx;
    return STP_OK;
  });
}

stp_term stp_array_value_at(stp_array_value v, stp_term index_value)
{
  return array_call<stp_term>(v, "stp_array_value_at", nullptr, [&](CArrayValue* av) {
    return export_term(av->cm, av->value.at(term_arg(av->cm, index_value, "stp_array_value_at", 1)));
  });
}

stp_term stp_array_value_as_term(stp_array_value v)
{
  return array_call<stp_term>(v, "stp_array_value_as_term", nullptr,
                              [](CArrayValue* av) { return export_term(av->cm, av->value.as_term()); });
}

// ============================================================ function values

void stp_fun_value_release(stp_fun_value v)
{
  if (v == nullptr)
    return;
  CFunValue* fv = cfun(v);
  CManager* cm = fv->cm;
  delete fv;
  cm_release(cm);
}

stp_sort stp_fun_value_sort(stp_fun_value v)
{
  return fun_call<stp_sort>(v, "stp_fun_value_sort", nullptr,
                            [](CFunValue* fv) { return export_sort(fv->cm, fv->value.sort()); });
}

uint32_t stp_fun_value_arity(stp_fun_value v)
{
  return fun_call<uint32_t>(v, "stp_fun_value_arity", 0,
                            [](CFunValue* fv) { return fv->value.sort().fun_arity(); });
}

stp_term stp_fun_value_else(stp_fun_value v)
{
  return fun_call<stp_term>(v, "stp_fun_value_else", nullptr,
                            [](CFunValue* fv) { return export_term(fv->cm, fv->value.else_value()); });
}

size_t stp_fun_value_size(stp_fun_value v)
{
  return fun_call<size_t>(v, "stp_fun_value_size", 0, [](CFunValue* fv) { return fv->value.size(); });
}

stp_status stp_fun_value_entry(stp_fun_value v, size_t i, size_t n, stp_term* args_out,
                               stp_term* value)
{
  return fun_call<stp_status>(v, "stp_fun_value_entry", STP_ERROR, [&](CFunValue* fv) {
    out_arg(args_out, "stp_fun_value_entry", 3);
    out_arg(value, "stp_fun_value_entry", 4);
    const std::uint32_t arity = fv->value.sort().fun_arity();
    if (n < arity)
      fail(ErrorCode::INVALID_ARGUMENT, "stp_fun_value_entry",
           "the buffer holds " + std::to_string(n) + " arguments, the function takes " +
               std::to_string(arity),
           2);
    const FunctionValue::Entry e = fv->value.entry(i);
    std::size_t done = 0;
    try
    {
      for (; done < e.args.size(); ++done)
        args_out[done] = export_term(fv->cm, e.args[done]);
      *value = export_term(fv->cm, e.value);
    }
    catch (...)
    {
      while (done-- > 0)
        unexport_last(fv->cm, args_out[done]);
      throw;
    }
    return STP_OK;
  });
}

stp_term stp_fun_value_apply(stp_fun_value v, size_t n, const stp_term* arg_values)
{
  return fun_call<stp_term>(v, "stp_fun_value_apply", nullptr, [&](CFunValue* fv) {
    return export_term(fv->cm,
                       fv->value.apply(term_args(fv->cm, n, arg_values, "stp_fun_value_apply", 2)));
  });
}

stp_term stp_fun_value_as_ite(stp_fun_value v, size_t n, const stp_term* formals)
{
  return fun_call<stp_term>(v, "stp_fun_value_as_ite", nullptr, [&](CFunValue* fv) {
    return export_term(fv->cm,
                       fv->value.as_ite_term(term_args(fv->cm, n, formals, "stp_fun_value_as_ite", 2)));
  });
}

// ============================================================ statistics

void stp_statistics_release(stp_statistics s)
{
  delete cstats(s);
}

size_t stp_statistics_size(stp_statistics s)
{
  return s == nullptr ? 0 : cstats(s)->names.size();
}

const char* stp_statistics_name(stp_statistics s, size_t i)
{
  if (s == nullptr || i >= cstats(s)->names.size())
    return nullptr;
  return cstats(s)->names[i].c_str();
}

bool stp_statistics_is_uint64(stp_statistics s, const char* name)
{
  return stats_call<bool>(s, "stp_statistics_is_uint64", false, [&](CStatistics* st) {
    const auto& entries = st->stats.entries();
    auto it = entries.find(str_arg(name, "stp_statistics_is_uint64", 1));
    return it != entries.end() && it->second.index() == 0;
  });
}

bool stp_statistics_is_double(stp_statistics s, const char* name)
{
  return stats_call<bool>(s, "stp_statistics_is_double", false, [&](CStatistics* st) {
    const auto& entries = st->stats.entries();
    auto it = entries.find(str_arg(name, "stp_statistics_is_double", 1));
    return it != entries.end() && it->second.index() == 1;
  });
}

stp_status stp_statistics_uint64(stp_statistics s, const char* name, uint64_t* out)
{
  return stats_call<stp_status>(s, "stp_statistics_uint64", STP_ERROR, [&](CStatistics* st) {
    *out_arg(out, "stp_statistics_uint64", 2) = st->stats.uint64(str_arg(name, "stp_statistics_uint64", 1));
    return STP_OK;
  });
}

stp_status stp_statistics_double(stp_statistics s, const char* name, double* out)
{
  return stats_call<stp_status>(s, "stp_statistics_double", STP_ERROR, [&](CStatistics* st) {
    *out_arg(out, "stp_statistics_double", 2) = st->stats.real(str_arg(name, "stp_statistics_double", 1));
    return STP_OK;
  });
}

char* stp_statistics_str(stp_statistics s, const char* name)
{
  return stats_call<char*>(s, "stp_statistics_str", nullptr, [&](CStatistics* st) {
    return dup_string(st->stats.str(str_arg(name, "stp_statistics_str", 1)));
  });
}

stp_tier stp_statistics_tier(const char* name)
{
  return guarded<stp_tier>(nullptr, nullptr, "stp_statistics_tier", STP_TIER_STABLE, [&] {
    return static_cast<stp_tier>(Statistics().tier(str_arg(name, "stp_statistics_tier", 0)));
  });
}

} // extern "C"
