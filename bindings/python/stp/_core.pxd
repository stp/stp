# AUTHORS: Andrew Teylu
#
# BEGIN DATE: September, 2026
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.

# _core.pxd -- the C API of <stp/stp.h> as Cython sees it. The three generated
# enumerations (stp_kind, stp_error_code, stp_option) come from _gen_enums.pxi,
# written by lib/Api/gen/generate.py into <build>/generated/python/.

from libc.stdint cimport uint8_t, uint32_t, uint64_t, int64_t

include "_gen_enums.pxi"

cdef extern from "<stdbool.h>":
    # C99 bool for the out-parameters and callbacks (Cython's bint is an int)
    ctypedef bint cbool "bool"

cdef extern from "stp/stp.h":
    # ------------------------------------------------------------ handles
    ctypedef struct stp_tm_s
    ctypedef stp_tm_s* stp_tm
    ctypedef struct stp_solver_s
    ctypedef stp_solver_s* stp_solver
    ctypedef struct stp_options_s
    ctypedef stp_options_s* stp_options
    ctypedef struct stp_model_s
    ctypedef stp_model_s* stp_model
    ctypedef struct stp_term_s
    ctypedef stp_term_s* stp_term
    ctypedef struct stp_sort_s
    ctypedef stp_sort_s* stp_sort
    ctypedef struct stp_array_value_s
    ctypedef stp_array_value_s* stp_array_value
    ctypedef struct stp_fun_value_s
    ctypedef stp_fun_value_s* stp_fun_value
    ctypedef struct stp_statistics_s
    ctypedef stp_statistics_s* stp_statistics

    # ------------------------------------------------------------ enums
    ctypedef enum stp_status:
        STP_OK
        STP_ERROR
    ctypedef enum stp_sort_kind:
        STP_SORT_BOOL
        STP_SORT_BV
        STP_SORT_FP
        STP_SORT_RM
        STP_SORT_REAL
        STP_SORT_ARRAY
        STP_SORT_FUN
        STP_SORT_UNINTERPRETED
    ctypedef enum stp_rm:
        STP_RM_RNE
        STP_RM_RNA
        STP_RM_RTP
        STP_RM_RTN
        STP_RM_RTZ
    ctypedef enum stp_result_kind:
        STP_SAT
        STP_UNSAT
        STP_UNKNOWN
    ctypedef enum stp_validity:
        STP_VALID
        STP_INVALID
        STP_UNKNOWN_VALIDITY
    ctypedef enum stp_unknown_reason:
        STP_REASON_NONE
        STP_REASON_TIMEOUT
        STP_REASON_CONFLICT_LIMIT
        STP_REASON_INTERRUPTED
        STP_REASON_INCOMPLETE
        STP_REASON_RESOURCE_LIMIT
        STP_REASON_CARRIER_EXHAUSTED
        STP_REASON_ASSUMED_INJECTIVITY
        STP_REASON_STOPPED_AFTER_CNF
        STP_REASON_OTHER
    ctypedef enum stp_format:
        STP_FORMAT_AUTO
        STP_FORMAT_SMTLIB2
        STP_FORMAT_SMTLIB1
        STP_FORMAT_CVC
        STP_FORMAT_DOT
        STP_FORMAT_GDL
    ctypedef enum stp_parse_mode:
        STP_PARSE_DECLARE_AND_ASSERT
        STP_PARSE_EXECUTE
        STP_PARSE_ONLY
    ctypedef enum stp_cnf_scope:
        STP_CNF_WHOLE
        STP_CNF_PARTIAL
        STP_CNF_OVER_APPROXIMATION
    ctypedef enum stp_tier:
        STP_TIER_STABLE
        STP_TIER_EXPERT
        STP_TIER_EXPERIMENTAL
        STP_TIER_DIAGNOSTIC
    ctypedef enum stp_settable:
        STP_SETTABLE_ANYTIME
        STP_SETTABLE_BEFORE_FIRST_CHECK
        STP_SETTABLE_CONSTRUCTION
    ctypedef enum stp_option_scope:
        STP_SCOPE_SOLVER
        STP_SCOPE_MANAGER
    ctypedef enum stp_fp_class:
        STP_FP_NORMAL
        STP_FP_SUBNORMAL
        STP_FP_ZERO
        STP_FP_INFINITY
        STP_FP_NAN
    ctypedef enum stp_internal_error_policy:
        STP_POISON
        STP_ABORT

    # ------------------------------------------------------------ by-value structs
    ctypedef struct stp_result:
        stp_result_kind kind
        stp_unknown_reason reason
    ctypedef struct stp_entailment:
        stp_validity kind
        stp_unknown_reason reason
    ctypedef struct stp_budget:
        bint has_time
        uint64_t time_ms
        bint has_conflicts
        uint64_t conflicts
    ctypedef struct stp_error:
        stp_error_code code
        bint recoverable
        const char* message
        const char* function
        int argument_index
        const char* option
    ctypedef struct stp_float_value:
        uint32_t exp_size
        uint32_t sig_size
        bint sign
        uint64_t biased_exponent
        stp_fp_class cls
    ctypedef struct stp_version:
        int major
        int minor
        int patch
        const char* string
        const char* git_sha
        const char* git_tag
        const char* build_info

    # ------------------------------------------------------------ library
    stp_version stp_get_version()
    char* stp_capability(const char* key)
    char* stp_capabilities()
    bint stp_has_sat_backend(const char* name)
    size_t stp_num_sat_backends()
    const char* stp_sat_backend_name(size_t i)
    void stp_free(void* p)
    const stp_error* stp_last_error()
    void stp_set_internal_error_policy(stp_internal_error_policy)
    stp_internal_error_policy stp_get_internal_error_policy()
    const char* stp_kind_name(stp_kind)
    const char* stp_kind_smtlib(stp_kind)
    const char* stp_rm_name(stp_rm)
    const char* stp_unknown_reason_name(stp_unknown_reason)
    const char* stp_error_code_name(stp_error_code)
    const char* stp_result_kind_name(stp_result_kind)
    const char* stp_validity_name(stp_validity)

    # ------------------------------------------------------------ term manager
    stp_tm stp_tm_new(stp_options manager_options)
    stp_tm stp_tm_new_with(bint simplify, stp_rm default_rounding_mode, uint32_t uf_sort_width)
    stp_tm stp_tm_copy(stp_tm)
    void stp_tm_release(stp_tm)
    uint64_t stp_tm_id(stp_tm)
    bint stp_tm_simplify_enabled(stp_tm)
    stp_rm stp_tm_default_rounding_mode(stp_tm)
    stp_status stp_tm_set_default_rounding_mode(stp_tm, stp_rm)
    uint32_t stp_tm_uf_sort_width(stp_tm)
    void stp_tm_scope_push(stp_tm)
    void stp_tm_scope_pop(stp_tm)
    size_t stp_tm_scope_depth(stp_tm)
    void stp_tm_release_all(stp_tm)
    const stp_error* stp_tm_error(stp_tm)
    size_t stp_tm_error_num_terms(stp_tm)
    stp_term stp_tm_error_term(stp_tm, size_t i)
    void stp_tm_clear_error(stp_tm)
    ctypedef void (*stp_error_callback)(const stp_error*, void* user)
    void stp_tm_set_error_callback(stp_tm, stp_error_callback, void* user)

    # ------------------------------------------------------------ sorts
    stp_sort stp_mk_bool_sort(stp_tm)
    stp_sort stp_mk_bv_sort(stp_tm, uint32_t width)
    stp_sort stp_mk_fp_sort(stp_tm, uint32_t exp_size, uint32_t sig_size)
    stp_sort stp_mk_fp16_sort(stp_tm)
    stp_sort stp_mk_fp32_sort(stp_tm)
    stp_sort stp_mk_fp64_sort(stp_tm)
    stp_sort stp_mk_fp128_sort(stp_tm)
    stp_sort stp_mk_rm_sort(stp_tm)
    stp_sort stp_mk_real_sort(stp_tm)
    stp_sort stp_mk_array_sort(stp_tm, stp_sort index, stp_sort element)
    stp_sort stp_mk_fun_sort(stp_tm, size_t arity, const stp_sort* domain, stp_sort codomain)
    stp_sort stp_tm_declare_sort(stp_tm, const char* name)
    stp_sort stp_mk_fresh_sort(stp_tm, const char* prefix)
    stp_sort stp_sort_copy(stp_sort)
    void stp_sort_release(stp_sort)
    stp_status stp_sort_get_kind(stp_sort, stp_sort_kind* out)
    stp_status stp_sort_bv_size(stp_sort, uint32_t* out)
    stp_status stp_sort_fp_exp_size(stp_sort, uint32_t* out)
    stp_status stp_sort_fp_sig_size(stp_sort, uint32_t* out)
    stp_sort stp_sort_array_index(stp_sort)
    stp_sort stp_sort_array_element(stp_sort)
    stp_status stp_sort_fun_arity(stp_sort, uint32_t* out)
    stp_sort stp_sort_fun_domain(stp_sort, uint32_t i)
    stp_sort stp_sort_fun_codomain(stp_sort)
    char* stp_sort_name(stp_sort)
    uint64_t stp_sort_id(stp_sort)
    char* stp_sort_str(stp_sort)
    stp_tm stp_sort_manager(stp_sort)

    # ------------------------------------------------------------ symbols and values
    stp_term stp_declare(stp_tm, const char* name, stp_sort)
    stp_term stp_mk_fresh(stp_tm, stp_sort, const char* prefix)
    stp_term stp_tm_symbol(stp_tm, const char* name)
    stp_status stp_tm_bind_symbol(stp_tm, const char* name, stp_term)
    size_t stp_tm_num_symbols(stp_tm)
    stp_term stp_tm_symbol_at(stp_tm, size_t i)
    size_t stp_tm_num_declared_sorts(stp_tm)
    stp_sort stp_tm_declared_sort_at(stp_tm, size_t i)
    stp_term stp_tm_term_from_id(stp_tm, uint64_t id)
    stp_term stp_mk_true(stp_tm)
    stp_term stp_mk_false(stp_tm)
    stp_term stp_mk_bool(stp_tm, bint)
    stp_term stp_mk_bv_uint64(stp_tm, uint32_t width, uint64_t value)
    stp_term stp_mk_bv_int64(stp_tm, uint32_t width, int64_t value)
    stp_term stp_mk_bv_str(stp_tm, uint32_t width, const char* digits, int base)
    stp_term stp_mk_bv_limbs(stp_tm, uint32_t width, size_t n, const uint64_t* lsb_first)
    stp_term stp_mk_bv_bytes(stp_tm, uint32_t width, size_t n, const uint8_t* bytes, bint little_endian)
    stp_term stp_mk_bv_wrapped(stp_tm, uint32_t width, uint64_t value)
    stp_term stp_mk_bv_zero(stp_tm, uint32_t width)
    stp_term stp_mk_bv_ones(stp_tm, uint32_t width)
    stp_term stp_mk_bv_min_signed(stp_tm, uint32_t width)
    stp_term stp_mk_bv_max_signed(stp_tm, uint32_t width)
    stp_term stp_mk_fp_from_bits(stp_tm, stp_sort fp, stp_term bv_value)
    stp_term stp_mk_fp_from_bits_str(stp_tm, stp_sort fp, const char* bits)
    stp_term stp_mk_fp(stp_tm, stp_term sign, stp_term exponent, stp_term significand)
    stp_term stp_mk_fp_pos_zero(stp_tm, stp_sort fp)
    stp_term stp_mk_fp_neg_zero(stp_tm, stp_sort fp)
    stp_term stp_mk_fp_pos_inf(stp_tm, stp_sort fp)
    stp_term stp_mk_fp_neg_inf(stp_tm, stp_sort fp)
    stp_term stp_mk_fp_nan(stp_tm, stp_sort fp)
    stp_term stp_mk_fp_double(stp_tm, stp_sort fp, stp_rm rm, double value)
    stp_term stp_mk_fp_decimal(stp_tm, stp_sort fp, stp_rm rm, const char* literal)
    stp_term stp_mk_rm(stp_tm, stp_rm)
    stp_term stp_mk_real_int64(stp_tm, int64_t)
    stp_term stp_mk_real_fraction(stp_tm, int64_t numerator, int64_t denominator)
    stp_term stp_mk_real_str(stp_tm, const char* literal)
    stp_term stp_mk_const_array(stp_tm, stp_sort array_sort, stp_term element)
    stp_term stp_array_from_bytes(stp_tm, size_t n, const uint8_t* bytes, uint32_t index_width)

    # ------------------------------------------------------------ generic construction
    stp_term stp_mk_term(stp_tm, stp_kind, size_t n, const stp_term* args)
    stp_term stp_mk_term_indexed(stp_tm, stp_kind, size_t n, const stp_term* args, size_t m, const uint32_t* idx)
    stp_term stp_mk_term_sorted(stp_tm, stp_kind, size_t n, const stp_term* args, size_t m, const uint32_t* idx, stp_sort result)

    # ------------------------------------------------------------ terms
    stp_term stp_term_copy(stp_term)
    stp_status stp_term_release(stp_term)
    uint64_t stp_term_id(stp_term)
    uint64_t stp_term_hash(stp_term)
    stp_tm stp_term_manager(stp_term)
    stp_status stp_term_get_kind(stp_term, stp_kind* out)
    stp_sort stp_term_sort(stp_term)
    stp_status stp_term_num_children(stp_term, size_t* out)
    stp_term stp_term_child(stp_term, size_t i)
    stp_status stp_term_num_indices(stp_term, size_t* out)
    stp_status stp_term_index(stp_term, size_t i, uint32_t* out)
    bint stp_term_is_value(stp_term)
    bint stp_term_is_const(stp_term)
    char* stp_term_symbol(stp_term)
    char* stp_term_str(stp_term)
    char* stp_term_to_string(stp_term, stp_format, bint share_subterms)
    stp_term stp_term_substitute(stp_term, size_t n, const stp_term* from_, const stp_term* to)
    stp_term stp_tm_simplify(stp_tm, stp_term)
    bint stp_term_same(stp_term, stp_term)
    stp_status stp_term_to_bool(stp_term, cbool* out)
    bint stp_term_fits_uint64(stp_term)
    bint stp_term_fits_int64(stp_term)
    stp_status stp_term_to_uint64(stp_term, uint64_t* out)
    stp_status stp_term_to_int64(stp_term, int64_t* out)
    char* stp_term_to_bv_string(stp_term, int base, bint pad)
    stp_status stp_term_bv_num_limbs(stp_term, size_t* out)
    stp_status stp_term_to_bv_limbs(stp_term, size_t n, uint64_t* out_lsb_first)
    stp_status stp_term_to_bv_bytes(stp_term, size_t n, uint8_t* out, bint little_endian)
    stp_status stp_term_to_fp(stp_term, stp_float_value* out)
    stp_status stp_term_fp_significand_limbs(stp_term, size_t n, uint64_t* out_lsb_first)
    char* stp_term_fp_bits(stp_term)
    stp_status stp_term_fp_to_double(stp_term, double* out)
    stp_status stp_term_fp_to_rational(stp_term, char** numerator, char** denominator)
    stp_status stp_term_to_rm(stp_term, stp_rm* out)
    char* stp_term_real_numerator(stp_term)
    char* stp_term_real_denominator(stp_term)
    bint stp_term_real_fits_int64(stp_term)
    stp_status stp_term_real_to_int64(stp_term, int64_t* num, int64_t* den)
    stp_status stp_term_real_to_double(stp_term, double* out)
    stp_status stp_term_to_uninterpreted_index(stp_term, uint64_t* out)

    # ------------------------------------------------------------ options
    stp_options stp_options_new()
    stp_options stp_options_copy(stp_options)
    void stp_options_delete(stp_options)
    const stp_error* stp_options_error(stp_options)
    void stp_options_clear_error(stp_options)
    stp_status stp_options_set_str(stp_options, const char* name, const char* value)
    stp_status stp_options_set_bool(stp_options, const char* name, bint)
    stp_status stp_options_set_int64(stp_options, const char* name, int64_t)
    stp_status stp_options_set_uint64(stp_options, const char* name, uint64_t)
    stp_status stp_options_set_duration_ms(stp_options, const char* name, uint64_t ms)
    stp_status stp_options_set_names(stp_options, const char* name, size_t n, const char* const* members)
    stp_status stp_options_set_args(stp_options, int argc, const char* const* argv)
    char* stp_options_get_str(stp_options, const char* name)
    stp_status stp_options_get_bool(stp_options, const char* name, cbool* out)
    stp_status stp_options_get_int64(stp_options, const char* name, int64_t* out)
    stp_status stp_options_get_uint64(stp_options, const char* name, uint64_t* out)
    stp_status stp_options_get_duration_ms(stp_options, const char* name, uint64_t* out)
    char* stp_options_resolved_str(stp_options, const char* name)
    bint stp_options_is_set(stp_options, const char* name)
    stp_status stp_options_reset(stp_options, const char* name)
    void stp_options_reset_all(stp_options)
    stp_status stp_options_resolve(stp_options)
    size_t stp_options_num_names(int tier)
    const char* stp_options_name(int tier, size_t i)
    char* stp_options_help(int tier)
    const char* stp_option_name(stp_option)
    stp_status stp_option_from_name(const char* name, stp_option* out)
    const char* stp_option_info_type(const char* name)
    const char* stp_option_info_python_key(const char* name)
    char* stp_option_info_default(const char* name)
    stp_tier stp_option_info_tier(const char* name)
    stp_settable stp_option_info_settable(const char* name)
    stp_option_scope stp_option_info_scope(const char* name)
    const char* stp_option_info_category(const char* name)
    const char* stp_option_info_help(const char* name)
    bint stp_option_info_supported(const char* name)
    stp_status stp_option_info_range(const char* name, cbool* has_min, int64_t* min, cbool* has_max, int64_t* max)
    size_t stp_option_info_num_values(const char* name)
    const char* stp_option_info_value(const char* name, size_t i)
    size_t stp_option_info_num_aliases(const char* name)
    const char* stp_option_info_alias(const char* name, size_t i)
    const char* stp_option_info_short(const char* name)
    const char* stp_option_info_negation(const char* name)

    # ------------------------------------------------------------ solver
    stp_solver stp_solver_new(stp_tm, stp_options)
    void stp_solver_delete(stp_solver)
    const stp_error* stp_solver_failed(stp_solver)
    void stp_solver_clear_error(stp_solver)
    stp_tm stp_solver_manager(stp_solver)
    stp_status stp_solver_set_str(stp_solver, const char* name, const char* value)
    stp_status stp_solver_set_bool(stp_solver, const char* name, bint)
    stp_status stp_solver_set_int64(stp_solver, const char* name, int64_t)
    stp_status stp_solver_set_uint64(stp_solver, const char* name, uint64_t)
    stp_status stp_solver_set_duration_ms(stp_solver, const char* name, uint64_t ms)
    stp_status stp_solver_set_names(stp_solver, const char* name, size_t n, const char* const* members)
    stp_status stp_solver_set_args(stp_solver, int argc, const char* const* argv)
    char* stp_solver_get_str(stp_solver, const char* name)
    stp_status stp_solver_get_bool(stp_solver, const char* name, cbool* out)
    stp_status stp_solver_get_int64(stp_solver, const char* name, int64_t* out)
    stp_status stp_solver_get_uint64(stp_solver, const char* name, uint64_t* out)
    stp_status stp_solver_get_duration_ms(stp_solver, const char* name, uint64_t* out)
    char* stp_solver_resolved_str(stp_solver, const char* name)
    bint stp_solver_option_is_set(stp_solver, const char* name)
    stp_status stp_solver_reset_option(stp_solver, const char* name)
    stp_options stp_solver_options_copy(stp_solver)
    stp_status stp_solver_assert(stp_solver, stp_term)
    stp_status stp_solver_push(stp_solver, uint32_t n)
    stp_status stp_solver_pop(stp_solver, uint32_t n)
    uint32_t stp_solver_level(stp_solver)
    size_t stp_solver_num_assertions(stp_solver)
    stp_term stp_solver_assertion(stp_solver, size_t i)
    stp_status stp_solver_reset_assertions(stp_solver)
    stp_status stp_solver_reset(stp_solver)
    stp_status stp_solver_check_sat(stp_solver, stp_result* out) nogil
    stp_status stp_solver_check_sat_assuming(stp_solver, size_t n, const stp_term* assumptions, stp_result* out) nogil
    stp_status stp_solver_check_sat_budget(stp_solver, size_t n, const stp_term* assumptions, const stp_budget*, stp_result* out) nogil
    stp_status stp_solver_entails(stp_solver, stp_term formula, const stp_budget*, stp_entailment* out) nogil
    char* stp_solver_last_reason_message(stp_solver)
    size_t stp_solver_num_unsat_assumptions(stp_solver)
    stp_term stp_solver_unsat_assumption(stp_solver, size_t i)
    stp_model stp_solver_model(stp_solver)
    stp_model stp_solver_candidate_model(stp_solver)
    stp_term stp_solver_value(stp_solver, stp_term)
    void stp_solver_interrupt(stp_solver) nogil
    void stp_solver_clear_interrupt(stp_solver) nogil
    bint stp_solver_interrupt_pending(stp_solver) nogil
    ctypedef cbool (*stp_terminate_callback)(void* user) noexcept
    stp_status stp_solver_set_terminator(stp_solver, stp_terminate_callback, void* user)
    stp_statistics stp_solver_statistics(stp_solver)
    stp_term stp_solver_symbol(stp_solver, const char* name)
    stp_status stp_solver_parse_smt2(stp_solver, const char* script, stp_parse_mode) nogil
    stp_status stp_solver_parse(stp_solver, const char* text, stp_format) nogil
    stp_status stp_solver_parse_file(stp_solver, const char* path, stp_format) nogil
    stp_term stp_solver_parse_term(stp_solver, const char* smt2_term)
    char* stp_solver_to_smt2(stp_solver, bint with_check_sat)
    char* stp_solver_to_string(stp_solver, stp_format)
    ctypedef void (*stp_text_sink)(const char* text, size_t len, void* user) noexcept
    stp_status stp_solver_write_cnf(stp_solver, stp_text_sink, void* user, stp_cnf_scope* scope) nogil
    void stp_solver_set_diagnostic_sink(stp_solver, stp_text_sink, void* user)
    ctypedef size_t (*stp_text_source)(char* buf, size_t max, void* user) noexcept
    stp_status stp_solver_parse_source(stp_solver, stp_text_source, void* user, stp_format,
                                       stp_parse_mode) nogil
    char* stp_solver_input_to_string(stp_solver, stp_format)
    void stp_solver_set_output_sink(stp_solver, stp_text_sink, void* user)
    ctypedef void (*stp_fatal_error_handler)(const char* message, void* user) noexcept
    void stp_solver_set_fatal_error_handler(stp_solver, stp_fatal_error_handler, void* user)
    ctypedef void (*stp_cnf_sink)(const char* dimacs, size_t len, stp_cnf_scope scope,
                                  void* user) noexcept
    void stp_solver_set_cnf_sink(stp_solver, stp_cnf_sink, void* user)

    # ------------------------------------------------------------ model
    stp_model stp_model_copy(stp_model)
    void stp_model_release(stp_model)
    stp_tm stp_model_manager(stp_model)
    stp_term stp_model_value(stp_model, stp_term)
    stp_term stp_model_try_value(stp_model, stp_term)
    stp_status stp_model_values(stp_model, size_t n, const stp_term* in_, stp_term* out)
    stp_status stp_model_bool(stp_model, stp_term, cbool* out)
    stp_status stp_model_uint64(stp_model, stp_term, uint64_t* out)
    stp_status stp_model_int64(stp_model, stp_term, int64_t* out)
    char* stp_model_bv_string(stp_model, stp_term, int base, bint pad)
    stp_status stp_model_fp(stp_model, stp_term, stp_float_value* out)
    stp_status stp_model_fp_to_double(stp_model, stp_term, double* out)
    stp_status stp_model_rm(stp_model, stp_term, stp_rm* out)
    stp_array_value stp_model_array_value(stp_model, stp_term array)
    stp_fun_value stp_model_fun_value(stp_model, stp_term fun)
    stp_status stp_model_array_bytes(stp_model, stp_term array, uint64_t first_index, size_t count, uint8_t* out)
    size_t stp_model_num_symbols(stp_model)
    stp_term stp_model_symbol(stp_model, size_t i)
    bint stp_model_in_core(stp_model, stp_term symbol)
    char* stp_model_to_smt2(stp_model)
    void stp_array_value_release(stp_array_value)
    stp_sort stp_array_value_sort(stp_array_value)
    stp_term stp_array_value_default(stp_array_value)
    size_t stp_array_value_size(stp_array_value)
    stp_status stp_array_value_entry(stp_array_value, size_t i, stp_term* index, stp_term* element)
    stp_term stp_array_value_at(stp_array_value, stp_term index_value)
    stp_term stp_array_value_as_term(stp_array_value)
    void stp_fun_value_release(stp_fun_value)
    stp_sort stp_fun_value_sort(stp_fun_value)
    uint32_t stp_fun_value_arity(stp_fun_value)
    stp_term stp_fun_value_else(stp_fun_value)
    size_t stp_fun_value_size(stp_fun_value)
    stp_status stp_fun_value_entry(stp_fun_value, size_t i, stp_term* args_out, stp_term* value)
    stp_term stp_fun_value_apply(stp_fun_value, size_t n, const stp_term* arg_values)
    stp_term stp_fun_value_as_ite(stp_fun_value, size_t n, const stp_term* formals)

    # ------------------------------------------------------------ statistics
    void stp_statistics_release(stp_statistics)
    size_t stp_statistics_size(stp_statistics)
    const char* stp_statistics_name(stp_statistics, size_t i)
    bint stp_statistics_is_uint64(stp_statistics, const char* name)
    bint stp_statistics_is_double(stp_statistics, const char* name)
    stp_status stp_statistics_uint64(stp_statistics, const char* name, uint64_t* out)
    stp_status stp_statistics_double(stp_statistics, const char* name, double* out)
    char* stp_statistics_str(stp_statistics, const char* name)
    stp_tier stp_statistics_tier(const char* name)


# ------------------------------------------------------------ the wrapper classes
cdef class Manager:
    cdef stp_tm _tm
    cdef unsigned long _owner   # the creating thread (informational)
    cdef bint _busy
    cdef object _live          # WeakValueDictionary: node id -> wrapper
    cdef dict _sorts           # sort id -> Sort wrapper
    cdef object __weakref__
    cdef int _check(self) except -1
    cdef object _wrap(self, stp_term h)
    cdef object _wrap_sort(self, stp_sort h)
    cdef int _fail(self, const char* fn) except -1
    cdef stp_term* _array(self, list terms, size_t* n, const char* fn) except NULL
    cdef object _mk(self, stp_kind kind, list args, tuple indices, Sort sort, const char* fn)

cdef class Sort:
    cdef stp_sort _h
    cdef Manager _m
    cdef object __weakref__

cdef class Term:
    cdef stp_term _h
    cdef Manager _m
    cdef size_t _key            # the manager's identity, kept as a C field so that it survives tp_clear
    cdef object __weakref__

cdef class OptionsHandle:
    cdef stp_options _o
    cdef int _fail(self, const char* fn) except -1

# What a solver's C callbacks are given as their user data: the SolverHandle,
# borrowed, until it is deallocated -- a delete the manager's busy state defers
# may still call back after that, and must find nothing.
cdef struct CallbackBox:
    void* owner

cdef class SolverHandle:
    cdef stp_solver _s
    cdef CallbackBox* _box
    cdef Manager _m
    cdef size_t _key
    cdef object _terminator
    cdef object _sink
    cdef object _out_sink
    cdef object _fatal_handler
    cdef object _cnf_sink
    cdef object _callback_error
    cdef object __weakref__
    cdef int _fail_mutate(self, const char* fn) except -1
    cdef int _live(self) except -1

cdef class ModelHandle:
    cdef stp_model _h
    cdef Manager _m
    cdef size_t _key
    cdef object __weakref__

cdef class ArrayValueHandle:
    cdef stp_array_value _h
    cdef Manager _m
    cdef size_t _key

cdef class FunValueHandle:
    cdef stp_fun_value _h
    cdef Manager _m
    cdef size_t _key

cdef class StatisticsHandle:
    cdef stp_statistics _h
    cdef Manager _m
    cdef size_t _key
