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
#ifndef UDEFFLAGS_H
#define UDEFFLAGS_H

#include "stp/Sat/SearchBias.h"
#include <cstdint>

namespace stp
{

/******************************************************************
 * Struct UserDefFlags:
 *
 * Some userdefined variables that are set through commandline
 * options.
 ******************************************************************/

struct UserDefinedFlags
{
  UserDefinedFlags(UserDefinedFlags const&) = delete;
  UserDefinedFlags& operator=(UserDefinedFlags const&) = delete;

public:
  /* Parsing options */
  bool smtlib1_parser_flag = false;
  bool smtlib2_parser_flag = false;

  /* collect and delete objects via interface. */
  bool cinterface_exprdelete_on_flag = true;

  /* Output details of how the solving went*/
  bool stats_flag = false;
  bool quick_statistics_flag = false;

  /* Control simplification */
  bool optimize_flag = true; // the Simplifier functions (which might increase the size).
  bool wordlevel_solve_flag = true;   // turn on word level bitvector solver
  bool propagate_equalities = true; // Remove equalities.
  bool bitConstantProp_flag = true; // Constant bit propagation enabled.
  bool enable_unconstrained = true;
  bool enable_flatten = true;
  bool enable_ite_context = false;
  bool enable_aig_core_simplify = false;
  bool enable_use_intervals = true;
  bool enable_pure_literals = true;
  bool enable_split_extracts = true;
  bool enable_sharing_aware_rewriting = true;
  bool enable_merge_same = false;
  bool enable_pair_extract = true;
  bool enable_common_subsum = true;

  int64_t AIG_rewrites_iterations = 0; // Number of iterations of AIG rewrites.
  int64_t size_reducing_fixed_point = 0;
  

  bool simplify_to_constants_only = false;

  bool array_difficulty_reversion = true;
  bool difficulty_reversion = true;


  // eagerly write through the array's function congruence axioms.
  bool ackermannisation = false;

  // Incremental solving (docs/incremental-solving.rst): keep one SAT solver
  // and one bit-blast/CNF encoding alive across (check-sat) calls, asserting
  // retractable formulas as SAT assumptions instead of re-solving from
  // scratch.
  //
  // AUTO -- the default -- lets the session switch itself on at its first
  // (push), subject to the engagement threshold below; sessions that never
  // push are untouched. ON engages the driver from the first solve, whether
  // or not the input ever pushes. OFF keeps every solve on the batch
  // pipeline, a pushing input included; the frontend's per-level verdict
  // cache, which is not the driver, keeps working either way.
  enum class IncrementalMode
  {
    AUTO = 0,
    ON,
    OFF
  };
  IncrementalMode incremental_mode = IncrementalMode::AUTO;

  // The real-solve ordinal at which an automatically incremental SMT-LIB
  // session starts using the persistent driver. -1 selects the measured
  // per-logic policy (QF_BV/QF_ABV: 32; other/unknown logics: 3), 1 engages
  // on the first solve, and 0 disables automatic driver engagement without
  // disabling the frontend's per-level verdict cache. --incremental=on always
  // engages from the first solve and ignores this threshold, and
  // --incremental=off never engages whatever it is set to.
  int64_t incremental_auto_engage_at = -1;

  // Emit fine-grained per-check and cumulative measurements for the
  // incremental driver. Kept separate from the general -s diagnostics so
  // profiling is not distorted by verbose pass/backend output.
  bool incremental_profile = false;

  // Run only the persistent assumption/refinement core. This disables the
  // fitted cross-level preprocessing, promotion, first-solve shortcuts and
  // adaptive backend policies, but deliberately keeps memory-relief epoch
  // rotation and every theory-correctness mechanism.
  bool incremental_core_only = false;

  // Diagnostic oracle for the CBP level trail: discard the engine on every
  // stack divergence and re-feed the surviving prefix, as the pre-trail
  // implementation did. This is intentionally off in normal solving.
  bool incremental_cbp_reset = false;

  // Explicit --incremental starts before there is any persistent state to
  // reuse. On a very large first stack, building the cross-level CBP engine
  // can cost more than the only solve; defer that bootstrap until a later
  // real check. 0 disables the deferral.
  int64_t incremental_cbp_bootstrap_limit = 100000;

  // How many DAG nodes the cross-level CBP engine may retain for the live
  // stack before it stops accepting levels. Charged against what the engine
  // actually holds -- levels share subgraphs by identity, so this is the
  // union over live levels, not the sum of their sizes. The default is the
  // measured policy; the override exists so the cap can be reached in a
  // test without a hundred-thousand-node file.
  int64_t incremental_cbp_feed_cap = 200000;

  // A relief rebuild re-derives the whole base semantically -- equality
  // propagation, substitution and constant-bit propagation over every base
  // conjunct at once -- before re-encoding it. That is worth doing on a base
  // the pass can actually digest and is unbounded work on one it cannot, so
  // it is skipped once the base passes this many DAG nodes; the raw base is
  // re-encoded instead, exactly as it is for array bases and for the three
  // rebuild reasons that are not about size. 0 skips it always.
  int64_t incremental_base_resimplify_limit = 100000;

  // The persistent encoding grows monotonically within an epoch; when the
  // solver's variable count passes this limit AND most encodings belong to
  // popped, never-returning content, the complete semantic/AIG/SAT encoding
  // epoch is rotated and reconstructed from the live stack. 0 disables this
  // SAT-size trigger; the independent semantic-cache trigger below may still
  // rotate.
  int64_t incremental_reencode_limit = 1000000;

  // Approximate DAG-node charge at which the driver exactly compares the
  // union pinned by semantic caches with the latest live stack. If dead
  // cached structure is at least four times the peak live union, rotate the
  // complete semantic/AIG epoch. Separate from the SAT-variable threshold so
  // diagnostic SAT limits do not turn into unrelated semantic policy knobs.
  // 0 disables semantic-cache-triggered relief.
  int64_t incremental_semantic_cache_limit = 1000000;

  // Promote a pushed level that has sat identical at the same depth for
  // many consecutive solves to permanent unit clauses: its assumption
  // disappears and its clauses join root-level preprocessing. A later
  // retraction of a promoted level restarts the solver, with the
  // stability threshold doubling on each such demotion.
  bool incremental_promote_units = true;

  // Decide whole-array equality/disequality (the extensional theory of
  // arrays) with the lemmas-on-demand procedure of Brummayer & Biere
  // (JSAT 2010). Runtime semantic option; it must be set before a
  // whole-array equality is constructed. Construction preserves an opaque
  // ARRAY_EQ, which is lowered only after the complete query is assembled.
  bool enable_array_equality = false;

  // Decide nonzero-arity uninterpreted functions over Bool, BitVec, declared
  // sorts, RoundingMode and FloatingPoint using dynamic Ackermann refinement.
  // An SMT-LIB logic containing UF enables it; this runtime option also lets
  // callers enable the theory for inputs whose declared logic omits UF.
  bool enable_uninterpreted_functions = false;

  // How many congruence lemmas one refuted candidate may install before the
  // solver is asked again; 0 is unlimited. Every conflict a candidate exposes
  // is refuted by that same assignment, so installing several together trades
  // clauses for whole SAT calls. The trade is not monotone: a small batch is
  // worth several rounds, while draining every conflict installs most of the
  // quadratic congruence encoding a round at a time and is slower than
  // emitting one. Measured over collision and pigeonhole families at 30..100
  // applications, 8 was the best of 1/2/4/8/16/32/unlimited everywhere and
  // 2.3x-4x faster than 1; unlimited was the worst setting tried. Setting 1
  // restricts each candidate to one installed congruence lemma.
  unsigned uf_lemmas_per_round = 8;

  // Whether to install a declaration's pairwise congruence constraints before
  // the first solve instead of waiting for a candidate to earn them.
  //
  // AUTO -- the default -- selects declarations whose pair count the policy
  // predicts is worth encoding up front, cheapest first, until the budget
  // below is spent. ON selects every declaration whatever the count. OFF
  // installs no congruence clause before the first solve, so a refuted
  // candidate has to earn each one. The dynamic checker runs in every mode,
  // so an eagerly encoded declaration that still produced a conflict would
  // be caught rather than silently answered.
  enum class UFEagerMode
  {
    AUTO = 0,
    ON,
    OFF
  };
  UFEagerMode uf_eager_mode = UFEagerMode::AUTO;

  // The AUTO budget, in congruence constraints. A declaration costs
  // C(v, 2) + c*v, where c counts its applications whose actuals are all
  // constants: two such applications either are the same hash-consed handle
  // or differ in some position, so they never need a constraint between them.
  //
  // Swept over 363 QF_UFBV benchmarks (every seventh of the local corpus,
  // 30s each, settings interleaved so none sits systematically early in the
  // schedule). Solved, of 363:
  //
  //   off  253 | 128  268 | 256  281 | 512  271 | 1536  247 | 4096  250
  //
  // The curve is unimodal: a little eager congruence beats none by a wide
  // margin, and a lot is worse than none, because the declarations a large
  // budget buys are the expensive ones whose pairs mostly go unused. Rerun
  // at 256 against 4096 it is 287 against 251 solved, 39 files gained
  // against 3 lost, and 16% less wall clock, with no verdict disagreeing.
  //
  // The counterweight, recorded because it is the evidence the previous
  // value was chosen on: a synthetic family of n applications that all
  // collide wants every one of its C(n, 2) pairs, so 256 declines it and it
  // slows down several-fold. Nothing in the tree pins that family, and the
  // corpus is what the default should serve; --uf-ackermann-budget restores
  // the old behaviour for a query known to be that shape.
  unsigned uf_eager_budget = 256;

  // Whether to bias the first candidate so that the scalars the congruence
  // checker reads start out pairwise different.
  //
  // The checker's work is driven by collisions: two applications whose
  // argument tuples read the same value and whose results do not. A solver
  // left to its own default phase has no reason to spread unconstrained
  // arguments out, so the first candidate collides on many of them at once
  // and each collision costs a lemma and a round. A phase hint is advisory --
  // it moves the search order and nothing else -- so biasing those scalars
  // apart can only change how quickly an answer is found, never which answer.
  bool uf_phase_hints = false;

  // The carrier width given to a sort introduced by (declare-sort S 0).
  //
  // An uninterpreted sort has no operations but equality, so a query
  // mentioning k terms of that sort is satisfiable exactly when it is
  // satisfiable over a domain of k elements. Any carrier with at least k
  // values therefore answers it, and a carrier with more values than the
  // query can distinguish costs only the bits nothing constrains -- so
  // over-approximating is sound and only under-approximating is not.
  //
  // The width has to be fixed when the sort is declared, before any term of
  // it exists, so it cannot be derived from k. 16 bits admits 65536 distinct
  // elements, which is far beyond the number of terms of a single
  // uninterpreted sort in practice; raise it if a query ever needs more.
  unsigned uf_sort_width = 16;

  // Narrow the result sort of a UF declaration whose applications are used
  // only for equality comparisons (both sides of the same declaration).
  // Reducing a 256-bit result to ceil(log2(N+1)) bits cuts the number of
  // AIG nodes per congruence constraint from ~511 to a handful. The
  // analysis is conservative: any non-equality use disqualifies the
  // declaration. Enabled by default; set to false if it causes trouble.
  bool uf_narrow_results = true;

  // For declarations whose results appear only in equality contexts, add
  // the reverse implication (= result_i result_j) => (= arg_i arg_j) in
  // the eager congruence encoding. This asserts injectivity, giving the
  // SAT solver bidirectional propagation between argument and result
  // equalities.
  //
  // Congruence itself is entailed by the query; its converse is not. So this
  // is the one thing the lowering installs that changes what the encoding
  // means: it describes the query with injectivity conjoined. Only models are
  // lost by that, so a `sat` found over it is a model of the query and needs
  // nothing done to it, while an `unsat` refutes the strengthened query and
  // may be the assumption's rather than the query's.
  //
  // So it is installed behind one activation symbol and assumed rather than
  // asserted: a refutation that used the assumption is taken back and the
  // query decided without it, which makes the flag verdict-preserving. See
  // STPMgr::solveRetractingInjectivity for the rule and STP::TopLevelSTP for
  // the case it cannot cover. Off by default, and not free: what it buys is
  // faster model-finding on a query whose functions are injective anyway, and
  // it costs a second search on one that is not.
  bool uf_inject_args = false;

  // Replace a (distinct x1 ... xn) whose operands are variables occurring
  // nowhere else with the strict chain x1 < x2 < ... < xn. Every permutation
  // of such operands maps the formula to itself, so fixing one of the n!
  // orderings loses no answer, and n-1 comparisons replace n(n-1)/2
  // disequalities that a bit-blaster would otherwise have to order for
  // itself. Batch pipeline only: the guard is re-checked against each
  // solve's own formula, so a later assert that mentions an operand simply
  // stops the rewrite from applying on the next solve.
  bool distinct_ordering = true;

  // construct the counterexample in terms of original variable based
  // on the counterexample returned by SAT solver
  bool print_counterexample_flag = false;
  bool print_binary_flag = false;

  // if this option is true then print the way dawson wants using a
  // different printer. do not use this printer.
  bool print_arrayval_declaredorder_flag = false;

  // flag to decide whether to print "valid/invalid" or not
  bool print_output_flag = false;

  // print the input back
  bool print_STPinput_back_flag = false;
  bool print_STPinput_back_SMTLIB2_flag = false;
  bool print_STPinput_back_CVC_flag = false;
  bool print_STPinput_back_dot_flag = false;
  bool print_STPinput_back_GDL_flag = false;

  bool print_nodes_flag = false;

  // output flags
  bool output_CNF_flag = false;

  /* Bitblasting options */

  // Hard cap on the AND gates the batch bit-blaster may build for one query.
  // -1 (the default) is no limit and leaves the blaster exactly as it was;
  // 0 gives up before the first gate. That is the same -1/0 convention
  // `--max-num-confl` and `--max-time` use, and deliberately so: a reader
  // who transfers their intuition here must not get the opposite of what
  // they asked for. Exceeding the cap abandons the query through the
  // soft-timeout path, so the answer is the same one a `--max-time` expiry
  // gives -- `unknown` on stdout in SMT-LIB mode (`Unknown.` in the CVC
  // language) with exit status 0, and SOLVER_UNKNOWN from the library.
  // (get-info :reason-unknown) is what tells this budget from the clock.
  //
  // The cap governs the two AIGs a batch solve builds -- the bit-blast in
  // ToSATAIG::bitblast() and the optional `--aig-core-simplification` pass,
  // which simply keeps its input when the cap fires. It is NOT enforced on
  // the incremental driver's persistent encoder, whose AIG outlives the
  // check that grew it and cannot be abandoned mid-blast; engaging that
  // driver with a budget set warns once on stderr rather than pretending
  // the cap is in force.
  //
  // It bounds the blast, not the process: CNF conversion (Aig_ManDupDfs plus
  // DAG-aware rewriting) and the SAT search itself allocate on top of it.
  int64_t aig_node_budget = -1;

  bool bv_eq_abstraction = false;
  // One width floor for both abstraction families: equalities and the
  // abstracted terms (comparisons, ITE, BVPLUS, BVMULT, BVDIV, BVMOD)
  // all abstract only at or above this operand width.
  unsigned bv_abstraction_width = 64;
  unsigned bv_eq_refine_width = 0;
  bool bv_term_abstraction = false;
  // BVMULT, BVDIV and BVMOD are the operations whose refinement has no compact
  // exact lemma: it rules out one pair of operand values at a time. They are
  // abstracted with everything else, and this turns just those three off for a
  // query that would rather not pay for the rounds at all.
  bool bv_term_abstraction_mult = true;
  // How many times one of those three may be blocked before its refinement
  // stops enumerating and encodes the operation exactly instead. Measured:
  // through about thirty rounds the abstraction is still two to four times
  // faster than not abstracting, by sixty it is break-even, and past that it
  // collapses -- a 64-bit factorisation spent 5816 rounds and ninety seconds
  // on a query the unabstracted solve answers in five hundredths of one.
  // Zero never escalates, which is what this was before.
  unsigned bv_term_abstraction_rounds = 32;

  // You can select these with any combination you want of true & false.
  bool division_variant_1 = true;
  bool division_variant_2 = true;
  bool division_variant_3 = false;
  bool adder_variant = true;
  bool bbbvle_variant =true;
  bool upper_multiplication_bound = false;
  bool bvplus_variant = true;
  bool conjoin_to_top = false;

  // Bit-blast the floating-point predicates -- comparisons, equalities and
  // classifications -- over already-packed operands natively (over the IEEE
  // bits) instead of via the SymFPU unpacking circuits.
  bool fp_native_cmp = true;

  // Bit-blast fp.mul under surviving native predicates with the hand-written
  // packed-operand circuit (BBfpMul) instead of the SymFPU unpacking
  // circuits. Experimental; off by default.
  bool fp_native_arith = false;

  // Recognise fp.isZero(fp.add ...) and encode the observed zero-result
  // condition directly instead of constructing and packing every result bit.
  // Experimental; requires native arithmetic and is off by default.
  bool fp_native_add_iszero = false;

  // Experimental strengthening for the native FP bit-blaster: mine simple
  // top-level finite box bounds and use them to omit NaN/infinity cases from
  // native packed-field circuits when those cases are already impossible.
  bool fp_native_domain = false;

  // Experimental native-domain arithmetic specialization. A known finite
  // semantic sign removes fp.add's opposite-sign cancellation datapath and
  // fp.mul's sign-dependent rounding, while explicit muxes retain signed zero.
  bool fp_native_known_sign = false;

  // Experimental floating-point domain prepass. It mines simple boxed
  // variable bounds from ordered FP comparisons and uses them to discharge
  // non-box ordered comparisons and zero-sum rows whose interval/domain facts
  // decide them.
  bool fp_domain_simplify = false;

  // Sound zero-fact extraction for boxed nonnegative FP symbols. It only
  // derives zero facts from same-sign rows whose terms are +/- one boxed
  // symbol. Two-term differences may propagate an already-established zero,
  // but terms are never algebraically cancelled through a rounded row. Zero
  // is encoded as zero magnitude bits so +0/-0 remain distinct.
  bool fp_domain_sound_zero_facts = false;

  // Sound row-level FP zero refutation. It recognises linear FP expressions
  // over boxed finite variables and rewrites a zero-row to false only when a
  // conservative target-format interval, evaluated in the original AST
  // association with rounding at every operation, excludes zero.
  bool fp_domain_row_bounds = false;

  int64_t multiplication_variant = 1;

  // If the bit-blaster discovers new constants, should the term simplifier be
  // re-run.
  bool simplify_during_BB_flag = false;


  /* CNF Generation options */
  bool simple_cnf = false; // don't use the good AIG based CNF conversion.

  // How much work to spend turning the AIG into CNF. Higher levels take longer
  // to generate but produce a smaller CNF, so the best setting depends on
  // whether a problem's cost is dominated by CNF generation or by solving.
  //
  // MEDIUM is ABC's Cnf_Derive(), a cut-enumeration and technology-mapping
  // pass. VERY_LOW is Cnf_DeriveFast(), which skips cut enumeration entirely.
  // LOW, HIGH and VERY_HIGH use ABC's newer Mf_ManGenerateCnf() at LUT sizes
  // 3, 6 and 8; its cost grows steeply with LUT size for little further gain
  // past 6.
  enum CNFEffort
  {
    CNF_EFFORT_VERY_LOW = 0,
    CNF_EFFORT_LOW,
    CNF_EFFORT_MEDIUM,
    CNF_EFFORT_HIGH,
    CNF_EFFORT_VERY_HIGH
  };

  enum CNFEffort cnf_effort = CNF_EFFORT_MEDIUM;

  bool exit_after_CNF = false;

  // Stop after parsing the input, skipping any check-sat commands.
  bool parse_only = false;

  // Whether the SMT-LIB2 lexer reads a character at a time, as needed when
  // stp is driven interactively over a pipe, rather than in blocks.
  // -1: character at a time for stdin, blocks for files. 0: blocks. 1:
  // character at a time.
  int64_t interactive_read = -1;

  /* SAT solving options */

  int64_t timeout_max_conflicts = -1;
  int num_solver_threads = 1;
  int64_t timeout_max_time = -1; // seconds

  // check the counterexample against the original input to STP
  bool check_counterexample_flag = false;

  // SMT-LIB (set-option :produce-models true): models must be readable
  // after sat answers. An input to the construct_counterexample_flag
  // derivations, deliberately separate from check_counterexample_flag --
  // asking for models is not asking for them to be verified, and
  // construction itself may be deferred to the first read.
  bool produce_models = false;

  // The C API's 'c'/'d' flags ask for a counterexample directly, with no
  // other trace of the request. Held here so the derivation below can be
  // recomputed per query rather than merely widened: a flag that only ever
  // gains value latches, and callers read it as "a model was asked for".
  bool request_counterexample = false;

  //This is derived from other settings.
  bool construct_counterexample_flag = false;

  // The caller-facing reasons a satisfiable answer must retain a readable
  // model. Theory refinement is an internal consumer and is deliberately a
  // separate input to modelConstructionRequired() below.
  bool callerRequestedModel() const
  {
    return check_counterexample_flag || print_counterexample_flag ||
           produce_models || request_counterexample;
  }

  // Derive the per-query construction flag from its actual inputs rather than
  // widening the previous query's value. Debug builds always construct so the
  // solver's internal model checks keep their established coverage.
  bool modelConstructionRequired(bool internalConsumer = false) const
  {
    bool required = callerRequestedModel() || internalConsumer;
#ifndef NDEBUG
    required = true;
#endif
    return required;
  }


  // Available back-end SAT solvers.
  enum SATSolvers
  {
    MINISAT_SOLVER = 0,
    SIMPLIFYING_MINISAT_SOLVER,
    CRYPTOMINISAT5_SOLVER,
    RISS_SOLVER,
    CADICAL_SOLVER
  };

  enum SATSolvers solver_to_use;

  // Which answer to tune the SAT search towards. NONE, the default, leaves
  // every backend at its own settings, so the option is opt-in.
  SearchBias search_bias = SearchBias::NONE;

  // Whether CaDiCaL may use bounded variable addition (its "factor"
  // technique). ON is the default: measured on QF_BV, where the AUTO
  // heuristic below never fires, it is worth a 0.76-0.80 geometric mean of
  // wall clock on hard instances (>10 s, 259 files, three rounds) and -12.5%
  // total wall over 42k easy ones, with no answer disagreements.
  //
  // AUTO enables it only for problems that still contain array operations
  // after simplification. That was the default when the flag landed, fitted
  // on QF_ABV alone: BVA is a large win on some array-refinement families
  // (wchains: up to 5x) and a loss on countbitstable, whose arrays are
  // Ackermannised away, so testing for surviving arrays separated the two.
  // It is kept as an explicit choice because it is the only way back to that
  // behaviour; on QF_BV it is equivalent to OFF.
  enum class BVAMode
  {
    AUTO = 0,
    ON,
    OFF
  };
  BVAMode cadical_factor = BVAMode::ON;

  // Whether ON above came from the command line rather than from the default.
  // A backend with no BVA declines the request, and that is worth a warning
  // only when a user actually asked for it -- otherwise every solve on a
  // pre-3.0 CaDiCaL build would carry one.
  bool cadical_factor_explicit = false;

  // Whether the incremental driver may retire CaDiCaL's probe-based
  // inprocessing mid-session. Inprobing re-runs over the whole
  // persistent encoding at every solve; on many-solve sessions that
  // recurring cost dominates what it earns (measured 2x on generated
  // variant-push corpora), while few-solve sessions genuinely profit
  // from it. AUTO -- the default -- retires it once a session has shown
  // enough solves, via one bounded solver rebuild; ON never retires;
  // OFF retires from the first driver solve.
  BVAMode incremental_inprobing = BVAMode::AUTO;

  bool get_print_output_at_all() const
  {
    return print_STPinput_back_flag || print_STPinput_back_SMTLIB2_flag ||
           print_STPinput_back_CVC_flag || print_STPinput_back_dot_flag ||
           print_STPinput_back_GDL_flag;
  }

  void disableSimplifications()
  {
    optimize_flag = false;
    enable_unconstrained = false;
    bitConstantProp_flag = false;
    enable_use_intervals = false;
    enable_pure_literals = false;
    wordlevel_solve_flag = false;
    propagate_equalities = false;
    enable_flatten = false;
    enable_split_extracts = false;
    enable_sharing_aware_rewriting = false;
    enable_merge_same = false;
    enable_pair_extract = false;
    enable_common_subsum = false;
    enable_ite_context = false;
    distinct_ordering = false;

    simple_cnf=true;
  }

  void disableSizeIncreasingSimplifications()
  {
     simplify_to_constants_only = true;
     enable_ite_context = false;

     // Can't get bigger so we won't need to revert.
     array_difficulty_reversion = false;
     difficulty_reversion = false;
  }

  // What the encoding options above actually did, as against what they were
  // allowed to do. Not settings: a caller that turns an abstraction on wants
  // to know it engaged, and a flag that reached no eligible operation and a
  // flag that is broken both abstract nothing -- only the candidate count
  // tells them apart. Cumulative over the manager's lifetime, and read
  // through vc_getCounter.
  //
  // Lives here rather than in STPMgr because the bit-blaster holds only these
  // flags, and the sites that would have to be counted are all inside it.
  struct EncodingCoverage
  {
    // One per abstractable node kind, indexed by AbstractionKind below.
    static const unsigned KINDS = 6;
    // Operations reaching the bit-blaster at or above bv_abstraction_width:
    // what the abstraction could have taken, whether or not it was on.
    uint64_t bv_candidates[KINDS] = {};
    // ... and what it did take.
    uint64_t bv_abstracted[KINDS] = {};
    // Rounds the CEGAR refiner ran, and blocking lemmas it installed.
    uint64_t bv_refinement_rounds = 0;
    uint64_t bv_blocking_lemmas = 0;
    // Uninterpreted-function applications the lowering decided, and the
    // constraints it installed for them.
    uint64_t uf_applications_lowered = 0;
    uint64_t uf_constraints_installed = 0;
    // Queries that reached bit-blasting at all: the denominator, without
    // which a zero above cannot be told from a query the simplifier settled.
    uint64_t queries_bitblasted = 0;
  };

  enum AbstractionKind
  {
    ABSTRACT_EQ = 0,
    ABSTRACT_COMPARE,
    ABSTRACT_ITE,
    ABSTRACT_PLUS,
    ABSTRACT_MULT,
    ABSTRACT_DIVMOD
  };

  EncodingCoverage coverage;

  UserDefinedFlags()
  {
#ifdef USE_CADICAL
    solver_to_use = CADICAL_SOLVER;
#else
#ifdef USE_CRYPTOMINISAT
    solver_to_use = CRYPTOMINISAT5_SOLVER;
#else
#ifdef USE_RISS
    solver_to_use = RISS_SOLVER;
#else
    solver_to_use = MINISAT_SOLVER;
#endif
#endif
#endif
  }
};
} // end of namespace

#endif
