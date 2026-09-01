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
#include "stp/Util/Attributes.h"
#include "stp/config.h"
#include <cstdint>
#include <iosfwd>
#include <string>

namespace stp
{

// Independently selectable families of algebraic facts used by BV term
// abstraction. The ordinal is also the coverage-counter index; the mask
// spelling keeps the command-line and C interfaces compact without turning
// every individual lemma into a permanent public option.
//
// The groups are disjoint: every fact the refiner can offer has exactly one
// owner here, so a mask with one bit set selects precisely that family and
// the per-group counters partition the schema total. In operation order,
// with each operation's mechanisms after its registries.
enum class BVSchemaGroup : unsigned
{
  // The schemas an enabled abstraction inherits: the seven division facts
  // that were already qualified, the divisor-value and bound schemas, and
  // multiplication's parity, trailing-zero and power-of-two schemas.
  BASE = 0,

  // Unsigned division.
  UDIV15,         // the highest-firing single fact outside BASE
  UDIV_OBSERVED,  // the ranked facts that fired on the qualification corpus
  UDIV_TAIL,      // the rest of the registry, which did not

  // Unsigned remainder.
  UREM,

  // Division and remainder mechanisms, rather than registry entries.
  QUOTIENT_ONE_QUOT,
  QUOTIENT_ONE_REM,
  QUOTIENT_THRESHOLDS,
  DIVISOR_MAGNITUDE,
  DIVREM_FULL,

  // Multiplication.
  MUL8,
  MUL_REF3,
  MUL_TAIL,

  // Addition. Measured, and deliberately not adopted: over 497 queries
  // chosen because they abstract a wide addition -- this family's best case
  // -- enabling it installed 30,519 lemmas and cost 19.9% and seven solves
  // against the inherited mask, regressing 162 queries and improving 15. It
  // stays selectable so that result stays reproducible, and stays out of
  // every profile.
  ADD,
  // The exact low-prefix mechanism addition and multiplication share. On the
  // same 497 queries it fired 9,525 times and moved nothing: +0.4%, with the
  // solved and timeout counts identical to the inherited mask.
  LOW_PREFIX,

  COUNT
};

constexpr unsigned BV_SCHEMA_GROUP_COUNT =
    static_cast<unsigned>(BVSchemaGroup::COUNT);

constexpr uint32_t bvSchemaGroupBit(BVSchemaGroup group)
{
  return uint32_t{1} << static_cast<unsigned>(group);
}

constexpr uint32_t BV_SCHEMA_GROUP_ALL =
    (uint32_t{1} << BV_SCHEMA_GROUP_COUNT) - 1;

// The mask an explicitly enabled abstraction inherits, and the only one the
// corpus qualification actually justified: the established schemas, plus the
// two families that were measured to decide queries on their own -- the UREM
// registry, which turns the wide remainder cases from a two-gigabyte external
// timeout into fractions of a second, and MulRef3, which takes one 512-bit
// rewrite candidate from 3.66s/766MB to 0.12s/65MB. Every broader profile
// below is an experiment that has to be asked for.
constexpr uint32_t BV_SCHEMA_GROUP_QUALIFIED =
    bvSchemaGroupBit(BVSchemaGroup::BASE) |
    bvSchemaGroupBit(BVSchemaGroup::UREM) |
    bvSchemaGroupBit(BVSchemaGroup::MUL_REF3);

// The complete observed single-record catalogue. Every schema here states a
// fact about one division, remainder, multiplication or addition on its own;
// the one relation that spans a quotient and its remainder together builds a
// full-width multiplier and stays out, in AGGRESSIVE below.
constexpr uint32_t BV_SCHEMA_GROUP_BROAD =
    bvSchemaGroupBit(BVSchemaGroup::BASE) |
    bvSchemaGroupBit(BVSchemaGroup::UDIV15) |
    bvSchemaGroupBit(BVSchemaGroup::UDIV_OBSERVED) |
    bvSchemaGroupBit(BVSchemaGroup::UREM) |
    bvSchemaGroupBit(BVSchemaGroup::MUL8) |
    bvSchemaGroupBit(BVSchemaGroup::MUL_REF3) |
    bvSchemaGroupBit(BVSchemaGroup::QUOTIENT_ONE_REM) |
    bvSchemaGroupBit(BVSchemaGroup::QUOTIENT_ONE_QUOT) |
    bvSchemaGroupBit(BVSchemaGroup::DIVISOR_MAGNITUDE);

// The same catalogue plus the full-width modular identity, which ties a
// quotient and its remainder to the dividend they came from. It reduces
// blocking and exact escalation the most aggressively of any profile and is
// still the slowest of them, because the identity builds a full-width
// multiplier; it exists to make that trade reproducible.
constexpr uint32_t BV_SCHEMA_GROUP_AGGRESSIVE =
    BV_SCHEMA_GROUP_BROAD | bvSchemaGroupBit(BVSchemaGroup::DIVREM_FULL);

constexpr unsigned BV_TERM_ABSTRACTION_QUALIFIED_ROUNDS = 32;
constexpr unsigned BV_TERM_ABSTRACTION_BROAD_ROUNDS = 16;
constexpr unsigned BV_TERM_ABSTRACTION_AGGRESSIVE_ROUNDS = 16;

// These defaults matter only after a caller explicitly turns BV term
// abstraction on. The global feature switch remains off.
constexpr uint32_t BV_SCHEMA_GROUP_DEFAULT = BV_SCHEMA_GROUP_QUALIFIED;
constexpr unsigned BV_TERM_ABSTRACTION_DEFAULT_ROUNDS =
    BV_TERM_ABSTRACTION_QUALIFIED_ROUNDS;

constexpr bool bvSchemaGroupEnabled(uint32_t mask, BVSchemaGroup group)
{
  return (mask & bvSchemaGroupBit(group)) != 0;
}

DLL_PUBLIC const char* bvSchemaGroupName(BVSchemaGroup group);

// Parse the comma-separated CLI spelling. `all` and `none` are aliases for
// the complete and empty masks and must stand alone. The output mask is left
// unchanged on error, with a diagnostic returned through `error`.
DLL_PUBLIC bool parseBVSchemaGroups(const std::string& text, uint32_t& mask,
                                    std::string& error);
DLL_PUBLIC std::string formatBVSchemaGroups(uint32_t mask);

// Parse one of the named mask/round pairs. Both outputs are left
// unchanged on error, so callers cannot accidentally apply half a profile.
DLL_PUBLIC bool parseBVTermAbstractionProfile(const std::string& text,
                                              uint32_t& mask, unsigned& rounds,
                                              std::string& error);

struct UserDefinedFlags;

// Print the abstraction coverage, refinement and exact-escalation counters
// reported by `-t`. The same reporter is used after an ordinary solve and by
// --exit-after-CNF once bit-blasting has populated the coverage counters.
DLL_PUBLIC void printAbstractionCoverage(const UserDefinedFlags& uf,
                                         std::ostream& out);

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

  // Abstract a read over a long write chain to a fresh variable constrained
  // by refinement lemmas, instead of expanding the full if-then-else chain.
  // The depth is how many may-alias write levels a read still expands
  // eagerly before the rest of its chain is abstracted.
  bool lazy_write_reads = true;
  int64_t lazy_write_reads_depth = 2;

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

  // How many index comparisons the eager array-equality arm may introduce
  // before the solve is left to refinement. Counted by
  // arrayCongruenceEstimate, which charges only the comparisons that survive
  // constant folding, so a query whose indexes are mostly literals is judged
  // on the work it actually causes rather than on how many reads it happens
  // to contain.
  //
  // 4000 admits the whole array-equality band that measurement says is worth
  // taking -- the store-permutation queries that pay for the arm score up to
  // 1830 -- with room above it. The value is a ceiling on a cost, not a
  // target: nothing is gained by being nearer it. --ackermanize is a request
  // and ignores this; 0 refuses every unasked selection.
  unsigned array_eager_budget = 4000;

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
  // The cap governs the transient AIGs a solve builds -- the batch bit-blast
  // in ToSATAIG::bitblast(), the optional `--aig-core-simplification` pass
  // (which simply keeps its input when the cap fires), and the exact AIG used
  // when a bit-vector abstraction gives up. It is NOT enforced on the
  // incremental driver's persistent encoder, whose AIG outlives the check
  // that grew it and cannot be abandoned mid-blast; engaging that driver with
  // a budget set warns once on stderr rather than pretending the cap is in
  // force.
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
  // BVMULT is one of the operations whose fallback rules out one pair of
  // operand values at a time. Keep its scope independent of division: the
  // circuit costs and the workloads which benefit from abstracting them are
  // materially different.
  bool bv_term_abstraction_mult = true;
  // BVDIV and BVMOD share an implementation and a refinement catalogue, but
  // no longer share BVMULT's scope switch. A caller can therefore leave the
  // expensive dividers abstract while encoding multiplication exactly, or
  // vice versa. Both switches default on, preserving the historical scope.
  bool bv_term_abstraction_divmod = true;
  // Interface bookkeeping rather than a solver knob: whether a caller named
  // the DIV/MOD scope itself.
  //
  // The older switch above it covered all three nonlinear operations, and
  // still does when it is the only one given. Once DIV/MOD has been set
  // explicitly it wins, whichever order the two arrive in -- which is what
  // the command line does through CLI11's occurrence count, and what the C
  // interface does through this flag. Without it the C interface would be
  // last-writer-wins while the command line was not, and the same pair of
  // settings would mean two different things depending on which one a caller
  // reached for.
  bool bv_term_abstraction_divmod_explicit = false;

  // Which of the other abstractable kinds --bv-term-abstraction takes.
  //
  // It used to take all of them, and the reason to doubt that looked
  // strong: an ITE, an addition and a comparison each bit-blast in a number
  // of gates linear in the width, where a multiplication is quadratic and a
  // division worse, so abstracting a linear operation saves little and costs
  // a free variable the refinement then has to pin down. On one 256-bit
  // industrial query the blaster was handed 82 comparisons, 79 if-then-elses
  // and 15 additions against 2 multiplications and 6 divisions: 184 free
  // variables to avoid encoding 8 operations.
  //
  // There, turning the three off changed nothing: the refinement ran 35
  // rounds either way -- the same rounds, over the same 8 arithmetic
  // abstractions -- and over 400 files of the same family it solved 245
  // against 247, inside the run-to-run spread. Over 329 SMT-LIB QF_BV
  // files the abstraction engages on, the same: 204 solved against 203,
  // PAR2 within half a percent.
  //
  // Inside a floating-point circuit it is not nothing. SymFPU lowers one
  // binary128 operation to hundreds of 106- to 229-bit if-then-elses,
  // adders and comparisons around one or two multiplications or divisions:
  // on a KLEE query of 25 such operations the blaster abstracted 348 ITEs,
  // 30 additions and 4 comparisons against 4 multiplications and 6
  // dividers, every round refined some 230 of them, and the solve took 34 s
  // where the arithmetic alone takes 3.4 s and, with the value lemma below
  // written compactly, 0.4 s. Bitwuzla's abstraction, which this is
  // measured against, abstracts multiplication, division and remainder
  // only. Off by default therefore: what the three buy on bit-vector
  // workloads is noise, and what they cost on floating-point ones is the
  // whole benefit.
  bool bv_term_abstraction_ite = false;
  bool bv_term_abstraction_plus = false;
  bool bv_term_abstraction_compare = false;

  // Ask the propositional structure what it settles before solving
  // properly; see SkeletonPreproc. Off by default: what it costs is a SAT
  // call over a formula the size of the query's Boolean skeleton, and what
  // it buys depends entirely on whether that structure decides anything.
  bool skeleton_preproc = false;

  // Replace an assertion where it appears inside another assertion; see
  // EmbeddedConstraints. Off by default while it is measured.
  bool embedded_constraints = false;
  // The ceiling on how many times one of those three may be blocked before
  // its refinement stops enumerating and encodes the operation exactly
  // instead. Measured: through about thirty rounds the abstraction is still
  // two to four times faster than not abstracting, by sixty it is
  // break-even, and past that it collapses -- a 64-bit factorisation spent
  // 5816 rounds and ninety seconds on a query the unabstracted solve
  // answers in five hundredths of one. Zero never escalates, which is what
  // this was before.
  //
  // Thirty-two, because that is what the inherited mask was measured at:
  // sixteen and thirty-two tied over 287 natural division/remainder
  // consumers, and sixteen additionally failed to terminate within the
  // external guard on one 512-bit case that thirty-two answered. The broad
  // experimental profiles pair their catalogue with sixteen, and select both
  // as one atomic decision.
  //
  // A ceiling and no longer the allowance itself: see the divisor below, and
  // valueLemmaAllowance() for how the two compose.
  unsigned bv_term_abstraction_rounds = BV_TERM_ABSTRACTION_DEFAULT_ROUNDS;
  // Interface bookkeeping rather than a solver knob: whether a caller named
  // the round ceiling itself, in the same shape and for the same reason as
  // bv_term_abstraction_divmod_explicit above.
  //
  // A profile is an atomic mask/round pair, so applying one writes this field
  // as well as the schema mask -- which means a caller who set the ceiling and
  // then chose a profile silently lost the ceiling, while one who did the two
  // the other way round kept it. The command line cannot reach that, because
  // CLI11 refuses --bv-term-abstraction-profile alongside
  // --bv-term-abstraction-rounds outright; only the C interface can, where a
  // configuration is a sequence of calls rather than one line. Once the
  // ceiling is named it survives a profile, whichever order the two arrive in.
  bool bv_term_abstraction_rounds_explicit = false;
  // Optionally make that a rate instead: `width / this`, floored at one and
  // capped by the ceiling above. The argument for it is that a blocking
  // lemma rules out one pair of operand values, so what one is worth falls
  // away as the operands widen -- one of 2^16 pairs at eight bits, one of
  // 2^106 at fifty-three -- and a flat allowance therefore means something
  // quite different at either end. A divisor of eight puts a 53-bit
  // multiply at six attempts and a 64-bit one at eight.
  //
  // Zero, which leaves the flat ceiling as the allowance, because the
  // argument did not survive measurement. Over 39 floating-point queries,
  // three interleaved repetitions, at two abstraction widths -- where the
  // rate gives an allowance of four and of three against the flat
  // thirty-two, an eight- to tenfold difference in what is spent:
  //
  //   width 33   flat 65.5s (52-66)   rate 60.7s (55-63)
  //   width 24   flat 112.4s (105-116) rate 110.1s (105-130)
  //
  // Ranges overlap at both, and at 33 the sign flips between repetitions.
  // That is not a result, and a default should not move without one.
  //
  // The likeliest reason it does not matter is the escalation this shares a
  // budget with: once giving up is cheap -- see BVExactEncoder, which is
  // what made the abstraction usable at all -- *when* you give up stops
  // being worth tuning. The corpus is also all binary32, so the widths the
  // rate is really aimed at are not in it; someone with 53- or 64-bit
  // operands may find otherwise, which is why the flag stays.
  unsigned bv_term_abstraction_value_divisor = 0;
  // An independent cap on BVDIV/BVMOD value-pair blocking, after the round
  // ceiling and optional width scaling above have been applied. This
  // separates the experiment callers actually want to run -- four, eight,
  // sixteen or thirty-two divider candidates -- from both multiplication and
  // `bv_term_abstraction_rounds`, which also bounds algebraic-schema
  // refinement. Zero means no additional cap, preserving every established
  // profile and the default allowance exactly.
  //
  // This is a measurement control, not a recommended policy. On a broad
  // 417-query floating-point-heavy population, 4 and 8 were clear regressions
  // and 16 was slower in three interleaved runs. Records frequently settled
  // after 16 bad candidates but before the old allowance, so repetition count
  // by itself could not identify when paying for an exact divider would help.
  unsigned bv_term_abstraction_divmod_value_limit = 0;
  // Escalate an abstracted BVMULT a piece at a time rather than all at once:
  // encode only the bits up to and a little past the lowest one the
  // candidate got wrong, and come back for more if that does not settle the
  // query. The low bits of a truncated product depend only on the low bits
  // of its operands, which is what makes the partial encoding a theorem
  // rather than a guess -- and is why it is BVMULT alone. A quotient's low
  // bits depend on the whole of both operands.
  //
  // Off by default: its benefit has not been measured, and each partial
  // encoding repeats the work for all lower bits.
  bool bv_term_abstraction_inc_bitblast = false;

  // Offer the whole active stack to the exact-stack preprocessor on every
  // check, not only on an explicitly forced first engagement, and offer it
  // stacks carrying plain array reads and floating point rather than plain
  // bit-vectors alone.
  //
  // What this is for: the per-level route encodes each level as it arrives
  // and never simplifies across the stack, so the SAT solver is handed a
  // formula nobody has been over. Measured on one floating-point query, the
  // batch pipeline spends 13ms in the simplifier, constant-bit propagation,
  // unconstrained removal, pure literals and strength reduction, and the
  // search then costs 10.1s; the per-level incremental route skips all five
  // and the same search costs 31.1s. Thirteen milliseconds is worth
  // twenty-one seconds.
  //
  // It is safe to offer speculatively. The trial preprocesses into an
  // assumption-scoped block, adopts it only when the complete DAG at least
  // halves, and otherwise returns before committing a clause or a model
  // definition, leaving the caller to continue down the ordinary path.
  //
  // Off, because what it buys is not one-signed. Over five KLEE sessions
  // driven incrementally from the third query, solver seconds:
  //
  //                             batch   per-level   with this
  //   sqr_longdouble-noflow      14.5        46.9        17.2
  //   sparse_matrices_klee_bug    8.7        53.9        38.4
  //   libmatheval_sym_f           7.3        42.9        40.7
  //   vectors_klee                9.3        31.6        47.0
  //   vectors_klee_bug            8.9        28.5        38.8
  //
  // It nearly closes the gap on the first, narrows it on the next two, and
  // opens it further on the last two -- and never reaches the batch column,
  // because the block is re-encoded per check where the batch pipeline pays
  // for its encoding once. Which of those a session gets is not predictable
  // from anything visible up front, so this is an interface rather than a
  // new default.
  //
  // What it is NOT is a fix for assumptions being weaker than units. That
  // was the other suspect and it is not the cause: the same query asserted
  // at base level and inside a pushed scope costs the same to within noise
  // (1.47s against 1.11s on one, 0.22s against 0.19s on another), while both
  // sit two to three times above the batch pipeline. The gap is the missing
  // simplification and nothing else.
  bool incremental_scoped_preprocessing = false;

  // Run the rewriting passes the batch pipeline runs -- strength reduction
  // over a derived interval domain, and common sub-sum extraction -- on each
  // piece the incremental driver prepares.
  //
  // The driver trades whole-formula simplification for a retained encoding,
  // and those two only conflict because what it retains is the encoding of
  // unsimplified terms. These passes do not force the trade: each is a
  // function of the piece it is handed and of nothing else, so a rewritten
  // piece is equivalent to the piece whatever the rest of the stack says now
  // or asserts later. The result caches beside the rest of preparePiece's
  // work and the encoding built from it stays valid for the session.
  //
  // Unconstrained-variable elimination is deliberately not among them: that
  // one needs to know what the rest of the formula does NOT contain, and a
  // later assertion can make it false.
  //
  // Off, and the reason is the interesting part: the retainable
  // simplification is not the valuable simplification. This buys 8% on one
  // standalone query (1.02s to 0.94s against a batch 0.41s) and nothing at
  // all on the workload it was written for -- four KLEE sessions driven
  // incrementally, solver seconds, plain against with:
  //
  //   sort_smallest_klee        13.1   13.7
  //   count_klee                 2.6    2.7
  //   sort_smallest_klee_bug    17.7   17.7
  //   sparse_matrices_klee_bug  46.5   48.3
  //
  // Nor is the rest of the gap conjuncts being prepared in isolation:
  // handing the driver the whole stack as a single conjunct, so that its own
  // simplification sees everything at once, changes nothing (1.04s against
  // 1.06s) while the batch pipeline is still 2.4x faster on the same
  // formula.
  //
  // What is left is constant-bit propagation over the whole formula,
  // unconstrained-variable elimination, pure literals and bit-vector
  // solving -- every one of them a pass whose conclusions depend on what the
  // formula does NOT contain, and every one therefore invalidated by the
  // next assertion. The driver trades simplification for a retained
  // encoding because for this class of pass the trade is forced. Choosing
  // per session which side of it to be on is the remedy that works.
  bool incremental_piece_rewriting = false;
  // Refine abstracted BVPLUS, BVMULT, BVDIV and BVMOD operations with
  // algebraic facts about every pair of operands whenever the candidate
  // contradicts one. Off restores the former operation-specific fallback:
  // exact addition, or one value-pair blocking lemma for multiplication,
  // division and remainder.
  bool bv_term_abstraction_schemas = true;

  // Which schema families the master switch above may offer. The default is
  // `qualified`, the only mask the corpus qualification justified; the broad
  // profiles are experiments a caller asks for, `all` reproduces the complete
  // experimental stack, and an empty mask leaves the operation-specific
  // fallback exactly as the master switch being off does.
  uint32_t bv_term_abstraction_schema_groups = BV_SCHEMA_GROUP_DEFAULT;
  // Interface bookkeeping, the twin of bv_term_abstraction_rounds_explicit
  // above and for the same reason.
  //
  // A profile is an atomic mask/round pair, and the ceiling half has been the
  // caller's once they name it since the ordering was fixed. The mask half was
  // left last-writer-wins, so the two halves of one pair resolved by opposite
  // rules: naming a ceiling and then choosing a profile kept the ceiling,
  // naming a group list and then choosing a profile lost the list. Whichever
  // rule is right, they should be the same rule, and first-wins is the one
  // that treats a caller's explicit choice as a choice -- which is what
  // vc_setSchemaGroups is: a list of families spelled out by name.
  bool bv_term_abstraction_schema_groups_explicit = false;

  // You can select these with any combination you want of true & false.
  // Variants 1-3 modify the recursive divider. Variant 4 replaces it with a
  // two-stage shift/subtract circuit that per step computes the borrow
  // chain once and reuses those carries for the conditional subtraction,
  // where the recursive circuit pays a full subtractor, a comparison and
  // up to three multiplexer layers per unrolled level: at 226 bits the
  // same division falls from 1,015,894 AIG nodes to 458,106, which is what
  // Bitwuzla's divider costs, and the two-copy fp.div micro query solves
  // three times faster. It is nonetheless off by default: over 311 KLEE
  // binary128 queries the smaller circuit solved 287 against 289 with the
  // recursive one, and on an escalated 256-bit refutation it turns a 39 s
  // proof into minutes -- the borrow chain hides the word-level slices a
  // CDCL refutation of a whole division leans on. Fewer gates is not
  // always an easier formula; the circuit stays selectable for the
  // workloads it does win.
  bool division_variant_1 = true;
  bool division_variant_2 = true;
  bool division_variant_3 = false;
  bool division_variant_4 = false;
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
  // Enabled by default, but only active when native arithmetic is selected.
  bool fp_native_add_iszero = true;

  // Mine simple top-level finite box bounds and use them to omit NaN/infinity
  // cases from native packed-field circuits when those cases are already
  // impossible. This does not enable the separate domain prepass or its
  // known-sign arithmetic specialization.
  bool fp_native_domain = true;

  // Experimental native-domain arithmetic specialization. A known finite
  // semantic sign removes fp.add's opposite-sign cancellation datapath and
  // fp.mul's sign-dependent rounding, while explicit muxes retain signed zero.
  bool fp_native_known_sign = false;

  // Experimental floating-point domain prepass. It mines simple boxed
  // variable bounds from ordered FP comparisons and uses them to discharge
  // non-box ordered comparisons and zero-sum rows whose interval/domain facts
  // decide them.
  bool fp_domain_simplify = false;

  // Decision-only extension of the FP domain prepass. Derive symbol endpoints
  // from top-level symbol/expression inequalities and from a narrowly
  // recognised zero-result addition. The derived facts may discharge
  // comparisons or expose contradictory boxes, but are not emitted as
  // additional constraints. Enabled by default; retain the flag for ablation.
  bool fp_domain_derived_bounds = true;

  // Propagation through an objective over semantic {0, 1} floating-point
  // selector symbols. Replace the objective only when interval exclusion
  // proves each selected endpoint necessary and their conjunction sufficient.
  // Exact extrema are the primary case. Enabled by default; retain the flag
  // so its solver effects can be ablated independently.
  bool fp_domain_extremal_selectors = true;

  // Sound zero-fact extraction for boxed nonnegative FP symbols. It only
  // derives zero facts from same-sign rows whose terms are +/- one boxed
  // symbol. Two-term differences may propagate an already-established zero,
  // but terms are never algebraically cancelled through a rounded row. Zero
  // is encoded as zero magnitude bits so +0/-0 remain distinct. Enabled by
  // default; this does not enable the general floating-point domain rewrite
  // prepass.
  bool fp_domain_sound_zero_facts = true;

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
  //
  // AUTO resolves from the difficulty score when the top level recorded one
  // (see ToSATAIG::bitblast): GIA_LOW below the threshold, NEW_MEDIUM at or
  // above it, because minimising the CNF is itself work and on a large blast
  // it is most of the work, while no measurement has found the smaller
  // formula buying solve time. Where no estimate exists, under array
  // refinement, or on a SAT backend other than CaDiCaL, it falls back to
  // the older choice between VERY_LOW and MEDIUM from the built AIG's size.
  enum CNFEffort
  {
    CNF_EFFORT_VERY_LOW = 0,
    CNF_EFFORT_LOW,
    CNF_EFFORT_MEDIUM,
    CNF_EFFORT_HIGH,
    CNF_EFFORT_VERY_HIGH,
    CNF_EFFORT_AUTO,
    // The in-house Tseitin writer, over the in-house AIG. Below very-low on
    // the scale and last in the enum, which are different facts: the ordinals
    // are the C interface's contract, so a new rung goes on the end however
    // little effort it spends.
    CNF_EFFORT_NEW_VERY_LOW,
    CNF_EFFORT_NEW_LOW,
    CNF_EFFORT_NEW_MEDIUM,

    // Mf_ManGenerateCnf again -- the same generator low, high and very-high
    // reach -- but over a Gia the blaster built itself rather than one
    // converted from an ABC Aig. Same LUT sizes, 3, 6 and 8, so gia-low
    // against low is a comparison of the two backends and nothing else.
    CNF_EFFORT_GIA_LOW,
    CNF_EFFORT_GIA_HIGH,
    CNF_EFFORT_GIA_VERY_HIGH
  };

  // Whether a level blasts through the Gia backend rather than ABC's Aig.
  static bool isGiaEffort(enum CNFEffort e)
  {
    return e == CNF_EFFORT_GIA_LOW || e == CNF_EFFORT_GIA_HIGH ||
           e == CNF_EFFORT_GIA_VERY_HIGH;
  }

  enum CNFEffort cnf_effort = CNF_EFFORT_AUTO;

  // AND-node count at or above which AUTO stops paying for CNF
  // minimisation: against the recorded estimate it selects NEW_MEDIUM
  // there, and on the estimate-less fallback it drops MEDIUM to VERY_LOW.
  //
  // High on purpose. Over a floating-point corpus, timed net of the ~9.5ms a
  // process spends starting before it solves anything, VERY_LOW is the better
  // choice at almost every size -- so the honest reading is that the crossover
  // is a property of the workload rather than a constant, and that this
  // heuristic should only override the effort where the evidence is
  // unambiguous. At 200k it switches the queries whose circuits are large
  // enough for minimising to be most of their cost -- six of the measured set,
  // every one a gain, geometric mean 0.45 -- and leaves everything else alone.
  //
  // A lower threshold measured better on totals and worse on regressions: at
  // 32k, fifteen gains against three losses. A caller who has measured their
  // own workload can move it, from the command line or through the
  // CNF_AUTO_THRESHOLD interface flag.
  unsigned cnf_auto_threshold = 200000;

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
    // Refinement passes that installed something, and individual blocking
    // lemmas they installed. A pass can install more than one lemma.
    uint64_t bv_refinement_rounds = 0;
    uint64_t bv_blocking_lemmas = 0;
    // Algebraic schema lemmas installed over abstracted arithmetic. Counted
    // apart from the blocking lemmas above because the two are not
    // interchangeable: the same number of each says very different things
    // about how a query was decided.
    uint64_t bv_schema_lemmas = 0;
    // Value-pair refinement which reached its allowance and installed the
    // operation's exact circuit. Split by the only two operation families
    // which use that path so a corpus can distinguish a divider problem from
    // a multiplier one without scraping diagnostic prose.
    uint64_t bv_exact_escalations = 0;
    uint64_t bv_exact_escalations_mult = 0;
    uint64_t bv_exact_escalations_divmod = 0;
    // What the refinement's FULL-WIDTH installs cost: an escalation, and the
    // paired DIV/REM recomposition, whose multiplier is as wide as one. The
    // counts above say how often a refinement was abandoned; these say what
    // was handed to the solver when it was. Publishing the totals makes the
    // question answerable from ordinary statistics and the C API rather than
    // only from the per-record fields the benchmark harness reads.
    //
    // Equal escalation counts can hide very different trades: an exact
    // multiplier is affordable where an exact divider may not be. Clauses and
    // variables come from the solver's own totals across the encode rather
    // than a circuit estimate, and microseconds measure only that encode.
    //
    // Wider than the escalations, because the paired identity costs as much as
    // one without any abstraction being given up -- it is why the aggressive
    // profile is the slowest, and leaving it out would have hidden the trade
    // these were added to expose. It is counted here and not in the escalation
    // counts above, which mean something narrower: a refinement that gave up
    // and said what the operation is.
    //
    // What is NOT here is the algebraic schemas, which have their own totals
    // below. They are the thing the profiles vary, so putting them in one
    // bucket with the full-width installs would make exactly the comparison
    // these exist for unreadable.
    uint64_t bv_exact_clauses = 0;
    uint64_t bv_exact_variables = 0;
    uint64_t bv_exact_microseconds = 0;
    // What the algebraic schemas cost, on the same terms.
    //
    // bv_schema_lemmas counts how many were installed, and one lemma is not
    // one price: the hand-written bounds are a comparison chain, the exact
    // prefixes are three columns of a multiplier, and a registry fact like
    // UDIV15 is three barrel shifters spliced through BVExactEncoder -- at
    // 256 bits, 229,374 clauses for that one fact, and 2,376,088 for the whole
    // UDIV registry. A profile is a choice of which schema families to enable,
    // so a schema total that does not say what they cost cannot answer the
    // question the profiles were built to ask, and for a while this one
    // reported nothing at all: the four registry splices went through the same
    // encoder as an escalation and were counted as neither.
    //
    // Written at every schema install, whichever mechanism installs it -- the
    // clause emitters in the refiner and the circuit splices alike -- because
    // which of the two a family happens to use is not something a reader
    // comparing profiles should have to know.
    //
    // Value-pair blocking lemmas are in neither total. They are W clauses over
    // known vectors, so reportRecords derives their cost from the round count
    // rather than measuring it.
    uint64_t bv_schema_clauses = 0;
    uint64_t bv_schema_variables = 0;
    uint64_t bv_schema_microseconds = 0;
    // The same total partitioned by BVSchemaGroup, so a mixed run can be
    // attributed without parsing diagnostic text. Every schema increment
    // must increment exactly one entry here as well.
    uint64_t bv_schema_group_lemmas[BV_SCHEMA_GROUP_COUNT] = {};
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
    // The backend a query gets when no --cryptominisat/--cadical/--minisat
    // was given. The order of preference is CryptoMiniSat, CaDiCaL,
    // MiniSat, and the first of those this build compiled in wins.
    // CryptoMiniSat leads because a build that went to the trouble of
    // linking it meant to use it; CaDiCaL follows because it is the only
    // backend on by default, so it is what a stock build solves with.
    // MiniSat is the last resort and is not guarded: CMakeLists.txt refuses
    // a build with no backend at all, so the fall-through is only reached
    // when MiniSat is the one that is there.
#if STP_BUILD_WITH_CRYPTOMINISAT
    solver_to_use = CRYPTOMINISAT5_SOLVER;
#elif STP_BUILD_WITH_CADICAL
    solver_to_use = CADICAL_SOLVER;
#else
    solver_to_use = MINISAT_SOLVER;
#endif
  }
};
} // end of namespace

#endif
