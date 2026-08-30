/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen, Andrew Teylu
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

#include "main_common.h"

#include <CLI/CLI.hpp>

#include <climits>
#include <initializer_list>
#include <iterator>
#include <string>
#include <vector>

using namespace stp;
using std::cout;
using std::cerr;
using std::endl;

/********************************************************************
 * MAIN FUNCTION:
 *
 * step 0. Parse the input into an ASTVec.
 * step 1. Do BV Rewrites
 * step 2. Bitblasts the ASTNode.
 * step 3. Convert to CNF
 * step 4. Convert to SAT
 * step 5. Call SAT to determine if input is SAT or UNSAT
 ********************************************************************/

class ExtraMain : public Main
{
public:
  int create_and_parse_options(int argc, char** argv);
  void create_options();
  int parse_options(int argc, char** argv);

  CLI::App app;

  // Pure flags, true when given on the command line.
  bool version = false;
  bool disable_simplifications = false;
  bool switch_word = false;
  bool disable_opt_inc = false;
  bool disable_cbitp = false;
  bool disable_equality = false;
  bool size_reducing_only = false;
  bool use_cvc = false;
  bool use_smtlib1 = false;
  bool use_smtlib2 = false;
#ifdef USE_MINISAT
  bool use_simplifying_minisat = false;
  bool use_minisat = false;
#endif
#ifdef USE_CRYPTOMINISAT
  bool use_cryptominisat = false;
#endif
#ifdef USE_CADICAL
  bool use_cadical = false;
#endif

  // Held as text until parse_options() turns it into UserFlags.search_bias.
  std::string search_bias;
  CLI::Option* search_bias_option = nullptr;

  // Likewise for UserFlags.cadical_factor.
  std::string cadical_factor;
#ifdef USE_CADICAL
  CLI::Option* cadical_factor_option = nullptr;
#endif

  // Likewise for UserFlags.incremental_inprobing.
  std::string incremental_inprobing;
#ifdef USE_CADICAL
  CLI::Option* incremental_inprobing_option = nullptr;
#endif

  // Likewise for UserFlags.incremental_mode. This one is a flag rather than
  // an option so that a bare --incremental keeps meaning what it always has;
  // a value has to be attached with '=', which is also what stops it from
  // swallowing the input file.
  std::string incremental;
  CLI::Option* incremental_option = nullptr;

  // Likewise for UserFlags.cnf_effort; always mapped, so it carries the
  // default spelling.
  std::string cnf_effort = "auto";

  // Likewise for the named mask of BV abstraction schema families.
  std::string bv_schema_groups = formatBVSchemaGroups(BV_SCHEMA_GROUP_DEFAULT);

  // A named, atomic schema-mask/refinement-round pair. Empty means the two
  // lower-level options retain their independently parsed values.
  std::string bv_abstraction_profile;

  // Which of the two scope options were actually given. The older MULT
  // switch covers all three nonlinear operations while it is the only one
  // supplied, and DIV/MOD wins once it is named -- in either argument order,
  // which is what makes this a presence check rather than a last-writer one.
  // vc_setInterfaceFlags resolves the same pair the same way, through
  // bv_term_abstraction_divmod_explicit.
  CLI::Option* bv_term_abstraction_mult_option = nullptr;
  CLI::Option* bv_term_abstraction_divmod_option = nullptr;

  // And whether the round ceiling was given, for the same kind of reason:
  // --bv-term-abstraction-profile carries a ceiling of its own, and the two
  // options exclude each other here, so this records what a run named for
  // bv_term_abstraction_rounds_explicit -- which is what the C interface
  // resolves the same pair with, where they do not exclude each other.
  CLI::Option* bv_rounds_option = nullptr;
  // ... and the group list, for the same reason: it is the other half of the
  // pair a profile applies, and resolves the same way.
  CLI::Option* bv_schema_groups_option = nullptr;

  // Tri-state: UserFlags.interactive_read is only overridden when the
  // option was given, so the value needs its own presence check.
  bool interactive = false;
  CLI::Option* interactive_option = nullptr;

  // Likewise for UserFlags.uf_eager_mode. An option rather than a flag: it
  // has no legacy bare spelling to preserve, and an option cannot swallow the
  // input file.
  std::string uf_ackermann;
  CLI::Option* uf_ackermann_option = nullptr;
};

int ExtraMain::create_and_parse_options(int argc, char** argv)
{
  create_options();
  int ret = parse_options(argc, argv);
  if (ret != 0)
  {
    return ret;
  }
  return 0;
}

void ExtraMain::create_options()
{
  app.usage("USAGE: stp [options] <input-file>\n"
            " where input is SMTLIB1/2 or CVC depending on options and file "
            "extension");

  // An empty group hides an option from --help; the input file is
  // positional-only.
  app.add_option("file", infile, "input file")->group("");

  const char* const general_group = "Most important options";
  app.set_help_flag("--help,-h", "print this help")->group(general_group);
  app.add_flag("--version", version, "print version number")
      ->group(general_group);

  const char* const simp_group = "Simplifications";

  // A value-taking bool: accepts 1/0, true/false, on/off, as
  // '--flattening false' or '--flattening=false'. capture_default_str()
  // shows the current UserFlags default in --help.
  auto bool_arg = [this](const char* name, bool& var, const char* desc,
                         const char* group) {
    return app.add_option(name, var, desc)->capture_default_str()->group(group);
  };
  auto int64_arg = [this](const char* name, int64_t& var, const char* desc,
                          const char* group) {
    return app.add_option(name, var, desc)->capture_default_str()->group(group);
  };

  app.add_flag("--disable-simplifications", disable_simplifications,
               "disable all simplifications")
      ->group(simp_group);
  app.add_flag("--switch-word,-w", switch_word, "switch off wordlevel solver")
      ->group(simp_group);
  app.add_flag("--disable-opt-inc,-a", disable_opt_inc,
               "disable rewriting simplifier")
      ->group(simp_group);
  app.add_flag("--disable-cbitp", disable_cbitp,
               "disable constant bit propagation")
      ->group(simp_group);
  app.add_flag("--disable-equality", disable_equality,
               "disable equality propagation")
      ->group(simp_group);
  app.add_flag("--size-reducing-only", size_reducing_only,
               "size reducing simplifications only")
      ->group(simp_group);

  bool_arg("--unconstrained-variable-elimination",
           bm->UserFlags.enable_unconstrained,
           "Unconstrained variables are eliminated.", simp_group);

  int64_arg("--aig-rewrite-passes", bm->UserFlags.AIG_rewrites_iterations,
            "Iterations of AIG rewriting to perform", simp_group);

  bool_arg("--flattening", bm->UserFlags.enable_flatten,
           "Enable sharing-aware flattening of >2 arity nodes", simp_group);

  bool_arg("--rewriting", bm->UserFlags.enable_sharing_aware_rewriting,
           "Enable sharing-aware rewriting", simp_group);

  bool_arg("--split-extracts", bm->UserFlags.enable_split_extracts,
           "Create new variables for some extracts", simp_group);

  bool_arg("--ite-context-simplifications", bm->UserFlags.enable_ite_context,
           "Use what is known to be true in an if-then-else node to simplify "
           "the true or false branches",
           simp_group);

  bool_arg("--aig-core-simplification", bm->UserFlags.enable_aig_core_simplify,
           "Simplify the propositional core with AIGs", simp_group);

  bool_arg("--use-intervals", bm->UserFlags.enable_use_intervals,
           "Simplify with interval analysis", simp_group);

  bool_arg("--pure-literals", bm->UserFlags.enable_pure_literals,
           "Pure literals are replaced.", simp_group);

  bool_arg("--common-subsum", bm->UserFlags.enable_common_subsum,
           "Factor sub-terms shared between n-ary bvadd nodes, and between "
           "n-ary bvmul nodes, into a single shared node, so the adder or "
           "multiplier is built once (needs --flattening)",
           simp_group);

  bool_arg("--pair-extract", bm->UserFlags.enable_pair_extract,
           "In an n-ary bvadd, replace a pair of addends whose possibly-one "
           "bits are disjoint by their bitwise-or, removing an adder stage",
           simp_group);

  bool_arg("--merge-same", bm->UserFlags.enable_merge_same,
           "Uses simple boolean algebra rules to combine conjuncts at the top "
           "level",
           simp_group);

  int64_arg("--size-reducing-fixed-point-limit",
            bm->UserFlags.size_reducing_fixed_point,
            "If the number of non-leaf nodes is fewer than this number, run "
            "size-reducing simplifications to a fixed-point. -1 means always.",
            simp_group);

  bool_arg("--simplify-to-constants-only,--simply_to_constants_only",
           bm->UserFlags.simplify_to_constants_only,
           "Use just the simplifications from the potentially size increasing "
           "suite that transform nodes to constants",
           simp_group);

  bool_arg("--difficulty-reversion,--difficulty_reversion",
           bm->UserFlags.difficulty_reversion,
           "Undo size increasing simplifications if they haven't made the "
           "problem simpler",
           simp_group);

  bool_arg("--distinct-ordering", bm->UserFlags.distinct_ordering,
           "replace a (distinct ...) over variables that occur nowhere else "
           "with a strict chain, which fixes one of the n! equivalent "
           "orderings the bit-blaster would otherwise search. Incremental "
           "solves keep the rewrite behind a retractable root assumption",
           simp_group);

  const char* const solver_group = "SAT Solver options";

#ifdef USE_CADICAL
  app.add_flag("--cadical", use_cadical, "use cadical as the solver")
      ->group(solver_group);
  cadical_factor_option =
      app.add_option("--cadical-factor", cadical_factor,
                     "let cadical use bounded variable addition: 'on' (the "
                     "default), 'off', or 'auto' (on only for problems with "
                     "array operations, which was the default until it was "
                     "measured on bitvector-only problems). Needs a CaDiCaL "
                     "3.x build; otherwise an explicit request is declined "
                     "with a warning")
          ->group(solver_group);
  incremental_inprobing_option =
      app.add_option(
             "--incremental-inprobing", incremental_inprobing,
             "cadical's probe-based inprocessing on the incremental "
             "driver's persistent solver: 'on' (always), 'off' (never), or "
             "'auto' (the default: retired once a session shows many "
             "solves, where re-probing the whole encoding every solve "
             "costs more than it earns)")
          ->group(solver_group);
#endif

#ifdef USE_CRYPTOMINISAT
  app.add_flag("--cryptominisat", use_cryptominisat,
               "use cryptominisat as the solver. Only use CryptoMiniSat 5.0 "
               "or above ")
      ->group(solver_group);
  app.add_option("--threads", bm->UserFlags.num_solver_threads,
                 "Number of threads for cryptominisat")
      ->capture_default_str()
      ->group(solver_group);
#endif

#ifdef USE_MINISAT
  app.add_flag("--simplifying-minisat", use_simplifying_minisat,
               "use installed simplifying minisat version as the solver")
      ->group(solver_group);
  app.add_flag("--minisat", use_minisat,
               "use installed minisat version as the solver ")
      ->group(solver_group);
#endif
  search_bias_option =
      app.add_option("--search-bias", search_bias,
                     "tune the SAT search towards one answer: 'unsat' (best "
                     "for unsatisfiable / verification workloads), 'sat', or "
                     "'none' (the default, leaving the solver at its own "
                     "settings). Solvers with no such setting ignore it")
          ->group(solver_group);

  const char* const refinement_group = "Refinement options";
  app.add_flag("--ackermanize,-r", bm->UserFlags.ackermannisation,
               "eagerly encode array-read axioms (Ackermannistaion)")
      ->group(refinement_group);
  app.add_flag("--array-equality", bm->UserFlags.enable_array_equality,
               "decide whole-array equality/disequality (extensional arrays) "
               "by lemmas on demand")
      ->group(refinement_group);
  bool_arg("--lazy-write-reads", bm->UserFlags.lazy_write_reads,
           "abstract a read over a long write chain to a fresh variable "
           "constrained by refinement lemmas, instead of expanding the "
           "whole if-then-else chain",
           refinement_group);
  int64_arg("--lazy-write-reads-depth",
            bm->UserFlags.lazy_write_reads_depth,
            "may-alias write levels a read still expands eagerly before the "
            "rest of its chain is abstracted",
            refinement_group);
  bool_arg("--bv-eq-abstraction", bm->UserFlags.bv_eq_abstraction,
           "replace wide BV equalities -- whatever their operands; the "
           "bit-blaster proxies non-input ones -- with fresh Boolean "
           "variables during bit-blasting, refining lazily via CEGAR",
           refinement_group);
  app.add_option("--bv-abstraction-width",
                 bm->UserFlags.bv_abstraction_width,
                 "minimum operand width at which --bv-eq-abstraction and "
                 "--bv-term-abstraction abstract an operation")
      ->group(refinement_group)
      ->capture_default_str();
  app.add_option("--bv-eq-refine-width",
                 bm->UserFlags.bv_eq_refine_width,
                 "initial prefix width for lazy BV equality refinement (0 = full)")
      ->group(refinement_group)
      ->capture_default_str();

  bool_arg("--bv-term-abstraction", bm->UserFlags.bv_term_abstraction,
           "abstract wide BVMULT, BVDIV and BVMOD during bit-blasting, "
           "refining lazily via CEGAR; the three options below add the "
           "cheaper kinds",
           refinement_group);
  bool_arg("--bv-term-abstraction-ite", bm->UserFlags.bv_term_abstraction_ite,
           "also abstract wide if-then-else (off: it is noise on bit-vector "
           "workloads and the whole benefit on floating-point ones)",
           refinement_group);
  bool_arg("--bv-term-abstraction-plus", bm->UserFlags.bv_term_abstraction_plus,
           "also abstract wide BVPLUS (off, for the same reason)",
           refinement_group);
  bool_arg("--bv-term-abstraction-compare",
           bm->UserFlags.bv_term_abstraction_compare,
           "also abstract wide inequalities (off, for the same reason)",
           refinement_group);
  bool_arg("--skeleton-preproc", bm->UserFlags.skeleton_preproc,
           "ask the query's propositional skeleton what it forces, and assert "
           "that before solving", refinement_group);
  bool_arg("--embedded-constraints", bm->UserFlags.embedded_constraints,
           "replace an assertion where it occurs inside another assertion",
           refinement_group);
  bv_term_abstraction_mult_option = bool_arg(
      "--bv-term-abstraction-mult", bm->UserFlags.bv_term_abstraction_mult,
      "scope for BVMULT, and for BVDIV and BVMOD unless the separate DIV/MOD "
      "option is also given, which overrides them in either order",
      refinement_group);
  bv_term_abstraction_divmod_option = bool_arg(
      "--bv-term-abstraction-divmod", bm->UserFlags.bv_term_abstraction_divmod,
      "independently override whether BVDIV and BVMOD are abstracted; turning "
      "it off leaves division and remainder encoded exactly from the start",
      refinement_group);
  bool_arg("--bv-term-abstraction-schemas",
           bm->UserFlags.bv_term_abstraction_schemas,
           "refine abstracted BVPLUS, BVMULT, BVDIV and BVMOD operations "
           "with algebraic facts that hold for every pair of operands before "
           "their operation-specific fallback",
           refinement_group);
  bv_schema_groups_option =
      app.add_option("--bv-term-abstraction-schema-groups", bv_schema_groups,
                     "comma-separated schema families allowed by "
                     "--bv-term-abstraction-schemas: base, udiv15, "
                     "udiv-observed, udiv-tail, urem, mul8, mul-ref3, "
                     "mul-tail, add, quotient-thresholds, low-prefix, "
                     "quotient-one-rem, quotient-one-quot, "
                     "divisor-magnitude, or divrem-full; 'all' selects the "
                     "complete experimental stack and 'none' selects no "
                     "schemas; semantic aliases are udiv, mul6, "
                     "quotient-one and divrem-identity")
          ->group(refinement_group)
          ->capture_default_str();
  bv_rounds_option =
      app.add_option("--bv-term-abstraction-rounds",
                     bm->UserFlags.bv_term_abstraction_rounds,
                     "ceiling on the blocking lemmas one abstracted "
                     "BVMULT/BVDIV/BVMOD may take before its refinement "
                     "encodes the operation exactly instead of enumerating "
                     "further operand pairs (0: never; enumerate without "
                     "limit)")
          ->group(refinement_group)
          ->capture_default_str();
  app.add_option("--bv-term-abstraction-profile", bv_abstraction_profile,
                 "apply an atomic schema-mask/round pair: 'qualified' is the "
                 "inherited base, UREM and MulRef3 mask at 32 rounds; "
                 "'broad' adds the observed UDIV and MUL8 facts, "
                 "divisor-magnitude and quotient-one facts at 16 rounds but "
                 "no paired DIV/REM relation; 'aggressive' adds the "
                 "full-width paired DIV/REM identity to that")
      ->group(refinement_group)
      ->excludes(bv_schema_groups_option)
      ->excludes(bv_rounds_option);
  app.add_option("--bv-term-abstraction-value-divisor",
                 bm->UserFlags.bv_term_abstraction_value_divisor,
                 "scale that allowance with the operand width, as "
                 "width/divisor floored at one and capped by the ceiling "
                 "above; a blocking lemma rules out one pair of operand "
                 "values, so what one is worth falls away as the operands "
                 "widen (0, the default: do not scale, which measured no "
                 "slower and no faster)")
      ->group(refinement_group)
      ->capture_default_str();
  app.add_option("--bv-term-abstraction-divmod-value-limit",
                 bm->UserFlags.bv_term_abstraction_divmod_value_limit,
                 "independent cap on BVDIV/BVMOD value-pair blocking after "
                 "the round ceiling and optional width scaling; unlike "
                 "--rounds this changes neither the algebraic-schema budget "
                 "nor BVMULT (0, the default: no additional cap)")
      ->group(refinement_group)
      ->capture_default_str();

  bool_arg("--bv-term-abstraction-inc-bitblast",
           bm->UserFlags.bv_term_abstraction_inc_bitblast,
           "escalate an abstracted BVMULT a piece at a time: encode the bits "
           "up to and a little past the lowest one the candidate got wrong, "
           "rather than the whole width at once",
           refinement_group);

  bool_arg("--incremental-piece-rewriting",
           bm->UserFlags.incremental_piece_rewriting,
           "run the batch pipeline's rewriting passes -- strength reduction "
           "over a derived interval domain, and common sub-sum extraction -- "
           "on each piece the incremental driver prepares; each is a "
           "function of its piece alone, so the result caches and the "
           "encoding built from it stays valid",
           refinement_group);

  bool_arg("--incremental-scoped-preprocessing",
           bm->UserFlags.incremental_scoped_preprocessing,
           "offer the whole active stack to the exact-stack preprocessor on "
           "every incremental check rather than only on a forced first "
           "engagement, and offer it stacks carrying array reads and "
           "floating point rather than plain bit-vectors alone",
           refinement_group);

  app.add_flag("--uninterpreted-functions",
               bm->UserFlags.enable_uninterpreted_functions,
               "decide uninterpreted functions over Bool, bit-vector, "
               "RoundingMode and floating-point sorts by dynamic Ackermann "
               "refinement, including when the input logic omits UF")
      ->group(refinement_group);
  app.add_option("--uf-lemmas-per-round",
                 bm->UserFlags.uf_lemmas_per_round,
                 "how many congruence lemmas one refuted candidate may "
                 "install (0: every conflict it exposes; 1: one conflict "
                 "per round)")
      ->group(refinement_group)
      ->capture_default_str();
  uf_ackermann_option =
      app.add_option("--uf-ackermann", uf_ackermann,
                     "whether to install a function's pairwise congruence "
                     "constraints before the first solve: 'on' (every "
                     "declaration), 'off' (none, so a candidate has to earn "
                     "each lemma), or 'auto' "
                     "(the default: the declarations whose pair count fits "
                     "the budget, cheapest first)")
          ->group(refinement_group);
  app.add_option("--uf-ackermann-budget", bm->UserFlags.uf_eager_budget,
                 "how many congruence constraints --uf-ackermann=auto may "
                 "install up front")
      ->group(refinement_group)
      ->capture_default_str();
  app.add_option("--array-ackermann-budget", bm->UserFlags.array_eager_budget,
                 "how many index comparisons eager array Ackermannisation may "
                 "introduce before read refinement is preferred; 0 selects it "
                 "only when asked for by name")
      ->group(refinement_group)
      ->capture_default_str();
  bool_arg("--uf-phase-hints", bm->UserFlags.uf_phase_hints,
           "bias the first candidate so the congruence checker's scalars "
           "start out pairwise different (advisory; affects search order "
           "only)", refinement_group);
  app.add_option("--uf-sort-width", bm->UserFlags.uf_sort_width,
                 "bit-vector width given to a sort introduced by "
                 "(declare-sort S 0); it bounds how many elements of that "
                 "sort a query can tell apart, so a larger value is always "
                 "sound and only a smaller one is not")
      ->group(refinement_group)
      // Bounded because both ends were reachable and neither failed cleanly.
      // Zero made every element of the sort a zero-width term, which the
      // legacy width checks read as a Boolean -- an abort on an asserting
      // build and a silently retyped model otherwise. The top end overflows
      // the (width + 63) / 64 word arithmetic the bit-vector layer is built
      // on and answered unsat for two elements of an unbounded sort. The
      // ceiling is well above any carrier a query can exhaust: 1024 bits
      // distinguishes more elements than a query can name.
      ->check(CLI::Range(1u, 1024u))
      ->capture_default_str();
  bool_arg("--uf-narrow-results", bm->UserFlags.uf_narrow_results,
           "narrow UF result sorts whose applications are used only for "
           "equality to ceil(log2(N+1)) bits, cutting the AIG cost of each "
           "congruence constraint from O(width) to O(log N)",
           refinement_group);
  bool_arg("--uf-inject-args", bm->UserFlags.uf_inject_args,
           "assume equality-only UF declarations are injective and encode it, "
           "giving the SAT solver bidirectional propagation between argument "
           "and result equalities. The assumption is not entailed by the "
           "query, so it is installed retractably: a refutation that used it "
           "is taken back and the query decided without it. Verdicts are "
           "unchanged; what this buys is faster model-finding on a query "
           "whose functions are injective anyway, and it costs a second "
           "search on one that is not",
           refinement_group);

  const char* const bb_group = "Bit-blasting options";
  bool_arg("--bb.div-v1", bm->UserFlags.division_variant_1,
           "unsigned division encoding variant 1", bb_group);

  bool_arg("--bb.div-v2", bm->UserFlags.division_variant_2,
           "unsigned division encoding variant 2", bb_group);

  bool_arg("--bb.div-v3", bm->UserFlags.division_variant_3,
           "unsigned division encoding variant 3", bb_group);

  bool_arg("--bb.add-v1", bm->UserFlags.adder_variant,
           "addition encoding variant 1", bb_group);

  bool_arg("--bb.add-v2", bm->UserFlags.bvplus_variant,
           "addition encoding variant 2", bb_group);

  bool_arg("--bb.vle-v1", bm->UserFlags.bbbvle_variant,
           "comparison encoding variant 1", bb_group);

  int64_arg("--bb.mult-variant", bm->UserFlags.multiplication_variant,
            "unsigned multiplication encoding. 1 (default) shifts and adds. "
            "14 is 1, except that a multiplier holding a run of constant one "
            "bits is Booth recoded. 15 is radix-4 modified Booth, which halves "
            "the partial-product rows and recodes symbolic multipliers too. "
            "16 chooses between 14 and 15 for each multiply. "
            "3, 4, 6, 7, 8, 9 and 13 Booth recode and differ in how the "
            "partial-product columns are summed. 5 uses the constant-bit "
            "multiplication bounds, and needs --bb.mult-v2. Any other value "
            "is an error, reported once bit-blasting reaches a multiply",
            bb_group);

  bool_arg("--bb.mult-v2", bm->UserFlags.upper_multiplication_bound,
           "unsigned multiplication variant 2", bb_group);

  bool_arg("--bb.conjoin-constant", bm->UserFlags.conjoin_to_top,
           "When constant-bit propagation detects a constant bit during AIG "
           "construction, assert the AIG node and replace it, in the AIG, by "
           "the constant bit",
           bb_group);

  bool_arg("--bb.fp-native-cmp", bm->UserFlags.fp_native_cmp,
           "Bit-blast floating-point predicates (comparisons, equalities, "
           "classifications) over already-packed operands natively instead of "
           "via the SymFPU unpacking circuits",
           bb_group);

  bool_arg("--bb.fp-native-arith", bm->UserFlags.fp_native_arith,
           "Bit-blast fp.add and fp.mul under surviving native predicates "
           "with the hand-written packed-operand circuits instead of the "
           "SymFPU unpacking circuits (experimental)",
           bb_group);

  bool_arg("--bb.fp-native-add-iszero",
           bm->UserFlags.fp_native_add_iszero,
           "Encode fp.isZero(fp.add ...) directly from its operands without "
           "constructing the complete rounded sum (enabled by default; "
           "works with both SymFPU and native arithmetic)",
           bb_group);

  bool_arg("--bb.fp-native-domain", bm->UserFlags.fp_native_domain,
           "Mine simple finite box bounds and omit NaN/infinity cases that "
           "are impossible under those top-level facts (enabled by default)",
           bb_group);

  bool_arg("--bb.fp-native-known-sign",
           bm->UserFlags.fp_native_known_sign,
           "Use finite semantic-sign facts in native fp.add/fp.mul to omit "
           "opposite-sign/sign-dependent circuitry while preserving signed "
           "zero (experimental; requires --bb.fp-native-domain)",
           bb_group);

  bool_arg("--fp-domain-simplify", bm->UserFlags.fp_domain_simplify,
           "Experimental FP prepass: mine boxed variable bounds, use boxed FP "
           "domain facts, and discharge ordered FP "
           "comparisons or zero-sum rows decided by those facts",
           bb_group);

  bool_arg("--fp-domain-derived-bounds",
           bm->UserFlags.fp_domain_derived_bounds,
           "Decision-only FP prepass (enabled by default): derive finite "
           "symbol bounds from top-level symbol/expression relations and "
           "zero-result additions, then discharge comparisons or "
           "contradictory boxes",
           bb_group);

  bool_arg("--fp-domain-extremal-selectors",
           bm->UserFlags.fp_domain_extremal_selectors,
           "FP prepass (enabled by default): replace an objective by "
           "necessary semantic {0,1} selector values only after proving "
           "their conjunction sufficient (primarily exact extrema)",
           bb_group);

  bool_arg("--fp-domain-sound-zero-facts",
           bm->UserFlags.fp_domain_sound_zero_facts,
           "Derive sound zero facts from "
           "association-safe same-sign boxed +/-1 rows and encode them as "
           "zero magnitude bits, preserving the +0/-0 distinction (enabled "
           "by default; does not enable --fp-domain-simplify)",
           bb_group);

  bool_arg("--fp-domain-row-bounds", bm->UserFlags.fp_domain_row_bounds,
           "Experimental FP prepass: recognise linear FP zero rows and "
           "rewrite them to false when association-preserving target-format "
           "interval endpoints exclude zero",
           bb_group);

  bool_arg("--bb.simplify-during-bb", bm->UserFlags.simplify_during_BB_flag,
           "When bit-blasting discovers that a non-constant child of a term "
           "blasts to an all-constant vector, rebuild the term with that "
           "constant and re-run the word-level term simplifier on it. Needs "
           "the rewriting simplifier, so not with --disable-opt-inc or "
           "--disable-simplifications",
           bb_group);

  int64_arg("--aig-node-budget", bm->UserFlags.aig_node_budget,
            "Number of AIG AND gates after which one query's bit-blast gives "
            "up. -1 means never, 0 means give up without blasting. Exceeding "
            "it abandons the query through the soft-timeout path, so the "
            "answer is the one --max-time gives -- \"unknown\" in SMT-LIB "
            "mode, with (get-info :reason-unknown) naming this budget, and "
            "\"Unknown.\" in the CVC language. "
            "Batch solves only: the incremental encoder's AIG outlives the "
            "check that grew it and is never capped, so engaging it with a "
            "budget set warns once instead. Bounds the blast, not the "
            "process -- CNF conversion and the SAT search allocate on top "
            "of it",
            bb_group);

  const char* const print_group = "Printing options";
  app.add_flag("--print-stpinput,-b", bm->UserFlags.print_STPinput_back_flag,
               "print STP input back to cout")
      ->group(print_group);
  app.add_flag("--print-back-CVC", bm->UserFlags.print_STPinput_back_CVC_flag,
               "print input in CVC format, then exit")
      ->group(print_group);
  app.add_flag("--print-back-SMTLIB2",
               bm->UserFlags.print_STPinput_back_SMTLIB2_flag,
               "print input in SMT-LIB2 format, then exit")
      ->group(print_group);
  app.add_flag("--print-back-GDL", bm->UserFlags.print_STPinput_back_GDL_flag,
               "print AiSee's graph format, then exit")
      ->group(print_group);
  app.add_flag("--print-back-dot", bm->UserFlags.print_STPinput_back_dot_flag,
               "print dotty/neato's graph format, then exit")
      ->group(print_group);
  app.add_flag("--print-counterex,-p", bm->UserFlags.print_counterexample_flag,
               "print counterexample")
      ->group(print_group);
  app.add_flag("--print-counterexbin,-y", bm->UserFlags.print_binary_flag,
               "print counterexample in binary")
      ->group(print_group);
  app.add_flag("--print-arrayval,-q",
               bm->UserFlags.print_arrayval_declaredorder_flag,
               "print arrayval declared order")
      ->group(print_group);
  app.add_flag("--print-functionstat,-s", bm->UserFlags.stats_flag,
               "print function statistics")
      ->group(print_group);
  app.add_flag("--print-quickstat,-t", bm->UserFlags.quick_statistics_flag,
               "print quick statistics")
      ->group(print_group);
  app.add_flag("--print-nodes,-v", bm->UserFlags.print_nodes_flag,
               "print nodes ")
      ->group(print_group);
  app.add_flag("--print-output,-n", bm->UserFlags.print_output_flag,
               "Print output")
      ->group(print_group);

  const char* const input_group = "Input options";
  app.add_flag("--SMTLIB1,-m", use_smtlib1, "use the SMT-LIB1 format parser")
      ->group(input_group);
  app.add_flag("--SMTLIB2", use_smtlib2, "use the SMT-LIB2 format parser")
      ->group(input_group);
  app.add_flag("--CVC", use_cvc, "use the CVC format parser")
      ->group(input_group);

  const char* const output_group = "Output options";
  app.add_flag("--output-CNF", bm->UserFlags.output_CNF_flag,
               "Save the CNF into output_[0..n].cnf. NOTE: variables cannot "
               "be mapped back, and problems solved by the preprocessing "
               "simplifier alone will not generate any CNF as the SAT solver "
               "is never invoked")
      ->group(output_group);

  const char* const misc_group = "Miscellaneous options";
  app.add_option("--cnf-auto-threshold", bm->UserFlags.cnf_auto_threshold,
                 "AIG AND-node count at or above which --cnf-generation-effort "
                 "auto drops from medium to very-low")
      ->capture_default_str()
      ->group(misc_group);
  app.add_option("--cnf-generation-effort", cnf_effort,
                 "effort spent minimising the CNF: auto, very-low, low, "
                 "medium, high, very-high, new-very-low, new-low, new-medium. "
                 "Higher is slower to "
                 "generate but yields a smaller CNF; auto picks between "
                 "very-low and medium from the size of the AIG, since "
                 "minimising a large one costs more than the solver saves, "
                 "and gia-low when --bv-term-abstraction is on. "
                 "The new-* rungs blast through STP's own AIG instead of "
                 "ABC's and write the CNF directly: new-very-low is plain "
                 "Tseitin, new-low recovers XOR and if-then-else, new-medium "
                 "also collapses n-ary ANDs and ORs. The gia-* rungs are low, "
                 "high and very-high again, reaching the same generator over "
                 "a Gia the blaster built rather than one converted from an "
                 "ABC AIG")
      ->capture_default_str()
      ->group(misc_group);

  app.add_flag("--exit-after-CNF", bm->UserFlags.exit_after_CNF,
               "exit after the CNF has been generated")
      ->group(misc_group);

  app.add_flag("--parse-only", bm->UserFlags.parse_only,
               "exit after parsing the input, without solving")
      ->group(misc_group);

  interactive_option =
      app.add_option("--interactive", interactive,
                     "read the input a character at a time, as needed when "
                     "driving stp interactively over a pipe. Off reads in "
                     "blocks, which is faster. Default: on when reading from "
                     "stdin, off when reading from a file. SMT-LIB2 only.")
          ->group(misc_group);

  incremental_option =
      app.add_flag("--incremental{on}", incremental,
                   "whether to solve incrementally -- keeping the SAT solver "
                   "and the bit-blasted encoding across (check-sat) commands, "
                   "asserting retractable formulas as SAT assumptions: 'on' "
                   "(from the first solve, pushes or no pushes), 'off' (never, "
                   "not even for an input that pushes), or 'auto' (the "
                   "default: an input that pushes switches it on for itself). "
                   "A bare --incremental means 'on'; a value must be attached "
                   "with '=' rather than spelled as a separate argument. "
                   "SMT-LIB2 only.")
          ->group(misc_group);

  int64_arg("--incremental-auto-engage-at",
            bm->UserFlags.incremental_auto_engage_at,
            "real-solve ordinal at which an automatically incremental "
            "SMT-LIB session engages the persistent driver; -1 uses the "
            "theory default (QF_BV/QF_ABV: 32, others: 3), 1 engages on "
            "the first solve, and 0 never engages automatically "
            "(--incremental=on still engages at 1, and --incremental=off "
            "engages never)",
            misc_group);

  app.add_flag("--incremental-profile", bm->UserFlags.incremental_profile,
               "print fine-grained per-check and cumulative timings and "
               "work counters for the incremental driver (use with "
               "--incremental=on to profile from the first check)")
      ->group(misc_group);

  app.add_flag("--incremental-core-only",
               bm->UserFlags.incremental_core_only,
               "run the minimal persistent assumption/refinement core "
               "without fitted preprocessing, promotion, or adaptive "
               "backend policies; memory-relief rebuilding remains active")
      ->group(misc_group);

  app.add_flag("--incremental-cbp-reset", bm->UserFlags.incremental_cbp_reset,
               "use reset and prefix re-feed instead of CBP level rollback "
               "on stack divergence (diagnostic oracle)")
      ->group(misc_group);

  int64_arg("--incremental-cbp-bootstrap-limit",
            bm->UserFlags.incremental_cbp_bootstrap_limit,
            "on a first incremental solve forced by --incremental=on, defer "
            "the cross-level CBP bootstrap when the assertion stack exceeds "
            "this many DAG nodes. 0 disables the deferral.",
            misc_group);

  int64_arg("--incremental-cbp-feed-cap", bm->UserFlags.incremental_cbp_feed_cap,
            "how many DAG nodes the cross-level CBP engine may retain for "
            "the live stack before it stops accepting levels; the charge is "
            "refunded when a level pops.",
            misc_group);

  int64_arg("--incremental-base-resimplify-limit",
            bm->UserFlags.incremental_base_resimplify_limit,
            "skip the whole-base semantic pass a relief rebuild runs when "
            "the base exceeds this many DAG nodes; the raw base is "
            "re-encoded instead. 0 always skips it.",
            misc_group);

  int64_arg("--incremental-reencode-limit",
            bm->UserFlags.incremental_reencode_limit,
            "rebuild the incremental solver from the live assertion stack "
            "once its variable count passes this limit and most encodings "
            "belong to popped content. 0 disables the rebuild.",
            misc_group);

  int64_arg("--incremental-semantic-cache-limit",
            bm->UserFlags.incremental_semantic_cache_limit,
            "rotate the complete incremental encoding epoch once semantic "
            "caches pass this approximate DAG-node charge and an exact "
            "retained/live graph check finds mostly popped content. 0 "
            "disables this trigger.",
            misc_group);

  app.add_flag("--incremental-promote-units,!--no-incremental-promote-units",
               bm->UserFlags.incremental_promote_units,
               "promote long-stable pushed levels to permanent unit "
               "clauses on the incremental driver; retracting a promoted "
               "level restarts its solver")
      ->group(misc_group);

  int64_arg("--max-num-confl,--max_num_confl,-g",
            bm->UserFlags.timeout_max_conflicts,
            "Number of conflicts after which the SAT solver gives up. "
            "-1 means never, 0 means give up without searching.",
            misc_group);

  int64_arg("--max-time,--max_time,-k", bm->UserFlags.timeout_max_time,
            "Number of seconds after which the SAT solver gives up. The "
            "budget is for the whole query, not for each call into the SAT "
            "solver. -1 means never, 0 means give up without searching.",
            misc_group);

  app.add_flag("--check-sanity,-d", bm->UserFlags.check_counterexample_flag,
               "construct counterexample and check it")
      ->group(misc_group);

  // ---------------------------------------------------------------------
  // Combinations where one option discards another's effect
  // ---------------------------------------------------------------------
  // Each pair below is one STP cannot honour both halves of: whichever the
  // code happens to apply last wins, and the other request never reaches the
  // solver. Reporting that is more useful than obeying half a command line,
  // most of all for the generated ones that option sweeps and build scripts
  // produce, where a silently dropped flag reads as a measurement.
  //
  // The options are looked up by name so that the definitions above stay as
  // they were; get_option() throws if a name here stops matching one, so
  // renaming an option cannot quietly drop its relationships.
  //
  // CLI11 tests whether an option was given, not what it was set to, so
  // '--disable-simplifications --flattening false' is refused as well, even
  // though the two agree. That is the same mistake in a milder form -- the
  // second option still had no bearing on the run -- and treating it the same
  // way keeps the rule to one sentence.
  //
  // Deliberately not here: the CVC/SMT-LIB1/SMT-LIB2 parser flags, which
  // parse_options() already rejects with a message of their own, and
  // --search-bias, documented as ignored by solvers that have no such setting
  // rather than as an error.
  auto excludes_all = [this](const std::string& name,
                             std::initializer_list<const char*> others) {
    CLI::Option* const option = app.get_option(name);
    for (const char* other : others)
    {
      option->excludes(app.get_option(other));
    }
  };

  // The solver flags are not applied in the order given: parse_options()
  // consults them in a fixed sequence, so 'stp --cadical --minisat' quietly
  // ran CaDiCaL. Only one of them can be meant. Which ones exist depends on
  // what was compiled in.
  std::vector<std::string> solver_flags;
#ifdef USE_CADICAL
  solver_flags.emplace_back("--cadical");
#endif
#ifdef USE_CRYPTOMINISAT
  solver_flags.emplace_back("--cryptominisat");
#endif
#ifdef USE_MINISAT
  solver_flags.emplace_back("--simplifying-minisat");
  solver_flags.emplace_back("--minisat");
#endif

  for (auto first = solver_flags.begin(); first != solver_flags.end(); ++first)
  {
    CLI::Option* const option = app.get_option(*first);
    for (auto second = std::next(first); second != solver_flags.end(); ++second)
    {
      option->excludes(app.get_option(*second));
    }
  }

#ifdef USE_CRYPTOMINISAT
  // A thread count is read only by CryptoMiniSat, so asking for one while
  // selecting a different solver gets neither threads nor a warning.
  //
  // --cadical-factor is deliberately not treated the same way: it is a
  // request CaDiCaL may decline with a warning rather than a setting that
  // must apply, and tests/query-files/CMakeLists.txt sweeps the whole corpus
  // with it appended to every invocation, so an exclusion would fail every
  // test in that run that names a solver.
  CLI::Option* const threads_option = app.get_option("--threads");
  for (const std::string& flag : solver_flags)
  {
    if (flag != "--cryptominisat")
    {
      threads_option->excludes(app.get_option(flag));
    }
  }
#endif

  // disableSimplifications() clears each of these after the command line has
  // been read, so a request for one alongside it never takes effect.
  excludes_all("--disable-simplifications",
               {"--switch-word", "--disable-opt-inc", "--disable-cbitp",
                "--disable-equality", "--unconstrained-variable-elimination",
                "--flattening", "--rewriting", "--split-extracts",
                "--ite-context-simplifications", "--use-intervals",
                "--pure-literals", "--common-subsum", "--pair-extract",
                "--merge-same", "--distinct-ordering"});

  // Likewise for what disableSizeIncreasingSimplifications() forces.
  excludes_all("--size-reducing-only",
               {"--simplify-to-constants-only",
                "--ite-context-simplifications", "--difficulty-reversion"});

  // The rewriting simplifier has to be on for this to do anything.
  excludes_all("--bb.simplify-during-bb",
               {"--disable-opt-inc", "--disable-simplifications"});

  // --parse-only stops before the SAT solver is reached, so there is never a
  // CNF for these two to write out or exit after.
  excludes_all("--parse-only", {"--output-CNF", "--exit-after-CNF"});

  // interactive_read is consulted only on the SMT-LIB2 path.
  excludes_all("--interactive", {"--CVC", "--SMTLIB1"});
}

int ExtraMain::parse_options(int argc, char** argv)
{
  try
  {
    app.parse(argc, argv);
  }
  catch (const CLI::CallForHelp&)
  {
    cout << app.help();
    exit(0);
  }
  catch (const CLI::ParseError& e)
  {
    cerr << "Error: " << e.what() << endl;
    cerr << "Please give '--help' to get help" << endl;
    exit(-1);
  }

  // The command line cannot reach the profile-versus-ceiling conflict at all
  // -- the two options exclude each other -- but a run that named the ceiling
  // records it anyway, so the flag means the same thing whichever front end
  // set it. Likewise for the group list, which is the other half of the same
  // pair and now resolves by the same rule.
  if (bv_rounds_option->count() != 0)
    bm->UserFlags.bv_term_abstraction_rounds_explicit = true;
  if (bv_schema_groups_option->count() != 0)
    bm->UserFlags.bv_term_abstraction_schema_groups_explicit = true;

  if (bv_term_abstraction_divmod_option->count() != 0)
    bm->UserFlags.bv_term_abstraction_divmod_explicit = true;
  else if (bv_term_abstraction_mult_option->count() != 0)
    bm->UserFlags.bv_term_abstraction_divmod =
        bm->UserFlags.bv_term_abstraction_mult;

  {
    std::string error;
    if (!parseBVSchemaGroups(bv_schema_groups,
                             bm->UserFlags.bv_term_abstraction_schema_groups,
                             error))
    {
      cerr << "ERROR: --bv-term-abstraction-schema-groups: " << error << endl;
      return -1;
    }
  }

  if (!bv_abstraction_profile.empty())
  {
    std::string error;
    if (!parseBVTermAbstractionProfile(
            bv_abstraction_profile,
            bm->UserFlags.bv_term_abstraction_schema_groups,
            bm->UserFlags.bv_term_abstraction_rounds, error))
    {
      cerr << "ERROR: --bv-term-abstraction-profile: " << error << endl;
      return -1;
    }
  }

  onePrintBack = bm->UserFlags.get_print_output_at_all();

  if (disable_opt_inc)
  {
    bm->UserFlags.optimize_flag = false;
  }

  if (switch_word)
  {
    bm->UserFlags.wordlevel_solve_flag = false;
  }

  if (disable_cbitp)
  {
    bm->UserFlags.bitConstantProp_flag = false;
  }

  if (interactive_option->count())
  {
    bm->UserFlags.interactive_read = interactive ? 1 : 0;
  }

  if (cnf_effort == "very-low")
    bm->UserFlags.cnf_effort = UserDefinedFlags::CNF_EFFORT_VERY_LOW;
  else if (cnf_effort == "low")
    bm->UserFlags.cnf_effort = UserDefinedFlags::CNF_EFFORT_LOW;
  else if (cnf_effort == "medium")
    bm->UserFlags.cnf_effort = UserDefinedFlags::CNF_EFFORT_MEDIUM;
  else if (cnf_effort == "high")
    bm->UserFlags.cnf_effort = UserDefinedFlags::CNF_EFFORT_HIGH;
  else if (cnf_effort == "very-high")
    bm->UserFlags.cnf_effort = UserDefinedFlags::CNF_EFFORT_VERY_HIGH;
  else if (cnf_effort == "auto")
    bm->UserFlags.cnf_effort = UserDefinedFlags::CNF_EFFORT_AUTO;
  else if (cnf_effort == "new-very-low")
    bm->UserFlags.cnf_effort = UserDefinedFlags::CNF_EFFORT_NEW_VERY_LOW;
  else if (cnf_effort == "new-low")
    bm->UserFlags.cnf_effort = UserDefinedFlags::CNF_EFFORT_NEW_LOW;
  else if (cnf_effort == "new-medium")
    bm->UserFlags.cnf_effort = UserDefinedFlags::CNF_EFFORT_NEW_MEDIUM;
  else if (cnf_effort == "gia-low")
    bm->UserFlags.cnf_effort = UserDefinedFlags::CNF_EFFORT_GIA_LOW;
  else if (cnf_effort == "gia-high")
    bm->UserFlags.cnf_effort = UserDefinedFlags::CNF_EFFORT_GIA_HIGH;
  else if (cnf_effort == "gia-very-high")
    bm->UserFlags.cnf_effort = UserDefinedFlags::CNF_EFFORT_GIA_VERY_HIGH;
  else
  {
    std::cerr << "Unknown --cnf-generation-effort value '" << cnf_effort
              << "'. Expected one of: auto, very-low, low, medium, high, "
                 "very-high, new-very-low, new-low, new-medium, gia-low, "
                 "gia-high, gia-very-high."
              << std::endl;
    return -1;
  }

  int selected_type = 0;
  if (use_cvc)
  {
    selected_type++;
    bm->UserFlags.smtlib1_parser_flag = false;
    bm->UserFlags.smtlib2_parser_flag = false;
  }

  if (use_smtlib2)
  {
    selected_type++;
    bm->UserFlags.smtlib1_parser_flag = false;
    bm->UserFlags.smtlib2_parser_flag = true;
  }

  if (use_smtlib1)
  {
    selected_type++;
    bm->UserFlags.smtlib1_parser_flag = true;
    bm->UserFlags.smtlib2_parser_flag = false;
  }

  if (selected_type > 1)
  {
    cerr << "ERROR: You have selected more than one parsing option from "
            "CVC/SMTLIB1/SMTLIB2"
         << endl;
    std::exit(-1);
  }

  if (selected_type == 0)
  {
    bm->UserFlags.smtlib2_parser_flag = true;
  }

#ifdef USE_MINISAT
  if (use_simplifying_minisat)
  {
    bm->UserFlags.solver_to_use = UserDefinedFlags::SIMPLIFYING_MINISAT_SOLVER;
  }

  if (use_minisat)
  {
    bm->UserFlags.solver_to_use = UserDefinedFlags::MINISAT_SOLVER;
  }
#endif

#ifdef USE_CRYPTOMINISAT
  if (use_cryptominisat)
  {
    bm->UserFlags.solver_to_use = UserDefinedFlags::CRYPTOMINISAT5_SOLVER;
  }
#endif

#ifdef USE_CADICAL
  if (use_cadical)
  {
    bm->UserFlags.solver_to_use = UserDefinedFlags::CADICAL_SOLVER;
  }
#endif

  if (search_bias_option->count())
  {
    if (search_bias == "sat")
      bm->UserFlags.search_bias = SearchBias::SAT;
    else if (search_bias == "unsat")
      bm->UserFlags.search_bias = SearchBias::UNSAT;
    else if (search_bias == "none")
      bm->UserFlags.search_bias = SearchBias::NONE;
    else
    {
      cerr << "ERROR: --search-bias must be one of 'sat', 'unsat' or 'none'"
           << endl;
      std::exit(-1);
    }
  }

#ifdef USE_CADICAL
  if (cadical_factor_option->count())
  {
    bm->UserFlags.cadical_factor_explicit = true;
    if (cadical_factor == "on")
      bm->UserFlags.cadical_factor = UserDefinedFlags::BVAMode::ON;
    else if (cadical_factor == "off")
      bm->UserFlags.cadical_factor = UserDefinedFlags::BVAMode::OFF;
    else if (cadical_factor == "auto")
      bm->UserFlags.cadical_factor = UserDefinedFlags::BVAMode::AUTO;
    else
    {
      cerr << "ERROR: --cadical-factor must be one of 'on', 'off' or 'auto'"
           << endl;
      std::exit(-1);
    }
  }

  if (incremental_inprobing_option->count())
  {
    if (incremental_inprobing == "on")
      bm->UserFlags.incremental_inprobing = UserDefinedFlags::BVAMode::ON;
    else if (incremental_inprobing == "off")
      bm->UserFlags.incremental_inprobing = UserDefinedFlags::BVAMode::OFF;
    else if (incremental_inprobing == "auto")
      bm->UserFlags.incremental_inprobing = UserDefinedFlags::BVAMode::AUTO;
    else
    {
      cerr << "ERROR: --incremental-inprobing must be one of 'on', 'off' "
              "or 'auto'"
           << endl;
      std::exit(-1);
    }
  }
#endif

  if (uf_ackermann_option->count())
  {
    typedef UserDefinedFlags::UFEagerMode Mode;
    if (uf_ackermann == "on")
      bm->UserFlags.uf_eager_mode = Mode::ON;
    else if (uf_ackermann == "off")
      bm->UserFlags.uf_eager_mode = Mode::OFF;
    else if (uf_ackermann == "auto")
      bm->UserFlags.uf_eager_mode = Mode::AUTO;
    else
    {
      cerr << "ERROR: --uf-ackermann must be one of 'on', 'off' or 'auto'"
           << endl;
      std::exit(-1);
    }
  }

  if (incremental_option->count())
  {
    if (incremental == "on")
      bm->UserFlags.incremental_mode = UserDefinedFlags::IncrementalMode::ON;
    else if (incremental == "off")
      bm->UserFlags.incremental_mode = UserDefinedFlags::IncrementalMode::OFF;
    else if (incremental == "auto")
      bm->UserFlags.incremental_mode = UserDefinedFlags::IncrementalMode::AUTO;
    else
    {
      cerr << "ERROR: --incremental must be one of 'on', 'off' or 'auto', "
              "attached with '=' (a bare --incremental means 'on')"
           << endl;
      std::exit(-1);
    }
  }

  // A flag's value has to be attached, so 'stp --incremental off' parses as
  // --incremental (which means 'on') followed by an input file named 'off' --
  // the opposite of what was asked for, reported as "Cannot open off", which
  // names neither half of the mistake.
  if (incremental_option->count() &&
      (infile == "on" || infile == "off" || infile == "auto"))
  {
    cerr << "ERROR: --incremental takes its value attached with '=', as "
            "--incremental="
         << infile
         << "; given as a separate argument it was read as the name of the "
            "input file"
         << endl;
    std::exit(-1);
  }

  /*
   * -1 is the only negative value with a meaning ("no limit"); anything more
   * negative than that is a mistake, and silently treating it as unlimited
   * hides it.
   */
  if (bm->UserFlags.timeout_max_conflicts < -1)
  {
    cerr << "ERROR: --max-num-confl must be -1 (no limit) or greater" << endl;
    std::exit(-1);
  }

  if (bm->UserFlags.timeout_max_time < -1)
  {
    cerr << "ERROR: --max-time must be -1 (no limit) or greater" << endl;
    std::exit(-1);
  }

  if (bm->UserFlags.aig_node_budget < -1)
  {
    cerr << "ERROR: --aig-node-budget must be -1 (no limit) or greater"
         << endl;
    std::exit(-1);
  }

  // The AND-gate counter the budget is compared against is ABC's
  // Aig_Man_t::nObjs[], an int. A budget it can never reach would be a cap
  // that silently never fires, which is worse than no cap at all.
  if (bm->UserFlags.aig_node_budget > INT_MAX)
  {
    cerr << "ERROR: --aig-node-budget must be at most " << INT_MAX
         << "; larger caps can never be reached" << endl;
    std::exit(-1);
  }

  if (bm->UserFlags.incremental_base_resimplify_limit < 0)
  {
    cerr << "ERROR: --incremental-base-resimplify-limit must be 0 or greater"
         << endl;
    std::exit(-1);
  }

  if (bm->UserFlags.incremental_cbp_feed_cap < 1)
  {
    cerr << "ERROR: --incremental-cbp-feed-cap must be at least 1" << endl;
    std::exit(-1);
  }

  if (bm->UserFlags.incremental_auto_engage_at < -1)
  {
    cerr << "ERROR: --incremental-auto-engage-at must be -1 (theory "
            "default), 0 (never), or greater"
         << endl;
    std::exit(-1);
  }

  if (disable_simplifications)
  {
    bm->UserFlags.disableSimplifications();
  }

  if (size_reducing_only)
  {
    bm->UserFlags.disableSizeIncreasingSimplifications();
  }

  if (disable_equality)
  {
    bm->UserFlags.propagate_equalities = false;
  }

  if (selected_type == 0)
  {
    // No parser is explicity requested.
    check_infile_type();
  }

  if (version)
  {
    printVersionInfo();
    exit(0);
  }

  return 0;
}

int main(int argc, char** argv)
{
  ExtraMain main;
  return main.main(argc, argv);
}
