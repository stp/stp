#!/bin/bash
#
# Differential fuzzing of STP against a trusted reference solver.
#
# Each iteration generates a batch of random problems with FuzzSMT, then runs
# STP -- under a randomly chosen option setting -- and the reference solver on
# each problem file individually, both under a short wall-clock timeout. A
# file is skipped unless both solvers finish and the checker answered
# sat/unsat; a file where the answers then differ is copied aside with both
# outputs. An STP crash counts: it truncates or garbles STP's answer, so it
# differs from the answer the checker gave.
#
# Runs until interrupted. Use fuzz.sh to run several copies in parallel.
#
# Usage: fuzz_single.sh [working-directory]
#
# The working directory defaults to a fresh temporary directory. It is wiped of
# *.smt2 files on startup and between iterations, so give it a directory of its
# own. Putting it on a tmpfs (/dev/shm) keeps the generated files off disk.
#
# Environment:
#   STP           STP binary. Default: the first of build_static_debug/stp,
#                 build/stp, build-debug/stp, build-release/stp in the source
#                 tree, else stp on PATH. A build with assertions enabled finds
#                 more, which is why the release directory comes last.
#   CHECKER       Reference solver, invoked as "$CHECKER file.smt2".
#                 Default: bitwuzla. Anything that prints one sat/unsat line
#                 per query and understands the bit-vector overflow
#                 predicates works; z3 5.0.0 and bitwuzla 0.9.1 were both
#                 checked. This is probed at startup, because a solver that
#                 gets it wrong turns every file into a bogus mismatch --
#                 z3 4.8.12 and boolector 3.0.1 both fail it, the latter on
#                 bvnego.
#
#                 A slow checker costs coverage rather than correctness:
#                 files it cannot answer inside TIMEOUT are skipped, and the
#                 checker's speed decides how much of the hard tail gets
#                 checked at all. That is what makes bitwuzla the default --
#                 on the floating-point-array files that crashed a pre-fix
#                 build it answers about 4 in 5 inside 10s where z3 5.0.0
#                 answers essentially none, so with z3 those crashes would
#                 be skipped as checker timeouts rather than reported.
#   FUZZSMT_JAR   fuzzsmt.jar, from the FuzzSMT release of Brummayer and Biere,
#                 "Fuzzing and Delta-Debugging SMT Solvers" (SMT'09).
#                 Default: searched for next to the source tree and in $HOME.
#   LOGICS        Logics to generate, with the FuzzSMT options that go with
#                 each and, after a '|', the STP options that logic needs.
#                 One entry per line, or separated by ';'. Overrides the
#                 built-in list below. For example
#
#                   LOGICS='QF_BV
#                           QF_ABV -mxn 1 -Mxn 3 | --array-equality' ./fuzz_single.sh
#
#                 One entry is drawn at random per iteration. See the comment
#                 on LOGIC_SETS below for the full syntax.
#
#   LOGIC         A single entry, for the same purpose. Ignored if LOGICS is
#                 set. Default: the built-in list.
#   QUERIES       Problem files generated per iteration. Default: 2500.
#   TIMEOUT       Per-solver wall-clock seconds per file; a file where either
#                 solver runs out is skipped. Default: 10.
#   FAIL_DIR      Where mismatches are saved.
#                 Default: $TMPDIR/stp-fuzz-failures.

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
source_root=$(cd -- "$script_dir/../.." && pwd)

# Find STP.
if [ -z "${STP:-}" ]; then
  for candidate in  "$source_root"/build_static_debug/stp \
                    "$source_root"/build/stp  \
                    "$source_root"/build-debug/stp \
                    "$source_root"/build-release/stp \
                   ; do
    if [ -x "$candidate" ]; then STP=$candidate; break; fi
  done
fi
STP=${STP:-$(command -v stp)}
if [ ! -x "${STP:-}" ]; then
  echo "No STP binary found. Build one, or set STP=/path/to/stp." >&2
  exit 1
fi

# Find the reference solver.
CHECKER=${CHECKER:-bitwuzla}
if ! command -v "$CHECKER" > /dev/null && [ ! -x "$CHECKER" ]; then
  echo "Reference solver '$CHECKER' not found. Set CHECKER=/path/to/solver." >&2
  exit 1
fi

# Find the generator.
if [ -z "${FUZZSMT_JAR:-}" ]; then
  for candidate in "$source_root"/../fuzzsmt/fuzzsmt.jar \
                   "$source_root"/deps/fuzzsmt/fuzzsmt.jar \
                   "$HOME"/fuzzsmt/fuzzsmt.jar; do
    if [ -r "$candidate" ]; then FUZZSMT_JAR=$candidate; break; fi
  done
fi
if [ ! -r "${FUZZSMT_JAR:-}" ]; then
  echo "fuzzsmt.jar not found. Set FUZZSMT_JAR=/path/to/fuzzsmt.jar." >&2
  exit 1
fi
if ! command -v java > /dev/null; then
  echo "java not found, it is needed to run fuzzsmt.jar." >&2
  exit 1
fi

# What to generate. One entry is drawn at random per iteration, so a run covers
# several shapes of problem instead of one. An entry is
#
#   <logic> [FuzzSMT options] [| STP options]
#
# The part before the '|' is passed to the generator, with `-g` (unguarded
# division) and `-bulk-export` appended, so entries need not repeat those. The
# part after it is handed to STP on top of the options drawn from the groups
# below -- that is for options a logic cannot be tested without, not for ones
# that merely deserve coverage: those belong in a group, where they get
# combined with everything else.
#
# The generator options are per-logic and FuzzSMT does not complain about ones
# that do not apply -- `QF_BV -mxn 1` is accepted and quietly generates plain
# QF_BV -- so check `java -jar fuzzsmt.jar` for the section belonging to the
# logic before adding an entry, and confirm the generated file really contains
# what the options were meant to add.
declare -a LOGIC_SETS=(
"QF_BV"
# Sub-sum extraction and pair extraction need n-ary bvadds that share addends,
# and the default -nary 3 -ref 1 hardly ever builds one: with it, both
# --common-subsum and --pair-extract leave the CNF byte-identical on every
# generated file. -nary 8 -ref 3 is where they start to bite.
"QF_BV -nary 8 -ref 3"
# Wide operands, which is what the abstraction group needs: at the shipped
# --bv-abstraction-width of 64 nothing generated at the default -Mbw 16 is
# wide enough, and this is the only entry where that group bites without the
# width being spelled out (13/30 for the equality family, 18/30 for terms).
"QF_BV -mbw 24 -Mbw 96 -Mc 4"
"QF_ABV"
# Array extensionality: -mxn/-Mxn are how many array pairs FuzzSMT compares
# with = or distinct. Without them it never equates two arrays, so the whole
# extensionality path goes unfuzzed -- and STP rejects such a file outright
# unless --array-equality is given, hence the pairing.
"QF_ABV -mxn 1 -Mxn 3 | --array-equality"
# Writes are what make the extensional cases interesting, and the default
# -Mw 5 is easily consumed by the reads.
"QF_ABV -mxn 1 -Mxn 3 -mw 3 -Mw 10 -Mar 5 | --array-equality"
# FuzzSMT draws floating-point sorts into this logic's array sorts, so
# selects and stores cross between the theories -- the region #824/#825 and
# their follow-ups lived in. The read counts matter: reads are what push an
# array past the eager-expansion regime, and the generator's defaults found
# nothing in 600 files where these counts crashed a pre-fix build about 4
# files in 100. --array-equality because the generated files compare whole
# arrays by default (-mxn/-Mxn default to 0..2 for this logic).
"QF_ABVFP -mr 12 -Mr 30 -mw 4 -Mw 12 -Mar 3 | --array-equality"
# Floating point with nothing else in the query, so the arithmetic circuits
# rather than the array machinery decide the encoding. -ref 3 is what makes
# the generator reuse a term, which is what puts an fp.add under an
# fp.isZero: --bb.fp-native-add-iszero changes 7 of 30 files here against 2
# of 20 on the array entry, and --bb.fp-native-domain 3 of 30 against 1.
"QF_FP -mvf 3 -Mvf 8 -mcf 2 -Mcf 6 -mvrm 1 -Mvrm 2 -ref 3"
# One array under a deep write chain, read many times. Every array entry
# above sits inside the eager-Ackermannisation regime -- the default budget
# of 4000 index comparisons covers them -- so there --ackermanize asks for
# what already happens and changes nothing; here it changes 18 of 30. It is
# also the only entry where the lazy write-chain cut has a chain long enough
# to cut (--lazy-write-reads-depth=0 changes 18/30, --lazy-write-reads=0
# 2/30), because that pass stands down whenever extensionality is active,
# which rules out the -mxn entries.
"QF_ABV -mar 1 -Mar 1 -mw 20 -Mw 40 -mr 8 -Mr 20 -mv 4 -Mv 8"
# Uninterpreted functions. -mf/-Mf and -mp/-Mp are how many uninterpreted
# functions and predicates FuzzSMT declares, and -ref 3 is what makes it
# apply one of them to arguments that may be equal, which is what the
# congruence checker exists for. At the generator's defaults the refinement
# loop never installs a lemma; at these counts --uf-ackermann off changes 23
# files in 30.
"QF_UFBV -mf 3 -Mf 5 -mp 2 -Mp 4 -ma 1 -Ma 2 -ref 3 -mv 2 -Mv 4 -mbw 2 -Mbw 8"
# The same with arrays in the query as well, so array read refinement and UF
# congruence refinement run in the one solve.
"QF_AUFBV -mf 2 -Mf 4 -mp 1 -Mp 3 -ref 3 -mr 4 -Mr 12 -mw 2 -Mw 8"
)

# LOGICS overrides the list, LOGIC gives a single entry. Split on both newlines
# and ';' so a one-line environment variable works as well as a multi-line one.
if [ -n "${LOGICS:-}" ]; then
  mapfile -t LOGIC_SETS < <(printf '%s\n' "$LOGICS" | tr ';' '\n' \
                            | sed -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//' -e '/^$/d')
elif [ -n "${LOGIC:-}" ]; then
  LOGIC_SETS=("$LOGIC")
fi
if [ "${#LOGIC_SETS[@]}" -eq 0 ]; then
  echo "No logics to generate: LOGICS is set but empty." >&2
  exit 1
fi

QUERIES=${QUERIES:-2500}
TIMEOUT=${TIMEOUT:-10}
FAIL_DIR=${FAIL_DIR:-${TMPDIR:-/tmp}/stp-fuzz-failures}
mkdir -p "$FAIL_DIR" || exit 1

# STP runs with an 80MB stack. The abc library STP bit-blasts through walks
# AIGs recursively, one stack frame per level (Gia_ManFromAig_rec, and
# formerly Aig_ObjReplace), so a deep AIG segfaults at the default 8MB and
# lands in FAIL_DIR as a bogus mismatch. 80MB is ~10x the deepest observed.
# The checker keeps its default: its stack is its own business.
# Probed here so a hard limit below it stops the run at startup, not as a
# confusing ulimit error in every iteration's second-err.txt.
STP_STACK_KB=81920
if ! (ulimit -S -s "$STP_STACK_KB") 2> /dev/null; then
  echo "Cannot raise the stack soft limit to ${STP_STACK_KB}kB (hard limit:" >&2
  echo "$(ulimit -H -s)kB). STP needs it for deep AIG recursions in abc;" >&2
  echo "raise the hard limit or run as a user allowed to." >&2
  exit 1
fi

path=${1:-$(mktemp -d "${TMPDIR:-/tmp}/stp-fuzz.XXXXXX")}
mkdir -p "$path" || exit 1
cd "$path" || exit 1

# Everything below deletes *.smt2 from this directory, on startup and after
# every iteration, so adopting the wrong one destroys its contents: pointed at
# a corpus or at tests/query-files it would wipe the lot. Only take over a
# directory that is empty or that a previous run left this marker in.
marker=.stp-fuzz-workdir
if [ ! -e "$marker" ] && [ -n "$(ls -A)" ]; then
  echo "Refusing to use '$path' as a working directory." >&2
  echo "It is not empty and no previous run of this script claimed it, and" >&2
  echo "every *.smt2 in it would be deleted. Give the fuzzer a directory of" >&2
  echo "its own, or pass no argument to get a fresh temporary one." >&2
  exit 1
fi
touch "$marker" || exit 1

rm -f -- *.smt2

echo "workdir: $path"
echo "stp:     $STP"
echo "checker: $CHECKER"
# Deliberately not cleared: it may hold findings from an earlier run that have
# not been triaged yet, and several workers share it. Say how many are already
# there so a directory found later is not mistaken for one this run produced.
existing=$(find "$FAIL_DIR" -mindepth 1 -maxdepth 1 -type d 2> /dev/null | wc -l)
if [ "$existing" -gt 0 ]; then
  echo "results: $FAIL_DIR ($existing already there from earlier runs, kept)"
else
  echo "results: $FAIL_DIR"
fi

# Every option-looking token in the help text, which is a superset of the
# declared options: the descriptions name options too, and those names are
# real. The trailing dot goes because a description ending "... needs
# --bb.mult-v2." would otherwise contribute an option that does not exist.
supported=$($STP --help 2>&1 | grep -o -- '--[a-zA-Z0-9.][a-zA-Z0-9.-]*' \
            | sed 's/\.$//' | sort -u)
if [ -z "$supported" ]; then
  echo "Could not get the option list from $STP" >&2
  exit 1
fi

# Check every entry actually generates what it says. A misspelt generator
# option is rejected outright, but a misspelt *logic* is not: FuzzSMT prints
# its usage text to stdout and exits 0, so without this the run would happily
# compare two solvers on a file of banner text. Requiring the emitted header to
# name the logic we asked for catches both.
echo "logics:"
declare -A logic_names=()
declare -a kept_logics=()
for entry in "${LOGIC_SETS[@]}"; do
  # Generator part | STP part; logic_opts comes out empty when there is no '|'.
  IFS='|' read -r gen logic_opts <<< "$entry"
  read -r -a gen_args <<< "$gen"
  gen_out=$(java -jar "$FUZZSMT_JAR" "${gen_args[@]}" -g -seed 1 2>&1)
  gen_rc=$?
  if [ "$gen_rc" -ne 0 ] || ! grep -q "^(set-logic  ${gen_args[0]})$" <<< "$gen_out"; then
    echo >&2
    echo "FuzzSMT cannot generate '$entry' (exit $gen_rc):" >&2
    echo "$gen_out" | head -20 | sed 's/^/  /' >&2
    echo "Check the logic name and the option list against" >&2
    echo "  java -jar $FUZZSMT_JAR" >&2
    exit 1
  fi
  # The whole entry goes if the binary lacks one of its options, not just the
  # option: the logic was listed on the understanding that STP gets these with
  # it, and generating it anyway makes every iteration a bogus mismatch.
  keep=1
  for opt in $(echo "$logic_opts" | grep -o -- '--[a-zA-Z0-9.][a-zA-Z0-9.-]*'); do
    if ! echo "$supported" | grep -qx -- "$opt"; then
      printf '  %s\n' "$entry  -- SKIPPED, $STP has no $opt" >&2
      keep=0
      break
    fi
  done
  if [ "$keep" -eq 0 ]; then continue; fi
  kept_logics+=("$entry")
  logic_names[${gen_args[0]}]=1
  printf '  %s\n' "$entry"
done
LOGIC_SETS=("${kept_logics[@]}")
if [ "${#LOGIC_SETS[@]}" -eq 0 ]; then
  echo "Every logic was skipped, there is nothing left to generate." >&2
  exit 1
fi

# FuzzSMT uses the bit-vector overflow predicates, which older solvers do not
# know. z3 4.8.12 for instance answers the query anyway and prints an extra
# (error ...) line, so it neither fails outright nor gives a usable answer --
# every iteration would land in FAIL_DIR looking like an STP bug. Check the
# checker before trusting a whole run to it. Once per logic, since what a
# solver accepts depends on it.
for logic in "${!logic_names[@]}"; do
  {
    echo "(set-logic $logic)"
    # The overflow predicates only exist where bit-vectors do; the other logics
    # get a trivial query, which still says whether the checker accepts them.
    case $logic in
      *BV*)
        echo "(declare-fun x () (_ BitVec 8))"
        echo "(declare-fun y () (_ BitVec 8))"
        for p in bvnego bvsaddo bvsdivo bvsmulo bvssubo bvuaddo bvumulo bvusubo; do
          if [ "$p" = bvnego ]; then
            echo "(assert (or (bvnego x) true))"
          else
            echo "(assert (or ($p x y) true))"
          fi
        done
        ;;
      *)
        echo "(assert true)"
        ;;
    esac
    echo "(check-sat)"
  } > probe.smt2
  probe_out=$(timeout 60 "$CHECKER" probe.smt2 2>&1)
  probe_rc=$?
  if [ "$probe_rc" -ne 0 ] || [ "$probe_out" != "sat" ]; then
    echo "Reference solver '$CHECKER' failed the startup probe for $logic (exit $probe_rc):" >&2
    echo "$probe_out" | sed 's/^/  /' >&2
    echo "It must print exactly 'sat' for a query using the bit-vector overflow" >&2
    echo "predicates. Upgrade it, or set CHECKER to one that does." >&2
    exit 1
  fi
done
rm -f probe.smt2

# Options are grouped by what they affect. Each iteration draws one entry from
# every group and concatenates the picks, so settings from different groups are
# exercised together instead of one at a time. Every group carries an empty
# entry, which is how it sits out an iteration; drawing empty from all of them
# reproduces the default configuration.
#
# Entries within a group are alternatives to each other, so put mutually
# exclusive options in the same group -- that is what stops --minisat and
# --cadical being handed over together. Options that combine freely belong in
# groups of their own.
#
# Since #789 the binary knows the same relationships and refuses a command line
# that pairs two options it cannot honour both of, so getting this wrong is no
# longer a silently degraded iteration: it is a rejected one, saved as a
# mismatch. `excludes_all` at the end of create_options() in tools/stp/main.cpp
# is the list to check an entry against.
#
# The other way to get a rejected command line is to name one option in two
# groups that can be drawn together: both pickers supply it and CLI11 refuses
# the repeat. That one the script checks for itself, after the groups are
# read -- see the clash check below -- because it is invisible to the
# per-entry probe that catches everything else here.
#
# An entry has to be non-default AND has to actually change the output,
# otherwise it silently re-runs the baseline and wastes the iteration. Check it
# against the "arg (=N)" defaults in `stp --help`, then confirm the emitted CNF
# really differs before adding it:
#
#   stp --output-CNF --exit-after-CNF f.smt2                  # baseline
#   stp <entry> --output-CNF --exit-after-CNF f.smt2          # with the entry
#
# A CNF compare cannot see an option that only steers refinement: --output-CNF
# writes the first encoding and nothing after it. Those are checked against the
# counters `stp -t` prints instead -- the "Abstraction refinement:" line for the
# entries in the abstraction group below.
#
# --bb.mult-v2=1 on its own looked reasonable and failed exactly that test:
# byte-identical CNF on every one of 49 QF_BV and QF_ABV files, because each
# site reading upper_multiplication_bound is gated behind constant-bit
# propagation having produced MultiplicationStats, which does not happen under
# the default multiplication variant. Paired with variant 5 it does bite, so
# that is the form kept below.
#
# Three options must never get an entry, whatever they change: --aig-node-budget,
# --max-num-confl and --max-time all abandon the query through the soft-timeout
# path, so STP answers "unknown" where the checker answered sat or unsat and
# every file is saved as a mismatch. A budget is what -k gives the whole run,
# not something to draw per iteration. The same goes for the --print-back-*
# and --parse-only options, which replace the answer with something else
# entirely.

declare -a OPTION_GROUPS=(simplify mult div shift bitblast abstract array uf
                          fp cnf solver bias misc)

# A group named here is drawn only when the iteration's logic matches the
# pattern, which is how options that do nothing outside one theory stay out of
# the draw everywhere else. The pattern is a shell glob, matched against the
# logic name.
declare -A GROUP_LOGIC_FILTER=(
[fp]='*FP*'
[array]='*A*'
[uf]='*UF*'
)

declare -a g_simplify=(
""
"--disable-simplifications"
"--disable-opt-inc"
"--disable-cbitp"
"--disable-equality"
"--size-reducing-only"
"--rewriting=0"
"--split-extracts=0"
"--use-intervals=0"
"--pure-literals=0"
"--difficulty-reversion=0"
"--flattening=0"
"--ite-context-simplifications=1"
"--merge-same=1"
"--simplify-to-constants-only=1"
"--size-reducing-fixed-point-limit=-1"
"--aig-core-simplification=1"

# This and the --flattening entry above are opt-outs because the flattening
# stack is on by default since #838, so an opt-in form only re-runs the
# baseline. Its third member --common-subsum has no entry either way: opting
# out of it is byte-identical on every generated file, the n-ary entry
# included, because the pass finds nothing to factor there.
"--pair-extract=0"

# A bit-blasting option, but it lives here because #789 made it exclude
# --disable-opt-inc and --disable-simplifications, which are entries above.
# Drawn from its own group it would be paired with them roughly one iteration
# in a hundred, and STP now rejects that command line outright.
"--bb.simplify-during-bb=1"

# These two have given wrong answers in the past, so they get extra exposure
# here rather than being trusted.
"--unconstrained-variable-elimination=0"
"--aig-rewrite-passes=1"

# Canonical linear combinations. Only the n-ary entry builds a term worth
# re-spelling: 5/17 there against 0 on both plain entries and 0 on the wide
# one. The addend limit is what stops a constant being distributed over a
# long sum, so the second entry pins it low enough to bind (4/17).
# It has to live in this group rather than one of its own:
# --disable-simplifications excludes it, and drawn separately the two would
# be offered together and the command line refused.
"--linear-form=1"
"--linear-form=1 --linear-form-addend-limit=4"

# Proving the equalities a query implies between the terms it applies one
# operator to, and asserting the ones that hold. Wants repeated applications
# of the same operator, so it is the n-ary entry (2/17) and the two UF ones
# (7/26 and 8/20) that reach it, and nothing on the plain entries.
#
# KNOWN TO ABORT, deliberately left drawing anyway. On a query with arrays:
#
#   Fatal Error: BBTerm: Illegal kind to BBTerm  (READ (WRITE ...) ...)
#
# 4 files in 30 on the QF_AUFBV entry and 1 in 30 on the deep-write-chain
# QF_ABV one, on the option alone with nothing else set -- exit 255, no
# answer, where the default answers fine. Every one of those files is saved
# as a mismatch, so an iteration drawing this entry with an array logic fills
# FAIL_DIR with hundreds of copies of the one bug. Triage by grepping
# what-happened.txt for the option name; what is left is everything else.
# Drop this entry back to a comment if that gets in the way of a hunt.
#
# Its two budgets get no entry: a generated query offers fewer candidates
# than --congruence-candidate-limit's 64 and settles each inside
# --congruence-candidate-conflicts' 20000, so neither binds (0/26), and
# limit=0 just turns the pass back off.
"--congruence-candidates=1"

# Not here: --switch-word, which turns the word-level solver off. A generated
# file has no top-level equation for it to solve, so both settings emit the
# same CNF on all 170 files measured across the logic entries below.
#
# Nor these four, each measured byte-identical on all 150 files across the
# five logic entries they could bite on:
#   --mulo-recognition=0   rewrites the double-width spellings of an overflow
#                          check into the overflow predicates. FuzzSMT emits
#                          bvumulo and friends directly, so there is never a
#                          spelling left to recognise.
#   --distinct-ordering=0  fixes one of the n! orderings of a (distinct ...)
#                          over variables used nowhere else. FuzzSMT only ever
#                          writes the binary (distinct a b), which is a
#                          disequality with no ordering to fix.
#   --skeleton-preproc=1   and --embedded-constraints=1 never fire on a
#                          generated query.
# And not --common-subsum-budget: --common-subsum itself is already absent
# for finding nothing to factor, so capping its tally changes nothing either.
)

# Multiplication: the variants are alternative settings of one option, so they
# have to share a group.
declare -a g_mult=(
""
# The default is 27: a constant multiplier Booth-recoded, a symbolic pair
# summed as ripple rows in canonical order with its runs of identical
# symbolic bits recoded too, a constant Booth declines on carry-save rows.
# 1 is the plain shift-and-add array it replaced, and the opt-out; 25 is the
# default with carry-save rows for the symbolic pair, 26 with ripple rows
# for the declined constant too, 22 is 25 without the run recoding.
"--bb.mult-variant=1"
"--bb.mult-variant=22"
"--bb.mult-variant=25"
"--bb.mult-variant=26"
"--bb.mult-variant=3"
"--bb.mult-variant=4"
"--bb.mult-variant=5"
"--bb.mult-variant=6"
"--bb.mult-variant=7"
"--bb.mult-variant=8"
"--bb.mult-variant=9"
"--bb.mult-variant=13"
# 14 only recodes a *constant* multiplier holding a run of ones, which the two
# plain logic entries never build: byte-identical CNF on all 24 of them. It is
# the "QF_BV -nary 8 -ref 3" entry that exercises it (3/30 files), so the two
# belong together -- dropping that logic entry silently stops fuzzing this
# variant. Wider constants reach it more often still (7/30 at -Mc 8 -Mbw 32).
# The same holds of the constant half of the default, 22, and of 21 and 23.
"--bb.mult-variant=14"
"--bb.mult-variant=17"
"--bb.mult-variant=18"
"--bb.mult-variant=19"
"--bb.mult-variant=20"
"--bb.mult-variant=21"
"--bb.mult-variant=23"
# 15 is the one Booth variant that recodes symbolic multipliers, and the only
# one that skips setColumnsToZero(), so it reaches a bit-blasting path none of
# the others do. 7/24 on the plain entries, as does 16.
"--bb.mult-variant=15"
"--bb.mult-variant=16"
# multWithBounds() is only reachable from variant 5, so pair them.
"--bb.mult-variant=5 --bb.mult-v2=1"
)

# Division and remainder. One group because these are alternatives in fact:
# v1 to v5 all rewire the same divider circuit, and the last three replace it
# outright, so an iteration drawing two would be testing whichever the
# blaster consults first.
#
# --bb.div-v2 is the exception to the rule that an entry has to change the
# output: both settings are the same function written two ways -- a strict
# less-than against the negation of the reversed one -- and structural
# hashing folds them back together, so the CNF is byte-identical on all 170
# files measured, under every rung of the cnf group. It is kept because the
# alternative encoder does run: what is being fuzzed is the code, not the
# difference.
#
# The rest do change it, on every logic entry that divides at all: v4 2/14,
# 9/17 and 2/12 on the three bit-vector entries, v5 3/14, 8/17 and 2/12,
# --bb.div-by-mult 7/14, 12/17 and 5/12, --bb.div-lemmas 5/14, 10/17 and
# 5/12. --bb.div-by-const only applies from --bb.div-by-const-width, which
# defaults to 64: opting out bites on the wide entry alone (1/12), and the
# width has to be spelled out for the other entries to reach the pass at all.
declare -a g_div=(
""
"--bb.div-v1=0"
"--bb.div-v2=0"
"--bb.div-v3=1"
"--bb.div-v4=1"
"--bb.div-v5=1"
"--bb.div-by-mult=1"
"--bb.div-lemmas=1"
"--bb.div-by-const=0"
"--bb.div-by-const-width=8"
)

# Symbolic-amount shifts: alternative settings of one option, so one group.
#
# Which entry bites depends on the operand width the iteration's logic draws.
# The selector variants 1 to 3 only apply between --bb.shift-onehot-minw (33)
# and --bb.shift-onehot-maxw (64), so variant 1 on its own reaches only the
# wide entry (4/12) and nothing else; dropping the floor to 1 is what lets
# the other logics exercise them (8/17 on the n-ary entry, 2/14 on plain
# QF_BV). Variant 4 is the opposite: it adds the exact prime implicates for
# shift amounts up to 5 bits wide, so it wants narrow operands -- 19/26 and
# 11/20 on the two UF entries, whose -Mbw is 8, against nothing on the plain
# and wide ones. The maxw entry narrows the window from the other end.
declare -a g_shift=(
""
"--bb.shift-variant=1"
"--bb.shift-variant=1 --bb.shift-onehot-minw=1"
"--bb.shift-variant=2 --bb.shift-onehot-minw=1"
"--bb.shift-variant=3 --bb.shift-onehot-minw=1"
"--bb.shift-variant=1 --bb.shift-onehot-minw=1 --bb.shift-onehot-maxw=8"
"--bb.shift-variant=4"
)

# The rest of bit-blasting. These are independent of each other, but keeping
# them in one group bounds how far a single iteration strays from the default.
#
# --bb.add-v1 is here for the same reason --bb.div-v2 is in the division
# group: Majority() against the three-conjunction OR is the same function
# twice, and the CNF is byte-identical on all 170 files measured.
#
# The two overflow detectors are on by default since #1113 and #1114, so the
# entries are the opt-outs, back to the double-width product each replaced:
# 3/14, 7/17 and 6/12 for unsigned, 5/14, 9/17 and 4/12 for signed. The
# multiply residue implicates are additions to whatever --bb.mult-variant
# built, which is why they are here and not in the mult group: 4/14, 13/17
# and 8/12 for the 3-bit block, 6/14, 14/17 and 8/12 for the 4-bit one.
declare -a g_bitblast=(
""
"--bb.add-v1=0"
"--bb.add-v2=0"
"--bb.vle-v1=0"
"--bb.conjoin-constant=1"
"--bb.umulo-schulte=0"
"--bb.smulo-schulte=0"
"--bb.mult-lemmas=3"
"--bb.mult-lemmas=4"
)

# Lazy bit-vector abstraction, the CEGAR path that replaces a wide operation
# or equality with a fresh variable and refines it. The width has to be
# spelled out: --bv-abstraction-width defaults to 64 while FuzzSMT's -Mbw
# defaults to 16, so on most entries nothing generated is wide enough at the
# shipped width and the family would be byte-identical to the baseline. At 8
# it changes the CNF on about half the files. Two logic entries reach it
# without help and are why the last entry carries no width: the wide-operand
# one, and the floating-point-array one, whose terms are 32 and 64 bits.
#
# The knobs under each family steer refinement, which happens after the first
# CNF is written and so is invisible to a CNF compare. They were checked
# against the "Abstraction refinement:" counters `stp -t` prints, and move
# them on 4 to 9 files in 30.
#
# The counts below are from that measurement, as changed/30 on the n-ary,
# wide and QF_ABV entries respectively. Entries pairing several knobs are
# deliberate: --bv-term-abstraction-ite, -plus and -compare each widen what
# is abstracted and are independent of each other, so one entry turning all
# three on covers the family without spending three draws on it.
#
# --bv-term-abstraction-profile excludes --bv-term-abstraction-schema-groups
# and --bv-term-abstraction-rounds (they set the same two things), so no
# entry may pair a profile with either. 'qualified' has no entry: it is the
# inherited base, and measured identical to the default on all 90 files.
declare -a g_abstract=(
""
"--bv-eq-abstraction=1 --bv-abstraction-width=8"
"--bv-eq-abstraction=1 --bv-abstraction-width=8 --bv-eq-refine-width=1"
# An equality one side of which the blast knows entirely. 12/30 and 8/30 on
# the two bit-vector entries.
"--bv-eq-abstraction=1 --bv-abstraction-width=8 --bv-eq-abstraction-constant-side=1"
"--bv-term-abstraction=1 --bv-abstraction-width=8"
"--bv-term-abstraction=1 --bv-abstraction-width=8 --bv-term-abstraction-schemas=0"
"--bv-term-abstraction=1 --bv-abstraction-width=8 --bv-term-abstraction-profile=aggressive"
"--bv-term-abstraction=1 --bv-abstraction-width=8 --bv-term-abstraction-profile=broad"
"--bv-term-abstraction=1 --bv-abstraction-width=8 --bv-term-abstraction-inc-bitblast=1"
"--bv-term-abstraction=1 --bv-term-abstraction-inc-bitblast=1"
# The cheaper kinds, which the default leaves alone. Separately, ite is
# 14/30, 10/30 and 16/30, plus 9/30, 6/30 and 9/30, compare 15/30, 12/30 and
# 19/30; the entry turning all three on is 16/30 on the n-ary one.
"--bv-term-abstraction=1 --bv-abstraction-width=8 --bv-term-abstraction-ite=1 --bv-term-abstraction-plus=1 --bv-term-abstraction-compare=1"
# Narrowing the scope the other way, which is what leaves division or
# multiplication encoded exactly from the start: 14/30, 10/30, 21/30 for the
# multiply scope and 11/30, 6/30, 14/30 for the DIV/MOD override.
"--bv-term-abstraction=1 --bv-abstraction-width=8 --bv-term-abstraction-mult=0"
"--bv-term-abstraction=1 --bv-abstraction-width=8 --bv-term-abstraction-divmod=0"
# How long a record may enumerate operand pairs before it gives up and
# encodes the operation exactly. 0 never escalates, 1 escalates at once,
# and the divisor scales the allowance with the operand width.
"--bv-term-abstraction=1 --bv-abstraction-width=8 --bv-term-abstraction-rounds=0"
"--bv-term-abstraction=1 --bv-abstraction-width=8 --bv-term-abstraction-rounds=1 --bv-term-abstraction-value-divisor=8"
# The constant-operand shortcut is on by default, so these opt out of it and
# then uncap what it caps: 7/30, 6/30, 10/30 either way.
"--bv-term-abstraction=1 --bv-abstraction-width=8 --bv-term-abstraction-constant-operands=0"
"--bv-term-abstraction=1 --bv-abstraction-width=8 --bv-term-abstraction-constant-operand-limit=0"
"--bv-term-abstraction=1 --bv-abstraction-width=8 --bv-term-abstraction-divmod-value-limit=1"
# The whole experimental schema stack, and none of it.
"--bv-term-abstraction=1 --bv-abstraction-width=8 --bv-term-abstraction-schema-groups=all"
"--bv-term-abstraction=1 --bv-abstraction-width=8 --bv-term-abstraction-schema-groups=none"

# Reaching the same abstraction from a UF solve. These belong to the uf
# group by subject, but they are here because --bv-abstraction-width is: an
# iteration drawing a width from each group hands STP the option twice and
# the command line is refused, which is what the clash check below forbids.
# The price of keeping them here is that they are also drawn for the nine
# non-UF logic entries, where they do nothing.
#
# --uf-bv-term-abstraction's default of 'auto' engages only for a query
# holding an operation at or above the width, so at the UF entries' -Mbw 8
# it declines. Spelled on with the width down at 8, 13/30 of them abstract
# something, and the two knobs that only matter once one does then bite as
# well: 6/30 for running the congruence checker beside the abstraction's
# refinement, 8/30 for the quotient-threshold schemas. ('off' gets no entry:
# it is what auto already does on these files.)
"--bv-abstraction-width=8 --uf-bv-term-abstraction=on"
"--bv-abstraction-width=8 --uf-bv-term-abstraction=on --uf-check-during-bv-refinement=0"
"--bv-abstraction-width=8 --uf-bv-term-abstraction=on --uf-quotient-threshold-schemas=0"
)

# Arrays, drawn only for the logics that have them. One group because these
# are alternatives in fact as well as in form: --ackermanize turns the lazy
# write-chain cut off outright -- markLazyChainCut stands down for it -- so an
# iteration drawing both would be testing the first alone.
#
# Which entry bites depends on which array entry the iteration drew. The
# budget default of 4000 index comparisons covers every array file the
# generator writes except the deep-chain one, so --ackermanize is inert on the
# rest (0/30) and changes 18/30 there; a budget of zero is the opposite
# setting, and changes 9/30 on the extensional entry and nothing on the chain.
#
# The index hints are the exception to the one-entry-per-alternative rule
# being enough: 'phase' and 'decide' differ from the default and from each
# other, so both are here. They need an array read whose index is free, which
# is the deep-chain entry (17/30) and the QF_AUFBV one (9/30); on the other
# array entries the indices are pinned and neither setting moves a counter.
declare -a g_array=(
""
"--ackermanize"
"--array-ackermann-budget=0"
"--lazy-write-reads=0"
"--lazy-write-reads-depth=0"
"--lazy-write-reads-depth=1"
"--lazy-write-reads-depth=8"
"--array-index-hints=phase"
"--array-index-hints=decide"
)

# Uninterpreted functions, drawn only for the UF logics. The eager policy and
# its budget set the same thing two ways, so they share a group with the
# refinement knobs that only matter once the policy is out of the way -- hence
# the pairings. --uf-lemmas-per-round is invisible to a CNF compare and was
# measured against `stp -s` with the timings scrubbed: 17/30.
declare -a g_uf=(
""
"--uf-ackermann on"
"--uf-ackermann off"
"--uf-ackermann-budget=0"
"--uf-ackermann off --uf-lemmas-per-round=1"
"--uf-ackermann off --uf-lemmas-per-round=0"
"--uf-ackermann off --uf-phase-hints=1"

# Not here, though they are UF options: the three --uf-bv-term-abstraction
# entries. They need --bv-abstraction-width spelled down to 8, and that
# option belongs to the abstract group, which is drawn for the UF logics
# too -- naming it in both is the one thing the clash check further down
# refuses. They live in the abstract group instead.
#
# Deliberately absent, each measured identical on all 46 files the two UF
# entries emit a CNF for, with the UF counters `stp -s` prints identical too:
#   --uf-propagate-equalities=0  the pass substitutes a couple of asserted
#                                atoms on 6 files in 30 and the CNF comes out
#                                byte-identical anyway, so turning it off
#                                only skips work nothing depended on.
#   --uf-narrow-results=0        narrows result sorts used only for equality;
#                                FuzzSMT feeds every application into
#                                arithmetic as well, so none qualifies.
#   --uf-skeleton-preproc=0      the skeleton forces nothing on these queries.
#   --uf-inject-args=1           wants equality-only declarations.
#   --uf-sort-width              only sizes a sort from (declare-sort S 0),
#                                which FuzzSMT never writes.
# Nor --uninterpreted-functions, which decides UF for a logic whose name
# omits it: FuzzSMT always names the logic correctly, so on the UF entries it
# asks for what already happens and on the others there is no UF to decide.
)

# Floating-point bit-blasting, drawn only for the FP logics: with no FP in the
# input both settings leave the CNF byte-identical, so anywhere else they are a
# wasted iteration.
#
# Every operation but fp.sqrt and fp.div now blasts natively by default, so
# most entries opt *out* -- the SymFPU circuit is the side that needs drawing.
# The two that stayed on SymFPU opt in instead. --bb.fp-native-cmp is not
# combined with an arithmetic entry: it only applies to predicates that stayed
# native.
#
# Deliberately absent: --bb.fp-native-known-sign, which reads zero on both
# entries even paired with the --bb.fp-native-domain it needs, and the whole
# --fp-domain-* prepass family, which wants asserted bounds a generated file
# does not carry.
#
# Counts below are out of the files that emit a CNF at all: 28 of the plain
# floating-point entry's 30, and 11 of the QF_ABVFP entry's 30. fp.sqrt and
# fp.div are the ones the plain entry reaches most (7/28 and 4/28); the
# conversions live on the array entry (7/11 against 2/28), which is where
# to_ubv and to_sbv are generated. --bb.fp-add-variant picks the alignment
# frame for the native adder, which is now in place without asking: paired it
# changed 15/28 and 7/11.
declare -a g_fp=(
""
"--bb.fp-native-cmp=0"
"--bb.fp-native-arith=0"
"--bb.fp-native-add-iszero=0"
"--bb.fp-native-domain=0"
"--bb.fp-native-sqrt=1"
"--bb.fp-native-div=1"
"--bb.fp-native-round=0"
"--bb.fp-native-rem=0"
"--bb.fp-native-minmax=0"
"--bb.fp-add-variant=1"
"--bb.fp-normalise-lemma=0"

# The packed-carrier conversions, and the whole native set at once. Worth
# having: 13/28 and 2/28 changed on the plain floating-point entry, 8/11 and
# 7/11 on the array one, and --bb.fp-native-all is every native circuit at
# once, 17/28 and 8/11.
"--bb.fp-native-pack=0"
"--bb.fp-native-conv=0"
"--bb.fp-native-all=0"
"--bb.fp-native-all=1"

# Absent because there is nothing to blast: --bb.fp-native-fma. FuzzSMT
# writes no fp.fma in either entry, so the option is byte-identical on all
# 60 files. It needs a logic entry that generates one before it is worth
# adding.
)

# CNF generation. One option selects between three encoders, so the rungs
# belong in one group: very-low..very-high minimise ABC's AIG, the new-*
# rungs blast through STP's own AIG and write the CNF from it directly, and
# the gia-* rungs reach the same generator over a Gia the bit-blaster built
# rather than one converted from an ABC AIG. Every rung here changes the CNF
# on every file that emits one -- 16 of 30 QF_BV files; the simplifier
# decides the rest before the SAT solver is reached.
#
# 'auto' and 'medium' are absent because they are what the empty entry
# already tests: auto is the default, and a generated file is always under
# --cnf-auto-threshold, so it picks medium.
declare -a g_cnf=(
""
"--cnf-generation-effort=very-low"
"--cnf-generation-effort=low"
"--cnf-generation-effort=high"
"--cnf-generation-effort=very-high"
"--cnf-generation-effort=new-very-low"
"--cnf-generation-effort=new-low"
"--cnf-generation-effort=new-medium"
# The fourth new-* rung. Missing until now, and it changes every file that
# emits a CNF at all -- 14/14 and 17/17 on the two plain entries.
"--cnf-generation-effort=new-high"
"--cnf-generation-effort=gia-low"
"--cnf-generation-effort=gia-high"
"--cnf-generation-effort=gia-very-high"
# The other way to reach very-low: the threshold auto drops to it above.
"--cnf-auto-threshold=0"
)

declare -a g_solver=(
""
"--cadical"
# Bounded variable addition, which is cadical's and needs a CaDiCaL 3.x build.
# On an older one these are dropped at startup; see the probe further down.
"--cadical --cadical-factor on"
"--cadical --cadical-factor off"
# 'auto' turns it on only for problems with array operations, so what this
# entry means depends on the logic the iteration drew.
"--cadical --cadical-factor auto"
# Keeping cadical's search trail across the solve calls of a refinement loop
# is on by default, so the entry is the opt-out, back to restarting each
# round from the root. It needs a loop that runs more than one round, which
# is the UF entries: 5/30 there, and nothing where refinement settles first
# time. Other backends have no trail to keep, hence the pairing.
"--cadical --refinement-trail-reuse=0"
"--cryptominisat"
"--cryptominisat --threads=4"
"--simplifying-minisat"
"--minisat"
)

# Which answer the SAT search is tuned towards. Independent of which solver is
# in use -- one without the setting ignores it -- so it gets its own group.
# 'none' is the default and is what the empty entry already tests.
declare -a g_bias=(
""
"--search-bias unsat"
"--search-bias sat"
)

# The incremental driver keeps the SAT solver and the bit-blasted encoding
# across (check-sat) commands. A generated file has exactly one, and the
# default 'auto' only switches over for an input that pushes, so without an
# entry here the whole driver goes unfuzzed. 'on' engages it from the first
# solve, which a profile confirms: the encoding is built and solved through
# the driver rather than the batch pipeline on every file. --core-only is
# the same driver without its fitted preprocessing and adaptive policies,
# and changes the work counters on 30/30.
#
# The rest of the --incremental-* family gets no entry: the CBP rollback
# knobs, the rebuild limits, the promotion and inprobing settings all only
# act from the second check onwards, and they move no counter on 30/30
# single-check files. Fuzzing them needs the generated files rewritten into
# push/pop sessions, which this script does not do.
#
# Sharing this group with --interactive makes one iteration in two an
# incremental one. Giving these entries a group of their own would raise
# that, at the cost of every other iteration carrying the driver too.
declare -a g_misc=(
""
"--interactive=1"
"--incremental=on"
"--incremental=on --incremental-core-only"
)

# --cadical-factor is accepted by the option parser whatever CaDiCaL is linked,
# but only a 3.x build can act on it; an older one declines the request with a
# warning per query, which buries the progress output and leaves the entries
# testing nothing. Ask once here so they are dropped like any other unsupported
# option. Only 'on' is worth probing: 'off' and 'auto' are silent either way,
# and with no bounded variable addition all three mean the same thing.
if echo "$supported" | grep -qx -- '--cadical-factor'; then
  echo '(set-logic QF_BV)(assert true)(check-sat)' > factor-probe.smt2
  if "$STP" --cadical --cadical-factor on factor-probe.smt2 2>&1 > /dev/null \
     | grep -q -- '--cadical-factor'; then
    supported=$(echo "$supported" | grep -vx -- '--cadical-factor')
    cadical_factor_declined=1
  fi
  rm -f factor-probe.smt2
fi

# Drop entries this binary doesn't understand, rather than have the option
# parser reject them and count every iteration as a mismatch. Catches both a stale build and
# typos in the arrays above. ($supported was read from --help further up.)
#
# The name check is not enough on its own: an entry can name an option this
# binary has and still give it a value it does not know -- a
# --cnf-generation-effort rung added after the binary was built, say -- which
# is refused at runtime with every iteration saved as a mismatch. So each
# entry that survives the name check is offered to the binary once, on a
# query small enough that answering it costs nothing.
echo '(set-logic QF_BV)(declare-fun x () (_ BitVec 4))(assert (= x x))(check-sat)' \
  > entry-probe.smt2
declare -a dropped=()
offered=0
for gname in "${OPTION_GROUPS[@]}"; do
  declare -n group="g_$gname"
  offered=$(( offered + ${#group[@]} ))
  declare -a checked=()
  for e in "${group[@]}"
    do
      keep=1
      for opt in $(echo "$e" | grep -o -- '--[a-zA-Z0-9.][a-zA-Z0-9.-]*'); do
        if ! echo "$supported" | grep -qx -- "$opt"; then
          if [ "$e" = "$opt" ]; then
            dropped+=("$gname: $e")
          else
            dropped+=("$gname: $e  ($opt is the missing one)")
          fi
          keep=0
          break
        fi
      done
      # $e is deliberately unquoted, some entries are two options.
      if [ $keep -eq 1 ] && ! "$STP" $e -d entry-probe.smt2 > /dev/null 2>&1; then
        dropped+=("$gname: $e  (the binary refused it)")
        keep=0
      fi
      if [ $keep -eq 1 ]; then checked+=("$e"); fi
  done
  group=("${checked[@]}")
  unset -n group
done
rm -f entry-probe.smt2

# Worth being loud about: a dropped entry is a code path that silently stops
# being fuzzed, and the run otherwise looks perfectly healthy for hours.
if [ "${#dropped[@]}" -gt 0 ]; then
  echo >&2
  echo "WARNING: ${#dropped[@]} of $offered option settings dropped, this build" >&2
  echo "  does not support them:" >&2
  printf '    %s\n' "${dropped[@]}" >&2
  echo "  Those code paths are NOT being fuzzed. Rebuild with them enabled if" >&2
  echo "  that is not deliberate." >&2
  if [ -n "${cadical_factor_declined:-}" ]; then
    echo "  --cadical-factor is in --help but the linked CaDiCaL has no bounded" >&2
    echo "  variable addition to turn on, so it was treated as unsupported." >&2
    echo "  A CaDiCaL 3.x build is needed to fuzz it." >&2
  fi
  echo >&2
fi

# The dropped check above catches an entry naming an option the binary lacks.
# This one catches the opposite, and is what keeps this file honest as options
# are added: an option the binary has that no group mentions. Without it a new
# option simply never gets fuzzed, and nothing says so.
#
# Everything genuinely out of scope is listed here with the reason, so the
# warning only fires for something new. Adding an option to this list is a
# decision to leave it unfuzzed -- prefer an entry in a group.
declare -a NOT_FUZZED=(
# Answer-replacing: these make STP print something that is not the sat/unsat
# the checker gave, so every file would be saved as a mismatch.
--help --version --parse-only --output-CNF --exit-after-CNF
--aig-node-budget --max-num-confl --max-time
--print-stpinput --print-back-CVC --print-back-SMTLIB2 --print-back-GDL
--print-back-dot --print-counterex --print-counterexbin --print-arrayval
--print-functionstat --print-quickstat --print-nodes --print-output
# Already fixed by the harness: -d is passed to every STP run, and the input
# is SMT-LIB2 by extension.
--check-sanity --CVC --SMTLIB1 --SMTLIB2
# Measured inert on every generated file; see the group comments below for
# what each would need before it is worth an entry.
--bb.fp-native-fma --bb.fp-native-known-sign
--fp-domain-simplify --fp-domain-derived-bounds --fp-domain-extremal-selectors
--fp-domain-sound-zero-facts --fp-domain-row-bounds
--mulo-recognition --distinct-ordering --skeleton-preproc
--embedded-constraints --common-subsum --common-subsum-budget --switch-word
--uninterpreted-functions --uf-propagate-equalities --uf-narrow-results
--uf-skeleton-preproc --uf-inject-args --uf-sort-width
--congruence-candidate-limit --congruence-candidate-conflicts
# Only act from the second (check-sat) onwards. A generated file has one, so
# fuzzing these needs the files rewritten into push/pop sessions, which this
# script does not do.
--incremental-auto-engage-at --incremental-profile --incremental-cbp-reset
--incremental-cbp-bootstrap-limit --incremental-cbp-feed-cap
--incremental-base-resimplify-limit --incremental-reencode-limit
--incremental-semantic-cache-limit --incremental-promote-units
--incremental-piece-rewriting --incremental-scoped-preprocessing
--incremental-inprobing
)

# $supported is the wrong list to check against: it harvests every
# option-looking token in the help text, so a description reading "unlike
# --rounds this changes ..." contributes --rounds, and an underscore alias
# spelt --max_num_confl contributes --max. Take the declared options instead,
# which are the ones anchored at the start of a help line, after an optional
# short form. Where a line gives two spellings the first is taken, which is
# the one the groups use.
# The trailing dot goes for the same reason it does above: a description
# wrapping onto a line that starts "--bb.mult-v2. 17 accumulates ..." looks
# like a declaration to an anchored match.
declared=$($STP --help 2>&1 | sed -e 's/ Excludes:.*//' \
           | grep -oP '^\s+(-\w,\s+)?\K--[a-zA-Z0-9.][a-zA-Z0-9.-]*' \
           | sed 's/\.$//' | sort -u)

# Read out of this file rather than out of the shell variables, so that a
# commented-out entry counts as mentioned: one of those is a deliberate record
# of an option known about and held back, not an oversight. $script_dir
# because the working directory was changed further up.
grouped=$(sed -n '/^declare -a g_/,/^)$/p' "$script_dir/${BASH_SOURCE[0]##*/}" \
          | grep -o -- '--[a-zA-Z0-9.][a-zA-Z0-9.-]*' | sed 's/\.$//' | sort -u)
# The options a logic entry carries are fuzzed too, on every iteration that
# draws that logic -- --array-equality is only ever supplied that way.
grouped=$(printf '%s\n%s\n' "$grouped" \
          "$(printf '%s\n' "${LOGIC_SETS[@]}" | sed 's/^[^|]*|//' \
             | grep -o -- '--[a-zA-Z0-9.][a-zA-Z0-9.-]*')" | sort -u)
declare -a unfuzzed=()
while read -r opt; do
  [ -z "$opt" ] && continue
  if grep -qx -- "$opt" <<< "$grouped"; then continue; fi
  if printf '%s\n' "${NOT_FUZZED[@]}" | grep -qx -- "$opt"; then continue; fi
  unfuzzed+=("$opt")
done <<< "$declared"
if [ "${#unfuzzed[@]}" -gt 0 ]; then
  echo >&2
  echo "WARNING: ${#unfuzzed[@]} option(s) this build has are named by no group:" >&2
  printf '    %s\n' "${unfuzzed[@]}" >&2
  echo "  They are not being fuzzed. Give each one an entry in the group it" >&2
  echo "  belongs to -- check first that it is non-default and that it really" >&2
  echo "  changes the CNF or a counter, as the comments on the groups explain" >&2
  echo "  -- or add it to NOT_FUZZED above with the reason it cannot be." >&2
  echo >&2
fi

# The empty entry never matches the filter, so a group cannot come out of that
# loop empty unless the group itself was written empty.
for gname in "${OPTION_GROUPS[@]}"; do
  declare -n group="g_$gname"
  if [ "${#group[@]}" -eq 0 ]; then
    echo "Option group '$gname' is empty." >&2
    exit 1
  fi
  filter=${GROUP_LOGIC_FILTER[$gname]:-}
  printf '  %-10s %2d entries%s\n' "$gname" "${#group[@]}" \
         "${filter:+  (only for $filter logics)}"
  unset -n group
done
printf '  %-10s %2d entries\n' "logics" "${#LOGIC_SETS[@]}"

# One option named by two groups that can be drawn together is a rejected
# command line, not a degraded iteration: a picker from each supplies it and
# CLI11 refuses the repeat with "At most 1 required but received 2", so STP
# exits 255 having answered nothing and every file of that iteration is saved
# as a mismatch. The entry probe further up cannot see it -- each entry is
# offered on its own, and each is fine on its own.
#
# Checked per logic, because which groups are drawn together depends on the
# filters: two groups that never apply to the same logic may share an option
# safely. An option belongs in exactly one of the groups that clash; if both
# need it, the entries in one of them have to do without and rely on a logic
# entry that reaches the code at the shipped default instead.
declare -A option_group=()
clashes=0
for entry in "${LOGIC_SETS[@]}"; do
  IFS='|' read -r gen logic_opts <<< "$entry"
  read -r -a gen_args <<< "$gen"
  option_group=()
  # The logic's own options go on the same command line, so they are part of
  # the check: a group naming --array-equality would collide with the entries
  # that carry it.
  for opt in $(echo "$logic_opts" | grep -o -- '--[a-zA-Z0-9.][a-zA-Z0-9.-]*'); do
    option_group[$opt]="the logic entry"
  done
  for gname in "${OPTION_GROUPS[@]}"; do
    filter=${GROUP_LOGIC_FILTER[$gname]:-}
    if [ -n "$filter" ] && [[ ${gen_args[0]} != $filter ]]; then continue; fi
    declare -n group="g_$gname"
    # Within a group only one entry is drawn, so a name repeated across that
    # group's entries is fine; sort -u makes this per-group, not per-entry.
    for opt in $(printf '%s\n' "${group[@]}" \
                 | grep -o -- '--[a-zA-Z0-9.][a-zA-Z0-9.-]*' | sort -u); do
      owner=${option_group[$opt]:-}
      if [ -n "$owner" ] && [ "$owner" != "$gname" ]; then
        echo "Groups '$owner' and '$gname' both set $opt, and both are drawn" >&2
        echo "  for ${gen_args[0]}. STP refuses a command line that names it twice." >&2
        clashes=$(( clashes + 1 ))
      else
        option_group[$opt]=$gname
      fi
    done
    unset -n group
  done
done
if [ "$clashes" -gt 0 ]; then
  echo "Fix the groups above; every iteration drawing both would be a bogus" >&2
  echo "mismatch rather than a test." >&2
  exit 1
fi

# Summed over the logics rather than a flat product, because a filtered group
# contributes only to the logics it applies to.
combinations=0
for entry in "${LOGIC_SETS[@]}"; do
  read -r -a gen_args <<< "${entry%%|*}"
  per_logic=1
  for gname in "${OPTION_GROUPS[@]}"; do
    filter=${GROUP_LOGIC_FILTER[$gname]:-}
    if [ -n "$filter" ] && [[ ${gen_args[0]} != $filter ]]; then continue; fi
    declare -n group="g_$gname"
    per_logic=$(( per_logic * ${#group[@]} ))
    unset -n group
  done
  combinations=$(( combinations + per_logic ))
done
echo "$combinations combinations"

#Don't want to fill up SHM.
# The marker goes too, so a clean exit leaves the directory empty and fuzz.sh
# can rmdir it. A run killed outright leaves the marker behind, which is what
# lets the next run recognise the directory as its own and wipe it.
trap 'rm -f -- *.smt2 expression.txt first.txt second.txt first-err.txt second-err.txt "$marker"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

# timeout(1) exits 124, or 128+9 when the grace period passes and it has to
# KILL. A file where either solver runs out is skipped rather than saved: a
# timeout says nothing about correctness.
timed_out() { [ "$1" -eq 124 ] || [ "$1" -eq 137 ]; }

while (true)
  do
    # One logic per iteration. Drawn before the options because a group can be
    # restricted to particular logics.
    entry=${LOGIC_SETS[ $RANDOM % ${#LOGIC_SETS[@]} ]}
    IFS='|' read -r gen logic_opts <<< "$entry"
    read -r -a gen_args <<< "$gen"
    read -r -a logic_args <<< "$logic_opts"
    logic=${gen_args[0]}

    # One pick per applicable group, concatenated. Empty picks contribute
    # nothing, so an all-empty draw leaves $se empty and tests the default
    # configuration.
    se=""
    for gname in "${OPTION_GROUPS[@]}"; do
      filter=${GROUP_LOGIC_FILTER[$gname]:-}
      if [ -n "$filter" ] && [[ $logic != $filter ]]; then continue; fi
      declare -n group="g_$gname"
      pick=${group[ $RANDOM % ${#group[@]} ]}
      if [ -n "$pick" ]; then se="${se:+$se }$pick"; fi
      unset -n group
    done

    # The logic's own STP options join the ones just drawn, so e.g. an
    # extensional entry always gets the option that lets STP read the file at
    # all.
    if [ "${#logic_args[@]}" -gt 0 ]; then se="${se:+$se }${logic_args[*]}"; fi

    # Without this check a generation failure is silent: no files appear,
    # nothing runs, and the loop spins at full speed testing nothing.
    if ! java -jar "$FUZZSMT_JAR" "${gen_args[@]}" -g -bulk-export "$QUERIES" \
              -seed `od -A n -t d -N 3 /dev/urandom`; then
      echo "fuzzsmt failed to generate '$entry' problems" >&2
      exit 1
    fi
    if ! compgen -G '_file*.smt2' > /dev/null; then
      echo "fuzzsmt wrote no _file*.smt2, is -bulk-export supported?" >&2
      exit 1
    fi

    echo "$se" > expression.txt
    for problem in _file*.smt2; do
      # Both solvers on the one file, concurrently. A file either solver
      # cannot answer inside TIMEOUT is skipped: a timeout says nothing
      # about correctness, and skipping is what keeps a slow checker (or a
      # hard instance) from stalling the run.
      timeout "$TIMEOUT" "$CHECKER" "$problem" > first.txt 2> first-err.txt &
      checker_job=$!
      # $se is deliberately unquoted, some entries are two options. The
      # subshell is where the stack limit checked at startup takes effect;
      # timeout and STP inherit it.
      (ulimit -S -s "$STP_STACK_KB" &&
       exec timeout "$TIMEOUT" "$STP" $se -d "$problem") \
        > second.txt 2> second-err.txt
      stp_rc=$?
      wait "$checker_job"
      checker_rc=$?
      if timed_out "$stp_rc" || timed_out "$checker_rc"; then
        continue
      fi

      # The comparison only means something when the checker produced an
      # answer: a checker that crashes or rejects the file (bitwuzla 0.9.1
      # segfaults on some of the floating-point-array files) says nothing
      # about STP, so such files are skipped like timeouts. STP gets no
      # such pass -- against a checker that answered, an STP crash garbles
      # or truncates second.txt and is reported as the mismatch it is.
      read -r checker_answer < first.txt || checker_answer=""
      case $checker_answer in
        sat|unsat) ;;
        *) continue;;
      esac

      if cmp -s first.txt second.txt; then
        continue
      fi

      # Without this check a full or unwritable FAIL_DIR would leave
      # $failure empty, cp would fail, and the evidence for a real bug
      # would be gone by the next iteration.
      if ! failure=$(mktemp -d "$FAIL_DIR/XXXXXX"); then
        echo "Could not create a directory under $FAIL_DIR to save a" >&2
        echo "mismatch in. Stopping rather than discarding it." >&2
        exit 1
      fi
      cp -- "$problem" expression.txt first.txt first-err.txt \
            second.txt second-err.txt "$failure"
      {
        echo "kind:    mismatch"
        echo "when:    $(date '+%Y-%m-%d %H:%M:%S')"
        echo "file:    $problem"
        echo "logic:   $entry"
        echo "options: $se"
        echo "stp:     $STP (exit $stp_rc)"
        echo "checker: $CHECKER (exit $checker_rc)"
      } > "$failure/what-happened.txt"
      echo -n "[mismatch $failure]"
    done
    echo -n "#"
    rm -f -- *.smt2 expression.txt first.txt second.txt first-err.txt second-err.txt
done
