#!/bin/bash
#
# Differential fuzzing of STP against a trusted reference solver.
#
# Each iteration generates a batch of random problems with FuzzSMT, then runs
# STP -- under a randomly chosen option setting -- and the reference solver on
# each problem file individually, both under a short wall-clock timeout. A
# file is skipped unless both solvers finish and the checker answered
# sat/unsat to every (check-sat) in it; a file where the answers then differ
# is copied aside with both outputs. An STP crash counts: it truncates or
# garbles STP's answer, so it differs from the answer the checker gave.
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
#   CHECKER       The default reference solver, invoked as
#                 "$CHECKER file.smt2" on every logic entry that does not
#                 name a checker of its own. Default: bitwuzla. Anything
#                 that prints one sat/unsat line per query and understands
#                 the bit-vector overflow predicates works; z3 5.0.0 and
#                 bitwuzla 0.9.1 were both checked. This is probed at
#                 startup, because a solver that gets it wrong turns every
#                 file into a bogus mismatch -- z3 4.8.12 and boolector
#                 3.0.1 both fail it, the latter on bvnego.
#
#                 A slow checker costs coverage rather than correctness:
#                 files it cannot answer inside TIMEOUT are skipped, and the
#                 checker's speed decides how much of the hard tail gets
#                 checked at all. That is what makes bitwuzla the default --
#                 on the floating-point-array files that crashed a pre-fix
#                 build it answers about 4 in 5 inside 10s where z3 5.0.0
#                 answers essentially none, so with z3 those crashes would
#                 be skipped as checker timeouts rather than reported.
#
#                 No one checker covers every logic, though: bitwuzla has no
#                 reals and refuses QF_AX, and on uninterpreted sorts it
#                 warns and answers "unknown". So the checker is per entry.
#                 The entries for those logics name z3 themselves (see
#                 LOGIC_SETS below), and setting CHECKER replaces only the
#                 default: an entry that names a checker keeps it, because
#                 it names one exactly where the default cannot answer.
#
#                 Every (logic, checker) pair in use is probed at startup
#                 with a query in that logic. An entry whose checker is
#                 missing or fails its probe is dropped with a warning and
#                 the run goes on with the others; only when nothing is
#                 left does it stop.
#   FUZZSMT_JAR   fuzzsmt.jar, from the FuzzSMT release of Brummayer and Biere,
#                 "Fuzzing and Delta-Debugging SMT Solvers" (SMT'09).
#                 Default: searched for next to the source tree and in $HOME.
#   LOGICS        Logics to generate, with the FuzzSMT options that go with
#                 each, after a '|' the STP options that logic needs, and
#                 after a second '|' the checker for it. One entry per line,
#                 or separated by ';'. Overrides the built-in list below.
#                 For example
#
#                   LOGICS='QF_BV
#                           QF_ABV -mxn 1 -Mxn 3 | --array-equality
#                           QF_LRA | | z3' ./fuzz_single.sh
#
#                 One entry is drawn at random per iteration. See the comment
#                 on LOGIC_SETS below for the full syntax.
#
#   LOGIC         A single entry, for the same purpose. Ignored if LOGICS is
#                 set. Default: the built-in list.
#   QUERIES       Problem files generated per iteration. Default: 2500.
#   TIMEOUT       Per-solver wall-clock seconds per (check-sat), so a session
#                 of n checks gets n times this; a file where either solver
#                 runs out is skipped. Default: 10.
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

# The default reference solver. Whether it, or the checker an entry names, can
# be run at all is settled per entry below, with the probe.
CHECKER=${CHECKER:-bitwuzla}

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
#   <logic> [FuzzSMT options] [| STP options [| checker]]
#
# The part before the '|' is passed to the generator, with `-g` (unguarded
# division) and `-bulk-export` appended, so entries need not repeat those. The
# part after it is handed to STP on top of the options drawn from the groups
# below -- that is for options a logic cannot be tested without, not for ones
# that merely deserve coverage: those belong in a group, where they get
# combined with everything else.
#
# The third part names the reference solver for the entry, where the default
# CHECKER cannot answer the logic; left out, the entry uses CHECKER. An entry
# that needs a checker but no STP options leaves the middle part empty:
# "QF_LRA | | z3".
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
# Bit-vectors and floating point with no arrays in the way, so the
# conversions between the two theories are what the query is about. -mconv
# is how many conversions FuzzSMT writes in each direction; at 2..6 fp.to_ubv
# appears in 91 files of 100 against 80 at the default 1..4, and a rounding
# to_fp from a bit-vector in 99.
"QF_BVFP -mconv 2 -Mconv 6"
# All of it at once: arrays whose index and element sorts are drawn from the
# bit-vector and floating-point sorts, uninterpreted functions, and the
# conversions. FuzzSMT declares the functions over bit-vectors only, but it
# applies them to terms converted out of floating point, and 85 files in 100
# have an application whose argument depends on a floating-point term. The
# counts follow the QF_AUFBV entry, without its -ref 3, which here takes the
# checker's timeouts from 13 files in 100 to 20. --array-equality because
# FuzzSMT compares whole arrays by default in this logic: without it STP
# refuses 69 files in 100.
"QF_AUFBVFP -mf 2 -Mf 4 -mp 1 -Mp 3 -mr 4 -Mr 12 -mw 2 -Mw 8 | --array-equality"
# The logics below are ones the default checker cannot answer, so each names
# z3. bitwuzla refuses QF_AX and the real logics outright, and on QF_UF it
# warns about equalities over uninterpreted sorts and answers "unknown".
#
# Uninterpreted sorts and functions over them, with nothing else. -ref 2 is
# what makes FuzzSMT apply a function to arguments that may be equal: at the
# generator's defaults --uf-ackermann on changes nothing in 60 files, here 19.
"QF_UF -mv 2 -Mv 4 -ref 2 | | z3"
# Arrays over two declared sorts, Index and Element. A few more reads and
# writes than the default: --ackermanize changes 34 files in 60 here against
# 24.
"QF_AX -mw 3 -Mw 12 -mr 3 -Mr 12 | | z3"
# Linear real arithmetic. FuzzSMT writes integer literals where a Real is
# expected, (> x 1) rather than (> x 1.0); STP reads them as reals, and the
# checker's startup probe asks for the same. The default -Mv 3 -Mc 3 builds
# tableaux too small for much of the lra group to act on; at these counts
# most of the simplex settings change 43 to 55 files in 60. Nearly every file
# is satisfiable.
"QF_LRA -mv 2 -Mv 5 -mc 2 -Mc 5 | | z3"
# The same with every atom asserted at the top level (-bool-and), which is
# what the presolve wants: definitions to substitute, bounds to derive, rows
# to drop. On the entry above the bound presolve is the only part that
# changes more than one file in 60; here all of it does. The price is that
# nearly every file is unsatisfiable, which the entry above balances.
"QF_LRA -bool-and | | z3"
# Uninterpreted functions over Real, decided by lazy congruence rounds. More
# functions and predicates than the default so that the rounds have
# something to break: the uflra group's round settings change 28 to 38 files
# in 60 here against 19 to 25 at the default counts.
"QF_UFLRA -mf 2 -Mf 4 -mp 1 -Mp 3 | | z3"
# Floating point and real arithmetic in one query -- the only entry that draws
# the fp and lra groups together; every other entry reaches one family or the
# other. -mconv 0 -Mconv 0 is load-bearing rather than tidying: the
# conversions FuzzSMT writes for an FP-and-Real logic include to_fp of a
# symbolic Real, which STP refuses by design ("only a Real constant converts
# to a float"), and it writes both directions under the one setting, so at
# any other -mconv every file dies in the parser. Without them the two
# theories sit side by side in one formula, which is the part nothing else
# covers.
#
# 29 of 30 files get a comparable answer from both STP and z3 inside the
# harness's own budget of TIMEOUT per check-sat, a better yield than most
# entries (the QF_ABVFP entry emits a CNF on 11 of 30). Measured on stp -s
# against no options: the fp group changes 21 of 30 files
# (--bb.fp-native-cmp=0) and 4 of 30 (--bb.fp-native-all=1), the lra group 9
# of 30 (--lra-soi=1) and 7 of 30 (--lra-row-order=2), with
# --lra-presolve-rows=0 inert on all 30. No STP/z3 disagreement in 30 files,
# so this is coverage rather than a find.
#
# The lra counts are a floor, not a measurement of the group: the LRA
# counters are printed by -t, and -t output is not reproducible between two
# identical runs -- 12 of 30 files differed on a control run after the
# obvious timing fields were normalised away -- so -s is the only surface
# that can be diffed, and it does not carry them.
"QF_FPLRA -mvf 3 -Mvf 6 -mcf 2 -Mcf 4 -mvrm 1 -Mvrm 2 -mv 2 -Mv 5 -mc 2 -Mc 5 -mconv 0 -Mconv 0 | | z3"
# Sessions. FuzzSMT's -incremental follows the formula's (check-sat) with
# further rounds, -mcs to -Mcs of them (default 1 to 3), each one to three
# of: push of one or two levels, pop of some of them, and assert of a fresh
# formula over the same constants; then (check-sat). About 85 files in 100
# push at least once. Everything a single-check file never reaches runs
# here: the assertion stack and its retraction on pop, the batch pipeline
# re-solving across pushes, and the persistent driver, which the default
# 'auto' engages at the 3rd solve on the non-bit-vector logics and the 32nd
# on QF_BV/QF_ABV -- so on a bit-vector session only the session group and
# the misc group's --incremental=on reach it. One entry per theory, with the
# generator counts of the single-check entry that found most, so a session
# carries the same terms the single-check files do. The second QF_BV entry
# has sessions of 9 to 17 checks, where the driver's adaptive policies have
# a history to act on; its rebuild and promotion limits still moved nothing
# there, see the session group. A session shares its checker with the
# single-check entry: both bitwuzla and z3 take push and pop as they come.
"QF_BV -incremental"
"QF_BV -incremental -mcs 8 -Mcs 16"
"QF_ABV -mxn 1 -Mxn 3 -mw 3 -Mw 10 -Mar 5 -incremental | --array-equality"
"QF_ABV -mar 1 -Mar 1 -mw 20 -Mw 40 -mr 8 -Mr 20 -mv 4 -Mv 8 -incremental"
"QF_ABVFP -mr 12 -Mr 30 -mw 4 -Mw 12 -Mar 3 -incremental | --array-equality"
"QF_FP -mvf 3 -Mvf 8 -mcf 2 -Mcf 6 -mvrm 1 -Mvrm 2 -ref 3 -incremental"
"QF_UFBV -mf 3 -Mf 5 -mp 2 -Mp 4 -ma 1 -Ma 2 -ref 3 -mv 2 -Mv 4 -mbw 2 -Mbw 8 -incremental"
"QF_AUFBV -mf 2 -Mf 4 -mp 1 -Mp 3 -ref 3 -mr 4 -Mr 12 -mw 2 -Mw 8 -incremental"
"QF_BVFP -mconv 2 -Mconv 6 -incremental"
"QF_UF -mv 2 -Mv 4 -ref 2 -incremental | | z3"
"QF_AX -mw 3 -Mw 12 -mr 3 -Mr 12 -incremental | | z3"
"QF_LRA -mv 2 -Mv 5 -mc 2 -Mc 5 -incremental | | z3"
"QF_UFLRA -mf 2 -Mf 4 -mp 1 -Mp 3 -incremental | | z3"
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
echo "checker: $CHECKER (the default; an entry may name its own)"
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

# An entry's parts: generator | STP options | checker. The later ones come out
# empty when the entry stops short of them, and an empty checker means the
# default. Trimmed, so "QF_LRA | | z3" names z3 and not " z3".
parse_entry() {
  IFS='|' read -r gen logic_opts entry_checker <<< "$1"
  read -r -a gen_args <<< "$gen"
  read -r -a logic_args <<< "$logic_opts"
  read -r entry_checker <<< "$entry_checker"
  entry_checker=${entry_checker:-$CHECKER}
}

# The startup probe's query for a logic: something small and satisfiable that
# uses what the generated files use, so a checker that would choke on them
# chokes here instead. What FuzzSMT writes that older or narrower solvers
# trip on:
#   - the bit-vector overflow predicates. z3 4.8.12 answers the query anyway
#     and prints an extra (error ...) line, so it neither fails outright nor
#     gives a usable answer, and every file would land in FAIL_DIR looking
#     like an STP bug.
#   - integer literals where a Real is expected, as in (> (+ x y) 1).
#   - uninterpreted sorts. bitwuzla accepts them, warns, and answers
#     "unknown" -- which the main loop skips file after file, so the logic
#     would run for hours and check nothing.
# A logic with no clause here still gets (assert true), which says at least
# whether the checker accepts the logic name.
#
# For a session entry ($2 set) the query goes on to push a contradiction,
# check, pop it and check again, and the checker has to answer sat, unsat,
# sat: one that takes push and pop but does not retract on pop would turn
# every session into a mismatch.
probe_query() {
  local logic=$1 incremental=${2:-} sort=""
  echo "(set-logic $logic)"
  case $logic in
    *BV*)
      sort='(_ BitVec 8)'
      echo "(declare-fun x () $sort)"
      echo "(declare-fun y () $sort)"
      for p in bvnego bvsaddo bvsdivo bvsmulo bvssubo bvuaddo bvumulo bvusubo; do
        if [ "$p" = bvnego ]; then
          echo "(assert (or (bvnego x) true))"
        else
          echo "(assert (or ($p x y) true))"
        fi
      done
      ;;
    *LRA*)
      sort=Real
      echo "(declare-fun x () Real)"
      echo "(declare-fun y () Real)"
      echo "(assert (> (+ x y) 1))"
      ;;
    QF_UF|QF_AX)
      sort=S
      echo "(declare-sort S 0)"
      echo "(declare-fun x () S)"
      echo "(declare-fun y () S)"
      echo "(assert (distinct x y))"
      ;;
    *)
      echo "(assert true)"
      ;;
  esac
  if [ -n "$sort" ] && [[ $logic == *UF* ]]; then
    echo "(declare-fun f ($sort) $sort)"
    echo "(assert (distinct (f x) (f y)))"
  fi
  if [ -n "$sort" ] && [[ $logic == QF_A* ]]; then
    echo "(declare-fun a () (Array $sort $sort))"
    echo "(assert (= (select (store a x y) x) y))"
  fi
  if [[ $logic == *FP* ]]; then
    echo "(declare-fun z () Float32)"
    echo "(assert (not (fp.isNaN (fp.add RNE z z))))"
  fi
  echo "(check-sat)"
  if [ -n "$incremental" ]; then
    echo "(push 1)"
    echo "(assert false)"
    echo "(check-sat)"
    echo "(pop 1)"
    echo "(check-sat)"
  fi
}

# Whether a generator part asks for a session. A word match, so that a
# generator option that merely starts with it would not count.
is_session() { [[ " $1 " == *" -incremental "* ]]; }

# Check every entry actually generates what it says. A misspelt generator
# option is rejected outright, but a misspelt *logic* is not: FuzzSMT prints
# its usage text to stdout and exits 0, so without this the run would happily
# compare two solvers on a file of banner text. Requiring the emitted header to
# name the logic we asked for catches both.
#
# Then check the entry's checker, once per logic and checker, since what a
# solver accepts depends on the logic. A failure drops the entry rather than
# stopping the run: the other logics are still worth fuzzing, and the warning
# says what was lost.
echo "logics:"
declare -A probe_failure=()
declare -a kept_logics=()
for entry in "${LOGIC_SETS[@]}"; do
  parse_entry "$entry"
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

  session=""
  expected=sat
  if is_session "$gen"; then
    session=1
    expected=$'sat\nunsat\nsat'
  fi
  key="${gen_args[0]}|$entry_checker|$session"
  if [ -z "${probe_failure[$key]+set}" ]; then
    if ! command -v "$entry_checker" > /dev/null && [ ! -x "$entry_checker" ]; then
      probe_failure[$key]="checker '$entry_checker' not found"
    else
      probe_query "${gen_args[0]}" "$session" > probe.smt2
      probe_out=$(timeout 60 "$entry_checker" probe.smt2 2>&1)
      probe_rc=$?
      if [ "$probe_rc" -ne 0 ] || [ "$probe_out" != "$expected" ]; then
        probe_failure[$key]="checker '$entry_checker' failed the probe"
        probe_failure[$key]+=" for ${gen_args[0]} (exit $probe_rc):"
        probe_failure[$key]+=" $(echo "$probe_out" | head -3 | tr '\n' ' ')"
      else
        probe_failure[$key]=""
      fi
    fi
  fi
  if [ -n "${probe_failure[$key]}" ]; then
    printf '  %s\n' "$entry  -- SKIPPED, ${probe_failure[$key]}" >&2
    continue
  fi
  kept_logics+=("$entry")
  printf '  %-72s [%s]\n' "$entry" "$entry_checker"
done
rm -f probe.smt2
LOGIC_SETS=("${kept_logics[@]}")
if [ "${#LOGIC_SETS[@]}" -eq 0 ]; then
  echo "Every logic was skipped, there is nothing left to generate." >&2
  echo "A checker has to print exactly 'sat' for its probe query (and 'unsat'" >&2
  echo "then 'sat' for a session's pushed contradiction): upgrade it," >&2
  echo "or set CHECKER, or the entry's own checker, to one that does." >&2
  exit 1
fi

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
# not something to draw per iteration. The same goes for --parse-only, which
# replaces the answer with something else entirely.

declare -a OPTION_GROUPS=(simplify mult div shift bitblast abstract array uf
                          ufsort fp fpabs lra uflra cnf solver bias misc
                          session)

# A group named here is drawn only for the logics it applies to, which is how
# options that do nothing outside one theory stay out of the draw everywhere
# else. The value is a list of shell globs, any one of which may match the
# logic name. A glob may carry a generator option after a colon, as in
# '*BV*:-incremental'; it then matches only an entry whose generator options
# include that word, which is how the session group is drawn for the
# -incremental entries alone.
#
# Write each against every logic name in LOGIC_SETS, not against the one the
# group was written for. '*A*' reads as "has arrays" and was this file's
# array filter until QF_LRA and QF_UFLRA arrived, both of which it matches;
# arrays are the logics whose name starts QF_A.
#
# The bit-vector groups are drawn wherever bit-vector terms exist, which is
# more than the logics with BV in their name: floating point is blasted
# through bit-vector circuits, and QF_UF and QF_AX give each declared sort a
# bit-vector carrier (--uf-sort-width). Where a group stops is measured, every
# entry of every group on 20 files of each new logic: the arithmetic groups
# change nothing on QF_UF, QF_AX or the real logics; the abstraction group
# changes nothing on the real logics beyond the CNF encoder cnf-auto picks
# (the cnf group covers that); and neither incremental entry changes anything
# on them.
declare -A GROUP_LOGIC_FILTER=(
[mult]='*BV* *FP*'
[div]='*BV* *FP*'
[shift]='*BV* *FP*'
[bitblast]='*BV* *FP* QF_UF QF_AX'
[abstract]='*BV* *FP* QF_UF QF_AX'
[array]='QF_A*'
[uf]='*UF*BV* QF_UF'
[ufsort]='QF_UF QF_AX'
[fp]='*FP*'
[fpabs]='*FP*'
[lra]='*LRA*'
[uflra]='QF_UFLRA'
[misc]='*BV* *FP* QF_UF QF_AX'
[session]='*BV*:-incremental *FP*:-incremental QF_UF:-incremental QF_AX:-incremental'
)

# Whether group $1 is drawn for logic $2, generated with the options $3. read
# rather than a bare for loop, so the patterns are not expanded against the
# files in the working directory.
group_applies() {
  local filter=${GROUP_LOGIC_FILTER[$1]:-} pattern option
  local -a patterns
  [ -z "$filter" ] && return 0
  read -r -a patterns <<< "$filter"
  for pattern in "${patterns[@]}"; do
    option=""
    if [[ $pattern == *:* ]]; then
      option=${pattern#*:}
      pattern=${pattern%%:*}
    fi
    # Unquoted on purpose: it is a pattern.
    if [[ $2 == $pattern ]]; then
      if [ -z "$option" ] || [[ " $3 " == *" $option "* ]]; then return 0; fi
    fi
  done
  return 1
}

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
"--interval-sets=1"
"--simplify-to-constants-only=1"
"--size-reducing-fixed-point-limit=-1"
"--aig-core-simplification=1"

# Read-time folding of constants and identities, a different pass from the
# simplifier stack: it changed the -s output on all of 30 bit-vector, 30 plain
# floating-point and 30 floating-point-array files, and on all 90 again when
# drawn on top of --disable-simplifications, so neither subsumes the other.
"--no-simplify"

# This and the --flattening entry above are opt-outs because the flattening
# stack is on by default since #838, so an opt-in form only re-runs the
# baseline. Its third member --common-subsum has no entry either way: opting
# out of it is byte-identical on every generated file, the n-ary entry
# included, because the pass finds nothing to factor there.
"--pair-extract=0"

# Common factor extraction, also on by default and so also an opt-out. This
# one does earn an entry where --common-subsum does not: the generator
# builds sums whose products share an operand on about 1 file in 300 at the
# default shape and 3 in 300 at the -nary 8 -ref 3 entry above, so the two
# settings are not the same run.
"--common-factor=0"

# A bit-blasting option, but it lives here because #789 made it exclude
# --disable-opt-inc and --disable-simplifications, which are entries above.
# Drawn from its own group it would be paired with them roughly one iteration
# in a hundred, and STP now rejects that command line outright.
"--bb.simplify-during-bb=1"

# These two have given wrong answers in the past, so they get extra exposure
# here rather than being trusted.
"--unconstrained-variable-elimination=0"
"--aig-rewrite-passes=1"

# Replaces a shared one-step term of an unconstrained variable by a fresh
# variable constrained to the term's image. It needs that term shared, which
# FuzzSMT rarely writes: the CNF changed on 5/96 QF_BV files, 4/96 wide
# QF_BV, 5/136 QF_ABV and 5/146 QF_BVFP, and 0 on the n-ary and QF_UFBV
# entries. Here rather than a group of its own so it is never drawn beside
# --disable-simplifications or the entry above, which leave it inert.
"--unconstrained-image-vars=1"

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
# It used to abort on array logics ("BBTerm: Illegal kind to BBTerm" on a
# READ) and on floating-point ones: the pass now leaves out any term whose
# cone holds an array or floating-point operation, which its sub-solve
# cannot blast. Since then 345 files across the array, UF, FP and n-ary
# entries agree with the checker.
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
# Not drawn for QF_UFLRA, where every entry but the first measured identical
# to the default on 120 files: a function over Real is decided by the lazy
# congruence rounds, not the refinement loop these steer. That logic has the
# uflra group instead, which carries the one entry that does bite there.
#
# Deliberately absent, each measured identical on all 46 files the two
# bit-vector UF entries emit a CNF for, with the UF counters `stp -s` prints
# identical too, and again on 120 QF_UF and 120 QF_UFLRA files:
#   --uf-narrow-results=0        narrows result sorts used only for equality;
#                                on the bit-vector entries FuzzSMT feeds every
#                                application into arithmetic as well, and on
#                                QF_UF the result sorts are declared ones,
#                                which --uf-sort-width sizes instead.
#   --uf-inject-args=1           changes nothing on any of the three logics.
# --uf-propagate-equalities and --uf-skeleton-preproc do nothing on the
# bit-vector entries -- the pass substitutes a couple of asserted atoms on 6
# files in 30 and the CNF comes out byte-identical anyway -- but they bite on
# QF_UF and QF_UFLRA, so they have entries in the ufsort and uflra groups.
# Nor --uninterpreted-functions, which decides UF for a logic whose name
# omits it: FuzzSMT always names the logic correctly, so on the UF entries it
# asks for what already happens and on the others there is no UF to decide.
)

# Declared sorts, which only QF_UF and QF_AX have: STP gives each
# (declare-sort S 0) a bit-vector carrier --uf-sort-width bits wide, 16 by
# default. A narrower carrier is only sound while the query cannot name more
# elements of the sort than it holds; below 8 STP notices and answers
# "unknown" on some files (7 of 120 QF_AX files at 4, 11 at 1), which the
# fuzzer would save as mismatches, and at 64 the QF_AX solve slows until 33
# files in 120 time out. 8 changes the output on 98 of 120 QF_UF files and 85
# of 120 QF_AX ones, and answered every one.
#
# Turning --uf-propagate-equalities off is the other setting that does
# anything on QF_UF, and only just: 5 files in 120. --uf-skeleton-preproc=off
# changed 2 and has no entry.
declare -a g_ufsort=(
""
"--uf-sort-width=8"
"--uf-propagate-equalities=off"
)

# Linear real arithmetic. Drawn for the two real logics only: on the others
# there is no simplex to steer.
#
# Counts are files whose `stp -s` counters (the LRA-METRICS line, the CNF
# size and CaDiCaL's conflict, decision and propagation counts) moved, out of
# 60 files of the plain QF_LRA entry, then out of 120 of the -bool-and one
# where that is the entry that reaches the code. The simplex settings bite
# on the plain entry: theory propagation off 55, the float driver off 54,
# forcing the float-to-exact reroute 52, row orders 1 to 3 49, 43 and 48,
# singleton ordering 53, early conflicts 51, sum-of-infeasibilities repair 50,
# the first search connected 55, persistent state 55, dormant rows 38 and 28
# with a cell floor, decision polarity off 49, conflict recovery off 11,
# bound presolve off 55. The rest of the presolve wants top-level facts, which
# only the -bool-and entry asserts: unconstrained folding off 3, monotone
# elimination 4 (and 3 with its work budget at zero), propagation off 16, row
# dominance off 12, substitution off 22, a growth or work guard on
# substitution 22 each, eight rounds 3.
#
# The two verifiers move no counter by design: they re-derive what the
# solver already trusts, and abort if the two disagree. They are here for the
# same reason --bb.div-v2 is in the division group: what is fuzzed is the
# checking code, and a disagreement is exactly what the fuzzer wants to see.
declare -a g_lra=(
""
"--lra-theory-propagation=0"
"--lra-float-driver=0"
"--lra-float-reroute=1 --lra-float-reroute-floor=0"
"--lra-row-order=1"
"--lra-row-order=2"
"--lra-row-order=3"
"--lra-singleton-ordering=1"
"--lra-early-conflicts=1"
"--lra-soi=1"
"--lra-first-search=1"
"--lra-persistent-state=1"
# The Real session on its own, without the persistent state that implies it.
# Acts from the second check onwards, so only on the -incremental entries,
# where it changes the -t counters on 15 of 20 generated QF_LRA sessions
# (the persistent state, 16 of 20). It is here and not in a group of its own
# for the reason --lra-extension-mode=1 gives below.
"--lra-incremental-session=1"
"--lra-float-dormant-rows=1"
"--lra-float-dormant-rows=1 --lra-float-dormant-min-cells=3"
"--lra-decision-polarity=0"
"--lra-conflict-recovery=0"
"--lra-presolve-bounds=0"
"--lra-presolve-unconstrained=0"
"--lra-presolve-monotone=1"
"--lra-presolve-monotone=1 --lra-presolve-monotone-work=0"
"--lra-presolve-propagate=0"
"--lra-presolve-rows=0"
"--lra-presolve-subst=0"
"--lra-presolve-subst-growth=1"
"--lra-presolve-subst-growth=1000000 --lra-presolve-subst-work=0"
"--lra-presolve-rounds=8"
"--lra-verify-conflicts=1"
"--lra-verify-canonical=1"

# Only QF_UFLRA's congruence rounds extend the arithmetic of a solve already
# under way, so this acts there alone (reusing the extended problem changes
# 38 files in 60, and nothing on QF_LRA). It lives here anyway because the
# solver refuses it beside --lra-persistent-state or a --lra-row-order --
# "LRA extension controls require batch solves" -- and it does so at solve
# time, as SOLVER_ERROR, not on the command line. Drawn from a group of its
# own, every such pairing would be saved as a mismatch.
"--lra-extension-mode=1"

# Not here; see NOT_FUZZED for the list:
#   the HiGHS options, and the ReLU ones that need it: a build without HiGHS
#                          (the default) refuses to solve a real query under
#                          any of them, and the entry probe, which offers
#                          entries on a bit-vector query, cannot see that.
#   the other ReLU options, the model reconstruction and screening settings:
#                          they act on a network of ReLU definitions, which
#                          FuzzSMT never writes, and moved nothing on 120
#                          plain QF_LRA files.
#   --lra-extension-mode=2 and 3, --lra-extension-restart-float-basis:
#                          on QF_UFLRA, where extensions happen, these moved
#                          at most 2 files in 60 beyond noise.
#   --lra-extension-restart-sat  copying the formula into a fresh CaDiCaL
#                          search moves 38 files in 60 on QF_UFLRA, but it is
#                          refused at solve time beside --cadical-factor on,
#                          which the solver group draws ("LRA SAT search reset
#                          requires CaDiCaL with factoring disabled": 188 of
#                          300 files), and beside --lra-persistent-state.
#                          Until the two refusals are made on the command line
#                          there is no group it can go in.
#   --lra-direct-bounds    1 moved 1 file of 240, and 2 answered "unknown" on
#                          a file the checker and STP's default call sat.
#   --lra-float-promotion-budget, --lra-dense-recovery, and
#   --lra-float-reroute=0  never reached: nothing generated trips the float
#                          tableau's limits.
#   the budgets in seconds are wall-clock.
)

# UF over Real, which QF_UFLRA alone has: those functions are decided by lazy
# congruence rounds rather than by the refinement loop the uf group steers.
# Counts are files whose counters moved, out of 60 of the QF_UFLRA entry.
# Keeping the running solve between rounds off 38; the round limit at 0 28,
# after which every remaining pair is stated at once; the full-expansion cap
# at 0 5; escalating to the transitive closure 8 on its own and 38 with a
# round limit that lets functions get stuck. --uf-ackermann on 53, the one
# uf-group entry that acts here -- off and the refinement knobs do not.
# Rewriting under top-level equalities, which auto skips when the query has
# Real content, 6, and 12 with the skeleton's facts as well. Separating
# model values off 5 of 60 against 2 of noise.
#
# --uf-congruence-closure=off and --uf-lazy-full-expansion-pairs=1 are
# absent: the first is what auto does below --uf-congruence-closure-min-apps,
# the second measured the same as 0.
declare -a g_uflra=(
""
"--uf-lazy-in-place=0"
"--uf-lazy-round-limit=0"
"--uf-lazy-full-expansion-pairs=0"
"--uf-congruence-closure=on"
"--uf-lazy-round-limit=1 --uf-lazy-full-expansion-pairs=0 --uf-congruence-closure=on"
"--uf-lazy-round-limit=1 --uf-lazy-full-expansion-pairs=0 --uf-congruence-closure-min-apps=1"
"--uf-ackermann on"
"--uf-propagate-equalities=on"
"--uf-propagate-equalities=on --uf-skeleton-preproc=on"
"--lra-separate-model-values=off"
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

# How the native fp.div relation spells its divisor-quotient product (#1225).
# Inert unless the native divider is on, so each entry pairs with it: drawn
# alone --bb.fp-div-product left the -s output identical on all 60 measured
# files, and paired it changed 16 of 30 plain floating-point files and 6 of 30
# array ones. product=2, which adds the redundant no-overflow clause on top of
# the ordinary bit-vector multiplier, changed 17/30 and 6/30. Spelling the
# product with the multiplier is also what lets --bb.mult-variant reach it, so
# these entries put the whole multiplier family behind fp.div.
"--bb.fp-native-div=1 --bb.fp-div-product=1"
"--bb.fp-native-div=1 --bb.fp-div-product=2"

# Absent because there is nothing to blast: --bb.fp-native-fma. FuzzSMT
# writes no fp.fma in either entry, so the option is byte-identical on all
# 60 files. It needs a logic entry that generates one before it is worth
# adding.
)

# Floating-point abstraction, the CEGAR path that replaces an operation with a
# surrogate of its own sort and refines it against the exact evaluator. Off by
# default, so every entry turns it on; drawn only for the FP logics, where it
# abstracts something on 61 of 80 plain floating-point files and 48 of 60
# floating-point-array ones. A group of its own rather than part of the fp
# group, so that it is drawn together with the native-circuit opt-outs.
#
# The counts below are files whose "FpAbstraction:" counters under `stp -s`
# moved against --fp-abstraction=1 alone, out of 80 plain and 60 array files.
# Which operations are abstracted, and how: all of them 60/48, chains of
# add/sub/rem 26/15, a width floor above binary32 56/34, the lower rule tiers
# 55/42, no reduced-precision bands 54/41 and none at binary128 6/6, and the
# two ways of overriding the constant-operand heuristic, off 48/28 and on 8/8.
# Declining pinned operations 47/30, and model repair off 21/10.
#
# Refinement is where generated queries seldom go -- 11 of the 140 took a
# value lemma -- so the entries that steer it bite on those files only:
# releasing at the first refuted candidate 2/9, releasing by restart rather
# than splicing 2/9 on top of that, box lemmas 1/8.
#
# The incremental entry only means something when the misc group draws
# --incremental=on, which it does one iteration in two, or on a QF_FP session
# of three or more checks, where the driver engages by itself; there it
# changes the whole -s output on 38 of 40 and 26 of 30 files. --incremental
# cannot be named here as well: the two groups are drawn together. The
# active-closure entry on top of it narrows the records checked to the
# active encoding units, which single-check files never tell apart (the -s
# output was identical on all 70 measured) and sessions do: 11 of 12
# generated QF_FP sessions, 6 of 12 beside --incremental=on.
declare -a g_fpabs=(
""
"--fp-abstraction=1"
"--fp-abstraction=1 --fp-abstraction-ops=all"
"--fp-abstraction=1 --fp-abstraction-chain-ops=add,sub,rem"
"--fp-abstraction=1 --fp-abstraction-width=64"
"--fp-abstraction=1 --fp-abstraction-tiers=0"
"--fp-abstraction=1 --fp-abstraction-tiers=1"
"--fp-abstraction=1 --fp-abstraction-significand-bits=0"
"--fp-abstraction=1 --fp-abstraction-significand-bits-wide=0"
"--fp-abstraction=1 --fp-abstraction-constant-operands=off"
"--fp-abstraction=1 --fp-abstraction-constant-operands=on"
"--fp-abstraction=1 --fp-abstraction-decline-pinned"
"--fp-abstraction=1 --fp-abstraction-repair=0"
"--fp-abstraction=1 --fp-abstraction-values=0"
"--fp-abstraction=1 --fp-abstraction-values=0 --fp-abstraction-restart-width=16"
"--fp-abstraction=1 --fp-abstraction-box-lemmas=1"
"--fp-abstraction=1 --fp-abstraction-incremental=1"
"--fp-abstraction=1 --fp-abstraction-incremental=1 --fp-abstraction-active-closure=1"

# Not here, each measured on the same 140 files:
#   --fp-abstraction-shape=0, --fp-abstraction-relational=0 and
#   --fp-abstraction-relational-last-width=16 steer lemmas a generated query
#                          hardly asks for: one file took a shape lemma and
#                          none a relational one, and the counters did not
#                          move under any of the three.
#   --fp-abstraction-phase-hints=1  moved no counter, CaDiCaL's conflict and
#                          decision counts included.
#   --fp-abstraction-restart-limit=0  releases by splicing, which is what the
#                          entry without a restart width already does:
#                          identical to it on all 140.
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
# Two writer options only the new-* rungs read, so each rides on one. On
# 19 QF_BV, 14 n-ary, 15 wide and 25 QF_UFBV files emitting a CNF:
# --cnf-link-shared-cells changed 5, 4, 4 and 23 of them under new-high,
# and --cnf-complete-ite 7, 6, 6 and 23 under new-medium. Under new-high
# --cnf-complete-ite changed none, so it does not ride on that rung.
"--cnf-generation-effort=new-high --cnf-link-shared-cells=1"
"--cnf-generation-effort=new-medium --cnf-complete-ite=1"
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
# across (check-sat) commands. A single-check file never reaches it, and the
# default 'auto' switches over for an input that pushes, and then only from
# the 32nd solve on QF_BV/QF_ABV and the 3rd elsewhere, so of the sessions
# the -incremental entries generate only the non-bit-vector ones of three or
# more checks engage it by default. 'on' engages it from the first solve,
# pushes or no pushes, which a profile confirms: the encoding is built and
# solved through the driver rather than the batch pipeline on every file.
# --core-only is the same driver without its fitted preprocessing and
# adaptive policies, and changes the work counters on 30/30.
#
# The rest of the --incremental-* family acts from the second check onwards,
# so it is drawn for the -incremental entries alone, from the session group
# below.
#
# Sharing this group with --interactive makes one iteration in two an
# incremental one. Giving these entries a group of their own would raise
# that, at the cost of every other iteration carrying the driver too. The
# fpabs group's --fp-abstraction-incremental relies on this group: it acts
# only in an iteration that has drawn the driver.
declare -a g_misc=(
""
"--interactive=1"
"--incremental=on"
"--incremental=on --incremental-core-only"
)

# The driver's session settings, drawn for the -incremental entries alone:
# each acts from the second (check-sat) onwards and moved no counter on 30/30
# single-check files. Measured against the counters --incremental-profile
# prints, times stripped, on 75 generated sessions of 2 to 4 checks across
# QF_BV, QF_ABV, QF_FP and QF_UFBV, and on 35 QF_BV/QF_ABV sessions of 9 to
# 17.
#
# --incremental-auto-engage-at is the 'auto' policy's threshold. The default
# engages the driver at the 32nd solve on QF_BV/QF_ABV and the 3rd elsewhere,
# so 1 and 2 (63/75) and 3 (37/75) are what reach the switch-over from the
# batch pipeline to the driver mid-session on a bit-vector logic at all, and
# 0 (4/75, the floating-point files; 9/12 on a QF_FP corpus) keeps the batch
# pipeline through a session the default would hand over. Unlike the misc
# group's --incremental=on these act only on a session that pushes, so about
# 15 files in 100 stay batch under them.
#
# The knobs ride on an engagement at the first solve, so that they act on
# every pushing file rather than only in the iterations where the misc group
# draws the driver: the CBP reset oracle 30/75 and 33/35, the CBP feed cap
# at its floor of 1 (0 is refused) 41/75, scoped preprocessing 55/75.
declare -a g_session=(
""
"--incremental-auto-engage-at=1"
"--incremental-auto-engage-at=2"
"--incremental-auto-engage-at=3"
"--incremental-auto-engage-at=0"
"--incremental-auto-engage-at=1 --incremental-cbp-reset"
"--incremental-auto-engage-at=1 --incremental-cbp-feed-cap=1"
"--incremental-auto-engage-at=1 --incremental-scoped-preprocessing=1"

# Not here, each 0/75 and 0/35 beside --incremental=on:
#   --incremental-cbp-bootstrap-limit=1  defers the CBP bootstrap of a forced
#                          first solve over a stack of more than one level,
#                          and a generated session's first check comes before
#                          its first push (cbp-bootstrap-deferred stayed 0 on
#                          all 110).
#   --incremental-base-resimplify-limit=0  acts in a memory-relief rebuild,
#                          which no generated session triggered
#                          (rebuild-relief stayed 0 on all 110).
#   --incremental-reencode-limit=1, --incremental-semantic-cache-limit=1:
#                          a rebuild needs most of the encoding to belong to
#                          popped content, which 17 checks of push, pop and
#                          assert do not leave behind.
#   --no-incremental-promote-units  promotion waits for a level to stay pushed
#                          across many solves.
#   --incremental-piece-rewriting=1  moved nothing, driver-clauses included,
#                          on the -nary 8 -ref 3 files among the 75 as well.
#   --incremental-inprobing  'auto' retires probing after many solves, more
#                          than a generated session has, so on and off both
#                          equal it.
#   --incremental-profile  prints the counters this group was measured by,
#                          to stderr, and decides nothing.
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
--print-counterex --print-functionstat --print-quickstat --print-nodes
--print-output
# Already fixed by the harness: -d is passed to every STP run, and the input
# is SMT-LIB2, the only language STP reads.
--check-sanity --SMTLIB2
# Answer-replacing in the same way: --stop-after-cnf answers "unknown" by
# design, so every file drawn with it would be saved as a mismatch.
--stop-after-cnf
# Decided elsewhere, or a second spelling of something already drawn: the
# file's own set-logic decides --logic, --sat-backend names the same backends
# the solver group draws by their own flags, and --simplify is the default-on
# half of the --no-simplify pair that the simplify group now draws.
--logic --sat-backend --simplify
# Not part of the encoding: --produce-models only toggles model building, and
# -d already asks for the answer the checker is compared against. --random-seed
# re-rolls the backend's randomisation and changes no clause; a fresh generated
# query every iteration already varies the search far more.
--produce-models --random-seed
# Measured inert on every generated file; see the group comments below for
# what each would need before it is worth an entry.
--bb.fp-native-fma --bb.fp-native-known-sign
--fp-domain-simplify --fp-domain-derived-bounds --fp-domain-extremal-selectors
--fp-domain-sound-zero-facts --fp-domain-row-bounds
--mulo-recognition --distinct-ordering --skeleton-preproc
--embedded-constraints --common-subsum --common-subsum-budget --switch-word
--uninterpreted-functions --uf-narrow-results --uf-inject-args
--congruence-candidate-limit --congruence-candidate-conflicts
# CaDiCaL's variable elimination settings. They need --cadical, but paired
# with it every one of elim=0, mineff=maxeff=0 and a raised minimum left
# the conflict, decision and propagation counts identical on all 108
# bit-vector, UF and floating-point files answered.
--cadical-elim --cadical-elimmineff --cadical-elimmaxeff
# Wall-clock: whether the budget fires depends on how loaded the machine is,
# so a mismatch drawn with it would not reproduce.
--fp-abstraction-budget
# Linear real arithmetic that no generated query reaches; see the comment at
# the end of the lra group. The HiGHS options, and the two ReLU ones that
# need it, are refused on a real query by a build without HiGHS, which is the
# default:
--lra-highs-replay --lra-highs-replay-nodes --lra-highs-cuts
--lra-highs-cut-limit --lra-highs-mip --lra-highs-lp --lra-relu-lp
--lra-relu-branch
# They act on networks of ReLU definitions, which FuzzSMT does not write:
--lra-relu-bounds --lra-relu-cases --lra-relu-lp-rounds
--lra-relu-property-branches --lra-relu-branch-nodes --lra-model-reconstruction
--lra-replay-screen --lra-boolean-bounds --lra-lp-screen --lra-lp-partial
# Nothing generated reaches them, or they moved too few files to be worth a
# draw; --lra-direct-bounds=2 also answers "unknown" on a satisfiable file:
--lra-dense-recovery --lra-float-promotion-budget --lra-direct-bounds
--lra-extension-restart-float-basis
# Refused at solve time beside --cadical-factor on; see the lra group.
--lra-extension-restart-sat
# Wall-clock budgets, and inert besides:
--lra-highs-seconds --lra-relu-auto-seconds --lra-relu-cases-seconds
--lra-relu-lp-seconds --lra-relu-lp-call-seconds --lra-relu-branch-seconds
# Driver settings the generated sessions never reach; the session group says
# why, each.
--incremental-profile --incremental-cbp-bootstrap-limit
--incremental-base-resimplify-limit --incremental-reencode-limit
--incremental-semantic-cache-limit --incremental-promote-units
--incremental-piece-rewriting --incremental-inprobing
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
  parse_entry "$entry"
  option_group=()
  # The logic's own options go on the same command line, so they are part of
  # the check: a group naming --array-equality would collide with the entries
  # that carry it.
  for opt in $(echo "$logic_opts" | grep -o -- '--[a-zA-Z0-9.][a-zA-Z0-9.-]*'); do
    option_group[$opt]="the logic entry"
  done
  for gname in "${OPTION_GROUPS[@]}"; do
    group_applies "$gname" "${gen_args[0]}" "$gen" || continue
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
  parse_entry "$entry"
  per_logic=1
  for gname in "${OPTION_GROUPS[@]}"; do
    group_applies "$gname" "${gen_args[0]}" "$gen" || continue
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
    parse_entry "$entry"
    logic=${gen_args[0]}

    # One pick per applicable group, concatenated. Empty picks contribute
    # nothing, so an all-empty draw leaves $se empty and tests the default
    # configuration.
    se=""
    for gname in "${OPTION_GROUPS[@]}"; do
      group_applies "$gname" "$logic" "$gen" || continue
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
      # cannot answer inside its budget is skipped: a timeout says nothing
      # about correctness, and skipping is what keeps a slow checker (or a
      # hard instance) from stalling the run. The budget is TIMEOUT per
      # (check-sat), so a session is not skipped for having several.
      budget=$(( TIMEOUT * $(grep -c '^(check-sat)' "$problem") ))
      timeout "$budget" "$entry_checker" "$problem" > first.txt 2> first-err.txt &
      checker_job=$!
      # $se is deliberately unquoted, some entries are two options. The
      # subshell is where the stack limit checked at startup takes effect;
      # timeout and STP inherit it.
      (ulimit -S -s "$STP_STACK_KB" &&
       exec timeout "$budget" "$STP" $se -d "$problem") \
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
      #
      # One line per (check-sat), every one of them sat or unsat, and a
      # clean exit: an "unknown" or an error on any check of a session says
      # nothing about STP's answer to that check, and a checker that
      # answered the first checks and then crashed (bitwuzla 0.9.1 does, on
      # some floating-point sessions) leaves a truncated first.txt that
      # would otherwise be saved as STP's mismatch. (awk rather than
      # grep -v: ugrep, which may be installed as grep, inverts -q -v
      # differently.)
      if [ "$checker_rc" -ne 0 ] || [ ! -s first.txt ] \
         || ! awk '$0 != "sat" && $0 != "unsat" { bad = 1 } END { exit bad }' \
                first.txt; then
        continue
      fi

      # STP declining is not STP being wrong. "unknown" is the answer it owes
      # whenever a sound one is out of reach: --uf-sort-width gives a declared
      # sort a carrier that many bits wide, and a query able to name more
      # elements of the sort than the carrier holds makes either answer a
      # guess, so STP says so instead. QF_AX at width 8 does that often --
      # 25 files in one hour against z3's unsat -- and every one landed in
      # FAIL_DIR, burying the real finds among them.
      #
      # Only a clean exit earns the pass. An "unknown" printed on the way out
      # of a crash leaves a non-zero status, and is still reported.
      #
      # A session is compared check by check, and the checks STP declined
      # are left out of it: the rest still have to agree, and so does the
      # number of them.
      if [ "$stp_rc" -eq 0 ] && grep -qx unknown second.txt; then
        if [ "$(wc -l < first.txt)" -eq "$(wc -l < second.txt)" ] \
           && paste -d ' ' first.txt second.txt \
              | awk '$2 != "unknown" && $1 != $2 { exit 1 }'; then
          continue
        fi
      elif cmp -s first.txt second.txt; then
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
        echo "checker: $entry_checker (exit $checker_rc)"
      } > "$failure/what-happened.txt"
      echo -n "[mismatch $failure]"
    done
    echo -n "#"
    rm -f -- *.smt2 expression.txt first.txt second.txt first-err.txt second-err.txt
done
