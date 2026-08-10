#!/bin/bash
#
# Differential fuzzing of STP against a trusted reference solver.
#
# Each iteration generates a batch of random problems with FuzzSMT, wraps every
# one of them in (push 1)/(pop 1) and concatenates them into a single
# multi-query file, then compares the answers of STP -- run under a randomly
# chosen option setting -- against the reference solver. Everything in the
# working directory is copied aside when the two disagree.
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
#                 build/stp, build_debug/stp, build-release/stp in the source
#                 tree, else stp on PATH. A build with assertions enabled finds
#                 more, which is why the release directory comes last.
#   CHECKER       Reference solver, invoked as "$CHECKER file.smt2".
#                 Default: z3. Anything that prints one sat/unsat line per
#                 query and understands the bit-vector overflow predicates
#                 works; z3 5.0.0 and bitwuzla 0.9.1 were both checked. This
#                 is probed at startup, because a solver that gets it wrong
#                 turns every iteration into a bogus mismatch -- z3 4.8.12 and
#                 boolector 3.0.1 both fail it, the latter on bvnego.
#
#                 On a 2500-query QF_ABV batch, z3 5.0.0 took 6.8s where
#                 bitwuzla 0.9.1 took 251s, so the checker is no longer the
#                 bottleneck. Both gave identical answers.
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
#                 The floating-point logics (QF_BVFP, QF_FP, QF_ABVFP, ...)
#                 generate and parse fine, and are the only way the
#                 --bb.fp-native-* options get exercised at all, but they are
#                 not in the built-in list because neither reference solver to
#                 hand can be trusted on them:
#
#                   z3 5.0.0        unusably slow. STP answered a 20-query
#                                   QF_BVFP batch in 9.6s; z3 had not finished
#                                   it after 400s.
#                   bitwuzla 0.9.1  segfaults part way through some batches
#                                   (not a stack limit -- it still dies with
#                                   the stack unlimited), so those iterations
#                                   land in FAIL_DIR with the checker, not STP,
#                                   as the one that failed. It also rejects
#                                   formats outside Float16/32/64/128, which
#                                   rules out -fp-any.
#
#                 The startup probe below will not catch either: both answer
#                 the trivial probe query. So before trusting an FP run, check
#                 the checker on a batch of the size QUERIES will produce, then
#
#                   CHECKER=<validated> QUERIES=100 LOGICS=QF_BVFP ./fuzz_single.sh
#   LOGIC         A single entry, for the same purpose. Ignored if LOGICS is
#                 set. Default: the built-in list.
#   QUERIES       Queries per generated file. Default: 2500.
#   CPU_LIMIT     Per-solver CPU seconds. Default: 3600.
#   FAIL_DIR      Where mismatches are saved.
#                 Default: $TMPDIR/stp-fuzz-failures.

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
source_root=$(cd -- "$script_dir/../.." && pwd)

# Find STP.
if [ -z "${STP:-}" ]; then
  for candidate in  "$source_root"/build_static_debug/stp \
                    "$source_root"/build/stp  \
                    "$source_root"/build_debug/stp \
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
CHECKER=${CHECKER:-z3}
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
"QF_ABV"
# Array extensionality: -mxn/-Mxn are how many array pairs FuzzSMT compares
# with = or distinct. Without them it never equates two arrays, so the whole
# extensionality path goes unfuzzed -- and STP rejects such a file outright
# unless --array-equality is given, hence the pairing.
"QF_ABV -mxn 1 -Mxn 3 | --array-equality"
# Writes are what make the extensional cases interesting, and the default
# -Mw 5 is easily consumed by the reads.
"QF_ABV -mxn 1 -Mxn 3 -mw 3 -Mw 10 -Mar 5 | --array-equality"
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
CPU_LIMIT=${CPU_LIMIT:-3600}
FAIL_DIR=${FAIL_DIR:-${TMPDIR:-/tmp}/stp-fuzz-failures}
mkdir -p "$FAIL_DIR" || exit 1

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

supported=$($STP --help 2>&1 | grep -o -- '--[a-zA-Z0-9.][a-zA-Z0-9.-]*' | sort -u)
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
# An entry has to be non-default AND has to actually change the output,
# otherwise it silently re-runs the baseline and wastes the iteration. Check it
# against the "arg (=N)" defaults in `stp --help`, then confirm the emitted CNF
# really differs before adding it:
#
#   stp --output-CNF --exit-after-CNF f.smt2                  # baseline
#   stp <entry> --output-CNF --exit-after-CNF f.smt2          # with the entry
#
# --bb.mult-v2=1 on its own looked reasonable and failed exactly that test:
# byte-identical CNF on every one of 49 QF_BV and QF_ABV files, because each
# site reading upper_multiplication_bound is gated behind constant-bit
# propagation having produced MultiplicationStats, which does not happen under
# the default multiplication variant. Paired with variant 5 it does bite, so
# that is the form kept below.

declare -a OPTION_GROUPS=(simplify mult bitblast fp cnf solver bias misc)

# A group named here is drawn only when the iteration's logic matches the
# pattern, which is how options that do nothing outside one theory stay out of
# the draw everywhere else. The pattern is a shell glob, matched against the
# logic name.
declare -A GROUP_LOGIC_FILTER=(
[fp]='*FP*'
)

declare -a g_simplify=(
""
"--disable-simplifications"
"--switch-word"
"--disable-opt-inc"
"--disable-cbitp"
"--disable-equality"
"--size-reducing-only"
"--rewriting=0"
"--split-extracts=0"
"--use-intervals=0"
"--pure-literals=0"
"--difficulty-reversion=0"
"--flattening=1"
"--ite-context-simplifications=1"
"--merge-same=1"
"--simplify-to-constants-only=1"
"--size-reducing-fixed-point-limit=-1"
"--aig-core-simplification=1"

# Both are documented as needing --flattening, and both do nothing without it
# on a generated file, so they are paired with it rather than listed alone.
"--flattening=1 --common-subsum=1"
"--flattening=1 --pair-extract=1"

# A bit-blasting option, but it lives here because #789 made it exclude
# --disable-opt-inc and --disable-simplifications, which are entries above.
# Drawn from its own group it would be paired with them roughly one iteration
# in a hundred, and STP now rejects that command line outright.
"--bb.simplify-during-bb=1"

# These two have given wrong answers in the past, so they get extra exposure
# here rather than being trusted.
"--unconstrained-variable-elimination=0"
"--aig-rewrite-passes=1"
)

# Multiplication: the variants are alternative settings of one option, so they
# have to share a group.
declare -a g_mult=(
""
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
"--bb.mult-variant=14"
# 15 is the one Booth variant that recodes symbolic multipliers, and the only
# one that skips setColumnsToZero(), so it reaches a bit-blasting path none of
# the others do. 7/24 on the plain entries, as does 16.
"--bb.mult-variant=15"
"--bb.mult-variant=16"
# multWithBounds() is only reachable from variant 5, so pair them.
"--bb.mult-variant=5 --bb.mult-v2=1"
)

# The rest of bit-blasting. These are independent of each other, but keeping
# them in one group bounds how far a single iteration strays from the default.
declare -a g_bitblast=(
""
"--bb.div-v1=0"
"--bb.div-v2=0"
"--bb.div-v3=1"
"--bb.add-v1=0"
"--bb.add-v2=0"
"--bb.vle-v1=0"
"--bb.conjoin-constant=1"
)

# Floating-point bit-blasting, drawn only for the FP logics: with no FP in the
# input both settings leave the CNF byte-identical, so anywhere else they are a
# wasted iteration. --bb.fp-native-arith only applies to predicates that stayed
# native, so it is not combined with turning --bb.fp-native-cmp off.
declare -a g_fp=(
""
"--bb.fp-native-cmp=0"
"--bb.fp-native-arith=1"
)

declare -a g_cnf=(
""
"--cnf-generation-effort=very-low"
"--cnf-generation-effort=very-high"
)

declare -a g_solver=(
""
"--cadical"
# Bounded variable addition, which is cadical's and needs a CaDiCaL 3.x build.
# On an older one these are dropped at startup; see the probe further down.
"--cadical --cadical-factor on"
"--cadical --cadical-factor off"
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

declare -a g_misc=(
""
"--ackermanize"
"--interactive=1"
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
      if [ $keep -eq 1 ]; then checked+=("$e"); fi
  done
  group=("${checked[@]}")
  unset -n group
done

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
trap 'rm -f -- *.smt2 expression.txt first.txt second.txt "$marker"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

# ulimit -t raises SIGXCPU and then SIGKILL. Running out of CPU is itself worth
# investigating -- these problems are small -- so a timeout is saved like any
# other failure, just labelled so triage knows which kind it is without having
# to re-run it.
timed_out() { [ "$1" -eq 152 ] || [ "$1" -eq 137 ]; }

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

    # Without this check a generation failure is silent: big.smt2 ends up
    # holding just the header, both solvers print nothing, the comparison
    # passes, and the loop spins at full speed testing nothing.
    if ! java -jar "$FUZZSMT_JAR" "${gen_args[@]}" -g -bulk-export "$QUERIES" \
              -seed `od -A n -t d -N 3 /dev/urandom`; then
      echo "fuzzsmt failed to generate '$entry' problems" >&2
      exit 1
    fi
    if ! compgen -G '_file*.smt2' > /dev/null; then
      echo "fuzzsmt wrote no _file*.smt2, is -bulk-export supported?" >&2
      exit 1
    fi

    sed -i '1i (push 1)' _file*.smt2
    sed -i -e "\$a (pop 1)" _file*.smt2

    # fuzzsmt writes (set-logic  LOGIC) with two spaces, once per generated
    # file; strip those and keep a single header. The header uses three spaces
    # so the sed below doesn't match it too.
    echo "(set-logic   $logic)" > big.smt2
    cat _file*.smt2 >> big.smt2
    sed -i "s/(set-logic  $logic)//g" big.smt2

    echo "$se" > expression.txt
    (ulimit -t "$CPU_LIMIT"; "$CHECKER" big.smt2 > first.txt) &
    checker_job=$!
    # $se is deliberately unquoted, some entries are two options.
    (ulimit -t "$CPU_LIMIT"; "$STP" $se -d big.smt2 > second.txt)
    stp_rc=$?
    wait "$checker_job"
    checker_rc=$?

    kind=""
    if timed_out "$stp_rc"; then
       kind="timeout-stp"
    elif timed_out "$checker_rc"; then
       kind="timeout-checker"
    elif (! cmp -s first.txt second.txt ); then
       kind="mismatch"
    fi

    if [ -n "$kind" ]; then
       # Without this check a full or unwritable FAIL_DIR would leave $failure
       # empty, cp would fail, and the evidence for a real bug would be gone
       # by the next iteration.
       if ! failure=$(mktemp -d "$FAIL_DIR/XXXXXX"); then
         echo "Could not create a directory under $FAIL_DIR to save a" >&2
         echo "$kind in. Stopping rather than discarding it." >&2
         exit 1
       fi
       cp -- * "$failure"
       {
         echo "kind:    $kind"
         echo "when:    $(date '+%Y-%m-%d %H:%M:%S')"
         echo "logic:   $entry"
         echo "options: $se"
         echo "stp:     $STP (exit $stp_rc)"
         echo "checker: $CHECKER (exit $checker_rc)"
       } > "$failure/what-happened.txt"
       echo -n "[$kind $failure]"
    else
       echo -n "#"
    fi
    rm -f -- *.smt2 expression.txt first.txt second.txt
done
