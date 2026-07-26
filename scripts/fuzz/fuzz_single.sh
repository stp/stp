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
#                 build/stp, build_debug/stp in the source tree, else stp on
#                 PATH. A build with assertions enabled finds more.
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
#   LOGIC         Logic to generate. Default: QF_ABV.
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

LOGIC=${LOGIC:-QF_ABV}
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
echo "results: $FAIL_DIR"

# FuzzSMT uses the bit-vector overflow predicates, which older solvers do not
# know. z3 4.8.12 for instance answers the query anyway and prints an extra
# (error ...) line, so it neither fails outright nor gives a usable answer --
# every iteration would land in FAIL_DIR looking like an STP bug. Check the
# checker before trusting a whole run to it.
{
  echo "(set-logic $LOGIC)"
  echo "(declare-fun x () (_ BitVec 8))"
  echo "(declare-fun y () (_ BitVec 8))"
  for p in bvnego bvsaddo bvsdivo bvsmulo bvssubo bvuaddo bvumulo bvusubo; do
    if [ "$p" = bvnego ]; then
      echo "(assert (or (bvnego x) true))"
    else
      echo "(assert (or ($p x y) true))"
    fi
  done
  echo "(check-sat)"
} > probe.smt2
probe_out=$(timeout 60 "$CHECKER" probe.smt2 2>&1)
probe_rc=$?
if [ "$probe_rc" -ne 0 ] || [ "$probe_out" != "sat" ]; then
  echo "Reference solver '$CHECKER' failed the startup probe (exit $probe_rc):" >&2
  echo "$probe_out" | sed 's/^/  /' >&2
  echo "It must print exactly 'sat' for a query using the bit-vector overflow" >&2
  echo "predicates. Upgrade it, or set CHECKER to one that does." >&2
  exit 1
fi
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

declare -a OPTION_GROUPS=(simplify mult bitblast cnf solver misc)

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
"--always-true=1"
"--merge-same=1"
"--simplify-to-constants-only=1"
"--bit-blast-simplification=-1"
"--size-reducing-fixed-point-limit=-1"
"--aig-core-simplification=1"

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

declare -a g_cnf=(
""
"--cnf-generation-effort=very-low"
"--cnf-generation-effort=very-high"
)

declare -a g_solver=(
""
"--cadical"
"--cryptominisat"
"--cryptominisat --threads=4"
"--simplifying-minisat"
"--minisat"
)

declare -a g_misc=(
""
"--ackermanize"
"--interactive=1"
)

# Drop entries this binary doesn't understand, rather than have boost reject
# them and count every iteration as a mismatch. Catches both a stale build and
# typos in the array above.
supported=$($STP --help 2>&1 | grep -o -- '--[a-zA-Z0-9.][a-zA-Z0-9.-]*' | sort -u)
if [ -z "$supported" ]; then
  echo "Could not get the option list from $STP" >&2
  exit 1
fi

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
  echo >&2
fi

# The empty entry never matches the filter, so a group cannot come out of that
# loop empty unless the group itself was written empty.
combinations=1
for gname in "${OPTION_GROUPS[@]}"; do
  declare -n group="g_$gname"
  if [ "${#group[@]}" -eq 0 ]; then
    echo "Option group '$gname' is empty." >&2
    exit 1
  fi
  printf '  %-10s %2d entries\n' "$gname" "${#group[@]}"
  combinations=$(( combinations * ${#group[@]} ))
  unset -n group
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
    # One pick per group, concatenated. Empty picks contribute nothing, so an
    # all-empty draw leaves $se empty and tests the default configuration.
    se=""
    for gname in "${OPTION_GROUPS[@]}"; do
      declare -n group="g_$gname"
      pick=${group[ $RANDOM % ${#group[@]} ]}
      if [ -n "$pick" ]; then se="${se:+$se }$pick"; fi
      unset -n group
    done

    # Without this check a generation failure is silent: big.smt2 ends up
    # holding just the header, both solvers print nothing, the comparison
    # passes, and the loop spins at full speed testing nothing.
    if ! java -jar "$FUZZSMT_JAR" "$LOGIC" -g -bulk-export "$QUERIES" \
              -seed `od -A n -t d -N 3 /dev/urandom`; then
      echo "fuzzsmt failed to generate $LOGIC problems" >&2
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
    echo "(set-logic   $LOGIC)" > big.smt2
    cat _file*.smt2 >> big.smt2
    sed -i "s/(set-logic  $LOGIC)//g" big.smt2

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
