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
#   STP           STP binary. Default: the first of build/stp, build_debug/stp,
#                 build_static_debug/stp in the source tree, else stp on PATH.
#                 A build with assertions enabled finds more.
#   CHECKER       Reference solver, invoked as "$CHECKER file.smt2".
#                 Default: bitwuzla. Anything that prints one sat/unsat line
#                 per query works, e.g. boolector, cvc5, z3.
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

LOGIC=${LOGIC:-QF_ABV}
QUERIES=${QUERIES:-2500}
CPU_LIMIT=${CPU_LIMIT:-3600}
FAIL_DIR=${FAIL_DIR:-${TMPDIR:-/tmp}/stp-fuzz-failures}
mkdir -p "$FAIL_DIR" || exit 1

path=${1:-$(mktemp -d "${TMPDIR:-/tmp}/stp-fuzz.XXXXXX")}
mkdir -p "$path" || exit 1
cd "$path" || exit 1
rm -f -- *.smt2

echo "workdir: $path"
echo "stp:     $STP"
echo "checker: $CHECKER"
echo "results: $FAIL_DIR"

# One entry is picked at random per iteration. Entries must be non-default,
# otherwise they just re-run the baseline "" entry and waste a cycle: check
# against the "arg (=N)" defaults in `stp --help` when adding to this list.

declare -a arr=(
# Baseline.
""

# Simplification.
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

# Bit-blasting.
"--bb.div-v1=0"
"--bb.div-v2=0"
"--bb.div-v3=1"
"--bb.add-v1=0"
"--bb.add-v2=0"
"--bb.vle-v1=0"
"--bb.conjoin-constant=1"
"--bb.mult-v2=1"
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

# CNF generation and solvers.
"--cnf-generation-effort=very-low"
"--cnf-generation-effort=very-high"
"--cadical"
"--cryptominisat"
"--cryptominisat --threads=4"
"--simplifying-minisat"
"--minisat"

# Misc.
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

declare -a checked=()
for e in "${arr[@]}"
  do
    keep=1
    for opt in $(echo "$e" | grep -o -- '--[a-zA-Z0-9.][a-zA-Z0-9.-]*'); do
      if ! echo "$supported" | grep -qx -- "$opt"; then
        echo "dropping unsupported entry: $e ($opt not in this build)" >&2
        keep=0
        break
      fi
    done
    if [ $keep -eq 1 ]; then checked+=("$e"); fi
done
arr=("${checked[@]}")
echo "${#arr[@]} option settings"

#Don't want to fill up SHM.
trap 'rm -f -- *.smt2 expression.txt first.txt second.txt' EXIT

while (true)
  do
    se=${arr[ $RANDOM % ${#arr[@]} ]}

    java -jar "$FUZZSMT_JAR" "$LOGIC" -g -bulk-export "$QUERIES" \
         -seed `od -A n -t d -N 3 /dev/urandom`
    sed -i '1i (push 1)' _file*.smt2
    sed -i -e "\$a (pop 1)" _file*.smt2

    #two spaces so the sed doesn't match it.
    echo "(set-logic   $LOGIC)" >> big.smt2
    cat _file*.smt2 >> big.smt2
    sed -i 's/(set-logic  QF_BV)//g' big.smt2
    sed -i "s/(set-logic  $LOGIC)//g" big.smt2

    echo "$se" > expression.txt
    (ulimit -t "$CPU_LIMIT"; "$CHECKER" big.smt2 > first.txt) &
    # $se is deliberately unquoted, some entries are two options.
    (ulimit -t "$CPU_LIMIT"; "$STP" $se -d big.smt2 > second.txt)

    wait
    if (! cmp -s first.txt second.txt ); then
       cp -- * "$(mktemp -d "$FAIL_DIR/XXXXXX")"
       echo -n "FAIL"
    fi

    rm -f -- *.smt2 expression.txt first.txt second.txt
    echo -n "#"
done
