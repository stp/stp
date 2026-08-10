#!/bin/bash
#
# Run several copies of fuzz_single.sh in parallel, each in its own working
# directory. Runs until interrupted; Ctrl-C stops every worker.
#
# Usage: fuzz.sh [jobs]
#
# Environment:
#   JOBS      Number of workers. Default: the [jobs] argument, else 1/8th
#             the number of cores.
#   FUZZ_DIR  Parent of the per-worker working directories. Default:
#             /dev/shm/stp-fuzz-$$ where tmpfs exists, else $TMPDIR/stp-fuzz-$$.
#             A directory we generate ourselves is removed on exit; one given
#             here is left alone beyond rmdir'ing the empty worker directories.
#
# Everything fuzz_single.sh reads (STP, CHECKER, FUZZSMT_JAR, LOGICS, FAIL_DIR,
# ...) is passed straight through, so e.g.
#
#   STP=~/stp/build_debug/stp CHECKER=bitwuzla ./fuzz.sh 8
#   LOGICS='QF_BV; QF_ABV -mxn 1 -Mxn 3' ./fuzz.sh 8

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
fuzzer="$script_dir/fuzz_single.sh"

# moreutils ships a different "parallel" with an incompatible command line
# (no --ungroup, no {}), so check which one is on PATH rather than just that
# something by that name exists.
if ! command -v parallel > /dev/null; then
  echo "GNU parallel not found; install it, or run $fuzzer directly." >&2
  exit 1
fi
if ! parallel --version 2> /dev/null | grep -q '^GNU parallel'; then
  echo "$(command -v parallel) is not GNU parallel (moreutils ships another" >&2
  echo "program by that name). Install GNU parallel, or run $fuzzer directly." >&2
  exit 1
fi

if command -v nproc > /dev/null; then
  cores=$(nproc)
else
  cores=$(getconf _NPROCESSORS_ONLN 2> /dev/null || echo 2)
fi
jobs=${1:-${JOBS:-$(( cores / 8 ))}}
[ "$jobs" -ge 1 ] 2> /dev/null || jobs=1

export OUR_PID=$$

if [ -z "${FUZZ_DIR:-}" ]; then
  if [ -d /dev/shm ] && [ -w /dev/shm ]; then
    FUZZ_DIR=/dev/shm/stp-fuzz-${OUR_PID}
  else
    FUZZ_DIR=${TMPDIR:-/tmp}/stp-fuzz-${OUR_PID}
  fi
  generated_fuzz_dir=1
fi

# Ctrl-C is the normal way out, so the cleanup has to be a trap: bash dies on
# the signal rather than running the rest of the script. The INT/TERM traps
# turn the signal into an exit so the EXIT trap gets its turn.
#
# Only a directory we named ourselves is safe to remove outright; a FUZZ_DIR
# from the environment may be a scratch area holding other things, so there we
# just rmdir the worker directories and the parent, which fails harmlessly if
# either is non-empty.
cleanup() {
  if [ -n "${generated_fuzz_dir:-}" ]; then
    rm -rf -- "$FUZZ_DIR"
  else
    for n in $(seq 1 "$jobs"); do rmdir -- "$FUZZ_DIR/$n" 2> /dev/null; done
    rmdir -- "$FUZZ_DIR" 2> /dev/null
  fi
  return 0
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

echo "starting $jobs workers under $FUZZ_DIR"

seq 1 "$jobs" | parallel --ungroup -j "$jobs" "$fuzzer" "$FUZZ_DIR/{}"
