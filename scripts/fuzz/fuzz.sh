#!/bin/bash
#
# Run several copies of fuzz_single.sh in parallel, each in its own working
# directory. Runs until interrupted; Ctrl-C stops every worker.
#
# Usage: fuzz.sh [jobs]
#
# Environment:
#   JOBS      Number of workers. Default: the [jobs] argument, else half the
#             cores, so a worker and its reference solver each get one.
#   FUZZ_DIR  Parent of the per-worker working directories. Default:
#             /dev/shm/stp-fuzz where tmpfs exists, else $TMPDIR/stp-fuzz.
#
# Everything fuzz_single.sh reads (STP, CHECKER, FUZZSMT_JAR, FAIL_DIR, ...) is
# passed straight through, so e.g.
#
#   STP=~/stp/build_debug/stp CHECKER=boolector ./fuzz.sh 8

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
fuzzer="$script_dir/fuzz_single.sh"

if command -v nproc > /dev/null; then
  cores=$(nproc)
else
  cores=$(getconf _NPROCESSORS_ONLN 2> /dev/null || echo 2)
fi
jobs=${1:-${JOBS:-$(( cores / 2 ))}}
[ "$jobs" -ge 1 ] 2> /dev/null || jobs=1

if [ -z "${FUZZ_DIR:-}" ]; then
  if [ -d /dev/shm ] && [ -w /dev/shm ]; then
    FUZZ_DIR=/dev/shm/stp-fuzz
  else
    FUZZ_DIR=${TMPDIR:-/tmp}/stp-fuzz
  fi
fi

echo "starting $jobs workers under $FUZZ_DIR"

pids=()
trap 'kill "${pids[@]}" 2> /dev/null' INT TERM

for i in $(seq 1 "$jobs"); do
  "$fuzzer" "$FUZZ_DIR/$i" &
  pids+=($!)
done

wait
