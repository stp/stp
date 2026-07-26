#!/usr/bin/env bash

# Default-off C API baseline differential for the array-equality
# feature, which promises that STP without --array-equality behaves
# exactly like STP before the feature existed.
#
# Builds the pinned pre-extension baseline commit from repository
# history with the same toolchain and configuration as the candidate
# build, compiles the identical tools/extdiff driver into both trees,
# runs both with array equality disabled, and requires the serialized
# observations (query status, entry counts, every (index, value) pair
# in returned order, stdout, stderr, exit status) to match byte for
# byte.
#
# Usage: extdiff-baseline-differential.sh <source_dir> <candidate_build_dir> [baseline_sha]
#
# Exit codes: 0 pass, 1 mismatch/error, 77 skip (baseline commit not
# available in this checkout, e.g. a shallow CI clone).

set -u -o pipefail

BASELINE_SHA_DEFAULT="381ef0011ac5f3c6463bcd3662914cb59e9ceaca"

SRC_DIR=$(readlink -f "${1:?source dir required}")
CAND_BUILD=$(readlink -f "${2:?candidate build dir required}")
BASELINE_SHA="${3:-$BASELINE_SHA_DEFAULT}"

CACHE_DIR="$CAND_BUILD/baseline-differential"
BASE_TREE="$CACHE_DIR/tree"
BASE_BUILD="$CACHE_DIR/build"
mkdir -p "$CACHE_DIR"

log() { echo "extdiff-differential: $*"; }

# ---------------------------------------------------------------- skip check
if ! git -C "$SRC_DIR" cat-file -e "$BASELINE_SHA^{commit}" 2>/dev/null; then
  log "baseline commit $BASELINE_SHA is not available in this checkout; skipping"
  exit 77
fi

cache_val() {
  sed -n "s/^$1:[A-Z]*=//p" "$CAND_BUILD/CMakeCache.txt" | head -1
}

BUILD_TYPE=$(cache_val CMAKE_BUILD_TYPE)
GENERATOR=$(cache_val CMAKE_GENERATOR)
MINISAT_INC=$(cache_val MINISAT_INCLUDE_DIRS)
MINISAT_LIB=$(cache_val MINISAT_LIBDIR)
CXX_COMPILER=$(cache_val CMAKE_CXX_COMPILER)
C_COMPILER=$(cache_val CMAKE_C_COMPILER)

# ------------------------------------------------------- baseline checkout
if [ -d "$BASE_TREE" ] &&
   [ "$(git -C "$BASE_TREE" rev-parse HEAD 2>/dev/null)" = "$BASELINE_SHA" ]; then
  log "reusing cached baseline checkout"
else
  rm -rf "$BASE_TREE"
  git -C "$SRC_DIR" worktree prune >/dev/null 2>&1
  if ! git -C "$SRC_DIR" worktree add --detach "$BASE_TREE" "$BASELINE_SHA" \
      >/dev/null 2>&1; then
    log "could not create baseline worktree; skipping"
    exit 77
  fi
  rm -rf "$BASE_BUILD"
fi

# Vendored ABC submodule content is not populated in a fresh worktree;
# share the candidate's copy (the pinned commit references the same
# submodule revision).
if [ ! -f "$BASE_TREE/lib/extlib-abc/CMakeLists.txt" ]; then
  rm -rf "$BASE_TREE/lib/extlib-abc"
  ln -s "$SRC_DIR/lib/extlib-abc" "$BASE_TREE/lib/extlib-abc"
fi

# Inject the identical driver into the baseline tree.
rm -rf "$BASE_TREE/tools/extdiff"
cp -r "$SRC_DIR/tools/extdiff" "$BASE_TREE/tools/extdiff"
if ! grep -q "add_subdirectory(extdiff)" "$BASE_TREE/tools/CMakeLists.txt"; then
  printf '\nadd_subdirectory(extdiff)\n' >> "$BASE_TREE/tools/CMakeLists.txt"
fi

# ---------------------------------------------------------- baseline build
CMAKE_ARGS=(-DCMAKE_BUILD_TYPE="${BUILD_TYPE:-RelWithDebInfo}"
            -DENABLE_TESTING=OFF
            -DNOCRYPTOMINISAT=ON
            -Wno-dev)
[ -n "$GENERATOR" ] && CMAKE_ARGS+=(-G "$GENERATOR")
[ -n "$MINISAT_INC" ] && CMAKE_ARGS+=(-DMINISAT_INCLUDE_DIRS="$MINISAT_INC")
[ -n "$MINISAT_LIB" ] && CMAKE_ARGS+=(-DMINISAT_LIBDIR="$MINISAT_LIB")
[ -n "$CXX_COMPILER" ] && CMAKE_ARGS+=(-DCMAKE_CXX_COMPILER="$CXX_COMPILER")
[ -n "$C_COMPILER" ] && CMAKE_ARGS+=(-DCMAKE_C_COMPILER="$C_COMPILER")

if [ ! -f "$BASE_BUILD/CMakeCache.txt" ]; then
  log "configuring baseline ($BASELINE_SHA)"
  mkdir -p "$BASE_BUILD"
  if ! cmake -S "$BASE_TREE" -B "$BASE_BUILD" "${CMAKE_ARGS[@]}" \
      > "$CACHE_DIR/baseline-configure.log" 2>&1; then
    log "baseline configure failed; see $CACHE_DIR/baseline-configure.log"
    exit 1
  fi
fi

log "building baseline extdiff"
if ! cmake --build "$BASE_BUILD" --target extdiff-bin \
    > "$CACHE_DIR/baseline-build.log" 2>&1; then
  log "baseline build failed; see $CACHE_DIR/baseline-build.log"
  exit 1
fi

log "building candidate extdiff"
if ! cmake --build "$CAND_BUILD" --target extdiff-bin \
    > "$CACHE_DIR/candidate-build.log" 2>&1; then
  log "candidate build failed; see $CACHE_DIR/candidate-build.log"
  exit 1
fi

# ------------------------------------------------------------------ compare
run_one() {
  # $1 binary  $2 tag
  "$1" > "$CACHE_DIR/$2.out" 2> "$CACHE_DIR/$2.err"
  echo $? > "$CACHE_DIR/$2.status"
}

run_one "$BASE_BUILD/extdiff" baseline
run_one "$CAND_BUILD/extdiff" candidate

fail=0
for f in out err status; do
  if ! cmp -s "$CACHE_DIR/baseline.$f" "$CACHE_DIR/candidate.$f"; then
    log "MISMATCH in $f:"
    diff -u "$CACHE_DIR/baseline.$f" "$CACHE_DIR/candidate.$f" | head -60
    fail=1
  fi
done

if [ "$fail" -ne 0 ]; then
  log "default-off C API observations diverge from baseline $BASELINE_SHA"
  exit 1
fi

log "default-off C API observations are byte-identical to baseline $BASELINE_SHA"
exit 0
