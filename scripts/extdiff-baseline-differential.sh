#!/usr/bin/env bash

# Default-off C API baseline differential for the array-equality
# feature, which promises that STP without --array-equality behaves
# exactly like an STP that does not carry the feature at all.
#
# Builds the pinned baseline commit from repository history with the
# same toolchain and configuration as the candidate build, compiles the
# identical tools/extdiff driver into both trees, runs both with array
# equality disabled, and requires the serialized observations (query
# status, entry counts, every exact (index, value) pair, stdout, stderr,
# exit status) to match byte for byte. The common driver canonicalizes
# counterexample-array pairs first because their returned order is
# unspecified and depends on internal node-creation IDs.
#
# Usage: extdiff-baseline-differential.sh <source_dir> <candidate_build_dir> [baseline_sha]
#
# Exit codes: 0 pass, 1 mismatch/error, 77 skip (baseline commit not
# available in this checkout, e.g. a shallow CI clone).

set -u -o pipefail

# The upstream commit this branch was last merged with -- deliberately
# not a frozen pre-feature commit. Both are "STP without the feature",
# but only this one holds upstream fixed across the comparison, so the
# difference it measures is the branch's own contribution and nothing
# else. A frozen pin measures the branch plus every upstream change made
# since, and cannot tell the two apart.
#
# That is not hypothetical: the pin used to be 381ef001, from before the
# feature existed, and upstream 78870389 ("SubstitutionMap: flat hash
# map for the solver map and replace() caches") changed the order in
# which a counterexample array's entries are returned. Two builds of
# pure upstream, one either side of it, reproduce both orders with no
# array-equality code present -- so the test failed on a change the
# branch had no part in, while saying nothing about the branch. The
# driver canonicalizes entry order now, so that particular change would
# no longer reach the comparison; the pin is not thereby redundant,
# since the next upstream change to an observed value need not be one
# any canonical form can normalize away.
#
# Advance this with each merge of upstream/master:
#   git merge-base HEAD upstream/master
BASELINE_SHA_DEFAULT="5b528b73c1cfc3c6e1f0b84ec838a3629dadf4e3"

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

# Vendored submodule content is not populated in a fresh worktree; share
# the candidate's copies (the baseline commit references the same
# submodule revisions). mimalloc has to be here as well as ABC: it is the
# default allocator, and configure fails outright rather than falling
# back when its directory is empty. The pre-feature pin predated it, so
# linking ABC alone was enough only for as long as the pin stayed there.
for sub in lib/extlib-abc lib/extlib-mimalloc; do
  if [ ! -f "$BASE_TREE/$sub/CMakeLists.txt" ]; then
    rm -rf "${BASE_TREE:?}/$sub"
    ln -s "$SRC_DIR/$sub" "$BASE_TREE/$sub"
  fi
done

# Inject the identical driver into the baseline tree.
rm -rf "$BASE_TREE/tools/extdiff"
cp -r "$SRC_DIR/tools/extdiff" "$BASE_TREE/tools/extdiff"
if ! grep -q "add_subdirectory(extdiff)" "$BASE_TREE/tools/CMakeLists.txt"; then
  printf '\nadd_subdirectory(extdiff)\n' >> "$BASE_TREE/tools/CMakeLists.txt"
fi

# ---------------------------------------------------------- baseline build
CMAKE_ARGS=(-DCMAKE_BUILD_TYPE="${BUILD_TYPE:-RelWithDebInfo}"
            -DENABLE_TESTING=OFF
            -DUSE_CRYPTOMINISAT=OFF
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

# Build a whole second STP, so ask for the machine. Without an explicit
# job count "cmake --build" hands the native tool its own default, and
# under the Makefiles generator that default is one job -- which is what
# this test was paying, silently, for the entire build it exists to make.
# Passing a number rather than a bare --parallel keeps make from being
# told to spawn without limit.
JOBS=$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)

log "building baseline extdiff (-j$JOBS)"
if ! cmake --build "$BASE_BUILD" --target extdiff-bin --parallel "$JOBS" \
    > "$CACHE_DIR/baseline-build.log" 2>&1; then
  log "baseline build failed; see $CACHE_DIR/baseline-build.log"
  exit 1
fi

log "building candidate extdiff (-j$JOBS)"
if ! cmake --build "$CAND_BUILD" --target extdiff-bin --parallel "$JOBS" \
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

log "canonicalized default-off C API observations are byte-identical to baseline $BASELINE_SHA"
exit 0
