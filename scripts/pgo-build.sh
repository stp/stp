#!/usr/bin/env bash
#
# Configure, build, train, and build again: the whole profile-guided cycle.
# configure.sh does the configuring, this decides what happens between the two
# passes.
#
# They share a build directory on purpose. GCC names each .gcda after the
# absolute path of the object file it came from, so a profile collected in one
# build directory is invisible from another; there is no arrangement in which
# the second pass can be a separate tree.

set -e -o pipefail

die () { echo "*** pgo-build.sh: $*" 1>&2; exit 1; }

usage () {
cat <<EOF
Usage: $0 [<option> ...] [<configure.sh option> ...]

Builds STP twice -- once instrumented, then again with what the first build
recorded while solving a corpus of queries -- and leaves the optimised build
in the build directory.

Options:
  -h, --help          display this help and exit
  --name=STR          build directory to use (default: build)
  --train=PATH        a directory to search for .smt2 queries, or one query.
                      Repeatable. Defaults to tests/query-files
  --jobs=N            parallel jobs for the builds and the training run

Everything else is passed to configure.sh, so the usual options work:

  ./scripts/pgo-build.sh release --lto --ninja --auto-download

and the compiler is chosen the same way it is for configure.sh, through the
environment. Measured, clang is the one worth using here -- its profile
reaches CaDiCaL's search and gcc's does not:

  CC=clang CXX=clang++ ./scripts/pgo-build.sh release --lto --ninja --auto-download

See "Link-time and profile-guided optimisation" in docs/building.rst for what
this is worth, what it costs, and what it does not do.
EOF
  exit 0
}

[ ! -e lib/AST ] && die "$0 not called from the STP source directory"

build_dir=build
train=()
passthrough=()
jobs=$( (nproc || sysctl -n hw.ncpu || echo 4) 2>/dev/null )

while [ $# -gt 0 ]; do
  case $1 in
    -h|--help) usage;;
    --name=*)  build_dir=${1##*=};;
    --train=*) train+=("${1##*=}");;
    --jobs=*)  jobs=${1##*=};;
    --name|--train|--jobs) die "missing argument to $1 (try -h)";;
    --pgo|--pgo=*) die "$1 is what this script is for: it runs both passes";;
    *)         passthrough+=("$1");;
  esac
  shift
done

[ ${#train[@]} -eq 0 ] && train=(tests/query-files)

root_dir=$(pwd)
prof_dir=$root_dir/$build_dir/pgo-data

# Clang's instrumentation puts its counters in their own sections and finds
# them through the __start___llvm_prf_* symbols the linker is supposed to
# synthesise.  Under ThinLTO those sections do not exist until after the LTO
# backend has run, and GNU ld decides the symbols before that, so a target
# whose inputs are all bytecode fails to link:
#
#   undefined reference to `__start___llvm_prf_names'
#
# lld creates them afterwards and links it.  It is also the linker this came
# out fastest with -- about 2% on the heaviest queries, same objects, same
# .text -- so when it is there and nobody has asked for another one, use it.
linker_opts=()
case " ${passthrough[*]} " in
  *-fuse-ld=*|*CMAKE_LINKER_TYPE*) ;;
  *)
    if "${CXX:-c++}" --version 2>/dev/null | head -1 | grep -qi clang \
       && command -v ld.lld >/dev/null 2>&1; then
      echo "==> linking with lld (clang's instrumented ThinLTO needs it)"
      linker_opts=(-DCMAKE_EXE_LINKER_FLAGS=-fuse-ld=lld
                   -DCMAKE_SHARED_LINKER_FLAGS=-fuse-ld=lld)
    fi
    ;;
esac

# STP builds its dependencies as separate CMake projects, and most of a hard
# query's time is spent inside two of them. A profile that covered only libstp
# would be a profile of the smaller half, so the dependencies are compiled with
# the same flags in both passes -- which means they have to be rebuilt between
# the passes, and that in turn means this build directory needs a dependency
# tree of its own rather than a shared one it would be rude to delete.
dep_dir=$root_dir/$build_dir/deps/install
for opt in "${passthrough[@]}"; do
  case $opt in
    --dep-dir=*) die "--dep-dir cannot be shared with a PGO build: the second"\
                     "pass has to recompile the dependencies with the profile";;
  esac
done

# Collect the training queries once, so both the count reported below and the
# run itself see the same list.
queries=$(mktemp)
trap 'rm -f "$queries"' EXIT
for t in "${train[@]}"; do
  if [ -d "$t" ]; then
    find "$t" -name '*.smt2' -type f
  elif [ -f "$t" ]; then
    echo "$t"
  else
    die "--train=$t is neither a file nor a directory"
  fi
done | sort > "$queries"
n_queries=$(wc -l < "$queries")
[ "$n_queries" -eq 0 ] && die "no .smt2 queries found in: ${train[*]}"

echo "==> pass 1: instrumented build in $build_dir"
rm -rf "$prof_dir"
mkdir -p "$prof_dir"
./configure.sh --name="$build_dir" --dep-dir="$dep_dir" --pgo=generate \
               -DPGO_DIR="$prof_dir" "${linker_opts[@]}" "${passthrough[@]}"
cmake --build "$build_dir" --parallel "$jobs"

stp_bin=$build_dir/stp
[ -x "$stp_bin" ] || die "no $stp_bin to train with"

echo "==> training on $n_queries queries from: ${train[*]}"
# Clang's runtime merges into one file per binary when the name contains %m,
# which is what keeps this from leaving one raw profile per process behind.
# GCC's runtime merges into the .gcda files whatever the name, and ignores it.
export LLVM_PROFILE_FILE="$prof_dir/stp-%m.profraw"
# A query that does not finish is a query that never writes its counters, so
# the cap is generous: the point is to survive a pathological input, not to
# bound the training run.
xargs -a "$queries" -P "$jobs" -I{} \
      sh -c 'timeout 300 "$0" --SMTLIB2 "$1" >/dev/null 2>&1 || true' \
      "$root_dir/$stp_bin" {}

# Which toolchain built it decides what shape the profile is in.  Asked of the
# compiler rather than read out of CMakeCache.txt, which does not carry
# CMAKE_CXX_COMPILER_ID: that one is worked out afresh on every configure and
# never cached.
cxx=$(sed -n 's/^CMAKE_CXX_COMPILER:.*=//p' "$build_dir/CMakeCache.txt")
[ -n "$cxx" ] || die "no CMAKE_CXX_COMPILER in $build_dir/CMakeCache.txt"
if "$cxx" --version 2>/dev/null | head -1 | grep -qi clang; then
  raw=$(find "$prof_dir" -name '*.profraw' | wc -l)
  [ "$raw" -eq 0 ] && die "the training run produced no profile"
  # Prefer the llvm-profdata that goes with this clang: a profile written by
  # one version is not always readable by another, and distributions install
  # several side by side.
  major=$("$cxx" -dumpversion 2>/dev/null | cut -d. -f1)
  profdata=""
  for cand in "llvm-profdata-$major" llvm-profdata; do
    command -v "$cand" >/dev/null 2>&1 && { profdata=$cand; break; }
  done
  [ -z "$profdata" ] && die "llvm-profdata is needed to merge a clang profile"
  echo "==> merging $raw raw profiles with $profdata"
  find "$prof_dir" -name '*.profraw' -print0 \
    | xargs -0 "$profdata" merge -output="$prof_dir/stp.profdata"
  find "$prof_dir" -name '*.profraw' -delete
else
  gcda=$(find "$prof_dir" -name '*.gcda' | wc -l)
  [ "$gcda" -eq 0 ] && die "the training run produced no profile"
  echo "==> collected $gcda profiles"
fi

echo "==> pass 2: optimised build in $build_dir"
# The dependencies were built instrumented too. ExternalProject remembers that
# it has already configured, built and installed them, so drop those three
# stamps -- and the tree they installed into -- to have them compiled again
# with the profile. The download and patch stamps stay, so nothing is fetched
# twice.
rm -f "$build_dir"/deps/src/*-EP-stamp/*-configure \
      "$build_dir"/deps/src/*-EP-stamp/*-build \
      "$build_dir"/deps/src/*-EP-stamp/*-install
rm -rf "$dep_dir"
./configure.sh --name="$build_dir" --dep-dir="$dep_dir" --pgo=use \
               -DPGO_DIR="$prof_dir" "${linker_opts[@]}" "${passthrough[@]}"
cmake --build "$build_dir" --parallel "$jobs"

echo "==> done: $build_dir/stp"
