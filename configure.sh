#!/usr/bin/env bash
#
# Turns configure-style options into a CMake invocation, and nothing else.
# Every default lives in CMakeLists.txt: an option not named on the command
# line is not passed on, so it keeps whatever the build decides for it.

set -e -o pipefail

usage () {
cat <<EOF
Usage: $0 [<build type>] [<option> ...]

Build types (default: RelWithDebInfo):
  debug            unoptimized, with debug symbols and assertions
  release          optimized, assertions off
  relwithdebinfo   optimized, with debug symbols and assertions
  minsizerel       optimized for size

General options:
  -h, --help          display this help and exit
  --name=STR          build directory to configure (default: build)
  --prefix=PATH       install prefix
  --ninja             generate for Ninja rather than Make

Dependencies:
  --auto-download     download and build dependencies that are not installed
  --local-deps        use no dependency from outside the build directory:
                      ignore installed copies and build them here instead.
                      Implies --auto-download unless --no-auto-download is
                      also given. A --abc-dir or similar still names a copy
  --abc-dir=PATH      an existing ABC build, rather than fetching one
  --dep-dir=PATH      install dependencies here, and look for them here.
                      Point several build directories at one path and only the
                      first builds anything. Defaults to \$STP_DEP_DIR if that
                      is set, otherwise to <build>/deps/install
  --dep-path=PATH     an additional read-only prefix to search (repeatable)

SAT backends (disable with --no-<name>):
  --cadical           use CaDiCaL
  --cadical-dir=PATH  a CaDiCaL checkout (implies --cadical)
  --cryptominisat     require CryptoMiniSat; --no-cryptominisat never uses it.
                      Named neither way, it is used if it is installed
  --minisat           use MiniSat

Features (disable with --no-<name>):
  --assertions        build with assertions
  --testing           build the test suite
  --python-bindings   build the Python interface
  --manpage           build and install the stp(1) manpage
  --static            build static libraries and a static binary
  --werror            treat compiler warnings as errors
  --sanitize          build with Clang's sanitizers
  --coverage          build with coverage instrumentation
  --lto               build with link-time optimisation
  --pgo=STEP          profile-guided optimisation: generate or use. Both steps
                      have to run in the same build directory.
                      scripts/pgo-build.sh runs them in order, training on
                      tests/query-files in between
  --tune-native       build with -mtune=native
  --allocator=NAME    mimalloc (default), tcmalloc or system

CMake options (advanced):
  -DVAR=VALUE         passed to cmake verbatim
EOF
  exit 0
}

die () {
  echo "*** configure.sh: $*" 1>&2
  exit 1
}

[ ! -e lib/AST ] && die "$0 not called from the STP source directory"

#--------------------------------------------------------------------------#
# Every one of these stays at "default" unless asked for, and only the ones
# that moved are passed to cmake. CMakeLists.txt owns the defaults; repeating
# them here is how the two come to disagree.

build_dir=build
buildtype=default
generator=default
install_prefix=default

abc_dir=default
auto_download=default
local_deps=default
dep_dir=${STP_DEP_DIR:-default}
dep_path=""

cadical=default
cadical_dir=default
cryptominisat=default
minisat=default

allocator=default
assertions=default
coverage=default
lto=default
manpage=default
pgo=default
python_bindings=default
sanitize=default
static=default
testing=default
tune_native=default
werror=default

cmake_opts=()

while [ $# -gt 0 ]
do
  case $1 in
    -h|--help) usage;;

    --name) die "missing argument to $1 (try -h)";;
    --name=*) build_dir=${1##*=};;

    --prefix) die "missing argument to $1 (try -h)";;
    --prefix=*)
        install_prefix=${1##*=}
        case $install_prefix in
          /*) ;;
          *) install_prefix=$(pwd)/$install_prefix;;
        esac
        ;;

    --ninja) generator=Ninja;;

    --auto-download) auto_download=ON;;
    --no-auto-download) auto_download=OFF;;

    --local-deps) local_deps=ON;;
    --no-local-deps) local_deps=OFF;;

    --abc-dir) die "missing argument to $1 (try -h)";;
    --abc-dir=*) abc_dir=${1##*=};;

    --dep-dir) die "missing argument to $1 (try -h)";;
    --dep-dir=*) dep_dir=${1##*=};;

    --dep-path) die "missing argument to $1 (try -h)";;
    --dep-path=*) dep_path="${dep_path:+${dep_path};}${1##*=}";;

    --cadical) cadical=ON;;
    --no-cadical) cadical=OFF;;
    --cadical-dir) die "missing argument to $1 (try -h)";;
    --cadical-dir=*) cadical_dir=${1##*=}; cadical=ON;;

    --cryptominisat) cryptominisat=ON;;
    --no-cryptominisat) cryptominisat=OFF;;

    --minisat) minisat=ON;;
    --no-minisat) minisat=OFF;;

    --allocator) die "missing argument to $1 (try -h)";;
    --allocator=*) allocator=${1##*=};;

    --assertions) assertions=ON;;
    --no-assertions) assertions=OFF;;

    --coverage) coverage=ON;;
    --no-coverage) coverage=OFF;;

    --lto) lto=ON;;
    --no-lto) lto=OFF;;

    --pgo) die "missing argument to $1 (try -h)";;
    --pgo=*) pgo=${1##*=}
        case $pgo in
          generate|use) ;;
          *) die "--pgo takes generate or use, not '$pgo'";;
        esac
        ;;

    --manpage) manpage=ON;;
    --no-manpage) manpage=OFF;;

    --python-bindings) python_bindings=ON;;
    --no-python-bindings) python_bindings=OFF;;

    --sanitize) sanitize=ON;;
    --no-sanitize) sanitize=OFF;;

    --static) static=ON;;
    --no-static) static=OFF;;

    --testing) testing=ON;;
    --no-testing) testing=OFF;;

    --tune-native) tune_native=ON;;
    --no-tune-native) tune_native=OFF;;

    --werror) werror=ON;;
    --no-werror) werror=OFF;;

    -D*) cmake_opts+=("$1");;

    -*) die "invalid option '$1' (try -h)";;

    *) case $1 in
         debug)          buildtype=Debug;;
         release)        buildtype=Release;;
         relwithdebinfo) buildtype=RelWithDebInfo;;
         minsizerel)     buildtype=MinSizeRel;;
         *)              die "invalid build type '$1' (try -h)";;
       esac
       ;;
  esac
  shift
done

#--------------------------------------------------------------------------#

# Nothing outside the build directory, and nothing in it yet, is a
# configuration that can only fail -- so asking for the first asks for the
# second. Settled here rather than in the case above so that the two flags may
# be given in either order, and only when --no-auto-download did not say
# otherwise.
[ "$local_deps" = ON ] && [ "$auto_download" = default ] && auto_download=ON

add () { [ "$2" != default ] && cmake_opts+=("-D$1=$2"); return 0; }

add CMAKE_BUILD_TYPE       "$buildtype"
add CMAKE_INSTALL_PREFIX   "$install_prefix"
add ENABLE_AUTO_DOWNLOAD   "$auto_download"
add STP_DEPS_LOCAL_ONLY    "$local_deps"
add ABC_DIR                "$abc_dir"
add STP_DEP_DIR            "$dep_dir"
add USE_CADICAL            "$cadical"
add CADICAL_DIR            "$cadical_dir"
add USE_CRYPTOMINISAT      "$cryptominisat"
add USE_MINISAT            "$minisat"
add STP_ALLOCATOR          "$allocator"
add ENABLE_ASSERTIONS      "$assertions"
add COVERAGE               "$coverage"
add ENABLE_LTO             "$lto"
add PGO                    "$pgo"
add BUILD_MANPAGE          "$manpage"
add ENABLE_PYTHON_INTERFACE "$python_bindings"
add SANITIZE               "$sanitize"
add STATICCOMPILE          "$static"
add ENABLE_TESTING         "$testing"
add TUNE_NATIVE            "$tune_native"
add WERROR                 "$werror"

[ -n "$dep_path" ] && cmake_opts+=("-DCMAKE_PREFIX_PATH=$dep_path")

[ "$generator" != default ] && cmake_opts+=(-G "$generator")

# SANITIZE FORCEs CMAKE_CXX_COMPILER to clang++ and says nothing about the C
# compiler, which would leave a build compiling its C with gcc and its C++ with
# clang -- and handing that mismatched pair to every dependency it builds. Name
# both instead, and let the normal detection run.
if [ "$sanitize" = ON ]; then
  export CC=${CC:-clang}
  export CXX=${CXX:-clang++}
fi

root_dir=$(pwd)
mkdir -p "$build_dir"

# The generator and the toolchain cannot be changed in a directory that has
# already been configured, and a stale entry is a confusing way to find that
# out.
[ -e "$build_dir/CMakeCache.txt" ] && rm "$build_dir/CMakeCache.txt"

cd "$build_dir"
cmake "$root_dir" "${cmake_opts[@]}"

# EOF
