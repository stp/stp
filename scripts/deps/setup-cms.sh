#!/usr/bin/env bash

set -e -u -o pipefail

# CryptoMiniSat needs GMP, both to build and to be found afterwards: the
# cryptominisat5Config.cmake it installs asks pkg-config for gmp. Nothing else
# in STP uses GMP, so install it here rather than as a baseline dependency --
# on Debian-likes that is `libgmp-dev`, on macOS `brew install gmp`.

dep_dir="deps"
install_dir=$(readlink -fm "${dep_dir}"/install)

[ ! -d "${install_dir}" ] && mkdir -p "${install_dir}"

dep="cms"

cd "${dep_dir}"

# CMS >= 5.14 builds its cadical/cadiback dependencies itself (via CMake
# FetchContent), so they no longer need to be built here.
#
# It also installs them, which matters to anything else using this prefix:
# ${install_dir} ends up holding a libcadical.a, its headers and its CMake
# package, none of which have anything to do with the CaDiCaL that
# the build produces for itself. Three separate things keep the two apart, and
# each of them had to be arranged:
#
#   - The library. CADICAL_DIR pins it with NO_DEFAULT_PATH, so this prefix
#     cannot supply it -- see the note in cmake/FindCaDiCaL.cmake.
#   - The header. Pinning the library does nothing for it: the header is found
#     on the include path, and this prefix puts a cadical/cadical.hpp there
#     under the very name STP uses. So the include directory goes to the one
#     file that includes cryptominisat.h and to nothing else -- see the note in
#     lib/Sat/CMakeLists.txt, and the assertion at the top of
#     include/stp/Sat/Cadical.h that catches it if that ever lapses.
#   - The prefix. ${install_dir} defaults to deps/install, which is also
#     STP_DEP_DIR, and that is the arrangement to avoid when USE_CADICAL is on
#     as well. Two things go wrong with it, and neither is fixable from the
#     STP side:
#
#       * That prefix's include directory is a usage requirement of every
#         dependency STP builds, so it reaches nearly every compile -- and the
#         cadical/cadical.hpp installed here then shadows STP's. The two
#         directories arrive from different targets, so no include order fixes
#         it; it came out wrong for the unit tests while the library was fine.
#       * It is on CMAKE_PREFIX_PATH unconditionally, so that the other scripts
#         here are found without flags, which means STP's own CaDiCaL lookup
#         finds this copy and stops. CADICAL_DIR pins past that one, but only
#         that one.
#
#     So install elsewhere when both backends are wanted. Trailing arguments
#     reach CMake, so -DCMAKE_INSTALL_PREFIX overrides the default; ci.yml's
#     cms-cadical job does that and checks the linked version afterwards.
#
# And then the link. Building CMS shared (-DBUILD_SHARED_LIBS=ON) is what makes
# the combination work, because the bundled CaDiCaL then stays inside
# libcryptominisat5.so; ci.yml's cms-cadical job does exactly that. A static
# CryptoMiniSat puts both archives on libstp's link line, which the guard after
# the CryptoMiniSat block in the top-level CMakeLists refuses -- unless STP is
# pointed at this prefix's CaDiCaL too, so that there is only one.
#
# Note also that the tag below does not pin the bundle: CMS fetches cadical
# and cadiback from meelgroup's default branches, so which version arrives
# depends on the day (5.14.7 brought CaDiCaL 2.1.3). cache-key.sh does not
# track that -- it folds in a revision only for repositories its own scripts
# clone unpinned -- so a cached deps/install can hold a bundle older than a
# fresh build would produce. That drift stays inside CryptoMiniSat, which is
# why it is tolerated rather than chased.

git clone https://github.com/msoos/cryptominisat "${dep}"
cd "${dep}"
# We specify the tags/commits for the other repositories, so do for this too
git checkout release/v5.14.7
mkdir build && cd build
# Build a static (PIC) library. It gets linked into libstp, so the installed
# stp/libstp do not depend on a libcryptominisat5.so that this script only
# installs inside the source checkout. STATIC_BINARY=OFF because the fully
# static cryptominisat5 executable needs static gmp/zlib, which we don't need.
#
# Release rather than CMake's default of RelWithDebInfo, which is what this
# built before: CryptoMiniSat compiles with -g -ggdb3 unless told otherwise,
# and that debug info is dead weight in a library nobody steps through -- it
# was two thirds of the static stp binary (76M, against 24M without).
#
# Note that this does not change the optimisation level. CryptoMiniSat pins
# -O2 for Release and RelWithDebInfo alike (see the -O2 add_compile_options
# in its CMakeLists), a deliberate upstream choice; Release only adds -g0.
# The cadical and cadiback it builds via FetchContent inherit both.
#
# Extra arguments are forwarded to CMake and come last, so every default above
# can be overridden by the caller. The one worth knowing about is the build
# type: pass -DCMAKE_BUILD_TYPE=RelWithDebInfo to get a solver a debugger can
# see into, at the cost of the archive sizes described above.
cmake -DENABLE_ASSERTIONS=OFF -DBUILD_SHARED_LIBS=OFF -DSTATIC_BINARY=OFF \
      -DCMAKE_BUILD_TYPE=Release \
      -DCMAKE_INSTALL_PREFIX:PATH="${install_dir}" "$@" ..
cmake --build . --parallel "$(nproc)"
cmake --install .
cd ..

# EOF
