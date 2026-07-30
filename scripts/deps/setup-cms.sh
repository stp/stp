#!/usr/bin/env bash

set -e -u -o pipefail

dep_dir="deps"
install_dir=$(readlink -fm "${dep_dir}"/install)

[ ! -d "${install_dir}" ] && mkdir -p "${install_dir}"

dep="cms"

cd "${dep_dir}"

# CMS >= 5.14 builds its cadical/cadiback dependencies itself (via CMake
# FetchContent), so they no longer need to be built here.

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
cmake -DENABLE_ASSERTIONS=OFF -DBUILD_SHARED_LIBS=OFF -DSTATIC_BINARY=OFF \
      -DCMAKE_BUILD_TYPE=Release \
      -DCMAKE_INSTALL_PREFIX:PATH="${install_dir}" ..
cmake --build . --parallel "$(nproc)"
cmake --install .
cd ..

# EOF
