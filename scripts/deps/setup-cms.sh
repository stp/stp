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
cmake -DENABLE_ASSERTIONS=OFF -DBUILD_SHARED_LIBS=OFF -DSTATIC_BINARY=OFF \
      -DCMAKE_INSTALL_PREFIX:PATH="${install_dir}" ..
cmake --build . --parallel "$(nproc)"
cmake --install .
cd ..

# EOF
