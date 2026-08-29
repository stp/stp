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

# Built with -DNOCADICAL=ON, so this CryptoMiniSat has no CaDiCaL in it.
#
# CMS >= 5.14 otherwise fetches cadical and cadiback itself (via CMake
# FetchContent) and installs them beside itself, and that copy is what the
# CaDiCaL machinery elsewhere in this tree exists to keep apart from STP's own:
# a libcadical.a and a cadical/cadical.hpp landing in ${install_dir} under the
# very names STP uses, plus an imported target named plainly `cadical` that a
# static libcryptominisat5 puts on libstp's link line -- which the guard after
# the CryptoMiniSat block in the top-level CMakeLists refuses, because two
# CaDiCaLs there collide. Fitting both in meant pointing STP at CryptoMiniSat's
# copy, one version behind (2.1.3 against the rel-3.0.1 this builds), which
# turns --cadical-factor off.
#
# NOCADICAL=ON removes the whole question: nothing is fetched, nothing is
# installed, no `cadical` target exists, and STP links its own pinned CaDiCaL
# next to a static CryptoMiniSat with no accommodation on either side. It is
# sound because STP never asks for the one thing CryptoMiniSat wants CaDiCaL
# for -- backbone extraction, reached only through the "backbone" simplification
# token or backbone_simpl(), neither of which is in a default schedule or in any
# STP call. See stp/cryptominisat, branch stp.
#
# That branch is release/v5.14.7 plus the option, so the version is the one
# this pinned before. cache-key.sh's note about an unpinned meelgroup bundle
# drifting no longer applies here: there is no bundle.

git clone https://github.com/stp/cryptominisat "${dep}"
cd "${dep}"
# We specify the tags/commits for the other repositories, so do for this too.
# The branch is `stp`, as on the other forks in that organisation; this is
# its head, pinned the way FindMiniSat/FindLibBF/FindABC pin theirs.
git checkout 261392c4e993f40638392012b689a0a4a7794355
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
      -DCMAKE_BUILD_TYPE=Release -DNOCADICAL=ON \
      -DCMAKE_INSTALL_PREFIX:PATH="${install_dir}" "$@" ..
cmake --build . --parallel "$(nproc)"
cmake --install .
cd ..

# EOF
