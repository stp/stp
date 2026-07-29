#!/usr/bin/env bash

set -e -u -o pipefail

dep_dir="deps"
install_dir=$(readlink -fm "${dep_dir}"/install)

[ ! -d "${install_dir}" ] && mkdir -p "${install_dir}"

dep="minisat"

cd "${dep_dir}"
git clone https://github.com/stp/minisat "${dep}"
cd "${dep}"
mkdir build && cd build
# minisat's cmake_minimum_required predates 3.5, which CMake 4 removed
# support for; the same floor is passed in the Windows CI job.
#
# Build a static (PIC) library, like setup-cms.sh does for CryptoMiniSat: it
# gets linked into libstp, so the installed stp/libstp do not depend on a
# libminisat.so that this script only installs inside the source checkout.
# minisat's CMake never sets PIC itself, so ask for it globally; without it
# the archive cannot be folded into the shared libstp.so. This also serves
# static STP builds, which look for libminisat.a.
#
# Extra arguments are forwarded to CMake, so a caller that needs a different
# flavour of the library can still ask for one.
cmake -DCMAKE_POLICY_VERSION_MINIMUM=3.12 -DSTATICCOMPILE=ON \
      -DCMAKE_POSITION_INDEPENDENT_CODE=ON \
      -DCMAKE_INSTALL_PREFIX:PATH="${install_dir}" "$@" ..
cmake --build . --parallel "$(nproc)"
cmake --install .
cd ..

# EOF
