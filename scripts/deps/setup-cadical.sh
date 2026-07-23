#!/usr/bin/env bash

set -e -u -o pipefail

dep_dir="deps"

[ ! -d "${dep_dir}" ] && mkdir -p "${dep_dir}"

dep="cadical"

cd "${dep_dir}"

# CaDiCaL uses its own configure script rather than CMake, and is consumed
# in place: STP's CADICAL_DIR points at this checkout, which holds the
# header in src/cadical.hpp and the static library in build/libcadical.a.
git clone https://github.com/arminbiere/cadical "${dep}"
cd "${dep}"
# We specify the tags/commits for the other repositories, so do for this too
git checkout rel-2.1.3
# -fPIC: libcadical.a is linked into libstp.so, and CaDiCaL's configure
# does not build position-independent code by default.
./configure -fPIC
make -j"$(nproc)"
cd ..

# EOF
