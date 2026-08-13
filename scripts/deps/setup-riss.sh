#!/usr/bin/env bash

set -e -u -o pipefail

dep_dir="deps"

[ ! -d "${dep_dir}" ] && mkdir -p "${dep_dir}"

dep="riss"

cd "${dep_dir}"

# Riss is consumed in place: STP's RISS_DIR points at this checkout, which
# holds the headers under riss/ and the static library in
# build/lib/libriss-coprocessor.a.
git clone https://github.com/conp-solutions/riss "${dep}"
cd "${dep}"
# We specify the tags/commits for the other repositories, so do for this too.
git checkout "${RISS_COMMIT:-41342f15a8e22c78ea7021e85cf4a98e79eb349c}"
# -w: Riss's own sources do not compile warning-free under current compilers,
# and this build is of upstream code we do not maintain. STP's -Werror still
# applies to STP's own sources; RissCore.cpp takes Riss's headers as system
# headers (see lib/Sat/CMakeLists.txt).
# gnu++14: Riss does not build as C++17. Only its .cc files need this -- the
# headers STP includes are C++17-clean.
# CMAKE_POSITION_INDEPENDENT_CODE: libriss-coprocessor.a is linked into
# libstp.so, and Riss's static target is not position-independent by default
# (its FPIC option only covers the shared target). Without this the link of
# libstp.so fails with "relocation R_X86_64_PC32 ... recompile with -fPIC".
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release \
      -DCMAKE_CXX_FLAGS="-w -std=gnu++14" \
      -DCMAKE_POSITION_INDEPENDENT_CODE=ON \
      -DCMAKE_POLICY_VERSION_MINIMUM=3.5
cmake --build build --target riss-coprocessor-lib-static -j"$(nproc)"
cd ..

# EOF
