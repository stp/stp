#!/usr/bin/env bash

set -e -u -o pipefail

dep_dir="deps"
dep="symfpu"

cd "${dep_dir}"
# SymFPU is header-only, so there is nothing to build or install -- cloning it
# is enough. STP's CMakeLists names github.com/stp/SymFPU, which 404s;
# martin-cs/symfpu is the upstream. FindSymFPU looks for
# symfpu/core/unpackedFloat.h under SYMFPU_INCLUDE_DIRS, so cloning it as
# deps/symfpu means SYMFPU_INCLUDE_DIRS must point at deps/ (see the CI configure
# steps).
git clone https://github.com/martin-cs/symfpu "${dep}"
# Pinned: an unpinned clone let any upstream push change what every build
# used. Bump deliberately -- in particular once martin-cs/symfpu#14 (small
# significand widths trip unpack's width invariant) is resolved.
git -C "${dep}" checkout --quiet 502cd63f7626d1f691c8df3869d76a37ae572556
cd ..

# EOF
