#!/usr/bin/env bash

set -e -u -o pipefail

dep_dir="deps"
install_dir=$(readlink -fm "${dep_dir}"/install)

[ ! -d "${install_dir}" ] && mkdir -p "${install_dir}"

dep="symfpu"

cd "${dep_dir}"
# SymFPU is header-only, so there is nothing to build or install -- cloning it
# is enough. STP's CMakeLists names github.com/stp/SymFPU, which 404s;
# martin-cs/symfpu is the upstream. FindSymFPU looks for
# symfpu/core/unpackedFloat.h under SYMFPU_INCLUDE_DIRS, so cloning it as
# deps/symfpu means SYMFPU_INCLUDE_DIRS must point at deps/ (see the CI configure
# steps).
git clone https://github.com/martin-cs/symfpu "${dep}"
cd ..

# EOF
