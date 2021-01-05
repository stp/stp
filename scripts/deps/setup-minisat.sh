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
cmake -DCMAKE_INSTALL_PREFIX:PATH="${install_dir}" ..
cmake --build . --parallel "$(nproc)"
cmake --install .
cd ..

# EOF
