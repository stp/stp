#!/usr/bin/env bash

set -e -u -o pipefail

dep_dir="deps"
install_dir=$(readlink -fm "${dep_dir}"/install)

[ ! -d "${install_dir}" ] && mkdir -p "${install_dir}"

dep="cms"

cd "${dep_dir}"

# Install cadical/cadiback first.

git clone https://github.com/meelgroup/cadical
cd cadical
# branch: "mate-only-libraries-1.8.0" on 2024-04-22.
git checkout c90592e
./configure 
make -j"$(nproc)"
cd ..

git clone https://github.com/meelgroup/cadiback
cd cadiback
# branch: "mate" on 2024-06-06.
git checkout 12dac17
./configure 
make -j"$(nproc)"
cd ..

git clone https://github.com/msoos/cryptominisat "${dep}"
cd "${dep}"
mkdir build && cd build
cmake -DNOSQLITE=ON -DCMAKE_INSTALL_PREFIX:PATH="${install_dir}" ..
cmake --build . --parallel "$(nproc)"
cmake --install .
cd ..

# EOF
