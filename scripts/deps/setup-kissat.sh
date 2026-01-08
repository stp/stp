#!/usr/bin/env bash

set -e -u -o pipefail

dep_dir=$(cd $(dirname $0); pwd)
dep="kissat"

cd "${dep_dir}"
git clone https://github.com/nindanaoto/kissat.git -b minisatapi "${dep}"
cd "${dep}"
./configure -fpic
make -j"$(nproc)"
cd ..

# EOF
