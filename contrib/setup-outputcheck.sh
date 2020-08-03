#!/usr/bin/env bash

set -e -o pipefail

dep_dir="deps"
install_dir=$(readlink -fm ${dep_dir}/install)

[ ! -d "${install_dir}" ] && mkdir -p "${install_dir}"

dep="OutputCheck"

cd ${dep_dir}
git clone https://github.com/stp/OutputCheck ${dep}
cd ..

# EOF
