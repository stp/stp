#!/usr/bin/env bash

set -e -u -o pipefail

dep_dir="deps"

dep="gtest"

# Pinned to a tag rather than tracking a default branch, so a CI cache built
# from this checkout stays valid until the pin here moves. Note that
# scripts/deps/cache-key.sh therefore does not need to resolve this repo's
# HEAD: the script hash already covers the pin.
#
# GTest is consumed from source - tests/CMakeLists.txt does add_subdirectory on
# deps/gtest - so there is nothing to build or install here. The clone is the
# whole job.
gtest_tag="v1.17.0"

[ ! -d "${dep_dir}" ] && mkdir -p "${dep_dir}"

cd "${dep_dir}"
git clone --depth 1 --branch "${gtest_tag}" \
    https://github.com/google/googletest "${dep}"

# EOF
