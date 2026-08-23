#!/usr/bin/env bash

# Print "key=<hash>" for use as a CI cache key for the deps directory.
#
# Every dependency is now pinned in the file that knows how to get it -- the
# Find modules under cmake/ for the ones the build can produce itself, and the
# scripts here for the ones a CI job still fetches by hand -- so hashing those
# files is enough. Move a pin, get a new key.
#
# This used to have to resolve a revision over the network, because OutputCheck
# was cloned without one and a cache built from it would otherwise be served
# for ever. It is pinned in tests/CMakeLists.txt now, so the key is a pure
# function of the tree.
#
# One gap is known and deliberately left open. CryptoMiniSat's own tag is
# pinned, but from 5.14 it fetches cadical and cadiback from meelgroup's
# default branches, so what it bundles is pinned by nothing here and a cached
# deps/install can hold an older bundle than a fresh build would produce.
# Folding those two in would invalidate this key -- and so rebuild
# CryptoMiniSat, the most expensive dependency in CI -- every time an unrelated
# fork moves. The bundle stays inside CryptoMiniSat, and STP's own CaDiCaL
# comes from CADICAL_DIR or from cmake/FindCaDiCaL.cmake and nowhere else, so
# the drift is not worth paying that for.

set -e -u -o pipefail

here=$(dirname "$0")
root=$(cd "${here}/../.." && pwd)

hash=$(
  {
    cat "${root}"/cmake/Find*.cmake
    cat "${root}"/cmake/deps-helper.cmake
    find "${root}"/cmake/deps-utils -type f | sort | xargs cat
    cat "${here}"/setup-*.sh
    # The FetchContent pins live beside what they are added to rather than in
    # a Find module: ABC and mimalloc in the top-level CMakeLists and lib's,
    # GoogleTest and OutputCheck in the test tree.
    grep -hE "GIT_TAG|GIT_REPOSITORY|ABC_GIT_TAG" \
        "${root}"/CMakeLists.txt "${root}"/tests/CMakeLists.txt
  } | sha256sum | cut -d' ' -f1
)

echo "key=${hash}"

# EOF
