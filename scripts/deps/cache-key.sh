#!/usr/bin/env bash

# Print "key=<hash>" for use as a CI cache key for the deps directory.
#
# Every dependency is pinned in the file that knows how to get it -- a Find
# module under cmake/, CryptoMiniSat's included now that the build produces
# that one too -- so hashing those files is enough. Move a pin, get a new key.
#
# This used to have to resolve a revision over the network, because OutputCheck
# was cloned without one and a cache built from it would otherwise be served
# for ever. It is pinned in tests/CMakeLists.txt now, so the key is a pure
# function of the tree.
#
# The gap this used to carry is closed. CryptoMiniSat's tag was pinned, but
# from 5.14 it fetched cadical and cadiback from meelgroup's default branches,
# so what it bundled was pinned by nothing here and a cached deps/install could
# hold an older bundle than a fresh build would produce. Built NOCADICAL it
# fetches neither, and its own commit is pinned in FindCryptoMiniSat.cmake,
# which is hashed below.

set -e -u -o pipefail

here=$(dirname "$0")
root=$(cd "${here}/../.." && pwd)

hash=$(
  {
    cat "${root}"/cmake/Find*.cmake
    cat "${root}"/cmake/deps-helper.cmake
    find "${root}"/cmake/deps-utils -type f | sort | xargs cat
    # The FetchContent pins live beside what they are added to rather than in
    # a Find module: mimalloc and unordered_dense in the top-level CMakeLists,
    # GoogleTest and OutputCheck in the test tree.
    grep -hE "GIT_TAG|GIT_REPOSITORY|ABC_GIT_TAG" \
        "${root}"/CMakeLists.txt "${root}"/tests/CMakeLists.txt
  } | sha256sum | cut -d' ' -f1
)

echo "key=${hash}"

# EOF
