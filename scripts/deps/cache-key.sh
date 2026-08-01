#!/usr/bin/env bash

# Print "key=<hash>" for use as a CI cache key for the deps directory.
#
# A setup script that clones without pinning a revision would keep being
# served a cache built from whatever that repository happened to contain the
# first time, so for those the commit the default branch currently points at
# is folded in: upstream movement then produces a new key. CryptoMiniSat,
# CaDiCaL, GTest and minisat are pinned to a tag or commit inside their
# scripts, which the script hash already covers -- OutputCheck, a test-only
# dependency that is never linked into anything, is the one that is not.

set -e -u -o pipefail

hash=$(
  {
    for repo in stp/OutputCheck; do
      git ls-remote "https://github.com/${repo}" HEAD
    done
    cat "$(dirname "$0")"/setup-*.sh
  } | sha256sum | cut -d' ' -f1
)

echo "key=${hash}"

# EOF
