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
#
# One gap is known and deliberately left open. CryptoMiniSat's own tag is
# pinned, but from 5.14 it fetches cadical and cadiback from meelgroup's
# default branches, so what it bundles is pinned by nothing here and a cached
# deps/install can hold an older bundle than a fresh build would produce.
# Folding those two in would invalidate this key -- and so rebuild
# CryptoMiniSat, the most expensive dependency in CI -- every time an
# unrelated fork moves. The bundle stays inside CryptoMiniSat, and STP's own
# CaDiCaL comes from CADICAL_DIR and nowhere else, so the drift is not worth
# paying that for.

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
