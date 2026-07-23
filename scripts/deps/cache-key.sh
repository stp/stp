#!/usr/bin/env bash

# Print "key=<hash>" for use as a CI cache key for the deps directory.
#
# The setup scripts clone most dependencies without pinning a revision, so
# hashing the scripts alone would keep serving a cache built from whatever
# those repositories happened to contain the first time. Fold in the commit
# their default branches currently point at, so upstream movement produces a
# new key. CryptoMiniSat is pinned to a tag inside its script, which the
# script hash already covers.

set -e -u -o pipefail

hash=$(
  {
    for repo in stp/minisat stp/googletest stp/OutputCheck; do
      git ls-remote "https://github.com/${repo}" HEAD
    done
    cat "$(dirname "$0")"/setup-*.sh
  } | sha256sum | cut -d' ' -f1
)

echo "key=${hash}"

# EOF
