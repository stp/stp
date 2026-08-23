#!/usr/bin/env bash

set -e -u -o pipefail

dep_dir="deps"

[ ! -d "${dep_dir}" ] && mkdir -p "${dep_dir}"

dep="libbf"

cd "${dep_dir}"

# Upstream LibBF publishes release tarballs on bellard.org and no git
# repository, so STP mirrors them in stp/libbf: master holds the releases
# verbatim, and the stp branch adds STP's MSVC portability changes on top.
# A version bump happens there, by importing the new tarball and rebasing
# that branch onto it; this script only names a commit of the result.
#
# rm -rf so a re-run starts over rather than failing on the directory left
# by the last one, as the tarball fetch this replaced did; ci-32bit.sh calls
# the script unguarded.
rm -rf "${dep}"
git clone https://github.com/stp/libbf "${dep}"
cd "${dep}"
# We specify the tags/commits for the other repositories, so do for this
# too -- and this code becomes part of libstp, so what is built should move
# because someone chose to move it. A commit rather than a tag: the stp
# branch is rebased onto each new import, so a tag on it would not survive.
git checkout 334e7aeec2b0b2be7768285f279b99d1368c5fa9

# The clone above is portable; the compile below is not. The Windows CI
# jobs run this script under git-bash with LIBBF_NO_BUILD set and compile
# with cl or MinGW gcc in their own step.
if [ -n "${LIBBF_NO_BUILD:-}" ]; then
    exit 0
fi

# Only the library proper: the mirror is verbatim, so it also carries the
# tests, benchmarks, softfp templates and pi/calculator programs, none of
# which STP uses.
#
# -fPIC: libbf.a is linked into libstp.so, like CaDiCaL's. STP's cmake
# consumes this checkout in place: LIBBF_DIR points here, at libbf.h and
# libbf.a.
${CC:-cc} -O2 -fPIC -Wall -c libbf.c -o libbf.o
${CC:-cc} -O2 -fPIC -Wall -c cutils.c -o cutils.o
${AR:-ar} rcs libbf.a libbf.o cutils.o

# EOF
