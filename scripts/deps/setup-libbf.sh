#!/usr/bin/env bash

set -e -u -o pipefail

script_dir="$(cd "$(dirname "$0")" && pwd)"

dep_dir="deps"

[ ! -d "${dep_dir}" ] && mkdir -p "${dep_dir}"

dep="libbf"

# LibBF has no git repository: upstream publishes release tarballs on
# bellard.org. Pin one and check its hash -- the code becomes part of
# libstp, so what is built must be what was reviewed. Override both
# together to try another release; anyone caching on this script's content
# must fold the overrides into their cache key, since an override never
# changes the script.
version="${LIBBF_VERSION:-2025-06-03}"
sha256="${LIBBF_SHA256:-4b23394d67a4a3c3266a38b66831094523fffb5d01974a5c05a0327b36b0a340}"
tarball="libbf-${version}.tar.gz"

cd "${dep_dir}"
rm -rf "${dep}"
mkdir "${dep}"
cd "${dep}"

# LIBBF_TARBALL names a pre-downloaded copy, for builds without network
# access; the hash check applies either way.
if [ -n "${LIBBF_TARBALL:-}" ]; then
    cp "${LIBBF_TARBALL}" "${tarball}"
else
    curl -fsSL -o "${tarball}" "https://bellard.org/libbf/${tarball}"
fi
echo "${sha256}  ${tarball}" | sha256sum -c -

# Only the library proper; the tarball's tests, benchmarks, softfp
# templates and pi/calculator programs are not used.
tar xzf "${tarball}" --strip-components=1 \
    "libbf-${version}/libbf.c" "libbf-${version}/libbf.h" \
    "libbf-${version}/cutils.c" "libbf-${version}/cutils.h"

# MSVC portability, kept as a patch so a version bump re-applies it
# mechanically rather than by hand; see the patch header for what and why.
patch -p1 < "${script_dir}/patches/0001-libbf-msvc-compat.patch"

# The fetch/verify/patch half above is portable; the compile below is
# not. The Windows CI job runs this script under git-bash with
# LIBBF_NO_BUILD set and compiles with cl in its own step.
if [ -n "${LIBBF_NO_BUILD:-}" ]; then
    exit 0
fi

# -fPIC: libbf.a is linked into libstp.so, like CaDiCaL's. STP's cmake
# consumes this checkout in place: LIBBF_DIR points here, at libbf.h and
# libbf.a.
${CC:-cc} -O2 -fPIC -Wall -c libbf.c -o libbf.o
${CC:-cc} -O2 -fPIC -Wall -c cutils.c -o cutils.o
${AR:-ar} rcs libbf.a libbf.o cutils.o

# EOF
