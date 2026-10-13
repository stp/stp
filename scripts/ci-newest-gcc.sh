#!/usr/bin/env bash

# Build and test STP with the newest GCC release, under -Werror. Run from the
# repository root inside the official GCC image:
#
#   docker run --rm -v "$(pwd)":/stp -w /stp gcc:16 ./scripts/ci-newest-gcc.sh
#
# The other gcc jobs use the runner's GCC 13, and each GCC release adds and
# sharpens warnings -- -Wmaybe-uninitialized above all, whose verdict moves
# with the compiler's optimiser. A tree that is clean under -Werror with GCC 13
# can fail to build for anyone on a current distribution who turns WERROR on.
#
# Every backend and every optional executable is enabled, so that as much of
# STP's own code as possible is compiled by the new compiler.

set -e -u -o pipefail

export DEBIAN_FRONTEND=noninteractive

# No build-essential: the image already has make and the C library's
# headers. Its GCC is the one in /usr/local; Debian's gcc-14 is there too,
# from the base image, which is why CC and CXX are named below.
apt-get update
apt-get install -y --no-install-recommends \
  bison \
  ca-certificates \
  ccache \
  cmake \
  flex \
  git \
  libgmp-dev \
  ninja-build \
  python3 \
  python3-pip \
  python3-setuptools \
  zlib1g-dev
pip3 install --break-system-packages -U 'lit~=23.1'

# The workspace is bind-mounted from the host, so it is owned by a
# different user than the one running in the container.
git config --global --add safe.directory '*'

g++ --version

stp_root="$(pwd)"

mkdir -p build-newest-gcc
cd build-newest-gcc
CC=gcc CXX=g++ cmake \
  -DSTP_DEP_DIR:PATH="${stp_root}/deps/install" \
  -DFETCHCONTENT_BASE_DIR:PATH="${stp_root}/deps/fetch" \
  -DENABLE_AUTO_DOWNLOAD:BOOL=ON \
  -DUSE_CADICAL:BOOL=ON \
  -DUSE_CRYPTOMINISAT:STRING=ON \
  -DUSE_MINISAT:BOOL=ON \
  -DSTP_BUILD_PARALLEL:BOOL=ON \
  -DBUILD_EXTRA_TOOLS:BOOL=ON \
  -DENABLE_TESTING:BOOL=ON \
  -DWERROR:BOOL=ON \
  -DPYTHON_EXECUTABLE:PATH="$(which python3)" \
  -DCMAKE_C_COMPILER_LAUNCHER=ccache \
  -DCMAKE_CXX_COMPILER_LAUNCHER=ccache \
  -G Ninja ..
ccache --zero-stats
# -k 0: a new GCC release tends to flag several places at once, and one run
# should name all of them.
cmake --build . --parallel "$(nproc)" -- -k 0
ccache --show-stats

ctest --parallel "$(nproc)" -VV --output-on-failure

# EOF
