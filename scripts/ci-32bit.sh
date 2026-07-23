#!/usr/bin/env bash

# Build and test STP with a 32-bit (i386) toolchain, to catch code that
# assumes 64-bit pointers or a 64-bit long. Run from the repository root
# inside an i386 Debian container:
#
#   docker run --rm -v "$(pwd)":/stp -w /stp i386/debian:bookworm \
#     linux32 ./scripts/ci-32bit.sh

set -e -u -o pipefail

export DEBIAN_FRONTEND=noninteractive

apt-get update
apt-get install -y --no-install-recommends \
  bison \
  build-essential \
  ca-certificates \
  cmake \
  flex \
  git \
  libboost-program-options-dev \
  ninja-build \
  python3 \
  python3-pip \
  python3-setuptools \
  zlib1g-dev
pip3 install --break-system-packages -U lit

# The workspace is bind-mounted from the host, so it is owned by a
# different user than the one running in the container.
git config --global --add safe.directory '*'

./scripts/deps/setup-minisat.sh
./scripts/deps/setup-gtest.sh
./scripts/deps/setup-outputcheck.sh

mkdir -p build-32bit
cd build-32bit
cmake \
  -DNOCRYPTOMINISAT:BOOL=ON \
  -DENABLE_TESTING:BOOL=ON \
  -DLIT_ARGS:STRING=-v \
  -DPYTHON_EXECUTABLE:PATH="$(which python3)" \
  -G Ninja ..
cmake --build . --parallel "$(nproc)"

# Tests whose RUN line uses "not" need it as a real executable under
# lit's default external shell; it comes with LLVM, which the GitHub
# Ubuntu images happen to ship but this container does not. Have lit
# use its internal shell, which implements "not" itself.
export LIT_USE_INTERNAL_SHELL=1

ctest --parallel "$(nproc)" -VV --output-on-failure

# EOF
