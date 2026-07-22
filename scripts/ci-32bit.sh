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
  strace \
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

# Temporary diagnostic: under lit the solver appears to never run for
# let_009 (a tee wrapper left no trace). Strace the lit run to see the
# exec and writes, and try a variant of the test without 'not'.
(
  cd tests/query-files
  LIT_BIN=$(sed -n 's/^add_test(query-files "\([^"]*\)".*/\1/p' CTestTestfile.cmake)
  PREFIX=$(sed -n 's/.*--config-prefix=\([^" ]*\).*/\1/p' CTestTestfile.cmake)

  sed 's/^; RUN: not %solver/; RUN: %solver/' \
    ../../tests/query-files/let-tests/let_009.smt2 \
    > ../../tests/query-files/let-tests/let_009_no_not.smt2

  echo "--- strace'd lit run:"
  strace -ff -e trace=process -s 300 -o /tmp/lit-strace \
    "$LIT_BIN" -a ${PREFIX:+--config-prefix=$PREFIX} --filter 'let_009' . || true
  echo "--- execve calls mentioning stp or OutputCheck or not:"
  grep -h "execve" /tmp/lit-strace* | grep -E "stp|OutputCheck|/not|bin/not" || true
  echo "--- exits and signals:"
  grep -hE "exited with|killed by" /tmp/lit-strace* | sort | uniq -c | sort -rn | head
  rm -f ../../tests/query-files/let-tests/let_009_no_not.smt2
  echo "--- end"
)

ctest --parallel "$(nproc)" -VV --output-on-failure

# EOF
