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

# Temporary diagnostic: the manual pipeline passes on i386 but the same
# test fails under lit, so run lit itself on just that test -- once
# plain, once with the solver wrapped to capture what it prints when
# lit spawns it.
(
  cd tests/query-files
  LIT_BIN=$(sed -n 's/^add_test(query-files "\([^"]*\)".*/\1/p' CTestTestfile.cmake)
  PREFIX=$(sed -n 's/.*--config-prefix=\([^" ]*\).*/\1/p' CTestTestfile.cmake)
  cat > /tmp/stp-tee <<'EOF'
#!/bin/bash
/stp/build-32bit/stp "$@" 2>&1 | tee -a /tmp/lit-solver.out
exit "${PIPESTATUS[0]}"
EOF
  chmod +x /tmp/stp-tee
  echo "--- plain lit run:"
  "$LIT_BIN" -a ${PREFIX:+--config-prefix=$PREFIX} --filter let_009 . || true
  echo "--- lit run with tee-wrapped solver:"
  "$LIT_BIN" -a ${PREFIX:+--config-prefix=$PREFIX} --param solver=/tmp/stp-tee \
    --filter let_009 . || true
  echo "--- solver output captured under lit:"
  cat -A /tmp/lit-solver.out || true
  echo "--- end"
)

ctest --parallel "$(nproc)" -VV --output-on-failure

# EOF
