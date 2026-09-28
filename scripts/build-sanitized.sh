#!/usr/bin/env bash
# Build STP with Clang ASan+UBSan and run the UF lifecycle surface.  This
# deliberately supplies C and C++ flags: ABC is C, while -DSANITIZE=ON only
# instruments C++ at this baseline.  The system allocator keeps mimalloc from
# replacing malloc underneath ASan.
#
# Usage:
#   scripts/build-sanitized.sh [build-dir] [lit-tool] [extra cmake args...]
#
# A SAT backend still has to be supplied when it is not discoverable in the
# usual deps directory, for example:
#   scripts/build-sanitized.sh build-sanitize "$(command -v lit)" \
#     -DUSE_CADICAL=ON -DCADICAL_DIR="$PWD/deps/cadical"
set -eu

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
sanitized_build="${1:-$repo_root/build-sanitize}"
lit_tool="${2:-$(command -v lit || true)}"
shift "$(( $# > 2 ? 2 : $# ))"

lit_cmake_arg=()
if [ -n "$lit_tool" ]; then
  lit_cmake_arg+=("-DLIT_TOOL=$lit_tool")
fi

cmake -S "$repo_root" -B "$sanitized_build" \
  -DCMAKE_BUILD_TYPE=RelWithDebInfo \
  -DCMAKE_C_COMPILER=clang \
  -DCMAKE_CXX_COMPILER=clang++ \
  -DCMAKE_C_FLAGS="-fsanitize=address,undefined -fno-omit-frame-pointer" \
  -DCMAKE_CXX_FLAGS="-fsanitize=address,undefined -fno-omit-frame-pointer" \
  -DCMAKE_EXE_LINKER_FLAGS="-fsanitize=address,undefined" \
  -DCMAKE_SHARED_LINKER_FLAGS="-fsanitize=address,undefined" \
  -DENABLE_ASSERTIONS=ON \
  -DENABLE_TESTING=ON \
  -DSTP_ALLOCATOR=system \
  "${lit_cmake_arg[@]}" \
  "$@"

cmake --build "$sanitized_build" --parallel "$(nproc)"

ASAN_OPTIONS=detect_leaks=1:halt_on_error=1 \
UBSAN_OPTIONS=halt_on_error=1:print_stacktrace=1 \
ctest --test-dir "$sanitized_build" \
  -R '(uninterpreted-functions|UninterpretedFunctions|UFChecker|UFRefinement|UFLowering)' \
  --output-on-failure

if [ -n "$lit_tool" ]; then
  (
    cd "$sanitized_build/tests/query-files"
    ASAN_OPTIONS=detect_leaks=1:halt_on_error=1 \
    UBSAN_OPTIONS=halt_on_error=1:print_stacktrace=1 \
      "$lit_tool" -s --config-prefix=RelWithDebInfo --filter='uf/' .
  )
fi

echo "Sanitized UF build and tests passed: $sanitized_build"
