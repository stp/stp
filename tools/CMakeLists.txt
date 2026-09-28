# AUTHORS: Dan Liew, Ryan Govostes, Mate Soos
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.

add_subdirectory(stp)
add_subdirectory(extdiff)

option(BUILD_EXTRA_TOOLS "Build extra tools" OFF)
if (BUILD_EXTRA_TOOLS)
  # rewrite_rule_gen constructs its solver through the factory, so any
  # backend serves it, but its own CMakeLists still needs CryptoMiniSat
  # (it links ABC directly). propagator_bench drives CryptoMiniSat's
  # fixed-count API directly. difficulty_bench only scores formulas and
  # works with any backend.
  add_subdirectory(rewrite_rule_gen)
  if (USE_CRYPTOMINISAT)
    add_subdirectory(propagator_bench)
  else()
    message(STATUS "Skipping propagator_bench: it needs CryptoMiniSat")
  endif()
  add_subdirectory(difficulty_bench)
endif()

# The floating-point self-test tools: ordinary executables that exit
# non-zero on failure. Built when testing needs them or when the extra
# tools are asked for -- not in a default build. They are registered with
# CTest from tests/CMakeLists.txt, which is processed after
# enable_testing() and after the checks that can turn ENABLE_TESTING off.
if (ENABLE_TESTING OR BUILD_EXTRA_TOOLS)
    add_subdirectory(test_fpbackend)
    add_subdirectory(test_fprewrites)
    add_subdirectory(c_handle_churn_benchmark)
endif()

# The floating-point rewrite-rule generator: enumerates small terms over a
# float variable and special constants, looking for sound collapses the
# SimplifyingNodeFactory is missing. A developer tool, not a test.
if (BUILD_EXTRA_TOOLS)
    add_subdirectory(fp_rewrite_gen)
endif()

