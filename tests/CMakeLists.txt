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

# -----------------------------------------------------------------------------
# Check we can find the lit tool
# -----------------------------------------------------------------------------
find_program(LIT_TOOL
             lit
             DOC "Path to lit tool"
            )

if(NOT LIT_TOOL)
    message(FATAL_ERROR "Could not find 'lit' tool. You need to install it by e.g. 'pip install lit' If it's already installed, set LIT_TOOL to the full path for lit")
endif()

# Checking absolute path because if(EXISTS ...) behaviour only well
# defined if path is absolute
IF(NOT IS_ABSOLUTE "${LIT_TOOL}")
    message(FATAL_ERROR "LIT_TOOL must be set to an absolute PATH")
endif()

if(NOT EXISTS "${LIT_TOOL}")
    # Can happen if users environment changes after initial configure
    message(FATAL_ERROR "LIT_TOOL is set but the path does not seem to exist. Try deleting the LIT_TOOL cache variable and reconfiguring")
endif()

set(LIT_ARGS -s CACHE STRING "Arguments to pass to lit")

# -----------------------------------------------------------------------------
# Find GTest library which will be used to drive tests
# -----------------------------------------------------------------------------
# GoogleTest devs don't recommend using a pre-built GTest library
# ( https://code.google.com/p/googletest/wiki/FAQ#Why_is_it_not_recommended_to_install_a_pre-compiled_copy_of_Goog ).
# Because of this, distros like Ubuntu don't provide a pre-built GTest library
# so ``find_package(GTest REQUIRED)`` fails.
#
# Instead it is recommended that projects build their own copy of GTest, which
# is what happens here: scripts/deps/setup-gtest.sh clones upstream googletest
# at a pinned tag into deps/gtest, and it is built from source as part of this
# build. Everyone therefore compiles the same GTest with the same flags as STP.
set(GTEST_PREFIX ${PROJECT_SOURCE_DIR}/deps/gtest)
if (NOT EXISTS "${GTEST_PREFIX}/CMakeLists.txt")
    message(FATAL_ERROR "Could not find GTest. Did you run scripts/deps/setup-gtest.sh?")
endif()

if (MSVC)
  # STP is built with the shared version of the CRT, gtest defaults to the
  # static one, and they can't be mixed. Foring gtest to use the dynamic one.
  set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)
endif()

# STP uses GTest alone, and installs none of it: building GMock and adding
# GTest to the install set would both be pure overhead.
set(BUILD_GMOCK   OFF CACHE BOOL "" FORCE)
set(INSTALL_GTEST OFF CACHE BOOL "" FORCE)

set(PREV_CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS}")
# GTest is a vendored third-party dependency; -Wno-error (which comes after the
# global -Werror, so it wins) keeps WERROR from failing the build on GTest's own
# warnings. STP's own test sources are still built with -Werror below.
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-format-nonliteral -Wno-missing-field-initializers")
if (WERROR AND NOT MSVC)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-error")
endif()
add_subdirectory(${GTEST_PREFIX} gtest)
set(CMAKE_CXX_FLAGS "${PREV_CMAKE_CXX_FLAGS}")
set(GTEST_BOTH_LIBRARIES gtest gtest_main)

# SYSTEM so warnings surfacing inside GTest's headers/macros (e.g. a
# -Wsign-compare in an EXPECT_EQ comparison helper) don't trip -Werror in
# STP's own test translation units that include them. The gtest target carries
# the same directory as a SYSTEM INTERFACE include, so this is belt and braces
# for any test target that includes the header without linking the library.
include_directories(SYSTEM ${GTEST_PREFIX}/googletest/include)

# Add handy macros/functions
include(AddSTPGTest)
include(AddGTestSuite)

# -----------------------------------------------------------------------------
# Provide option for running unit tests with valgrind
# -----------------------------------------------------------------------------
option(USE_VALGRIND "Use Valgrind when running unit tests" OFF)

# Leaks are reported but do not fail a test: the tests under tests/api/C
# create Expr handles through the C API and mostly never call vc_DeleteExpr,
# so about thirty of them leak a few bytes each by construction. Memory errors
# -- invalid accesses, uninitialised values -- do fail. Add
# --errors-for-leak-kinds=definite here if you want to hunt the leaks.
set(VALGRIND_ARGS
    --error-exitcode=1
    --leak-check=full
    --errors-for-leak-kinds=none
    --track-origins=yes
    CACHE STRING "Arguments passed to valgrind when USE_VALGRIND is on"
   )

set(VALGRIND_TEST_TIMEOUT 10800
    CACHE STRING "Per-test CTest timeout in seconds when USE_VALGRIND is on"
   )

if(USE_VALGRIND)
    # Make sure valgrind is currently in PATH
    find_program(VALGRIND_TOOL valgrind
                 NO_CMAKE_PATH
                 NO_CMAKE_ENVIRONMENT_PATH
                 NO_CMAKE_SYSTEM_PATH
                )

    if(NOT VALGRIND_TOOL)
        message(FATAL_ERROR "Cannot find valgrind in your PATH")
    else()
        message(STATUS "Found valgrind : ${VALGRIND_TOOL}")
    endif()

    # AddSTPGTest runs each GoogleTest executable through this. Only those: the
    # query-file tests drive the stp binary, which links mimalloc by default,
    # and mimalloc gets its memory from mmap rather than malloc, so memcheck
    # cannot see individual allocations there. Build with
    # -DSTP_ALLOCATOR=system if you want to valgrind the binary itself.
endif()

# -----------------------------------------------------------------------------
# Tests that drive STP by using query files (e.g. smt2, smt and cvc files)
# -----------------------------------------------------------------------------

option(TEST_QUERY_FILES
       "Enable tests that use query files to drive STP" 
       ON
      )

if(TEST_QUERY_FILES)
    add_subdirectory(query-files)
endif()

# -----------------------------------------------------------------------------
# Tests that test STP's various different public APIs
# -----------------------------------------------------------------------------

# FIXME: Enable by default
option(TEST_APIS
       "Enable tests that test STP's public APIs" 
       ON
      )

if(TEST_APIS)
    add_subdirectory(api)
endif()

# -----------------------------------------------------------------------------
# Unit tests
# -----------------------------------------------------------------------------

option(TEST_UNITS
       "Enable unit tests"
       ON
      )

if(TEST_UNITS)
    add_subdirectory(unit-tests)
endif()

# -----------------------------------------------------------------------------
# The floating-point self-test tools (built under tools/ whenever
# ENABLE_FLOATING_POINT and ENABLE_TESTING are on) exit non-zero on failure,
# so they run as plain CTest tests.
# -----------------------------------------------------------------------------

if (ENABLE_FLOATING_POINT)
    add_test(NAME test_fpbackend COMMAND test_fpbackend)
    add_test(NAME test_fprewrites COMMAND test_fprewrites)
endif()
