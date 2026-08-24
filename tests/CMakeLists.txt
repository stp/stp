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
# lit is the last thing here that a machine had to have been prepared for: it
# is not a library STP links but a program the tests are driven by, it is not
# packaged by every distribution, and `pip install lit` into the system
# interpreter is not something a build should ask for. So it is treated like
# every other dependency -- named explicitly, found if installed, and otherwise
# fetched, which for a Python program means a virtual environment of its own in
# the build tree.
#
#   LIT_TOOL              rung 0, an absolute path to a lit
#   an installed lit      rung 1
#   ENABLE_AUTO_DOWNLOAD  rung 3, pip install into ${CMAKE_BINARY_DIR}/venv
set(LIT_VERSION "18.1.8" CACHE STRING "lit version to install when one has to be")
mark_as_advanced(LIT_VERSION)

find_program(LIT_TOOL lit DOC "Path to lit tool")

if(NOT LIT_TOOL AND ENABLE_AUTO_DOWNLOAD)
    set(STP_VENV_DIR "${PROJECT_BINARY_DIR}/venv")
    # Created once and reused: pip is slow, and reconfiguring is not rare.
    if(NOT EXISTS "${STP_VENV_DIR}/bin/lit")
        message(STATUS "Creating a virtual environment for lit: ${STP_VENV_DIR}")
        execute_process(
            COMMAND "${PYTHON_EXECUTABLE}" -m venv "${STP_VENV_DIR}"
            RESULT_VARIABLE _venv_rc OUTPUT_QUIET)
        if(NOT _venv_rc EQUAL 0)
            message(FATAL_ERROR
                "Could not create a virtual environment with "
                "${PYTHON_EXECUTABLE} -m venv. On Debian-likes the venv module "
                "is a separate package (python3-venv); install it, or install "
                "lit yourself and point -DLIT_TOOL at it.")
        endif()
        # Quiet unless it fails, in which case pip's own diagnosis is the
        # useful part and gets printed with ours.
        execute_process(
            COMMAND "${STP_VENV_DIR}/bin/pip" install --quiet
                    --disable-pip-version-check "lit==${LIT_VERSION}"
            RESULT_VARIABLE _pip_rc
            OUTPUT_VARIABLE _pip_out ERROR_VARIABLE _pip_out)
        if(NOT _pip_rc EQUAL 0)
            message(FATAL_ERROR
                "Could not install lit==${LIT_VERSION} into ${STP_VENV_DIR}:\n"
                "${_pip_out}\n"
                "Install lit yourself and point -DLIT_TOOL at it.")
        endif()
    endif()
    set(LIT_TOOL "${STP_VENV_DIR}/bin/lit" CACHE FILEPATH "Path to lit tool" FORCE)
    message(STATUS "Using lit ${LIT_VERSION} from ${STP_VENV_DIR}")
endif()

if(NOT LIT_TOOL)
    message(FATAL_ERROR
        "Could not find the 'lit' tool, which the tests are driven by. "
        "Configure with -DENABLE_AUTO_DOWNLOAD=ON to have it installed into a "
        "virtual environment in the build tree, install it yourself "
        "(pip install lit) and put it on PATH, or point -DLIT_TOOL at one. "
        "To build without the tests, configure with -DENABLE_TESTING=OFF.")
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
# is what happens here: it is fetched at a pinned tag and built from source as
# part of this build, so everyone compiles the same GTest with the same flags
# as STP.
#
# So GTest is the one dependency here that is fetched but not built by an
# ExternalProject. An ExternalProject builds in a separate CMake invocation,
# with its own cache and its own flags, which is exactly what must not happen:
# GTest has to be compiled with STP's flags, with gtest_force_shared_crt under
# MSVC, and with whatever a sanitizer build has put in CMAKE_CXX_FLAGS. That
# needs add_subdirectory(), which needs the source to exist during *this*
# configure -- which is what FetchContent is for and ExternalProject is not.
#
# GTEST_DIR is rung 0, and handing it to FetchContent as the source directory
# rather than branching on it keeps one code path: FetchContent skips the
# download entirely when it is told where the source already is.
include(FetchContent)

set(GTEST_DIR "${PROJECT_SOURCE_DIR}/deps/gtest" CACHE PATH
    "Path to a googletest checkout to build GTest from")

if (EXISTS "${GTEST_DIR}/CMakeLists.txt")
    if (NOT DEFINED FETCHCONTENT_SOURCE_DIR_GOOGLETEST)
        set(FETCHCONTENT_SOURCE_DIR_GOOGLETEST "${GTEST_DIR}")
    endif()
elseif (NOT DEFINED FETCHCONTENT_SOURCE_DIR_GOOGLETEST AND NOT ENABLE_AUTO_DOWNLOAD)
    # Unlike an ExternalProject, FetchContent downloads at configure time, so
    # there is no deferred rung to fall through to and the gate has to be
    # checked by hand.
    message(FATAL_ERROR
        "Could not find googletest, which ENABLE_TESTING needs. Configure "
        "with -DENABLE_AUTO_DOWNLOAD=ON to have it cloned here, point "
        "-DGTEST_DIR at an existing checkout, or build without the tests "
        "with -DENABLE_TESTING=OFF.")
endif()

FetchContent_Declare(
    googletest
    GIT_REPOSITORY https://github.com/google/googletest
    GIT_TAG v1.17.0
)

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
# Does the add_subdirectory(), inside the flags set just above.
FetchContent_MakeAvailable(googletest)
set(CMAKE_CXX_FLAGS "${PREV_CMAKE_CXX_FLAGS}")
set(GTEST_BOTH_LIBRARIES gtest gtest_main)

# SYSTEM so warnings surfacing inside GTest's headers/macros (e.g. a
# -Wsign-compare in an EXPECT_EQ comparison helper) don't trip -Werror in
# STP's own test translation units that include them. The gtest target carries
# the same directory as a SYSTEM INTERFACE include, so this is belt and braces
# for any test target that includes the header without linking the library.
include_directories(SYSTEM ${googletest_SOURCE_DIR}/googletest/include)

# -----------------------------------------------------------------------------
# Find OutputCheck, which the query-file tests match solver output with
# -----------------------------------------------------------------------------
# A tree of Python, so there is nothing to build and nothing to install --
# FetchContent populates it and stops, because it has no CMakeLists for
# MakeAvailable to descend into.
#
# Pinned, which it never was before. It was the one dependency whose revision
# nothing recorded, which is why scripts/deps/cache-key.sh has to resolve its
# HEAD over the network to build a CI cache key: with a pin here, the key can
# be a hash of these files and nothing else.
set(OUTPUTCHECK_DIR "${PROJECT_SOURCE_DIR}/deps/OutputCheck" CACHE PATH
    "Path to an OutputCheck checkout")

if (EXISTS "${OUTPUTCHECK_DIR}/bin/OutputCheck")
    if (NOT DEFINED FETCHCONTENT_SOURCE_DIR_OUTPUTCHECK)
        set(FETCHCONTENT_SOURCE_DIR_OUTPUTCHECK "${OUTPUTCHECK_DIR}")
    endif()
elseif (NOT DEFINED FETCHCONTENT_SOURCE_DIR_OUTPUTCHECK AND NOT ENABLE_AUTO_DOWNLOAD)
    message(FATAL_ERROR
        "Could not find OutputCheck, which the query-file tests need. "
        "Configure with -DENABLE_AUTO_DOWNLOAD=ON to have it cloned here, "
        "point -DOUTPUTCHECK_DIR at an existing checkout, or build without "
        "the tests with -DENABLE_TESTING=OFF.")
endif()

FetchContent_Declare(
    outputcheck
    GIT_REPOSITORY https://github.com/stp/OutputCheck
    GIT_TAG e0133ed42b091a7ddea6b901055e142447819a9e
)
FetchContent_MakeAvailable(outputcheck)

# Handed to lit through lit.site.cfg rather than worked out inside lit.cfg from
# the source tree, which is where it used to be assumed to sit.
set(STP_OUTPUTCHECK_TOOL "${outputcheck_SOURCE_DIR}/bin/OutputCheck")
if (NOT EXISTS "${STP_OUTPUTCHECK_TOOL}")
    message(FATAL_ERROR "OutputCheck was found at ${outputcheck_SOURCE_DIR} "
                        "but has no bin/OutputCheck in it")
endif()
message(STATUS "Found OutputCheck: ${STP_OUTPUTCHECK_TOOL}")

# OutputCheck ships a `not` helper whose shebang is #!/usr/bin/env python, and
# a great many systems have no bare `python` -- only python3. lit already puts
# OutputCheck's bin/ on PATH so that helper can be found; give it a `python` to
# find there too, pointing at the interpreter this build already settled on.
#
# Without this every error-path test -- each one a `not %solver ...` -- fails,
# because the shebang cannot be resolved and the helper feeds OutputCheck an
# empty stream. That was already true of any freshly cloned OutputCheck; it
# simply used to be worked around by hand, one machine at a time.
#
# Not on Windows: `not` is a shell script with a POSIX shebang, so it would not
# run there whatever is on PATH, and the Windows jobs do not run lit.
if (NOT WIN32)
    set(STP_PYTHON_SHIM_DIR "${CMAKE_CURRENT_BINARY_DIR}/python-shim")
    file(MAKE_DIRECTORY "${STP_PYTHON_SHIM_DIR}")
    file(CREATE_LINK "${PYTHON_EXECUTABLE}" "${STP_PYTHON_SHIM_DIR}/python"
         SYMBOLIC)
else()
    set(STP_PYTHON_SHIM_DIR "")
endif()

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
# ENABLE_TESTING is on) exit non-zero on failure, so they run as plain
# CTest tests.
# -----------------------------------------------------------------------------

add_test(NAME test_fpbackend COMMAND test_fpbackend)
add_test(NAME test_fprewrites COMMAND test_fprewrites)

# -----------------------------------------------------------------------------
# Default-off baseline differential for the array-equality feature
#
# Builds the pinned pre-extension baseline commit from repository history
# with the candidate's toolchain, runs the identical C API observation
# driver (tools/extdiff) against both with array equality disabled, and
# requires byte-identical output after canonicalizing the API's unspecified
# counterexample-array entry order. Skips cleanly when the baseline commit is
# unavailable (e.g. shallow CI clones). The baseline checkout/build is cached
# inside the build tree, so only the first run pays for it.
#
# Opt-in (-DTEST_BASELINE_DIFFERENTIAL=ON): the first run configures and
# compiles an entire second STP from git history, which a plain ctest
# invocation should not pay for by surprise.
# -----------------------------------------------------------------------------

option(TEST_BASELINE_DIFFERENTIAL
       "Enable the default-off C API baseline differential test"
       OFF
      )

if(TEST_BASELINE_DIFFERENTIAL AND BUILD_EXECUTABLES)
    add_test(
      NAME default-off-capi-baseline-differential
      COMMAND ${PROJECT_SOURCE_DIR}/scripts/extdiff-baseline-differential.sh
              ${PROJECT_SOURCE_DIR} ${PROJECT_BINARY_DIR}
    )
    set_tests_properties(default-off-capi-baseline-differential PROPERTIES
      SKIP_RETURN_CODE 77
      TIMEOUT 1800
      LABELS "baseline-differential"
    )
endif()
