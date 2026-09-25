# AUTHORS: Andrew Teylu
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

# Find IMath, the arbitrary-precision integer and rational library underneath
# STP's exact linear real arithmetic. Required: every build of STP that solves
# QF_LRA needs it, which is every build.
#
#   IMath            imported target, carrying the headers and the archive
#   IMATH_INCLUDE_DIR / IMATH_LIBRARY   what the target was built from
#
# See cmake/deps-helper.cmake for the ladder this follows -- with one rung
# missing. There is deliberately no system rung: STP applies a patch that
# renames IMath's GMP-shaped private type (mpz_t, which collides with a real
# GMP in the same link) and makes its tuning globals immutable. STP's own
# sources name the renamed type, so an unpatched copy -- distribution package
# or otherwise -- would not compile against them, and silently linking one
# would be worse than not finding it.

include(deps-helper)

# Rung 0. A copy already built by a previous run, or built deliberately, in the
# layout this file installs.
set(IMATH_DIR "" CACHE PATH
    "Path to a built, STP-patched IMath: a prefix holding include/imrat.h and lib/ with the imath library")

# A copy at deps/imath is used with no flags, as cmake/FindLibBF.cmake uses
# deps/libbf, and for the same reason it is kept apart from IMATH_DIR: a named
# copy is an answer, a directory that happens to hold one is a place to look,
# and only the second is skipped under STP_DEPS_LOCAL_ONLY, being in the source
# tree rather than this build directory.
if(NOT IMATH_DIR AND NOT STP_DEPS_LOCAL_ONLY)
    set(IMATH_DIR "${PROJECT_SOURCE_DIR}/deps/imath")
endif()

set(_imath_include_paths "${STP_DEP_DIR}/include")
set(_imath_library_paths "${STP_DEP_DIR}/lib")
if(IMATH_DIR)
    list(PREPEND _imath_include_paths "${IMATH_DIR}/include")
    list(PREPEND _imath_library_paths "${IMATH_DIR}/lib")
endif()

set(IMath_FOUND_SYSTEM FALSE)
find_path(IMATH_INCLUDE_DIR NAMES imrat.h
          PATHS ${_imath_include_paths}
          NO_DEFAULT_PATH)
find_library(IMATH_LIBRARY NAMES imath
             PATHS ${_imath_library_paths}
             NO_DEFAULT_PATH)
unset(_imath_include_paths)
unset(_imath_library_paths)

if(NOT (IMATH_INCLUDE_DIR AND IMATH_LIBRARY))
    # Rungs 2 and 3.
    check_ep_downloaded("IMath-EP")
    if(NOT IMath-EP_DOWNLOADED)
        check_auto_download("IMath" "")
    endif()

    # v1.35. A commit rather than the tag, so that a retagged release cannot
    # change what STP builds; the patch below is pinned to exactly this tree.
    set(IMath_VERSION "a4de3dea7e65e2374a91d9938e292b887896fd24")

    set(IMath_ARCHIVE
        "${CMAKE_STATIC_LIBRARY_PREFIX}imath${CMAKE_STATIC_LIBRARY_SUFFIX}")

    # The patch is regenerated with zero context so that `git diff --check`
    # accepts it, which is why applying it needs --unidiff-zero. Upstream
    # carries no CMakeLists, so supply the one that builds the two files STP
    # needs against STP's allocation hooks.
    ExternalProject_Add(
        IMath-EP
        ${STP_EP_COMMON_CONFIG}
        GIT_REPOSITORY https://github.com/creachadair/imath
        GIT_TAG ${IMath_VERSION}
        PATCH_COMMAND git apply --unidiff-zero
                      "${CMAKE_CURRENT_LIST_DIR}/deps-utils/imath-no-gmp-names-immutable-tuning.patch"
              COMMAND ${CMAKE_COMMAND} -E copy
                      "${CMAKE_CURRENT_LIST_DIR}/deps-utils/imath-CMakeLists.txt"
                      <SOURCE_DIR>/CMakeLists.txt
        CMAKE_ARGS ${STP_EP_COMMON_CMAKE_ARGS}
                   -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR>
                   -DCMAKE_INSTALL_LIBDIR=lib
                   "-DSTP_IMATH_ALLOC_HOOKS_HEADER=${PROJECT_SOURCE_DIR}/lib/Lra/ImathAllocHooks.h"

        # Without this Ninja refuses to generate: the archive is a link input
        # that does not exist when the generator runs.
        BUILD_BYPRODUCTS <INSTALL_DIR>/lib/${IMath_ARCHIVE}
    )
    add_dependencies(deps IMath-EP)

    set(IMATH_INCLUDE_DIR "${STP_DEP_DIR}/include")
    set(IMATH_LIBRARY "${STP_DEP_DIR}/lib/${IMath_ARCHIVE}")
endif()

set(IMath_FOUND TRUE)

# UNKNOWN rather than STATIC: what was found is whatever IMATH_DIR holds, and
# CMake puts the path on the link line either way.
#
# SYSTEM as well as ordinary includes: the headers are third-party C that
# STP's -Wconversion/-Wsign-conversion policy is not meant to judge.
add_library(IMath UNKNOWN IMPORTED GLOBAL)
set_target_properties(IMath PROPERTIES
    IMPORTED_LOCATION "${IMATH_LIBRARY}"
    INTERFACE_INCLUDE_DIRECTORIES "${IMATH_INCLUDE_DIR}"
    INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${IMATH_INCLUDE_DIR}"
)

# An imported target carries no build order of its own. Everything that
# includes IMath's headers has to wait for the ExternalProject to install
# them, not just for its archive to appear.
if(TARGET IMath-EP)
    add_dependencies(IMath IMath-EP)
endif()

# EOF
