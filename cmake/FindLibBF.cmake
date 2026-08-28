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

# Find LibBF, which folds the real literals in floating-point input --
# ((_ to_fp 8 24) RNE 1.5) -- to their exactly-rounded bits while parsing.
# Required: every build of STP parses that syntax.
#
#   LibBF            imported target, carrying the header and the archive
#   LIBBF_INCLUDE_DIR / LIBBF_LIBRARY   what the target was built from
#
# See cmake/deps-helper.cmake for the ladder this follows.

include(deps-helper)

# Rung 0.
set(LIBBF_DIR "" CACHE PATH
    "Path to a built LibBF: the directory containing libbf.h and the bf library")

# A LibBF already built at deps/libbf -- which is where the setup script this
# replaces put one -- is still used with no flags. That used to be LIBBF_DIR's
# default, which made it indistinguishable from a LIBBF_DIR the caller named,
# and the two are not the same thing: a named copy is an answer, a directory
# that happens to hold one is a place to look. Only the second is skipped under
# STP_DEPS_LOCAL_ONLY, being in the source tree rather than this build
# directory -- and only by keeping them apart can an explicit
# -DLIBBF_DIR=<source>/deps/libbf still mean what it says.
if(NOT LIBBF_DIR AND NOT STP_DEPS_LOCAL_ONLY)
    set(LIBBF_DIR "${PROJECT_SOURCE_DIR}/deps/libbf")
endif()

set(LibBF_FOUND_SYSTEM FALSE)

# Whether LIBBF_DIR holds a LibBF is the test, not whether it is set: a path
# that has none falls through to the rung below rather than failing, which is
# what makes the deps/libbf fallback above a fallback.
if(LIBBF_DIR AND EXISTS "${LIBBF_DIR}/libbf.h")
    find_path(LIBBF_INCLUDE_DIR NAMES libbf.h PATHS "${LIBBF_DIR}" NO_DEFAULT_PATH)
    find_library(LIBBF_LIBRARY NAMES bf PATHS "${LIBBF_DIR}" NO_DEFAULT_PATH)
    if(NOT LIBBF_INCLUDE_DIR OR NOT LIBBF_LIBRARY)
        message(FATAL_ERROR
            "LIBBF_DIR is '${LIBBF_DIR}', which has libbf.h but no bf library "
            "beside it. Finish building it there, or point LIBBF_DIR "
            "somewhere else.")
    endif()
    set(LibBF_FOUND_SYSTEM TRUE)
elseif(NOT STP_DEPS_LOCAL_ONLY)
    # Rung 1, which STP_DEPS_LOCAL_ONLY skips. PATHS, not NO_DEFAULT_PATH: this
    # is the rung that is meant to search the system, and STP_DEP_DIR is on
    # CMAKE_PREFIX_PATH, so a LibBF that an earlier build directory installed
    # there is found here and no ExternalProject is created below.
    find_path(LIBBF_INCLUDE_DIR NAMES libbf.h)
    find_library(LIBBF_LIBRARY NAMES bf)
    if(LIBBF_INCLUDE_DIR AND LIBBF_LIBRARY)
        set(LibBF_FOUND_SYSTEM TRUE)
    endif()
endif()

if(NOT LibBF_FOUND_SYSTEM)
    # Rungs 2 and 3.
    check_ep_downloaded("LibBF-EP")
    if(NOT LibBF-EP_DOWNLOADED)
        check_auto_download("LibBF" "")
    endif()

    # Upstream publishes release tarballs on bellard.org and no repository, so
    # STP mirrors them in stp/libbf: master holds the releases verbatim, one
    # commit each, and the stp branch adds STP's MSVC portability changes on
    # top. A commit rather than a tag, because that branch is rebased onto each
    # new import and a tag on it would not survive -- which is also why this is
    # a git clone rather than a tarball with a checksum.
    set(LibBF_VERSION "3df8db0a56efd2a621cd04dd16c881be66403f2a")

    set(LibBF_ARCHIVE
        "${CMAKE_STATIC_LIBRARY_PREFIX}bf${CMAKE_STATIC_LIBRARY_SUFFIX}")

    ExternalProject_Add(
        LibBF-EP
        ${STP_EP_COMMON_CONFIG}
        GIT_REPOSITORY https://github.com/stp/libbf
        GIT_TAG ${LibBF_VERSION}
        # The mirror is the upstream tarball verbatim, so it also carries tests,
        # benchmarks, softfp templates and a calculator demo, and it has no
        # CMakeLists of its own. Supply one that builds the two files STP needs.
        PATCH_COMMAND ${CMAKE_COMMAND} -E copy
                      "${CMAKE_CURRENT_LIST_DIR}/deps-utils/libbf-CMakeLists.txt"
                      <SOURCE_DIR>/CMakeLists.txt
        CMAKE_ARGS ${STP_EP_COMMON_CMAKE_ARGS}
                   -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR>
                   -DCMAKE_INSTALL_LIBDIR=lib

        # Without this Ninja refuses to generate: the archive is a link input
        # that does not exist when the generator runs.
        BUILD_BYPRODUCTS <INSTALL_DIR>/lib/${LibBF_ARCHIVE}
    )
    add_dependencies(deps LibBF-EP)

    set(LIBBF_INCLUDE_DIR "${STP_DEP_DIR}/include")
    set(LIBBF_LIBRARY "${STP_DEP_DIR}/lib/${LibBF_ARCHIVE}")
endif()

set(LibBF_FOUND TRUE)

# UNKNOWN rather than STATIC: what was found is whatever LIBBF_DIR or the
# system holds, and CMake puts the path on the link line either way.
#
# Both include properties, and both are needed: INTERFACE_INCLUDE_DIRECTORIES
# is what puts the directory on a consumer's compile line, while
# INTERFACE_SYSTEM_INCLUDE_DIRECTORIES only asks for it to be spelled -isystem.
# SYSTEM matters here -- the header typedefs __int128 on 64-bit targets, which
# gcc's -pedantic rejects in the one translation unit that includes it.
add_library(LibBF UNKNOWN IMPORTED GLOBAL)
set_target_properties(LibBF PROPERTIES
    IMPORTED_LOCATION "${LIBBF_LIBRARY}"
    INTERFACE_INCLUDE_DIRECTORIES "${LIBBF_INCLUDE_DIR}"
    INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${LIBBF_INCLUDE_DIR}"
)

mark_as_advanced(LibBF_FOUND)
mark_as_advanced(LibBF_FOUND_SYSTEM)
mark_as_advanced(LIBBF_INCLUDE_DIR)
mark_as_advanced(LIBBF_LIBRARY)

if(LibBF_FOUND_SYSTEM)
    message(STATUS "Found LibBF: ${LIBBF_LIBRARY}")
else()
    message(STATUS "Building LibBF ${LibBF_VERSION}: ${LIBBF_LIBRARY}")
    add_dependencies(LibBF LibBF-EP)
endif()

# EOF
