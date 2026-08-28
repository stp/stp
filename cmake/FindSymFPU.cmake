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

# Find SymFPU, the header-only library behind STP's floating-point support.
# Required: every build of STP solves the SMT-LIB floating-point theory.
#
#   SymFPU               imported interface target carrying the include path
#   SYMFPU_INCLUDE_DIRS  the directory that *contains* a symfpu/ directory,
#                        because STP includes "symfpu/core/add.h" and friends
#
# SYMFPU_INCLUDE_DIRS is also an input, and is rung 0 of the ladder in
# cmake/deps-helper.cmake.

include(deps-helper)

set(SymFPU_FOUND_SYSTEM FALSE)

if(SYMFPU_INCLUDE_DIRS)
    # Rung 0.
    if(NOT EXISTS "${SYMFPU_INCLUDE_DIRS}/symfpu/core/unpackedFloat.h")
        message(FATAL_ERROR
            "SYMFPU_INCLUDE_DIRS is '${SYMFPU_INCLUDE_DIRS}', which has no "
            "symfpu/core/unpackedFloat.h under it. It should be the directory "
            "*containing* a symfpu clone, not the clone itself.")
    endif()
    set(SymFPU_FOUND_SYSTEM TRUE)
elseif(NOT STP_DEPS_LOCAL_ONLY)
    # Rung 1, which STP_DEPS_LOCAL_ONLY skips.
    find_path(SYMFPU_INCLUDE_DIR NAMES symfpu/core/unpackedFloat.h)
    if(SYMFPU_INCLUDE_DIR)
        set(SYMFPU_INCLUDE_DIRS "${SYMFPU_INCLUDE_DIR}")
        set(SymFPU_FOUND_SYSTEM TRUE)
    endif()
endif()

if(NOT SymFPU_FOUND_SYSTEM)
    # Rungs 2 and 3.
    check_ep_downloaded("SymFPU-EP")
    if(NOT SymFPU-EP_DOWNLOADED)
        check_auto_download("SymFPU" "" SYMFPU_INCLUDE_DIRS)
    endif()

    # stp/symfpu is a fork laid out like the ABC one: main tracks upstream and
    # the `stp` branch, which this pins a commit of, carries STP's four
    # correctness fixes as commits. They used to be patch files applied at
    # configure time; as commits each one names what it fixes, and a bump is a
    # rebase in that repository where a conflict says which change upstream has
    # met.
    set(SymFPU_COMMIT "d358a6defeace0cd44695e7d922fc62c2f8b8ee8")
    set(SymFPU_CHECKSUM "2557cc598ebde7e6d673cbb7f48a6f0928a18e38bbd3a5b00d126c0f45ba79f1")

    ExternalProject_Add(
        SymFPU-EP
        ${STP_EP_COMMON_CONFIG}
        URL https://github.com/stp/symfpu/archive/${SymFPU_COMMIT}.tar.gz
        URL_HASH SHA256=${SymFPU_CHECKSUM}
        # Header-only: nothing to configure, nothing to build. STP includes
        # "symfpu/core/...", so the headers go under a symfpu/ directory and
        # the include path is its parent.
        CONFIGURE_COMMAND ""
        BUILD_COMMAND ""
        INSTALL_COMMAND ${CMAKE_COMMAND} -E copy_directory
                        <SOURCE_DIR>/core <INSTALL_DIR>/include/symfpu/core
        COMMAND ${CMAKE_COMMAND} -E copy_directory
                <SOURCE_DIR>/utils <INSTALL_DIR>/include/symfpu/utils
    )
    add_dependencies(deps SymFPU-EP)

    set(SYMFPU_INCLUDE_DIRS "${STP_DEP_DIR}/include")
endif()

set(SymFPU_FOUND TRUE)

# SYSTEM: SymFPU is upstream code whose warnings STP does not control, and it
# is a template library, so its headers are compiled as part of every
# translation unit that instantiates the float blaster.
add_library(SymFPU INTERFACE IMPORTED GLOBAL)
set_target_properties(SymFPU PROPERTIES
    INTERFACE_INCLUDE_DIRECTORIES "${SYMFPU_INCLUDE_DIRS}"
    INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${SYMFPU_INCLUDE_DIRS}"
)

mark_as_advanced(SymFPU_FOUND)
mark_as_advanced(SymFPU_FOUND_SYSTEM)
mark_as_advanced(SYMFPU_INCLUDE_DIR)

if(SymFPU_FOUND_SYSTEM)
    message(STATUS "Found SymFPU: ${SYMFPU_INCLUDE_DIRS}")
else()
    message(STATUS "Building SymFPU ${SymFPU_COMMIT}: ${SYMFPU_INCLUDE_DIRS}")
    add_dependencies(SymFPU SymFPU-EP)
endif()

# EOF
