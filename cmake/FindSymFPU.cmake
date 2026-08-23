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
else()
    # Rung 1.
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

    set(SymFPU_COMMIT "502cd63f7626d1f691c8df3869d76a37ae572556")
    set(SymFPU_CHECKSUM "238fc92456032230495d681ae6868b3c9488fd9b9394ca01e9c9b77098d2c336")

    # STP carries four fixes to SymFPU that upstream has not taken. They used
    # to be applied to a submodule working tree at configure time, by a
    # function that had to check whether each one was already applied -- since
    # the tree persisted between configures, and a second build directory
    # against the same source would otherwise have applied them twice. An
    # ExternalProject unpacks a fresh tree and patches it once, so all of that
    # goes away.
    #
    # A tarball rather than a git clone, deliberately: ExternalProject's update
    # step for a git source re-runs `git checkout`, which reverts a patched
    # working tree. A URL has no update step to fight.
    find_program(PATCH_EXECUTABLE patch)
    if(NOT PATCH_EXECUTABLE)
        message(FATAL_ERROR
            "SymFPU has to be patched before it can be built, and `patch` was "
            "not found. Install it, or point SYMFPU_INCLUDE_DIRS at a copy "
            "that has been patched already.")
    endif()

    file(GLOB SymFPU_PATCHES "${CMAKE_CURRENT_LIST_DIR}/deps-utils/symfpu/*.patch")
    list(SORT SymFPU_PATCHES)
    set(SymFPU_PATCH_COMMAND "")
    foreach(_patch ${SymFPU_PATCHES})
        list(APPEND SymFPU_PATCH_COMMAND
             COMMAND ${PATCH_EXECUTABLE} -p1 -d <SOURCE_DIR> -i "${_patch}")
    endforeach()
    # PATCH_COMMAND expects the first command without the COMMAND keyword.
    list(REMOVE_AT SymFPU_PATCH_COMMAND 0)

    ExternalProject_Add(
        SymFPU-EP
        ${STP_EP_COMMON_CONFIG}
        URL https://github.com/martin-cs/symfpu/archive/${SymFPU_COMMIT}.tar.gz
        URL_HASH SHA256=${SymFPU_CHECKSUM}
        PATCH_COMMAND ${SymFPU_PATCH_COMMAND}
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
