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

# Find nlohmann/json, the header-only JSON library stp-p writes its reports
# and statistics with. Only tools/stp-p uses it, and only when
# STP_BUILD_PARALLEL is ON; a default build never looks for it.
#
#   NlohmannJson      imported interface target carrying the include path
#   NLOHMANN_JSON_DIR a directory containing nlohmann/json.hpp, or an
#                     include/ directory that does; rung 0 of the ladder in
#                     cmake/deps-helper.cmake
#
# Rung 1 is the system copy (Debian and Ubuntu: nlohmann-json3-dev; Fedora:
# json-devel; openSUSE: nlohmann_json-devel). Otherwise a pinned release is
# downloaded and its headers installed into STP_DEP_DIR at build time.

include(deps-helper)

set(NlohmannJson_FOUND FALSE)
set(NlohmannJson_FOUND_SYSTEM FALSE)

if(NLOHMANN_JSON_DIR)
    # Rung 0.
    find_path(NLOHMANN_JSON_INCLUDE_DIR NAMES nlohmann/json.hpp
              PATHS "${NLOHMANN_JSON_DIR}" "${NLOHMANN_JSON_DIR}/include"
              NO_DEFAULT_PATH)
    if(NOT NLOHMANN_JSON_INCLUDE_DIR)
        message(FATAL_ERROR
            "NLOHMANN_JSON_DIR is '${NLOHMANN_JSON_DIR}', but there is no "
            "nlohmann/json.hpp in it or in its include/ directory.")
    endif()
    set(NlohmannJson_FOUND_SYSTEM TRUE)
elseif(NOT STP_DEPS_LOCAL_ONLY)
    # Rung 1, which STP_DEPS_LOCAL_ONLY skips.
    find_path(NLOHMANN_JSON_INCLUDE_DIR NAMES nlohmann/json.hpp)
    if(NLOHMANN_JSON_INCLUDE_DIR)
        set(NlohmannJson_FOUND_SYSTEM TRUE)
    endif()
endif()

if(NOT NlohmannJson_FOUND_SYSTEM)
    # Rungs 2 and 3.
    check_ep_downloaded("NlohmannJson-EP")
    if(NOT NlohmannJson-EP_DOWNLOADED)
        check_auto_download("NlohmannJson" "-DSTP_BUILD_PARALLEL=OFF" NLOHMANN_JSON_DIR)
    endif()

    set(NLOHMANN_JSON_VERSION "3.12.0")
    set(NLOHMANN_JSON_CHECKSUM "42f6e95cad6ec532fd372391373363b62a14af6d771056dbfc86160e6dfff7aa")

    # Header-only: no upstream configure or build is needed. The release
    # archive contains the headers without the repository's tests and data.
    ExternalProject_Add(
        NlohmannJson-EP
        ${STP_EP_COMMON_CONFIG}
        URL https://github.com/nlohmann/json/releases/download/v${NLOHMANN_JSON_VERSION}/json.tar.xz
        URL_HASH SHA256=${NLOHMANN_JSON_CHECKSUM}
        CONFIGURE_COMMAND ""
        BUILD_COMMAND ""
        INSTALL_COMMAND ${CMAKE_COMMAND} -E copy_directory
                        <SOURCE_DIR>/include/nlohmann <INSTALL_DIR>/include/nlohmann
    )
    add_dependencies(deps NlohmannJson-EP)

    set(NLOHMANN_JSON_INCLUDE_DIR "${STP_DEP_DIR}/include")
else()
    # stp-p's reports keep their keys in order (nlohmann::ordered_json), which
    # arrived in 3.9.0. Check local copies now; the pinned release above is
    # new enough, but its headers will not exist until the build runs.
    # The macros are in json.hpp up to 3.10, then in detail/abi_macros.hpp.
    set(NLOHMANN_JSON_VERSION "")
    foreach(_header json.hpp detail/abi_macros.hpp)
        set(_path "${NLOHMANN_JSON_INCLUDE_DIR}/nlohmann/${_header}")
        if(NLOHMANN_JSON_VERSION STREQUAL "" AND EXISTS "${_path}")
            file(STRINGS "${_path}" _lines
                 REGEX "#define NLOHMANN_JSON_VERSION_(MAJOR|MINOR|PATCH) ")
            set(_parts "")
            foreach(_part MAJOR MINOR PATCH)
                string(REGEX MATCH "NLOHMANN_JSON_VERSION_${_part} +([0-9]+)" _m "${_lines}")
                if(_m)
                    list(APPEND _parts "${CMAKE_MATCH_1}")
                endif()
            endforeach()
            list(LENGTH _parts _count)
            if(_count EQUAL 3)
                string(REPLACE ";" "." NLOHMANN_JSON_VERSION "${_parts}")
            endif()
        endif()
    endforeach()
    if(NLOHMANN_JSON_VERSION STREQUAL "")
        message(FATAL_ERROR
            "Cannot read the version of the nlohmann/json in "
            "${NLOHMANN_JSON_INCLUDE_DIR}; STP_BUILD_PARALLEL needs 3.9.0 or later.")
    endif()
    if(NLOHMANN_JSON_VERSION VERSION_LESS "3.9.0")
        message(FATAL_ERROR
            "STP_BUILD_PARALLEL needs nlohmann/json 3.9.0 or later (ordered_json); "
            "${NLOHMANN_JSON_INCLUDE_DIR} has ${NLOHMANN_JSON_VERSION}. Point "
            "NLOHMANN_JSON_DIR at a newer copy, or configure with "
            "-DSTP_BUILD_PARALLEL=OFF.")
    endif()
endif()
set(NlohmannJson_FOUND TRUE)

# SYSTEM: upstream code whose warnings STP does not control.
add_library(NlohmannJson INTERFACE IMPORTED GLOBAL)
set_target_properties(NlohmannJson PROPERTIES
    INTERFACE_INCLUDE_DIRECTORIES "${NLOHMANN_JSON_INCLUDE_DIR}"
    INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${NLOHMANN_JSON_INCLUDE_DIR}"
)

mark_as_advanced(NlohmannJson_FOUND)
mark_as_advanced(NlohmannJson_FOUND_SYSTEM)
mark_as_advanced(NLOHMANN_JSON_INCLUDE_DIR)

if(NlohmannJson_FOUND_SYSTEM)
    message(STATUS "Found nlohmann/json ${NLOHMANN_JSON_VERSION}: ${NLOHMANN_JSON_INCLUDE_DIR}")
else()
    message(STATUS "Building nlohmann/json ${NLOHMANN_JSON_VERSION}: ${NLOHMANN_JSON_INCLUDE_DIR}")
    add_dependencies(NlohmannJson NlohmannJson-EP)
endif()
