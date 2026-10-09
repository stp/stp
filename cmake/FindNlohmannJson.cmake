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
# json-devel; openSUSE: nlohmann_json-devel). There is no download rung.

include(deps-helper)

set(NlohmannJson_FOUND FALSE)

if(NLOHMANN_JSON_DIR)
    # Rung 0.
    find_path(NLOHMANN_JSON_INCLUDE_DIR NAMES nlohmann/json.hpp
              PATHS ${NLOHMANN_JSON_DIR} ${NLOHMANN_JSON_DIR}/include
              NO_DEFAULT_PATH)
    if(NOT NLOHMANN_JSON_INCLUDE_DIR)
        message(FATAL_ERROR
            "NLOHMANN_JSON_DIR is '${NLOHMANN_JSON_DIR}', but there is no "
            "nlohmann/json.hpp in it or in its include/ directory.")
    endif()
elseif(NOT STP_DEPS_LOCAL_ONLY)
    # Rung 1, which STP_DEPS_LOCAL_ONLY skips.
    find_path(NLOHMANN_JSON_INCLUDE_DIR NAMES nlohmann/json.hpp)
endif()

if(NOT NLOHMANN_JSON_INCLUDE_DIR)
    message(FATAL_ERROR
        "STP_BUILD_PARALLEL needs nlohmann/json (stp-p's reports). Install "
        "it (Debian/Ubuntu: nlohmann-json3-dev) or point NLOHMANN_JSON_DIR "
        "at a copy, or configure with -DSTP_BUILD_PARALLEL=OFF.")
endif()
# stp-p's reports keep their keys in order (nlohmann::ordered_json), which
# arrived in 3.9.0. The version macros are in json.hpp itself up to 3.10, and
# in detail/abi_macros.hpp from 3.11 on.
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
set(NlohmannJson_FOUND TRUE)

# SYSTEM: upstream code whose warnings STP does not control.
add_library(NlohmannJson INTERFACE IMPORTED GLOBAL)
set_target_properties(NlohmannJson PROPERTIES
    INTERFACE_INCLUDE_DIRECTORIES "${NLOHMANN_JSON_INCLUDE_DIR}"
    INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${NLOHMANN_JSON_INCLUDE_DIR}"
)

mark_as_advanced(NlohmannJson_FOUND)
mark_as_advanced(NLOHMANN_JSON_INCLUDE_DIR)

message(STATUS "Found nlohmann/json ${NLOHMANN_JSON_VERSION}: ${NLOHMANN_JSON_INCLUDE_DIR}")
