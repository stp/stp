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

# Find CLI11, the header-only command-line parser the stp binary uses.
#
#   CLI11      imported interface target carrying the include path
#   CLI11_DIR  a directory containing CLI/CLI.hpp; rung 0 of the ladder in
#              cmake/deps-helper.cmake
#
# Only tools/stp/main.cpp includes it, so only that target links this.

include(deps-helper)

set(CLI11_FOUND_SYSTEM FALSE)

if(CLI11_DIR)
    # Rung 0.
    find_path(CLI11_INCLUDE_DIR NAMES CLI/CLI.hpp
              PATHS ${CLI11_DIR} ${CLI11_DIR}/include NO_DEFAULT_PATH)
    if(NOT CLI11_INCLUDE_DIR)
        message(FATAL_ERROR
            "CLI11_DIR is '${CLI11_DIR}', but there is no CLI/CLI.hpp in it "
            "or in its include/ directory.")
    endif()
    set(CLI11_FOUND_SYSTEM TRUE)
elseif(NOT STP_DEPS_LOCAL_ONLY)
    # Rung 1, which STP_DEPS_LOCAL_ONLY skips. CLI11 is header-only and widely
    # packaged, so this often answers.
    find_path(CLI11_INCLUDE_DIR NAMES CLI/CLI.hpp)
    if(CLI11_INCLUDE_DIR)
        set(CLI11_FOUND_SYSTEM TRUE)
    endif()
endif()

if(NOT CLI11_FOUND_SYSTEM)
    # Rungs 2 and 3.
    check_ep_downloaded("CLI11-EP")
    if(NOT CLI11-EP_DOWNLOADED)
        check_auto_download("CLI11" "")
    endif()

    set(CLI11_VERSION "2.7.2")
    set(CLI11_CHECKSUM "46eef3101da70852ec7af026e09d485ccee81813331c8c6052d39344443b83da")

    # Header-only, and CLI11's own CMake build does a good deal more than copy
    # headers -- tests, examples, a single-header generator -- none of which
    # STP wants. Copying include/CLI is the whole of what it needs.
    ExternalProject_Add(
        CLI11-EP
        ${STP_EP_COMMON_CONFIG}
        URL https://github.com/CLIUtils/CLI11/archive/refs/tags/v${CLI11_VERSION}.tar.gz
        URL_HASH SHA256=${CLI11_CHECKSUM}
        CONFIGURE_COMMAND ""
        BUILD_COMMAND ""
        INSTALL_COMMAND ${CMAKE_COMMAND} -E copy_directory
                        <SOURCE_DIR>/include/CLI <INSTALL_DIR>/include/CLI
    )
    add_dependencies(deps CLI11-EP)

    set(CLI11_INCLUDE_DIR "${STP_DEP_DIR}/include")
endif()

set(CLI11_FOUND TRUE)

# SYSTEM: CLI11 is upstream code whose warnings STP does not control, and it is
# a large header compiled into the one translation unit that includes it.
add_library(CLI11 INTERFACE IMPORTED GLOBAL)
set_target_properties(CLI11 PROPERTIES
    INTERFACE_INCLUDE_DIRECTORIES "${CLI11_INCLUDE_DIR}"
    INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${CLI11_INCLUDE_DIR}"
)

mark_as_advanced(CLI11_FOUND)
mark_as_advanced(CLI11_FOUND_SYSTEM)
mark_as_advanced(CLI11_INCLUDE_DIR)

if(CLI11_FOUND_SYSTEM)
    message(STATUS "Found CLI11: ${CLI11_INCLUDE_DIR}")
else()
    message(STATUS "Building CLI11 ${CLI11_VERSION}: ${CLI11_INCLUDE_DIR}")
    add_dependencies(CLI11 CLI11-EP)
endif()

# EOF
