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
# Create binary
# -----------------------------------------------------------------------------
# Everything the two front ends share: parsing, print-back, and the solve.
# They differ only in how they read their options. An object library so the
# translation unit is named once and compiled once, rather than stp_simple
# reaching across directories for ../stp/main_common.cpp.
#
# Built whenever executables are, including under ONLY_SIMPLE, where
# stp_simple is the only consumer.
if(BUILD_EXECUTABLES)
    add_library(stp_main_common OBJECT main_common.cpp)
    # main_common.cpp reaches the generated ASTKind.h through NodeFactory.h.
    # As a standalone object library it does not inherit the generator
    # dependency from libstp, so name it here or a parallel build can compile
    # this TU before ASTKind.h exists (as every other consumer target does).
    add_dependencies(stp_main_common ASTKind_header)
endif()

if(BUILD_EXECUTABLES AND NOT ONLY_SIMPLE)
    if(NOT EXISTS "${PROJECT_SOURCE_DIR}/lib/extlib-cli11/include/CLI/CLI.hpp")
        message(FATAL_ERROR "The CLI11 submodule is missing. Run: "
                            "git submodule update --init lib/extlib-cli11")
    endif()

    add_executable(stp-bin
        main.cpp
        $<TARGET_OBJECTS:stp_main_common>
    )

    # CLI11 is header-only and used by this one translation unit, so the
    # vendored include directory is all it needs; nothing is linked and
    # nothing leaks into libstp's link interface.
    target_include_directories(stp-bin PRIVATE
        "${PROJECT_SOURCE_DIR}/lib/extlib-cli11/include"
    )

    set_target_properties(stp-bin PROPERTIES
        OUTPUT_NAME stp
        RUNTIME_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}
        INSTALL_RPATH_USE_LINK_PATH TRUE
    )

    # The allocator goes on the executable, not on libstp: it must interpose
    # malloc for the whole process, and an embedder of libstp gets to keep
    # whatever allocator it chose. Listing it first keeps its definitions ahead
    # of libc for static archives.
    target_link_libraries(stp-bin
        ${STP_ALLOCATOR_LIBRARY}
        stp
    )

    install(TARGETS stp-bin
        RUNTIME DESTINATION "${CMAKE_INSTALL_BINDIR}"
    )
endif()
