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
if(BUILD_EXECUTABLES)
    add_executable(stp-bin
        main.cpp
        main_common.cpp
    )
    # main_common.cpp reaches the generated ASTKind.h through NodeFactory.h,
    # and main.cpp the option registry's generated tables through
    # lib/Api/Internal.h, so name both generators here or a parallel build can
    # compile these TUs before their headers exist.
    add_dependencies(stp-bin ASTKind_header stp_api_tables)

    set_target_properties(stp-bin PROPERTIES
        OUTPUT_NAME stp
        RUNTIME_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}
        INSTALL_RPATH_USE_LINK_PATH TRUE
    )

    # The allocator goes on the executable, not on libstp: it must interpose
    # malloc for the whole process, and an embedder of libstp gets to keep
    # whatever allocator it chose. Listing it first keeps its definitions ahead
    # of libc for static archives.
    #
    # CLI11 is header-only and used by main.cpp alone, so all it contributes is
    # an include directory; nothing of it is linked. It is named here rather
    # than in a second target_link_libraries() call because CMake refuses to
    # mix the plain and keyword signatures on one target, and this one is
    # plain.
    target_link_libraries(stp-bin
        ${STP_ALLOCATOR_LIBRARY}
        stp
        CLI11
    )
    # main.cpp registers the command line from the 3.x option registry, whose
    # rows and appliers are declared in lib/Api/Internal.h: an in-tree header,
    # not an installed one, hence the source-tree include directory.
    target_include_directories(stp-bin PRIVATE ${PROJECT_SOURCE_DIR}/lib)

    install(TARGETS stp-bin
        RUNTIME DESTINATION "${CMAKE_INSTALL_BINDIR}"
    )
endif()
