# AUTHORS: Dan Liew, Ryan Gvostes, Mate Soos
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


# FIXME: Merge into one library
add_library(cinterface OBJECT
    c_interface.cpp
)

add_library(cppinterface OBJECT
    cpp_interface.cpp
)

add_dependencies(cinterface ASTKind_header)

# FIXME: Remove this
# For legacy reasons make the interface header files available in include/stp/ in the build directory
if (NOT ("${PROJECT_BINARY_DIR}" STREQUAL "${PROJECT_SOURCE_DIR}"))
    add_custom_target(CopyPublicHeaders ALL)
    set(HEADER_DEST "${PROJECT_BINARY_DIR}/include/stp")
    foreach(public_header c_interface.h cpp_interface.h)
        add_custom_command(TARGET CopyPublicHeaders PRE_BUILD
                           COMMAND ${CMAKE_COMMAND} -E make_directory ${HEADER_DEST}
                           COMMAND ${CMAKE_COMMAND} -E echo "LEGACY: Copying ${public_header} to ${HEADER_DEST}"
                           COMMAND ${CMAKE_COMMAND} -E copy_if_different "${PROJECT_SOURCE_DIR}/include/stp/${public_header}" "${HEADER_DEST}/${public_header}"
                          )
    endforeach()
endif()
