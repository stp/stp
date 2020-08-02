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

find_package(Perl)

set(AST_KIND_HEADER_LOCATION "${PROJECT_BINARY_DIR}/include/stp/AST/ASTKind.h")
if(NOT STP_TIMESTAMPS)
  set(GK_FLAGS "--no-timestamp")
endif()
add_custom_command(
    OUTPUT  ${CMAKE_CURRENT_BINARY_DIR}/ASTKind.cpp ${AST_KIND_HEADER_LOCATION}
    COMMAND ${PERL_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/genkinds.pl ${GK_FLAGS} --file ${CMAKE_CURRENT_SOURCE_DIR}/ASTKind.kinds
    COMMAND ${CMAKE_COMMAND} -E make_directory ${PROJECT_BINARY_DIR}/include/stp/AST
    COMMAND ${CMAKE_COMMAND} -E rename ${CMAKE_CURRENT_BINARY_DIR}/ASTKind.h ${AST_KIND_HEADER_LOCATION}
    MAIN_DEPENDENCY ${CMAKE_CURRENT_SOURCE_DIR}/genkinds.pl
    DEPENDS ASTKind.kinds
)

add_custom_target(ASTKind_header ALL DEPENDS ${AST_KIND_HEADER_LOCATION})

add_library(AST OBJECT
    ${CMAKE_CURRENT_BINARY_DIR}/ASTKind.cpp
    ASTInterior.cpp
    ASTNode.cpp
    ASTUtil.cpp
    ASTBVConst.cpp
    ASTmisc.cpp
    ASTSymbol.cpp
    MutableASTNode.cpp
)

add_dependencies(AST ASTKind_header)
