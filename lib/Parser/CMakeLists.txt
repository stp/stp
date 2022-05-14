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

include(CheckIncludeFile)

set(SOURCES LetMgr.cpp)
set(TOLEX cvc smt2 smt)

check_include_file("unistd.h" HAVE_UNISTD_H)
if (HAVE_UNISTD_H)
  set(FLEX_COMPATIBILITY_ARGS "")
else()
  set(FLEX_COMPATIBILITY_ARGS "--nounistd")
endif()

foreach(_file ${TOLEX})
    add_custom_command(
        OUTPUT  ${CMAKE_CURRENT_BINARY_DIR}/parse${_file}.tab.cpp ${CMAKE_CURRENT_BINARY_DIR}/parse${_file}.tab.h ${CMAKE_CURRENT_BINARY_DIR}/lex${_file}.cpp

        COMMAND ${BISON_EXECUTABLE} --debug -v -b ${CMAKE_CURRENT_BINARY_DIR}/parse${_file} -d -Dapi.prefix={${_file}} ${CMAKE_CURRENT_SOURCE_DIR}/${_file}.y

        COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_BINARY_DIR}/parse${_file}.tab.c ${CMAKE_CURRENT_BINARY_DIR}/parse${_file}.tab.cpp

        COMMAND ${FLEX_EXECUTABLE} ${FLEX_COMPATIBILITY_ARGS} -Ce --header-file=${CMAKE_CURRENT_BINARY_DIR}/${_file}_flex_header.h -o${CMAKE_CURRENT_BINARY_DIR}/lex${_file}.cpp --prefix=${_file} ${CMAKE_CURRENT_SOURCE_DIR}/${_file}.lex

        DEPENDS ${_file}.lex ${_file}.y ASTKind_header
    )
    add_custom_target(parser_header${_file} ALL
        DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/parse${_file}.tab.cpp ${CMAKE_CURRENT_BINARY_DIR}/lex${_file}.cpp
    )

    set(SOURCES
        ${SOURCES}
        ${CMAKE_CURRENT_BINARY_DIR}/lex${_file}.cpp
        ${CMAKE_CURRENT_BINARY_DIR}/parse${_file}.tab.cpp
    )
    if (NOT MSVC)
        set_source_files_properties(lex${_file}.cpp
            PROPERTIES COMPILE_FLAGS
            "-Wno-unneeded-internal-declaration -Wno-unreachable-code")
    endif()
endforeach()

add_library(parser OBJECT
     ${SOURCES}
)

foreach(_file ${TOLEX})
    add_dependencies(parser parser_header${_file})
endforeach()

