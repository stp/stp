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


# bison --debug -v -o parsecvc.cpp -d -p cvc cvc.y
# flex -Cfe -olexcvc.cpp -Pcvc cvc.lex
# bison --debug -v -o parsesmt.cpp -d -p smt smt.y
# flex -Cfe -olexsmt.cpp -Psmt smt.lex
# bison --debug -v -o parsesmt2.cpp -d -p smt2 smt2.y
# flex -Cfe -olexsmt2.cpp -Psmt2 smt2.lex
# Making dependencies
# rm parsesmt.hpp parsecvc.hpp parsesmt2.hpp
# make[1]: Leaving directory `/home/soos/development/stp-fast-prover-code/stp/src/parser'
# make[1]: Entering directory `/home/soos/development/stp-fast-prover-code/stp/src/parser'
# bison --debug -v -o parsecvc.cpp -d -p cvc cvc.y
# flex -Cfe -olexcvc.cpp -Pcvc cvc.lex
# bison --debug -v -o parsesmt.cpp -d -p smt smt.y
# flex -Cfe -olexsmt.cpp -Psmt smt.lex
# bison --debug -v -o parsesmt2.cpp -d -p smt2 smt2.y
# flex -Cfe -olexsmt2.cpp -Psmt2 smt2.lex

set(SOURCES LetMgr.cpp)
set(TOLEX cvc smt2 smt)
foreach(_file ${TOLEX})
    add_custom_command(
        OUTPUT  ${CMAKE_CURRENT_BINARY_DIR}/parse${_file}.cpp  ${CMAKE_CURRENT_BINARY_DIR}/lex${_file}.cpp
        COMMAND ${BISON_EXECUTABLE} --debug -v -o ${CMAKE_CURRENT_BINARY_DIR}/parse${_file}.cpp -d -p ${_file} ${CMAKE_CURRENT_SOURCE_DIR}/${_file}.y
        COMMAND ${FLEX_EXECUTABLE} -Cfe -o${CMAKE_CURRENT_BINARY_DIR}/lex${_file}.cpp -P${_file} ${CMAKE_CURRENT_SOURCE_DIR}/${_file}.lex
        DEPENDS ${_file}.lex ${_file}.y
    )
    add_custom_target(parser_header${_file} ALL
        DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/parse${_file}.cpp ${CMAKE_CURRENT_BINARY_DIR}/lex${_file}.cpp
    )
    set(SOURCES
        ${SOURCES}
        ${CMAKE_CURRENT_BINARY_DIR}/lex${_file}.cpp
        ${CMAKE_CURRENT_BINARY_DIR}/parse${_file}.cpp
    )
endforeach()

add_library(parser OBJECT
     ${SOURCES}
)

foreach(_file ${TOLEX})
    add_dependencies(parser parser_header${_file})
endforeach()

