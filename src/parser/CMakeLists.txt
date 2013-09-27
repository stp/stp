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

include_directories(${CMAKE_SOURCE_DIR}/src/AST/)
include_directories(${CMAKE_CURRENT_BINARY_DIR})
include_directories(${CMAKE_CURRENT_SOURCE_DIR})

add_library(parser
     ${SOURCES}
)
target_link_libraries(parser
    cppinterface
)
foreach(_file ${TOLEX})
    add_dependencies(parser parser_header${_file})
endforeach()

