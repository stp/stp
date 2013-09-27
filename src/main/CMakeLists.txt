include_directories(${CMAKE_CURRENT_BINARY_DIR}/../AST/)

configure_file("${CMAKE_CURRENT_SOURCE_DIR}/GitSHA1.cpp.in" "${CMAKE_CURRENT_BINARY_DIR}/GitSHA1.cpp" @ONLY)

add_library(globalstp
    Globals.cpp
    ${CMAKE_CURRENT_BINARY_DIR}/GitSHA1.cpp
)
