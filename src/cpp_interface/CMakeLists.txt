include_directories(${CMAKE_SOURCE_DIR}/src/AST/)
include_directories(${CMAKE_BINARY_DIR}/src/AST/)

add_library(cppinterface
    cpp_interface.cpp
)

add_dependencies(cppinterface ASTKind_header)