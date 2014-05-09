include_directories(${CMAKE_SOURCE_DIR}/src/AST/)
include_directories(${CMAKE_BINARY_DIR}/src/AST/)

add_library(cppinterface OBJECT
    cpp_interface.cpp
)

add_dependencies(cppinterface ASTKind_header)

stp_add_public_header(cppinterface cpp_interface.h)
