include_directories(${CMAKE_SOURCE_DIR}/src/AST/)
include_directories(${CMAKE_BINARY_DIR}/src/AST/)

add_library(cinterface OBJECT
    c_interface.cpp
)

add_dependencies(cinterface ASTKind_header)

stp_add_public_header(cinterface c_interface.h)
