#add_custom_target(ASTKind_header ALL DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/ASTKind.h)
include_directories(${CMAKE_CURRENT_BINARY_DIR}/../AST/)

add_library(cinterface
    c_interface.cpp
)

add_dependencies(cinterface ASTKind_header)