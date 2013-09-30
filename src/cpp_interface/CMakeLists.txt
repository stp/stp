include_directories(${CMAKE_SOURCE_DIR}/src/AST/)
include_directories(${CMAKE_BINARY_DIR}/src/AST/)

add_library(cppinterface OBJECT
    cpp_interface.cpp
)

add_dependencies(cppinterface ASTKind_header)

# -----------------------------------------------------------------------------
# Copy over public headers
# -----------------------------------------------------------------------------

set(public_headers cpp_interface.h)
copy_public_headers(cppinterface "${public_headers}")
