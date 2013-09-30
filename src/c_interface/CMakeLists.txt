include_directories(${CMAKE_SOURCE_DIR}/src/AST/)
include_directories(${CMAKE_BINARY_DIR}/src/AST/)

add_library(cinterface OBJECT
    c_interface.cpp
)

add_dependencies(cinterface ASTKind_header)

# -----------------------------------------------------------------------------
# Copy over public headers
# -----------------------------------------------------------------------------

set(public_headers c_interface.h)
copy_public_headers(cinterface "${public_headers}")
