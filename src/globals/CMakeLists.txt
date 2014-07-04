add_library(stpglobals OBJECT
    Globals.cpp
)

add_dependencies(stpglobals ASTKind_header)

# Eurgh: Generated header is build directory, this added include might be needed elsewhere
include_directories(${CMAKE_BINARY_DIR}/src/AST)
