include_directories(${CMAKE_SOURCE_DIR}/src/AST/)
include_directories(${CMAKE_BINARY_DIR}/src/AST/)

add_library(abstractionrefinement OBJECT
    AbstractionRefinement.cpp
    CounterExample.cpp
)
add_dependencies(abstractionrefinement ASTKind_header)
