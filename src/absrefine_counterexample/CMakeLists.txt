include_directories(${CMAKE_SOURCE_DIR}/src/AST/)
add_library(abstractionrefinement
    AbstractionRefinement.cpp
    CounterExample.cpp
)
add_dependencies(abstractionrefinement ASTKind_header)