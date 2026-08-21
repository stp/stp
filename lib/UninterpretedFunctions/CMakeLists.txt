add_library(uninterpretedfunctions OBJECT
    UFDecl.cpp
    UFContext.cpp
    UFLowering.cpp
)

add_dependencies(uninterpretedfunctions ASTKind_header)
