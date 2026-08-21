add_library(uninterpretedfunctions OBJECT
    UFDecl.cpp
    UFContext.cpp
    UFLowering.cpp
    UFChecker.cpp
    UFLemma.cpp
    UFModel.cpp
)

add_dependencies(uninterpretedfunctions ASTKind_header)
