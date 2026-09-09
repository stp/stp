add_library(uninterpretedfunctions OBJECT
    UFDecl.cpp
    UFContext.cpp
    UFPreLowering.cpp
    UFLowering.cpp
    UFChecker.cpp
    UFLemma.cpp
    UFRefinement.cpp
    UFCongruencePropagator.cpp
    UFModel.cpp
)

add_dependencies(uninterpretedfunctions ASTKind_header)
