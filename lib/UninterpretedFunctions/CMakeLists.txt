add_library(uninterpretedfunctions OBJECT
    UFDecl.cpp
    UFContext.cpp
    UFPreLowering.cpp
    UFLowering.cpp
    UFChecker.cpp
    UFLemma.cpp
    UFRefinement.cpp
    UFModel.cpp
)

# UFModel.cpp reaches the exact-rational header, which includes <imrat.h>.
# For IMath's INTERFACE_INCLUDE_DIRECTORIES; see the note in
# lib/AbsRefineCounterExample/CMakeLists.txt.
target_link_libraries(uninterpretedfunctions PRIVATE IMath)

add_dependencies(uninterpretedfunctions ASTKind_header)
