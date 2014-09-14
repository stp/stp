add_library(stpglobals OBJECT
    Globals.cpp
)

add_dependencies(stpglobals ASTKind_header)
