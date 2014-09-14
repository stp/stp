add_library(stpmgr OBJECT
    STP.cpp
    STPManager.cpp
)

add_dependencies(stpmgr ASTKind_header)
