include_directories("/home/soos/development/smt/libabc/src")
add_definitions(-DLIN64 -DSIZEOF_VOID_P=8 -DSIZEOF_LONG=8 -DSIZEOF_INT=4)

add_library(tosat OBJECT
    BitBlaster.cpp
    ToSATBase.cpp
    AIG/BBNodeManagerAIG.cpp
    AIG/ToCNFAIG.cpp
    AIG/ToSATAIG.cpp
    AIG/BBNodeAIG.cpp
    ASTNode/ClauseList.cpp
    ASTNode/SimpBool.cpp
    ASTNode/ToCNF.cpp
    ASTNode/ToSAT.cpp
)

add_dependencies(tosat ASTKind_header)
