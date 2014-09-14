add_library(tosat OBJECT
    BitBlaster.cpp
    ToSATBase.cpp
    AIG/BBNodeManagerAIG.cpp
    AIG/ToCNFAIG.cpp
    AIG/ToSATAIG.cpp
    ASTNode/ClauseList.cpp
    ASTNode/SimpBool.cpp
    ASTNode/ToCNF.cpp
    ASTNode/ToSAT.cpp
)

add_dependencies(tosat ASTKind_header)
