include_directories(${CMAKE_SOURCE_DIR}/src/AST/)
include_directories(${CMAKE_BINARY_DIR}/src/AST/)

add_library(tosat
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
target_link_libraries(tosat
    printer
)