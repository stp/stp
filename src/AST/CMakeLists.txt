add_custom_command(
    OUTPUT  ${CMAKE_CURRENT_BINARY_DIR}/ASTKind.cpp  ${CMAKE_CURRENT_BINARY_DIR}/ASTKind.h
    COMMAND perl ${CMAKE_CURRENT_SOURCE_DIR}/genkinds.pl --file ${CMAKE_CURRENT_SOURCE_DIR}/ASTKind.kinds
    DEPENDS ASTKind.kinds
)

add_custom_target(ASTKind_header ALL DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/ASTKind.h)
include_directories(${CMAKE_CURRENT_BINARY_DIR})

add_library(AST OBJECT
    ${CMAKE_CURRENT_BINARY_DIR}/ASTKind.cpp
    ArrayTransformer.cpp
    ASTInterior.cpp
    ASTNode.cpp
    ASTUtil.cpp
    ASTBVConst.cpp
    ASTmisc.cpp
    ASTSymbol.cpp
    RunTimes.cpp

    NodeFactory/HashingNodeFactory.cpp
    NodeFactory/NodeFactory.cpp
    NodeFactory/SimplifyingNodeFactory.cpp
    NodeFactory/TypeChecker.cpp
)

add_dependencies(AST ASTKind_header)
