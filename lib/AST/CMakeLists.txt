find_package(Perl)

set(AST_KIND_HEADER_LOCATION "${CMAKE_BINARY_DIR}/include/stp/AST/ASTKind.h")
add_custom_command(
    OUTPUT  ${CMAKE_CURRENT_BINARY_DIR}/ASTKind.cpp ${AST_KIND_HEADER_LOCATION}
    COMMAND ${PERL_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/genkinds.pl --file ${CMAKE_CURRENT_SOURCE_DIR}/ASTKind.kinds
    COMMAND ${CMAKE_COMMAND} -E make_directory ${CMAKE_BINARY_DIR}/include/stp/AST
    COMMAND ${CMAKE_COMMAND} -E rename ${CMAKE_CURRENT_BINARY_DIR}/ASTKind.h ${AST_KIND_HEADER_LOCATION}
    DEPENDS ASTKind.kinds
)

add_custom_target(ASTKind_header ALL DEPENDS ${AST_KIND_HEADER_LOCATION})

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
