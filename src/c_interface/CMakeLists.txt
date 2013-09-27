#add_custom_target(ASTKind_header ALL DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/ASTKind.h)
include_directories(${CMAKE_SOURCE_DIR}/src/AST/)

add_library(cinterface
    c_interface.cpp
)

add_dependencies(cinterface ASTKind_header)

# -----------------------------------------------------------------------------
# Copy over public headers
# -----------------------------------------------------------------------------

set(public_headers c_interface.h)
foreach(public_header ${public_headers})
    add_custom_command(TARGET cinterface PRE_BUILD
                       COMMAND ${CMAKE_COMMAND} -E
                           echo Copying public header ${public_header}
                       COMMAND ${CMAKE_COMMAND} -E
                           copy ${CMAKE_CURRENT_SOURCE_DIR}/${public_header}
                                ${CMAKE_BINARY_DIR}/include/stp/${public_header}
                      )
endforeach()
