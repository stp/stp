# FIXME: Merge into one library
add_library(cinterface OBJECT
    c_interface.cpp
)

add_library(cppinterface OBJECT
    cpp_interface.cpp
)

add_dependencies(cinterface ASTKind_header)

# FIXME: Remove this
# For legacy reasons make the interface header files available in include/stp/ in the build directory
if (NOT ("${CMAKE_BINARY_DIR}" STREQUAL "${CMAKE_SOURCE_DIR}"))
    add_custom_target(CopyPublicHeaders ALL)
    set(HEADER_DEST "${PROJECT_BINARY_DIR}/include/stp")
    foreach(public_header c_interface.h cpp_interface.h)
        add_custom_command(TARGET CopyPublicHeaders PRE_BUILD
                           COMMAND ${CMAKE_COMMAND} -E make_directory ${HEADER_DEST}
                           COMMAND ${CMAKE_COMMAND} -E echo "LEGACY: Copying ${public_header} to ${HEADER_DEST}"
                           COMMAND ${CMAKE_COMMAND} -E copy_if_different "${PROJECT_SOURCE_DIR}/include/stp/${public_header}" "${HEADER_DEST}/${public_header}"
                          )
    endforeach()
endif()
